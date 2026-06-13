use crate::reachability::is_range_reachable;
use crate::types::{ClassBase, ClassLiteral, Type, TypeVarBoundOrConstraints, binding_type};
use crate::{Db, HasDefinition, HasType, SemanticModel};
use ruff_db::parsed::parsed_module;
use ruff_python_ast as ast;
use ruff_text_size::Ranged;
use rustc_hash::FxHashSet;
use ty_python_core::definition::{Definition, DefinitionKind};
use ty_python_core::{attribute_scopes, semantic_index, use_def_map};

use super::{
    ImportAliasResolution, ResolvedDefinition, definitions_for_name, extract_class_literal,
    reachable_definitions,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ImplementationRoot<'db>(ClassLiteral<'db>);

/// Returns implementation roots for an attribute expression `x.y`.
///
/// ```py
/// def f(animal: Animal):
///     animal.sound
///            ^^^^^
/// ```
///
/// For a receiver of type `Animal`, this returns `Animal` as the root. For a receiver of type
/// `Dog`, the root is `Dog`: inherited behavior resolves through `Dog`'s MRO, and sibling classes
/// such as `Cat` are not included.
pub fn implementation_roots_for_attribute<'db>(
    model: &SemanticModel<'db>,
    attribute: &ast::ExprAttribute,
) -> Vec<ImplementationRoot<'db>> {
    let db = model.db();

    let Some(lhs_ty) = attribute.value.inferred_type(model) else {
        return Vec::new();
    };

    let mut roots = Vec::new();
    let mut seen = FxHashSet::default();
    collect_implementation_root_classes(db, lhs_ty, &mut seen, &mut roots);
    roots.into_iter().map(ImplementationRoot).collect()
}

/// Returns the implementation root for a method declaration.
///
/// ```py
/// class Animal:
///     def speak(self): ...
///         ^^^^^
///
/// class Dog(Animal):
///     def speak(self): ...
/// ```
///
/// The containing class is used as the root. This does not walk to parent classes: on `Dog.speak`,
/// the root is `Dog`, so `Animal.speak` is not included.
pub fn implementation_root_for_method<'db>(
    model: &SemanticModel<'db>,
    function: &ast::StmtFunctionDef,
) -> Option<ImplementationRoot<'db>> {
    let db = model.db();
    let function_definition = function.definition(model);
    let containing_scope = function_definition.scope(db);

    let class_node = containing_scope.node(db).as_class()?;

    let class_definition =
        semantic_index(db, containing_scope.file(db)).expect_single_definition(class_node);
    let class_ty = binding_type(db, class_definition);
    extract_class_literal(db, class_ty).map(ImplementationRoot)
}

/// Returns the implementation root for a class declaration.
///
/// ```py
/// class Animal:
///       ^^^^^^
///     pass
///
/// class Dog(Animal): ...
/// class Cat(Animal): ...
/// ```
///
/// The clicked class is the root. This walks down the hierarchy only: clicking a subclass returns
/// that class and its own subclasses, not its parents.
pub fn implementation_root_for_class<'db>(
    model: &SemanticModel<'db>,
    class: &ast::StmtClassDef,
) -> Option<ImplementationRoot<'db>> {
    let db = model.db();
    extract_class_literal(db, binding_type(db, class.definition(model))).map(ImplementationRoot)
}

/// Returns implementation roots for a class reference, such as a base class, an annotation, or a
/// constructor call.
///
/// ```py
/// class Animal: ...
///
/// class Dog(Animal): ...
///           ^^^^^^
/// ```
///
/// Names that don't resolve to a class object (for example instance variables) return nothing.
///
/// The name is resolved to the definition it refers to rather than using its inferred value type,
/// because a class used as an annotation (`x: Animal`) infers as an instance of that class, which
/// is indistinguishable from an actual instance variable. The resolved definition's type is a class
/// object precisely when the name refers to a class.
pub fn implementation_roots_for_class_reference<'db>(
    model: &SemanticModel<'db>,
    name: &ast::ExprName,
) -> Vec<ImplementationRoot<'db>> {
    let db = model.db();
    let mut roots = Vec::new();
    let mut seen = FxHashSet::default();
    for resolved in definitions_for_name(
        model,
        name.id.as_str(),
        name.into(),
        ImportAliasResolution::ResolveAliases,
    ) {
        let ResolvedDefinition::Definition(definition) = resolved else {
            continue;
        };
        // Only references that resolve to a class object (a base class, annotation, `Animal()`, or
        // a name bound to a class) are class implementation requests; instances resolve to their
        // own definitions, whose type is the instance rather than the class object.
        let ty = binding_type(db, definition);
        let root = match ty {
            Type::ClassLiteral(_) | Type::SubclassOf(_) | Type::GenericAlias(_) => {
                extract_class_literal(db, ty)
            }
            _ => None,
        };
        let Some(root) = root else {
            continue;
        };
        if !seen.insert(root) {
            continue;
        }
        roots.push(ImplementationRoot(root));
    }
    roots
}

/// Returns the definition for an implementation root, if it has one.
pub fn implementation_root_definition<'db>(
    db: &'db dyn Db,
    root: ImplementationRoot<'db>,
) -> Option<ResolvedDefinition<'db>> {
    Some(ResolvedDefinition::Definition(root.0.definition(db)?))
}

/// Finds the member definition selected by normal Python MRO lookup for `root`.
///
/// ```py
/// class Animal:
///     def speak(self): ...
///
/// class Dog(Animal):
///     pass
///
/// class LoudDog(Dog):
///     def speak(self): ...
/// ```
///
/// For root `Dog` and member `speak`, this returns `Animal.speak` because that is the definition
/// `Dog` inherits through MRO.
///
/// The first entry is the definition that would be selected for the root class itself, using MRO
/// lookup. That matters for concrete subclasses that inherit a member without overriding it. After
/// that, callers can use `implementation_member_definitions_for_file` to scan candidate classes.
pub fn implementation_mro_member_definitions<'db>(
    db: &'db dyn Db,
    root: ImplementationRoot<'db>,
    member_name: &str,
) -> Vec<ResolvedDefinition<'db>> {
    mro_member_definitions(db, root.0, member_name)
}

/// Returns class implementations from `file` whose MRO contains `root`.
pub fn implementation_class_definitions_for_file<'db>(
    db: &'db dyn Db,
    file: ruff_db::files::File,
    root: ImplementationRoot<'db>,
) -> Vec<ResolvedDefinition<'db>> {
    let mut definitions = Vec::new();

    for candidate in reachable_class_literals_in_file(db, file) {
        if !class_mro_contains(db, candidate, root.0) {
            continue;
        }
        let Some(definition) = candidate.definition(db) else {
            continue;
        };
        let resolved = ResolvedDefinition::Definition(definition);
        if !definitions.contains(&resolved) {
            definitions.push(resolved);
        }
    }

    definitions
}

/// Returns member implementations from classes in `file` whose MRO contains `root`.
pub fn implementation_member_definitions_for_file<'db>(
    db: &'db dyn Db,
    file: ruff_db::files::File,
    root: ImplementationRoot<'db>,
    member_name: &str,
) -> Vec<ResolvedDefinition<'db>> {
    let mut definitions = Vec::new();

    for candidate in reachable_class_literals_in_file(db, file) {
        if !class_mro_contains(db, candidate, root.0) {
            continue;
        }

        for definition in own_member_definitions(db, candidate, member_name).unwrap_or_default() {
            if !definitions.contains(&definition) {
                definitions.push(definition);
            }
        }
    }

    definitions
}

/// Finds the member definition selected by normal Python MRO lookup for `class`.
///
/// This intentionally stops at the first class in the MRO that defines `member_name`; inherited
/// members should navigate to the definition that actually provides the behavior for the receiver.
fn mro_member_definitions<'db>(
    db: &'db dyn Db,
    class: ClassLiteral<'db>,
    member_name: &str,
) -> Vec<ResolvedDefinition<'db>> {
    class
        .iter_mro(db)
        .filter_map(ClassBase::into_class)
        .find_map(|class| own_member_definitions(db, class.class_literal(db), member_name))
        .unwrap_or_default()
}

fn reachable_class_literals_in_file(
    db: &dyn Db,
    file: ruff_db::files::File,
) -> Vec<ClassLiteral<'_>> {
    let index = semantic_index(db, file);
    let parsed = parsed_module(db, file).load(db);
    let mut classes = Vec::new();

    for scope_id in index.scope_ids() {
        let scope = scope_id.node(db);
        let Some(class_node) = scope.as_class() else {
            continue;
        };

        let definition = index.expect_single_definition(class_node);
        if !matches!(definition.kind(db), DefinitionKind::Class(_)) {
            continue;
        }

        let file_scope_id = scope_id.file_scope_id(db);
        if !is_range_reachable(db, index, file_scope_id, class_node.node(&parsed).range()) {
            continue;
        }

        if let Some(class) = extract_class_literal(db, binding_type(db, definition)) {
            classes.push(class);
        }
    }

    classes
}

fn class_mro_contains<'db>(
    db: &'db dyn Db,
    class: ClassLiteral<'db>,
    target: ClassLiteral<'db>,
) -> bool {
    class
        .iter_mro(db)
        .filter_map(ClassBase::into_class)
        .any(|class| class.class_literal(db) == target)
}

/// Returns member definitions for `member_name` that are declared directly in `class`.
///
/// ```py
/// class Animal:
///     def speak(self): ...
///
/// class Dog(Animal):
///     pass
///
/// class Cat(Animal):
///     def speak(self): ...
/// ```
///
/// For member `speak`, this returns nothing for `Dog` because it only inherits the member, but it
/// returns `Cat.speak` for `Cat` because it is defined directly in `Cat`.
///
/// A class-body definition (method or attribute) takes priority and determines this class's
/// contribution when present. Otherwise, instance attributes assigned in the class's own method
/// bodies (`self.member = ...`) are used.
///
/// Subclasses that only inherit the member do not add a new implementation target. The inherited
/// definition is already returned by the root MRO lookup; this only finds subclasses that define a
/// new method body or attribute.
///
/// Returns `None` if `class` has no reachable user-visible definitions for `member_name`. Returns
/// `Some` with an empty vector if the class defines the symbol but none of the reachable
/// definitions are implementation targets (`def` methods or attributes).
fn own_member_definitions<'db>(
    db: &'db dyn Db,
    class: ClassLiteral<'db>,
    member_name: &str,
) -> Option<Vec<ResolvedDefinition<'db>>> {
    let class = class.as_static()?;
    let class_scope = class.body_scope(db);

    let class_place_table = ty_python_core::place_table(db, class_scope);
    if let Some(place_id) = class_place_table.symbol_id(member_name) {
        let use_def = use_def_map(db, class_scope);
        let definitions = reachable_definitions(
            db,
            use_def
                .reachable_symbol_declarations(place_id)
                .filter_map(|declaration| declaration.declaration.definition())
                .chain(
                    use_def
                        .reachable_symbol_bindings(place_id)
                        .filter_map(|binding| binding.binding.definition()),
                ),
        );
        if !definitions.is_empty() {
            return Some(
                definitions
                    .into_iter()
                    .filter_map(|definition| member_implementation_definition(db, definition))
                    .collect(),
            );
        }
    }

    let file = class_scope.file(db);
    let index = semantic_index(db, file);
    let mut instance_definitions = Vec::new();
    for function_scope_id in attribute_scopes(db, class_scope) {
        let Some(place_id) = index
            .place_table(function_scope_id)
            .member_id_by_instance_attribute_name(member_name)
        else {
            continue;
        };
        let use_def = index.use_def_map(function_scope_id);
        instance_definitions.extend(
            use_def
                .reachable_member_declarations(place_id)
                .filter_map(|declaration| declaration.declaration.definition())
                .chain(
                    use_def
                        .reachable_member_bindings(place_id)
                        .filter_map(|binding| binding.binding.definition()),
                ),
        );
    }

    let instance_definitions = reachable_definitions(db, instance_definitions);
    if instance_definitions.is_empty() {
        return None;
    }
    Some(
        instance_definitions
            .into_iter()
            .filter_map(|definition| member_implementation_definition(db, definition))
            .collect(),
    )
}

/// Normalize a member definition to the implementation target that should be navigated to.
fn member_implementation_definition<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
) -> Option<ResolvedDefinition<'db>> {
    match definition.kind(db) {
        // `def` statements collapse overload declarations to their concrete implementation below.
        DefinitionKind::Function(_) => {}
        // Attribute definitions (`sound: str = ...`, `sound = ...`, a bare `sound: str`
        // declaration, or `self.sound = ...`) are implementation targets as-is.
        DefinitionKind::Assignment(_) | DefinitionKind::AnnotatedAssignment(_) => {
            return Some(ResolvedDefinition::Definition(definition));
        }
        // Other kinds (imports, comprehension targets, ...) can stop MRO lookup, but should not
        // themselves become implementation targets.
        _ => return None,
    }

    // Use the inferred function type to collapse overload declarations to their concrete
    // implementation. If inference cannot produce a function literal, keep the original `def` as a
    // conservative fallback.
    let Some(function) = binding_type(db, definition).as_function_literal() else {
        return Some(ResolvedDefinition::Definition(definition));
    };

    let (_, implementation) = function.overloads_and_implementation(db);
    if implementation.is_some() {
        return Some(ResolvedDefinition::Definition(function.last_definition(db)));
    }

    // Stub overload declarations can still map to a real source implementation later.
    if definition.file(db).is_stub(db) {
        return Some(ResolvedDefinition::Definition(definition));
    }

    // Non-stub overload-only groups have no runtime implementation to navigate to.
    None
}

/// Normalizes a receiver type into the class roots used for implementation lookup.
fn collect_implementation_root_classes<'db>(
    db: &'db dyn Db,
    ty: Type<'db>,
    seen: &mut FxHashSet<ClassLiteral<'db>>,
    roots: &mut Vec<ClassLiteral<'db>>,
) {
    match ty.resolve_type_alias(db) {
        Type::Union(union) => {
            // `pet: Dog | Cat` can dispatch through either `Dog` or `Cat`.
            for element in union.elements(db) {
                collect_implementation_root_classes(db, *element, seen, roots);
            }
        }
        Type::Intersection(intersection) => {
            // Finite intersections can stand for alternatives like `Dog` or `Cat`.
            if let Some(alternatives) = intersection.finite_alternatives(db) {
                for alternative in alternatives {
                    collect_implementation_root_classes(db, alternative, seen, roots);
                }
            }
        }
        Type::TypeVar(typevar) => match typevar.typevar(db).bound_or_constraints(db) {
            // `T: Animal` can dispatch through the `Animal` bound.
            Some(TypeVarBoundOrConstraints::UpperBound(bound)) => {
                collect_implementation_root_classes(db, bound, seen, roots);
            }
            // `T: (Dog, Cat)` can dispatch through either constraint.
            Some(TypeVarBoundOrConstraints::Constraints(constraints)) => {
                collect_implementation_root_classes(db, constraints.as_type(db), seen, roots);
            }
            None => {}
        },
        ty => {
            // `dog: Dog` maps directly to the `Dog` class root.
            let root = match ty {
                Type::ClassLiteral(_) | Type::GenericAlias(_) | Type::SubclassOf(_) => {
                    extract_class_literal(db, ty)
                }
                Type::NominalInstance(_)
                | Type::ProtocolInstance(_)
                | Type::KnownInstance(_)
                | Type::LiteralValue(_)
                | Type::TypedDict(_)
                | Type::NewTypeInstance(_) => extract_class_literal(db, ty)
                    .or_else(|| extract_class_literal(db, ty.to_meta_type(db))),
                _ => None,
            };

            if let Some(root) = root
                && seen.insert(root)
            {
                roots.push(root);
            }
        }
    }
}
