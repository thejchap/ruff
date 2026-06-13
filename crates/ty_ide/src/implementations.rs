use crate::goto::{Definitions, GotoTarget};
use crate::scan::scan_project_files;
use crate::{Db, NavigationTargets, RangedValue};
use ruff_db::files::{File, FileRange};
use ruff_db::source::source_text;
use ruff_text_size::Ranged;
use ty_python_semantic::{
    ImplementationRoot, ResolvedDefinition, SemanticModel, contains_identifier,
    implementation_class_definitions_for_file, implementation_member_definitions_for_file,
    implementation_mro_member_definitions, implementation_root_definition,
    implementation_root_for_class, implementation_root_for_method,
    implementation_roots_for_attribute, implementation_roots_for_class_reference,
};

const MAX_MIN_FILES_PER_PARALLEL_JOB: usize = 64;

pub(crate) fn implementations(
    db: &dyn Db,
    file: File,
    goto_target: &GotoTarget,
) -> Option<RangedValue<NavigationTargets>> {
    let model = SemanticModel::new(db, file);

    let implementations = match goto_target {
        GotoTarget::Expression(ruff_python_ast::ExprRef::Attribute(attribute))
        | GotoTarget::Call {
            callable: ruff_python_ast::ExprRef::Attribute(attribute),
            ..
        } => member_implementations(
            db,
            implementation_roots_for_attribute(&model, attribute),
            attribute.attr.as_str(),
        ),
        GotoTarget::Expression(ruff_python_ast::ExprRef::Name(name))
        | GotoTarget::Call {
            callable: ruff_python_ast::ExprRef::Name(name),
            ..
        } => class_implementations(db, implementation_roots_for_class_reference(&model, name)),
        GotoTarget::FunctionDef(function) => implementation_root_for_method(&model, function)
            .map(|root| member_implementations(db, vec![root], function.name.as_str()))
            .unwrap_or_default(),
        GotoTarget::ClassDef(class) => implementation_root_for_class(&model, class)
            .map(|root| class_implementations(db, vec![root]))
            .unwrap_or_default(),
        _ => return None,
    };

    if implementations.is_empty() {
        return None;
    }

    let implementation_targets = Definitions::new(implementations)
        .map_stubs_for_implementation(model.db())?
        .into_navigation_targets(model.db());

    Some(RangedValue {
        range: FileRange::new(file, goto_target.range()),
        value: implementation_targets,
    })
}

fn member_implementations<'db>(
    db: &'db dyn Db,
    roots: Vec<ImplementationRoot<'db>>,
    member_name: &str,
) -> Vec<ResolvedDefinition<'db>> {
    let mut definitions = Vec::new();

    for root in roots {
        let root_definitions = implementation_mro_member_definitions(db, root, member_name);

        // If the root class has no MRO-selected member, don't return subclass-only definitions for
        // the same name.
        if root_definitions.is_empty() {
            continue;
        }

        for definition in root_definitions {
            if !definitions.contains(&definition) {
                definitions.push(definition);
            }
        }

        for file in scan_project_files(db, MAX_MIN_FILES_PER_PARALLEL_JOB, |db, file| {
            if contains_identifier(&source_text(db, file), member_name) {
                vec![file]
            } else {
                Vec::new()
            }
        }) {
            for definition in
                implementation_member_definitions_for_file(db, file, root, member_name)
            {
                if !definitions.contains(&definition) {
                    definitions.push(definition);
                }
            }
        }
    }

    definitions
}

fn class_implementations<'db>(
    db: &'db dyn Db,
    roots: Vec<ImplementationRoot<'db>>,
) -> Vec<ResolvedDefinition<'db>> {
    let mut definitions = Vec::new();

    for root in roots {
        if let Some(root_definition) = implementation_root_definition(db, root) {
            if !definitions.contains(&root_definition) {
                definitions.push(root_definition);
            }
        }

        for file in scan_project_files(db, MAX_MIN_FILES_PER_PARALLEL_JOB, |_db, file| vec![file]) {
            for definition in implementation_class_definitions_for_file(db, file, root) {
                if !definitions.contains(&definition) {
                    definitions.push(definition);
                }
            }
        }
    }

    definitions
}
