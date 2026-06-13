use crate::Db;
use rayon::prelude::*;
use ty_project::parallel::{ParallelIteratorExt, minimum_parallel_job_len};

/// Runs a caller-provided scan over every project file in parallel.
///
/// The scan closure owns feature-specific filtering, such as skipping the origin file or applying
/// a cheap identifier prefilter. Results are flattened in deterministic project path order, even
/// though each file is scanned concurrently.
pub(crate) fn scan_project_files<T, F>(
    db: &dyn Db,
    maximum_minimum_job_len: usize,
    scan_file: F,
) -> Vec<T>
where
    T: Send,
    F: Fn(&dyn Db, ruff_db::files::File) -> Vec<T> + Send + Sync,
{
    let project_files = db.project().files(db);
    let mut files: Vec<_> = project_files.iter().copied().collect();
    files.sort_by(|a, b| a.path(db).as_str().cmp(b.path(db).as_str()));
    let minimum_job_len = minimum_parallel_job_len(files.len(), maximum_minimum_job_len);
    files
        .into_par_iter()
        .with_min_len(minimum_job_len)
        .map_with_db(db, scan_file)
        .flat_map_iter(|file_results| file_results)
        .collect()
}
