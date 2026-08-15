use std::fs;
use std::path::{Path, PathBuf};

/// Directories that contain generated output or vendored dependency trees.
/// Keeping this policy here prevents language frontends from drifting apart.
pub(crate) fn is_generated_directory(path: &Path) -> bool {
    matches!(
        path.file_name().and_then(|name| name.to_str()),
        Some(".git" | "target" | "_build" | "node_modules" | ".zig-cache" | "zig-out")
    )
}

pub(crate) fn contains_generated_component(path: &Path) -> bool {
    path.components().any(|component| {
        matches!(
            component.as_os_str().to_str(),
            Some(".git" | "target" | "_build" | "node_modules" | ".zig-cache" | "zig-out")
        )
    })
}

/// Collect source files deterministically while excluding generated trees.
/// A single file is accepted when its extension belongs to the frontend.
pub(crate) fn collect_source_files(
    path: &Path,
    extensions: &[&str],
) -> std::io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    if path.is_file() {
        if has_extension(path, extensions) {
            files.push(path.to_path_buf());
        }
    } else if path.is_dir() {
        collect_directory(path, extensions, &mut files)?;
    }
    files.sort_unstable();
    Ok(files)
}

/// Collect compiler artifacts under a generated tree. Unlike source walking,
/// this deliberately descends into `_build`/`target` when it is the root.
pub(crate) fn collect_files_with_extension(
    directory: &Path,
    extension: &str,
) -> std::io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    collect_all(directory, extension, &mut files)?;
    files.sort_unstable();
    Ok(files)
}

pub(crate) fn paths_match(left: &Path, right: &Path) -> bool {
    left == right
        || left
            .canonicalize()
            .ok()
            .zip(right.canonicalize().ok())
            .is_some_and(|(left, right)| left == right)
}

fn collect_directory(
    directory: &Path,
    extensions: &[&str],
    files: &mut Vec<PathBuf>,
) -> std::io::Result<()> {
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_unstable_by_key(fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            if !is_generated_directory(&path) {
                collect_directory(&path, extensions, files)?;
            }
        } else if file_type.is_file() && has_extension(&path, extensions) {
            files.push(path);
        }
    }
    Ok(())
}

fn collect_all(directory: &Path, extension: &str, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if !directory.is_dir() {
        return Ok(());
    }
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_unstable_by_key(fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            collect_all(&path, extension, files)?;
        } else if file_type.is_file()
            && path.extension().and_then(|value| value.to_str()) == Some(extension)
        {
            files.push(path);
        }
    }
    Ok(())
}

fn has_extension(path: &Path, extensions: &[&str]) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extensions.contains(&extension))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_directory_policy_is_shared_by_all_frontends() {
        for directory in [
            ".git",
            "target",
            "_build",
            "node_modules",
            ".zig-cache",
            "zig-out",
        ] {
            assert!(is_generated_directory(Path::new(directory)));
            assert!(contains_generated_component(
                Path::new("src").join(directory).as_path()
            ));
        }
        assert!(!is_generated_directory(Path::new("src")));
    }
}
