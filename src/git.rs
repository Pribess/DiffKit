use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::DiffkitResult;

static SNAPSHOT_SEQUENCE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GitEndpoint {
    Revision(String),
    Worktree,
}

impl GitEndpoint {
    pub fn label(&self) -> &str {
        match self {
            Self::Revision(revision) => revision,
            Self::Worktree => "worktree",
        }
    }
}

#[derive(Debug)]
pub struct GitComparison {
    pub root: PathBuf,
    pub before: GitEndpoint,
    pub after: GitEndpoint,
    pub changed_paths: Vec<PathBuf>,
    restricted: bool,
}

impl GitComparison {
    pub fn discover(
        directory: &Path,
        revisions: &[String],
        pathspecs: &[PathBuf],
    ) -> DiffkitResult<Self> {
        if revisions.len() > 2 {
            return Err(std::io::Error::other("git accepts zero, one, or two revisions").into());
        }
        let root = git_root(directory)?;
        let (before, after) = match revisions {
            [] => (
                GitEndpoint::Revision("HEAD".to_owned()),
                GitEndpoint::Worktree,
            ),
            [revision] => (
                GitEndpoint::Revision(format!("{revision}^")),
                GitEndpoint::Revision(revision.clone()),
            ),
            [before, after] => (
                GitEndpoint::Revision(before.clone()),
                GitEndpoint::Revision(after.clone()),
            ),
            _ => unreachable!("revision arity was checked before Git discovery"),
        };
        validate_endpoint(&root, &before)?;
        validate_endpoint(&root, &after)?;
        let changed_paths = changed_paths(&root, &before, &after, pathspecs)?;
        Ok(Self {
            root,
            before,
            after,
            changed_paths,
            restricted: !pathspecs.is_empty(),
        })
    }

    pub fn materialize(&self) -> DiffkitResult<(GitSnapshot, GitSnapshot)> {
        let before = GitSnapshot::create(&self.root, &self.before)?;
        let after = GitSnapshot::create(&self.root, &self.after)?;
        if self.restricted {
            restrict_snapshot(before.path(), after.path(), &self.changed_paths)?;
        }
        Ok((before, after))
    }
}

fn restrict_snapshot(before: &Path, after: &Path, selected_paths: &[PathBuf]) -> DiffkitResult<()> {
    let selected = selected_paths
        .iter()
        .map(|relative| {
            let source = after.join(relative);
            let contents = source.is_file().then(|| fs::read(source)).transpose()?;
            Ok((relative.clone(), contents))
        })
        .collect::<std::io::Result<Vec<_>>>()?;

    // Both directories are DiffKit-owned unique temporary snapshots. Rebase
    // the analysis-side `after` tree on `before`, then overlay only selected
    // Git changes.
    fs::remove_dir_all(after)?;
    fs::create_dir(after)?;
    copy_worktree(before, after)?;
    for (relative, contents) in selected {
        let destination = after.join(relative);
        match contents {
            Some(contents) => {
                if let Some(parent) = destination.parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::write(destination, contents)?;
            }
            None if destination.is_file() => fs::remove_file(destination)?,
            None if destination.is_dir() => fs::remove_dir_all(destination)?,
            None => {}
        }
    }
    Ok(())
}

#[derive(Debug)]
pub struct GitSnapshot {
    directory: PathBuf,
    label: String,
}

impl GitSnapshot {
    fn create(root: &Path, endpoint: &GitEndpoint) -> DiffkitResult<Self> {
        let sequence = SNAPSHOT_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "diffkit-git-snapshot-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory)?;
        let snapshot = Self {
            directory,
            label: endpoint.label().to_owned(),
        };
        match endpoint {
            GitEndpoint::Revision(revision) => snapshot.copy_revision(root, revision)?,
            GitEndpoint::Worktree => copy_worktree(root, snapshot.path())?,
        }
        Ok(snapshot)
    }

    pub fn path(&self) -> &Path {
        &self.directory
    }

    pub fn label(&self) -> &str {
        &self.label
    }

    fn copy_revision(&self, root: &Path, revision: &str) -> DiffkitResult<()> {
        let listing = git_output(root, ["ls-tree", "-r", "-z", "--name-only", revision])?;
        for raw_path in listing
            .split(|byte| *byte == 0)
            .filter(|path| !path.is_empty())
        {
            let relative = bytes_to_path(raw_path)?;
            let spec = format!("{revision}:{}", relative.to_string_lossy());
            let contents = git_output_bytes(root, [OsStr::new("show"), OsStr::new(&spec)])?;
            let destination = self.directory.join(&relative);
            if let Some(parent) = destination.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(destination, contents)?;
        }
        Ok(())
    }
}

impl Drop for GitSnapshot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

fn git_root(directory: &Path) -> DiffkitResult<PathBuf> {
    let output = git_output(directory, ["rev-parse", "--show-toplevel"])?;
    let root = String::from_utf8(output)?;
    Ok(PathBuf::from(root.trim()))
}

fn validate_endpoint(root: &Path, endpoint: &GitEndpoint) -> DiffkitResult<()> {
    if let GitEndpoint::Revision(revision) = endpoint {
        git_output(
            root,
            ["rev-parse", "--verify", &format!("{revision}^{{commit}}")],
        )?;
    }
    Ok(())
}

fn changed_paths(
    root: &Path,
    before: &GitEndpoint,
    after: &GitEndpoint,
    pathspecs: &[PathBuf],
) -> DiffkitResult<Vec<PathBuf>> {
    let mut arguments = vec![
        OsStr::new("diff"),
        OsStr::new("--no-renames"),
        OsStr::new("--name-only"),
        OsStr::new("-z"),
    ];
    let before_label;
    let after_label;
    match (before, after) {
        (GitEndpoint::Revision(before), GitEndpoint::Revision(after)) => {
            before_label = before.as_str();
            after_label = after.as_str();
            arguments.push(OsStr::new(before_label));
            arguments.push(OsStr::new(after_label));
        }
        (GitEndpoint::Revision(before), GitEndpoint::Worktree) => {
            before_label = before.as_str();
            arguments.push(OsStr::new(before_label));
        }
        (GitEndpoint::Worktree, _) => {
            return Err(std::io::Error::other("worktree can only be the after endpoint").into());
        }
    }
    if !pathspecs.is_empty() {
        arguments.push(OsStr::new("--"));
        arguments.extend(pathspecs.iter().map(|path| path.as_os_str()));
    }
    let output = git_output_bytes(root, arguments)?;
    let mut paths = output
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
        .map(bytes_to_path)
        .collect::<Result<BTreeSet<_>, _>>()?;

    if matches!(after, GitEndpoint::Worktree) {
        let mut untracked_args = vec![
            OsStr::new("ls-files"),
            OsStr::new("--others"),
            OsStr::new("--exclude-standard"),
            OsStr::new("-z"),
        ];
        if !pathspecs.is_empty() {
            untracked_args.push(OsStr::new("--"));
            untracked_args.extend(pathspecs.iter().map(|path| path.as_os_str()));
        }
        let untracked = git_output_bytes(root, untracked_args)?;
        for path in untracked
            .split(|byte| *byte == 0)
            .filter(|path| !path.is_empty())
        {
            paths.insert(bytes_to_path(path)?);
        }
    }
    Ok(paths.into_iter().collect())
}

fn copy_worktree(source: &Path, destination: &Path) -> DiffkitResult<()> {
    copy_directory(source, destination, source)
}

fn copy_directory(source: &Path, destination: &Path, root: &Path) -> DiffkitResult<()> {
    let mut entries = fs::read_dir(source)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let file_type = entry.file_type()?;
        let path = entry.path();
        let relative = path.strip_prefix(root).unwrap_or(&path);
        if should_skip(relative) {
            continue;
        }
        let target = destination.join(relative);
        if file_type.is_dir() {
            fs::create_dir_all(&target)?;
            copy_directory(&path, destination, root)?;
        } else if file_type.is_file() {
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::copy(path, target)?;
        } else if file_type.is_symlink() {
            let resolved = fs::canonicalize(&path)?;
            if resolved.starts_with(root) && resolved.is_file() {
                if let Some(parent) = target.parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::copy(resolved, target)?;
            }
        }
    }
    Ok(())
}

fn should_skip(relative: &Path) -> bool {
    relative.components().any(|component| {
        matches!(
            component.as_os_str().to_str(),
            Some(".git" | "target" | "_build" | "node_modules" | ".zig-cache" | "zig-out")
        )
    })
}

fn git_output<'a>(
    directory: &Path,
    arguments: impl IntoIterator<Item = &'a str>,
) -> DiffkitResult<Vec<u8>> {
    git_output_bytes(directory, arguments.into_iter().map(OsStr::new))
}

fn git_output_bytes<I, S>(directory: &Path, arguments: I) -> DiffkitResult<Vec<u8>>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let output = Command::new("git")
        .args(arguments)
        .current_dir(directory)
        .output()?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        let message = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        Err(std::io::Error::other(if message.is_empty() {
            format!("git exited with {}", output.status)
        } else {
            message
        })
        .into())
    }
}

#[cfg(unix)]
fn bytes_to_path(bytes: &[u8]) -> std::io::Result<PathBuf> {
    use std::os::unix::ffi::OsStrExt;
    Ok(PathBuf::from(OsStr::from_bytes(bytes)))
}

#[cfg(not(unix))]
fn bytes_to_path(bytes: &[u8]) -> std::io::Result<PathBuf> {
    String::from_utf8(bytes.to_vec())
        .map(PathBuf::from)
        .map_err(std::io::Error::other)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_revision_arity_before_running_git() {
        let error =
            GitComparison::discover(Path::new("."), &["a".into(), "b".into(), "c".into()], &[])
                .unwrap_err();
        assert!(error.to_string().contains("zero, one, or two"));
    }

    #[test]
    fn skips_generated_and_dependency_directories() {
        assert!(should_skip(Path::new("target/debug/app")));
        assert!(should_skip(Path::new("web/node_modules/pkg")));
        assert!(!should_skip(Path::new("src/main.rs")));
    }
}
