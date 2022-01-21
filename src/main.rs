use std::env;
use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

trait PathExt {
    fn with_stem(&self, stem: impl AsRef<OsStr>) -> PathBuf;
    fn rename(&self, to: impl AsRef<Path>) -> Result<(), Error>;
}

impl PathExt for Path {
    /// Creates an owned `PathBuf` like `self` but with the given file stem.
    ///
    /// # Examples
    /// ```
    /// use std::path::{Path, PathBuf};
    ///
    /// let path = Path::new("/tmp/foo.txt");
    /// assert_eq!(path.with_stem("bar"), PathBuf::from("/tmp/bar.txt"));
    /// ```
    fn with_stem(&self, stem: impl AsRef<OsStr>) -> PathBuf {
        let mut out = self.with_file_name(stem.as_ref());
        if let Some(ext) = self.extension() {
            out.set_extension(ext);
        }

        out
    }

    fn rename(&self, to: impl AsRef<Path>) -> Result<(), Error> {
        fs::rename(self, to).map_renumber_err(|| self.to_owned())
    }
}

#[derive(Debug)]
enum Error {
    UnsafePattern(String),
    InvalidPattern(String),
    MixedFileSystemObjects,
    Io(std::io::Error, PathBuf),
}

impl std::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;

        write!(
            f,
            "{}",
            match self {
                UnsafePattern(pattern) => format!("Pattern {pattern:?} is unsafe."),
                InvalidPattern(pattern) => format!("Invalid pattern \"{pattern}\"."),
                MixedFileSystemObjects => "Input contains both files and directories.".to_string(),
                Io(e, path) => format!("Couldn't access file or directory {path:?}: {e}"),
            }
        )
    }
}

impl From<glob::GlobError> for Error {
    fn from(e: glob::GlobError) -> Self {
        let path = e.path().to_owned();
        Self::Io(e.into_error(), path)
    }
}

trait ResultExt<T> {
    fn map_renumber_err(self, f: impl FnOnce() -> PathBuf) -> Result<T, Error>;
}

impl<T> ResultExt<T> for Result<T, std::io::Error> {
    fn map_renumber_err(self, f: impl FnOnce() -> PathBuf) -> Result<T, Error> {
        self.map_err(|e| Error::Io(e, f()))
    }
}

/// Get the paths to renumber.
///
/// If all of the paths are:
///    files: a single `Vec` of paths is returned.
///    directories: a `Vec` of the files (and only files) in each directory is returned.
///    mixed: an error is returned.
fn get_paths(pattern: &str) -> Result<Vec<Vec<PathBuf>>, Error> {
    let glob_options = glob::MatchOptions {
        case_sensitive: false,
        require_literal_separator: false,
        require_literal_leading_dot: true,
    };

    let paths = glob::glob_with(pattern, glob_options)
        .map_err(|_| Error::InvalidPattern(pattern.to_string()))?
        .collect::<Result<Vec<_>, _>>()?;

    let file_types = paths
        .iter()
        .map(|p| {
            fs::symlink_metadata(p)
                .map(|m| m.file_type())
                .map_renumber_err(|| p.clone())
        })
        .collect::<Result<Vec<_>, _>>()?;

    let mut out: Vec<Vec<PathBuf>> = if file_types.iter().all(|m| m.is_file()) {
        vec![paths]
    } else if file_types.iter().all(|m| m.is_dir()) {
        paths
            .into_iter()
            .map(|dir| {
                Ok(dir
                    .read_dir()
                    .map_renumber_err(|| dir.clone())?
                    .filter_map(|maybe_entry| match maybe_entry {
                        Ok(entry) => entry
                            .file_type()
                            .map_renumber_err(|| entry.path())
                            .map(|m| m.is_file().then(|| entry.path()))
                            .transpose(),
                        Err(e) => Some(Err(Error::Io(e, dir.clone()))),
                    })
                    .collect::<Result<Vec<_>, _>>()?)
            })
            .collect::<Result<Vec<_>, Error>>()?
    } else {
        return Err(Error::MixedFileSystemObjects);
    };

    for dir in &mut out {
        dir.retain(|p| !p.ends_with("desktop.ini"));
    }

    Ok(out)
}

/// Returns `true` if the pattern is unsafe, `false` otherwise.
///
/// A pattern is considered unsafe if it seems like something the user likely would never want to
/// do, like renumbering root.
fn check_unsafe_pattern(pattern: &str) -> bool {
    ["/", "/*", "/**", "/.", "/..", "/*/", "/**/", "/./", "/../"].contains(&pattern)
}

fn run(pattern: &str) -> Result<usize, Error> {
    if check_unsafe_pattern(pattern) {
        return Err(Error::UnsafePattern(pattern.to_string()));
    }

    let mut dirs = get_paths(pattern)?;
    for dir in &mut dirs {
        dir.sort_unstable_by(|a, b| {
            natord::compare_ignore_case(
                &a.as_os_str().to_string_lossy(),
                &b.as_os_str().to_string_lossy(),
            )
        });
    }

    for dir in &dirs {
        let padding = dir.len().to_string().len();
        for (n, path) in dir.iter().enumerate() {
            let new_path = path.with_stem(format!("{:0padding$}", n + 1, padding = padding));
            path.rename(new_path)?;
        }
    }

    Ok(dirs.iter().map(|dir| dir.len()).sum())
}

fn main() {
    match env::args().nth(1).as_deref() {
        None | Some("-h" | "--help") => println!("Usage: renumber [-h] [--help] PATTERN"),
        Some(pattern) => match run(pattern) {
            Ok(count) => println!("Renumbered {count} files"),
            Err(err_msg) => println!("Error: {err_msg}"),
        },
    }
}
