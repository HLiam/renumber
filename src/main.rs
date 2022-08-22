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

trait SliceExt {
    fn natural_sort_unstable(&mut self);
}

impl<S: AsRef<OsStr>> SliceExt for [S] {
    fn natural_sort_unstable(&mut self) {
        self.sort_unstable_by(|a, b| {
            natord::compare_ignore_case(
                &a.as_ref().to_string_lossy(),
                &b.as_ref().to_string_lossy(),
            )
        })
    }
}

// TODO: change this to use Anyhow.
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
    fn should_ignore(p: impl AsRef<Path>) -> bool {
        p.as_ref().ends_with("desktop.ini")
    }

    let glob_options = glob::MatchOptions {
        case_sensitive: false,
        require_literal_separator: false,
        require_literal_leading_dot: true,
    };

    let paths = glob::glob_with(pattern, glob_options)
        .map_err(|_| Error::InvalidPattern(pattern.to_string()))?
        .filter(|r| r.as_ref().map(|p| !should_ignore(p)).unwrap_or(true))
        .collect::<Result<Vec<_>, _>>()?;

    let file_types = paths
        .iter()
        .map(|p| {
            fs::symlink_metadata(p)
                .map(|m| m.file_type())
                .map_renumber_err(|| p.clone())
        })
        .collect::<Result<Vec<_>, _>>()?;

    if file_types.iter().all(|m| m.is_file()) {
        Ok(vec![paths])
    } else if file_types.iter().all(|m| m.is_dir()) {
        paths
            .into_iter()
            .map(|dir| {
                dir.read_dir()
                    .map_renumber_err(|| dir.clone())?
                    .filter_map(|maybe_entry| {
                        match maybe_entry.map(|entry| (entry.file_type(), entry.path())) {
                            Ok((Ok(m), p)) if !should_ignore(&p) && m.is_file() => Some(Ok(p)),
                            Ok((Ok(_), _)) => None,
                            Ok((Err(e), p)) => Some(Err(Error::Io(e, p))),
                            Err(e) => Some(Err(Error::Io(e, dir.clone()))),
                        }
                    })
                    .collect()
            })
            .collect()
    } else {
        Err(Error::MixedFileSystemObjects)
    }
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
        dir.natural_sort_unstable();
    }

    for dir in &dirs {
        // TODO: use `{int}::log10` when it's stabilized.
        let padding = (dir.len() as f64).log10().floor() as usize + 1;
        for (n, path) in dir.iter().enumerate() {
            path.rename(path.with_stem(format!("{:0padding$}", n + 1, padding = padding)))?;
        }
    }

    Ok(dirs.iter().map(|dir| dir.len()).sum())
}

fn main() {
    match env::args().nth(1).as_deref() {
        None | Some("-h" | "--help") => println!("Usage: renumber [-h] [--help] PATTERN"),
        Some(pattern) => match run(pattern) {
            Ok(count) => println!(
                "Renumbered {count} file{}",
                if count == 1 { "" } else { "s" }
            ),
            Err(err_msg) => eprintln!("Error: {err_msg}"),
        },
    }
}
