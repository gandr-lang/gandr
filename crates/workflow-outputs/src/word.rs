//! The word of a change for a kind of output.
//!
//! A change of an output that nobody intended must fail, as a golden file
//! fails it. A commit that intends the change says so with the trailer
//! `Changes-output: <kind>`. One trailer can name two or more kinds, with a
//! comma or a space between them.

use std::path::Path;
use std::process::Command;
use std::process::Stdio;

use crate::store::Kind;

/// The key of the trailer that names the kinds whose values a commit changes.
pub const TRAILER: &str = "Changes-output";

/// Whether `trailers` names `kind`. Each line of `trailers` is the value of
/// one trailer.
///
/// # Specification
/// - ensures: true when one word of one line is the name of the kind. A word
///   ends at a comma, a space or a tab.
///
/// # Adequacy
/// - hypothesis: L3 — a value with two kinds names each one, and a word that
///   starts with the name of a kind does not name the kind.
/// - witness: `word::tests::a_trailer_names_each_kind_that_it_lists`
#[inline]
#[must_use]
pub fn names(
    trailers: &str,
    kind: Kind,
) -> bool
{
    trailers
        .lines()
        .flat_map(|line| line.split([',', ' ', '\t']))
        .any(|word| word == kind.0)
}

/// Whether a commit of `base..head` of the repository `root` names `kind` in
/// a trailer. With no head, the range ends at `HEAD`: a change of the work
/// tree that no commit holds has no word.
///
/// # Specification
/// - ensures: the answer of [`names`] for the values of the trailer in the
///   commits of the range.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// One line when git does not start, or when it refuses the range.
#[inline]
pub fn named(
    root: &Path,
    base: &str,
    head: Option<&str>,
    kind: Kind,
) -> Result<bool, String>
{
    let range = format!("{base}..{}", head.unwrap_or("HEAD"));
    let format = format!("--format=%(trailers:key={TRAILER},valueonly=true)");
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["log", format.as_str(), range.as_str()])
        .stdin(Stdio::null())
        .output()
        .map_err(|error| format!("git log: {error}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!(
            "git log {range}: {}",
            stderr
                .lines()
                .rev()
                .find(|line| !line.trim().is_empty())
                .unwrap_or("no message")
        ));
    }
    Ok(names(&String::from_utf8_lossy(&output.stdout), kind))
}

#[cfg(test)]
mod tests
{
    use super::names;
    use crate::compute::RECOVERY;
    use crate::compute::ROLES;

    /// A trailer names each kind that it lists, and no other kind.
    #[test]
    fn a_trailer_names_each_kind_that_it_lists()
    {
        assert!(names("roles\n", ROLES), "one kind on one line");
        assert!(
            !names("roles\n", RECOVERY),
            "a kind that the line does not list"
        );
        assert!(names("recovery, roles\n", ROLES), "the second of two kinds");
        assert!(
            names("recovery, roles\n", RECOVERY),
            "the first of two kinds"
        );
        assert!(
            names("\nrecovery\n\nroles\n", ROLES),
            "a kind of a second commit"
        );
        assert!(
            !names("roles-of-a-sort\n", ROLES),
            "a word that starts with the name"
        );
        assert!(!names("", ROLES), "no trailer");
    }
}
