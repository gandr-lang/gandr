//! The list of the inputs of one check at one commit, and its digest.

use core::fmt;

use sha2::Digest as _;

use crate::name::Check;
use crate::name::Commit;

/// The SHA-256 of a text, as 64 hexadecimal digits.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Digest(String);

impl From<&[u8]> for Digest
{
    /// The digest of `text`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the SHA-256 of `text`, as 64 hexadecimal digits in lower
    ///   case.
    /// - provides: the digest that a record of a verdict binds.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the reference is SHA-256 itself, which the test
    ///   pins by two published vectors.
    ///
    /// # Cost
    /// - allocation: the 64 digits, growth within the size of a digest
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the published digests of the empty text and of `abc`;
    ///   a swapped nibble, a digit in upper case or a lost byte changes a
    ///   vector.
    /// - witness: `list::tests::a_digest_is_the_sha_256_of_its_text`
    #[inline]
    fn from(text: &[u8]) -> Self
    {
        let mut hex = String::with_capacity(64);
        for byte in sha2::Sha256::digest(text) {
            for nibble in [byte >> 4_u8, byte & 0x0f] {
                hex.push(char::from_digit(u32::from(nibble), 16).unwrap_or('0'));
            }
        }
        Self(hex)
    }
}

impl fmt::Display for Digest
{
    /// Writes the 64 digits.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a line of a digest ends with the digits, so writing
    ///   nothing changes the asserted line.
    /// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The inputs of one check at one commit, one line for each: the name of an
/// input, a tab, and its object or its digest.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct List(Vec<String>);

impl From<Vec<String>> for List
{
    /// The list whose lines are `lines`, in their order.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the list of the script on tree one; a list with no
    ///   line changes the asserted output.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    fn from(lines: Vec<String>) -> Self
    {
        Self(lines)
    }
}

impl List
{
    /// The digest of the list.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the SHA-256 of the lines in the order of their bytes, each
    ///   with a newline after it.
    /// - provides: one name for the inputs of a check, which two trees with the
    ///   same inputs share.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the reference is the script before this crate,
    ///   whose digests the cases pin.
    ///
    /// # Cost
    /// - allocation: the lines in order and their text, growth within the lines
    ///   of the list
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the digests of the script on three trees; the line of
    ///   the grep sorts between two paths, so a digest of the lines as they
    ///   stand, or with no newline, changes each pinned digest.
    /// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
    /// - witness: `tests::cli::a_changed_crate_changes_its_digest_and_runs_its_own_grep`
    #[inline]
    #[must_use]
    pub fn digest(&self) -> Digest
    {
        let mut ordered: Vec<&[u8]> = self.0.iter().map(String::as_bytes).collect();
        ordered.sort_unstable();
        let mut text: Vec<u8> = Vec::new();
        for line in ordered {
            text.extend_from_slice(line);
            text.push(b'\n');
        }
        Digest::from(text.as_slice())
    }
}

impl fmt::Display for List
{
    /// Writes each line in the order of the list, with a newline after it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the paths in their order, then the line of the table for a
    ///   check of the table, then the line of the task, then one line for each
    ///   grep.
    /// - provides: what `gate inputs list` prints.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the list of the script on tree one; a lost line or a
    ///   lost newline changes the asserted output.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for line in &self.0 {
            writeln!(f, "{line}")?;
        }
        Ok(())
    }
}

/// The list of one check at one commit, with both names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Listed
{
    /// The commit.
    commit: Commit,
    /// The check.
    check: Check,
    /// The inputs of the check at the commit.
    list: List,
}

impl Listed
{
    /// The list `list` of `check` at `commit`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each line of a digest holds the commit, the check and
    ///   the digest of its own pair, so two names in the other order change the
    ///   asserted lines.
    /// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
    #[inline]
    #[must_use]
    pub const fn new(
        commit: Commit,
        check: Check,
        list: List,
    ) -> Self
    {
        Self {
            commit,
            check,
            list,
        }
    }

    /// The commit of the list.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each line of a digest starts with the commit of its
    ///   pair, so the commit of another pair changes the asserted lines.
    /// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
    #[inline]
    #[must_use]
    pub const fn commit(&self) -> &Commit
    {
        &self.commit
    }

    /// The check of the list.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each line of a digest names the check of its pair, so
    ///   the check of another pair changes the asserted lines.
    /// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
    #[inline]
    #[must_use]
    pub const fn check(&self) -> &Check
    {
        &self.check
    }

    /// The inputs of the check at the commit.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the digest of a pair is the digest of its own list,
    ///   so the list of another pair changes the asserted digests.
    /// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
    #[inline]
    #[must_use]
    pub const fn list(&self) -> &List
    {
        &self.list
    }
}

#[cfg(test)]
mod tests
{
    use super::Digest;

    #[test]
    fn a_digest_is_the_sha_256_of_its_text()
    {
        assert_eq!(
            Digest::from(b"".as_slice()).to_string(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            Digest::from(b"abc".as_slice()).to_string(),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }
}
