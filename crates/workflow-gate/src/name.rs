//! The names that a run takes from its caller: a commit, a check and a scope.

use core::fmt;

/// A commit or a tree, as git reads the word.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Commit(String);

impl From<&str> for Commit
{
    /// Names the commit `word`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the word of the commit, setup
    ///
    /// # Adequacy
    /// - hypothesis: L2 — git reads each path at the commit by this word, so an
    ///   emptied word makes each object absent and changes the list of the
    ///   script.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    fn from(word: &str) -> Self
    {
        Self(word.to_owned())
    }
}

impl AsRef<str> for Commit
{
    /// The word of the commit.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — git reads each path at the commit by this word, so an
    ///   empty word makes each object absent and changes the list of the
    ///   script.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for Commit
{
    /// Writes the commit as the caller gave it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a line of a digest starts with its commit, so writing
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

/// A check, by the name of its task.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Check(String);

impl From<&str> for Check
{
    /// Names the check `task`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the name of the check, setup
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the check's name selects its row of the tables and
    ///   stands in the line of its task, so an emptied name changes the list of
    ///   the script.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    fn from(task: &str) -> Self
    {
        Self(task.to_owned())
    }
}

impl AsRef<str> for Check
{
    /// The name of the check's task.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the check's name selects its row of the tables, so an
    ///   empty name drops the line of the grep from the list of the script.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for Check
{
    /// Writes the check's task name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal names the check that mise does not list, so
    ///   writing nothing changes the asserted message.
    /// - witness: `tests::cli::a_check_that_mise_does_not_list_is_refused`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// A scope: the package flags of Cargo that select the crates of a check.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Scope(String);

impl From<&str> for Scope
{
    /// The scope that `flags` states.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the flags of the scope, setup
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each `--exclude` of the flags takes a crate out of
    ///   the scope, so an emptied scope keeps the directory of crate `c` in the
    ///   list of the script.
    /// - witness: `tests::cli::an_excluded_crate_stays_when_a_scoped_crate_needs_it`
    #[inline]
    fn from(flags: &str) -> Self
    {
        Self(flags.to_owned())
    }
}

impl AsRef<str> for Scope
{
    /// The flags of the scope.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each `--exclude` of the flags takes a crate out of
    ///   the scope, so empty flags keep the directory of crate `c` in the list
    ///   of the script.
    /// - witness: `tests::cli::an_excluded_crate_stays_when_a_scoped_crate_needs_it`
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}
