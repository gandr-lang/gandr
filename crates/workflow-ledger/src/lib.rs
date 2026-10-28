//! **The debt ledger**: the findings a check has committed to owe, one key per
//! line, so a new finding refuses and a fixed one leaves its line stale. The
//! corpus comment gate and the prose check keep one each; what they key a
//! finding by is theirs, and the discipline is this crate's.
//!
//! - [`Ledger::read`] reads a ledger's text: one key per line, a blank line or
//!   a `#` line skipped.
//! - [`Ledger::check`] compares findings with it: each finding whose key the
//!   ledger lacks is new, each key no finding carries is stale ([`Verdict`]).
//! - [`write()`] gives the text that regenerates a ledger: the header as `#`
//!   lines, then each distinct key once, in the key's order.
//!
//! A key is any type that reads from a line ([`FromStr`]), writes back as one
//! ([`fmt::Display`]) and orders. The comment gate keys an item by its path,
//! name and digest with the kind beside it; the prose check by path, rule and
//! sentence digest. A key never holds a line number, so moving a finding keeps
//! its key and changing it retires the old one.

pub mod error;

extern crate alloc;

use alloc::collections::BTreeSet;
use core::fmt;
use core::fmt::Write as _;
use core::str::FromStr;

pub use crate::error::LedgerError;

/// A ledger's text, as read from its file or written to it.
///
/// # Specification
/// - provides: the bytes a ledger file holds.
#[derive(Clone, Copy, Debug)]
pub struct Text<'text>(pub &'text str);

/// A ledger's header: the lines written above its keys, each without the
/// `# ` [`write()`] gives it.
///
/// # Specification
/// - provides: what a ledger says of its own lines, for the reader who opens
///   the file.
#[derive(Clone, Copy, Debug)]
pub struct Header<'header>(pub &'header str);

/// The keys a ledger holds: the debt a check has committed to owe.
///
/// # Specification
/// - provides: the committed side of a check's comparison.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Ledger<K>
{
    /// The keys, each once, in order.
    held: BTreeSet<K>,
}

impl<K: Ord + FromStr> Ledger<K>
{
    /// The ledger `text` holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, one key per line that is neither blank nor a `#`
    ///   line once trimmed, each read from the trimmed line; a key written
    ///   twice is held once.
    /// - provides: the committed debt.
    /// - fails: [`LedgerError::Unread`] naming the first line no key reads
    ///   from.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written ledger reads back to its keys, a blank or
    ///   `#` line is no key, and the first unreadable line is the one named; a
    ///   skipped trim or a header read as a key changes the result.
    /// - witness: `tests::a_written_ledger_reads_back_and_skips_its_header`
    /// - witness: `tests::the_first_unreadable_line_is_named`
    #[inline]
    pub fn read(text: Text<'_>) -> Result<Self, LedgerError>
    {
        let mut held = BTreeSet::new();
        for line in text.0.lines().map(str::trim) {
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let Ok(key) = line.parse::<K>()
            else {
                return Err(LedgerError::Unread {
                    line: line.to_owned(),
                });
            };
            held.insert(key);
        }
        Ok(Self { held })
    }
}

impl<K: Ord> Ledger<K>
{
    /// What `findings` owe against the ledger, each finding keyed by `key`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Verdict::new`] holds the first finding of each key the
    ///   ledger lacks, in the findings' order; [`Verdict::stale`] each held key
    ///   no finding carries, in the keys' order.
    /// - provides: the check's verdict: clean exactly when both are empty.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the outcome is the verdict itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held finding, a new one, a repeated new one and a
    ///   stale key are four observations; a repeated finding counted twice or a
    ///   held key reported stale changes the verdict.
    /// - witness: `tests::a_new_finding_and_a_stale_key_are_each_named_once`
    #[inline]
    #[must_use]
    pub fn check<'findings, F, Keying>(
        &self,
        findings: &'findings [F],
        key: Keying,
    ) -> Verdict<'findings, '_, F, K>
    where
        Keying: Fn(&F) -> K,
    {
        let mut owed = BTreeSet::new();
        let mut new = Vec::new();
        for finding in findings {
            let owes = key(finding);
            if !self.held.contains(&owes) && !owed.contains(&owes) {
                new.push(finding);
            }
            owed.insert(owes);
        }
        let stale = self
            .held
            .iter()
            .filter(|held| !owed.contains(*held))
            .collect();
        Verdict { new, stale }
    }
}

/// What a check's findings owe against its ledger.
///
/// # Specification
/// - provides: the two ways findings and a ledger disagree, each named so the
///   check prints it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Verdict<'findings, 'ledger, F, K>
{
    /// The first finding of each key the ledger lacks, in the findings' order.
    pub new: Vec<&'findings F>,
    /// Each held key no finding carries, in the keys' order.
    pub stale: Vec<&'ledger K>,
}

impl<F, K> Verdict<'_, '_, F, K>
{
    /// Whether the findings and the ledger agree: nothing new and nothing
    /// stale.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Ledger::check`].
    /// - witness: `tests::a_new_finding_and_a_stale_key_are_each_named_once`
    #[inline]
    #[must_use]
    pub fn is_clean(&self) -> bool
    {
        self.new.is_empty() && self.stale.is_empty()
    }
}

/// The text that regenerates a ledger: `header`'s lines each as a `# ` line,
/// then each distinct key of `keys` once, in the key's order, every line ended
/// by a newline.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the result reads back through [`Ledger::read`] to the distinct
///   keys of `keys`, whenever each key's text reads back to it.
/// - provides: the bytes a check's write mode commits.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is the text itself.
///
/// # Adequacy
/// - hypothesis: L3 — two unsorted repeated keys under a two-line header write
///   in order, each once, under `#` lines; a missed sort, dedup or terminator
///   changes the text.
/// - witness: `tests::a_written_ledger_reads_back_and_skips_its_header`
#[inline]
#[must_use]
pub fn write<K, Keys>(
    header: Header<'_>,
    keys: Keys,
) -> String
where
    K: Ord + fmt::Display,
    Keys: IntoIterator<Item = K>,
{
    let mut text = String::new();
    for line in header.0.lines() {
        text.push_str("# ");
        text.push_str(line);
        text.push('\n');
    }
    let keys: BTreeSet<K> = keys.into_iter().collect();
    for key in &keys {
        writeln!(text, "{key}").unwrap_or_default();
    }
    text
}

#[cfg(test)]
mod tests
{
    use super::Header;
    use super::Ledger;
    use super::LedgerError;
    use super::Text;
    use super::write;

    #[test]
    fn a_written_ledger_reads_back_and_skips_its_header()
    {
        let text = write(Header("the debt\nwritten, never edited"), [
            "b z", "a m", "b z",
        ]);
        assert_eq!(text, "# the debt\n# written, never edited\na m\nb z\n");
        let read = Ledger::<String>::read(Text(&format!("{text}\n   \n  c d  \n")));
        assert_eq!(
            read.map(|ledger| ledger.held.into_iter().collect::<Vec<_>>()),
            Ok(vec!["a m".to_owned(), "b z".to_owned(), "c d".to_owned()])
        );
    }

    #[test]
    fn the_first_unreadable_line_is_named()
    {
        assert_eq!(
            Ledger::<u8>::read(Text("# counts\n7\nseven\n300\n")),
            Err(LedgerError::Unread {
                line: "seven".to_owned()
            })
        );
    }

    #[test]
    fn a_new_finding_and_a_stale_key_are_each_named_once()
    {
        let ledger = Ledger::<u8>::read(Text("1\n2\n9\n")).expect("the ledger reads");
        let findings = [(1, "held"), (3, "new"), (2, "held"), (3, "repeated")];
        let verdict = ledger.check(&findings, |&(key, _)| key);
        assert_eq!(verdict.new, vec![&(3, "new")]);
        assert_eq!(verdict.stale, vec![&9]);
        assert!(!verdict.is_clean());
        let settled = ledger.check(&[(1, "a"), (2, "b"), (9, "c")], |&(key, _)| key);
        assert!(settled.is_clean());
    }
}
