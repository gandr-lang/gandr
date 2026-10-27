//! The ledger: the committed prose debt, one line per finding, so a new
//! finding refuses and a fixed one leaves a stale line to delete.
//!
//! A line is `PATH RULE DIGEST`: the file, the rule and the first sixteen
//! hexadecimal digits of the sentence's BLAKE3 digest. The digest keys the
//! sentence, not its line, so moving a sentence keeps its key and rewording it
//! retires the old one.

extern crate alloc;

use alloc::collections::BTreeSet;
use core::fmt;
use core::fmt::Write as _;

use crate::error::ProseError;
use crate::passage::Text;
use crate::rules::Finding;
use crate::rules::Rule;

/// The hexadecimal digits of the digest a key keeps.
const DIGITS: usize = 16;

/// One ledger line: a finding's file, rule and sentence digest.
///
/// # Specification
/// - provides: what the ledger records of a finding.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Key
{
    /// The file.
    pub path: String,
    /// The rule.
    pub rule: Rule,
    /// The sentence's digest, sixteen hexadecimal digits.
    pub digest: String,
}

impl Key
{
    /// The key of `finding`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same sentence keys alike wherever it moves, and a
    ///   reworded one keys apart; digesting the line instead changes both.
    /// - witness: `ledger::tests::a_moved_sentence_keeps_its_key_and_a_reworded_one_does_not`
    #[inline]
    #[must_use]
    pub fn of(finding: &Finding) -> Self
    {
        let digest = blake3::hash(finding.sentence.as_bytes()).to_hex();
        Self {
            path: finding.path.clone(),
            rule: finding.rule,
            digest: digest.get(.. DIGITS).unwrap_or_default().to_owned(),
        }
    }
}

impl fmt::Display for Key
{
    /// Writes `PATH RULE DIGEST`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a key renders and reads back; a dropped field breaks
    ///   the trip.
    /// - witness: `ledger::tests::a_ledger_reads_back_what_it_writes`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{} {} {}", self.path, self.rule, self.digest)
    }
}

/// The ledger's keys, from its text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success, one key per line that is neither blank nor a `#`
///   comment, each a path, a rule's name and sixteen hexadecimal digits,
///   separated by single spaces.
/// - provides: the committed debt.
/// - fails: [`ProseError::Ledger`] naming the first line that is not a key.
/// - panics: none.
/// - executable: none — the outcome is the parse itself.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a written ledger reads back, and lines with an unknown
///   rule, a short digest or a missing field are refused.
/// - witness: `ledger::tests::a_ledger_reads_back_what_it_writes`
#[inline]
pub fn read(text: Text<'_>) -> Result<BTreeSet<Key>, ProseError>
{
    let mut keys = BTreeSet::new();
    for line in text.0.lines() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let refuse = || ProseError::Ledger {
            line: line.to_owned(),
        };
        let mut fields = line.rsplitn(3, ' ');
        let (Some(digest), Some(rule), Some(path)) = (fields.next(), fields.next(), fields.next())
        else {
            return Err(refuse());
        };
        let rule = rule.parse::<Rule>().ok().ok_or_else(refuse)?;
        if path.is_empty()
            || digest.len() != DIGITS
            || !digest.bytes().all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(refuse());
        }
        keys.insert(Key {
            path: path.to_owned(),
            rule,
            digest: digest.to_owned(),
        });
    }
    Ok(keys)
}

/// The ledger's text for `keys`: a header, then one line per key in order.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`read`].
/// - witness: `ledger::tests::a_ledger_reads_back_what_it_writes`
#[inline]
#[must_use]
pub fn write(keys: &BTreeSet<Key>) -> String
{
    let mut text = String::from(
        "# The prose debt `check:prose` names (crates/workflow-prose/README.md): a\n# finding \
         here passes, a new one refuses, a fixed one leaves its line stale.\n# Written by `mise \
         run check:prose --write`; never edited by hand.\n",
    );
    for key in keys {
        writeln!(text, "{key}").unwrap_or_default();
    }
    text
}

#[cfg(test)]
mod tests
{
    extern crate alloc;

    use alloc::collections::BTreeSet;

    use super::Key;
    use super::read;
    use super::write;
    use crate::error::ProseError;
    use crate::passage::Text;
    use crate::rules::Finding;
    use crate::rules::Rule;

    /// A finding in `$path` on line `$line` of `$sentence`.
    macro_rules! finding {
        ($path:literal, $line:literal, $sentence:literal) => {
            Finding {
                path: $path.to_owned(),
                line: crate::passage::comments(
                    Text($path),
                    Text(&format!("{}/// x", "\n".repeat($line - 1))),
                )
                .into_iter()
                .next()
                .unwrap()
                .line,
                rule: Rule::Passive,
                sentence: $sentence.to_owned(),
            }
        };
    }

    #[test]
    fn a_moved_sentence_keeps_its_key_and_a_reworded_one_does_not()
    {
        let here = Key::of(&finding!("corpus/a.gandr", 3, "It is reduced."));
        let moved = Key::of(&finding!("corpus/a.gandr", 9, "It is reduced."));
        let reworded = Key::of(&finding!("corpus/a.gandr", 3, "It is rewritten."));
        assert_eq!(here, moved);
        assert_ne!(here, reworded);
        assert_eq!(here.digest.len(), 16);
    }

    #[test]
    fn a_ledger_reads_back_what_it_writes()
    {
        let keys: BTreeSet<Key> = [
            Key::of(&finding!("corpus/b.gandr", 1, "One.")),
            Key::of(&finding!("corpus/a b.gandr", 2, "Two.")),
        ]
        .into_iter()
        .collect();
        let text = write(&keys);
        assert_eq!(read(Text(&text)), Ok(keys));
        for line in [
            "corpus/a.gandr Passive 0123",
            "corpus/a.gandr Unknown 0123456789abcdef",
            "corpus/a.gandr 0123456789abcdef",
        ] {
            assert_eq!(
                read(Text(line)),
                Err(ProseError::Ledger {
                    line: line.to_owned()
                })
            );
        }
    }
}
