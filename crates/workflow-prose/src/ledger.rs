//! The prose ledger's key: what `corpus/prose.ledger` records of a finding.
//! The ledger itself, its reading, its verdict and its writing, is
//! `gandr-workflow-ledger`'s.
//!
//! A line is `PATH RULE DIGEST`: the file, the rule and the first sixteen
//! hexadecimal digits of the sentence's BLAKE3 digest. The digest keys the
//! sentence, not its line, so moving a sentence keeps its key and rewording it
//! retires the old one.

use core::fmt;
use core::str::FromStr;

use gandr_workflow_ledger::Header;

use crate::rules::Finding;
use crate::rules::Rule;

/// The hexadecimal digits of the digest a key keeps.
const DIGITS: usize = 16;

/// The header `corpus/prose.ledger` is written under.
pub const HEADER: Header<'static> = Header(
    "The prose debt `check:prose` names (crates/workflow-prose/README.md): a\nfinding here \
     passes, a new one refuses, a fixed one leaves its line stale.\nWritten by `mise run \
     check:prose --write`; never edited by hand.",
);

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

/// Why a line is no key: it is not a path, a rule and sixteen hexadecimal
/// digits.
///
/// # Specification
/// - provides: the refusal [`Key`]'s parse gives; the ledger names the line.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unkeyed;

impl FromStr for Key
{
    type Err = Unkeyed;

    /// The key a ledger line spells.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, a path, a rule's name and sixteen hexadecimal
    ///   digits, the last two split from the right at single spaces, so a path
    ///   may hold a space.
    /// - provides: one held key of the committed debt.
    /// - fails: [`Unkeyed`] for a missing field, an unknown rule, an empty
    ///   path, or a digest that is not sixteen hexadecimal digits.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written key reads back, and lines with an unknown
    ///   rule, a short digest or a missing field are refused.
    /// - witness: `ledger::tests::a_ledger_reads_back_what_it_writes`
    #[inline]
    fn from_str(line: &str) -> Result<Self, Unkeyed>
    {
        let mut fields = line.rsplitn(3, ' ');
        let (Some(digest), Some(rule), Some(path)) = (fields.next(), fields.next(), fields.next())
        else {
            return Err(Unkeyed);
        };
        let rule = rule.parse::<Rule>().map_err(|_unknown| Unkeyed)?;
        if path.is_empty()
            || digest.len() != DIGITS
            || !digest.bytes().all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(Unkeyed);
        }
        Ok(Self {
            path: path.to_owned(),
            rule,
            digest: digest.to_owned(),
        })
    }
}

#[cfg(test)]
mod tests
{
    use gandr_workflow_ledger::Ledger;
    use gandr_workflow_ledger::LedgerError;
    use gandr_workflow_ledger::Text;
    use gandr_workflow_ledger::write;

    use super::HEADER;
    use super::Key;
    use crate::rules::Finding;
    use crate::rules::Rule;

    /// A finding in `$path` on line `$line` of `$sentence`.
    macro_rules! finding {
        ($path:literal, $line:literal, $sentence:literal) => {
            Finding {
                path: $path.to_owned(),
                line: crate::passage::comments(
                    crate::passage::Text($path),
                    crate::passage::Text(&format!("{}/// x", "\n".repeat($line - 1))),
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
        let findings = [
            finding!("corpus/b.gandr", 1, "One."),
            finding!("corpus/a b.gandr", 2, "Two."),
        ];
        let text = write(HEADER, findings.iter().map(Key::of));
        let ledger = Ledger::<Key>::read(Text(&text)).expect("the written ledger reads");
        assert_eq!(
            ledger.check(&findings, Key::of).standing(),
            gandr_workflow_ledger::Standing::Agreed
        );
        for line in [
            "corpus/a.gandr Passive 0123",
            "corpus/a.gandr Unknown 0123456789abcdef",
            "corpus/a.gandr 0123456789abcdef",
        ] {
            assert_eq!(
                Ledger::<Key>::read(Text(line)),
                Err(LedgerError::Unread {
                    line: line.to_owned()
                })
            );
        }
    }
}
