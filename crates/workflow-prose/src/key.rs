//! The key of a finding: its file, its rule and the digest of its sentence.
//!
//! The digest is the first sixteen hexadecimal digits of the BLAKE3 digest of
//! the sentence. The digest keys the sentence, not its line, so moving a
//! sentence keeps its key and rewording it retires the old one. The values of
//! the kind `prose` of the outputs hold the rule and the digest of each key.

use crate::rules::Finding;
use crate::rules::Rule;

/// The hexadecimal digits of the digest a key keeps.
const DIGITS: usize = 16;

/// The key of a finding: its file, its rule and the digest of its sentence.
///
/// The digest is the first sixteen hexadecimal digits of the sentence's
/// BLAKE3 digest. Moving a sentence keeps its key, and rewording it retires
/// the key.
///
/// # Specification
/// - provides: what the kind `prose` of the outputs holds of a finding.
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
    /// - witness: `key::tests::a_moved_sentence_keeps_its_key_and_a_reworded_one_does_not`
    ///
    /// # Cost
    /// - allocation: the key's path and digest, durable by the value of the
    ///   kind
    #[inline]
    #[must_use]
    pub fn of(finding: &Finding) -> Self
    {
        let digest = blake3::hash(finding.sentence.as_bytes()).to_hex();
        Self {
            path: String::from(&*finding.path),
            rule: finding.rule,
            digest: digest.get(.. DIGITS).unwrap_or_default().to_owned(),
        }
    }
}

#[cfg(test)]
mod tests
{
    use super::Key;
    use crate::rules::Finding;
    use crate::rules::Rule;

    /// A finding in `$path` on line `$line` of `$sentence`.
    macro_rules! finding {
        ($path:literal, $line:literal, $sentence:literal) => {
            Finding {
                path: $path.into(),
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
}
