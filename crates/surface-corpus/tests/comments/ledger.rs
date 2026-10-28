//! The committed ledger and the difference a run owes against it. The
//! ledger's reading, verdict and writing are `gandr-workflow-ledger`'s; a key
//! here is the whole line a finding owes.

use anodized::spec;
use gandr_workflow_ledger::Header;
use gandr_workflow_ledger::Ledger;
use gandr_workflow_ledger::LedgerError;

use crate::comments::judge::Finding;

/// The ledger's header: the shape of every line after it.
const HEADER: Header<'static> = Header(
    "key kind. The key is path:name:digest, or path:block.member:digest for a block's member, \
     the digest the first sixteen hex digits of BLAKE3 over the item's text with whitespace \
     collapsed and comments and the attribute block left out; path:<file> for a source's head \
     comment; path:comment:digest for an item comment, the digest over its text. The kind is \
     uncommented, or unshaped:<rule> for a comment outside the shape \
     (crates/surface-corpus/README.md § Comments)",
);

/// One way the findings and the ledger disagree.
///
/// # Specification
/// - provides: a finding the ledger does not hold, or a ledger line no finding
///   still owes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Discrepancy
{
    /// A finding the ledger does not hold.
    Unledgered
    {
        /// The ledger key.
        line: String,
        /// The sentence naming the file and the item.
        detail: String,
    },
    /// A ledger line no finding still owes.
    Stale
    {
        /// The ledger key.
        line: String,
    },
}

impl Discrepancy
{
    /// The ledger key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn line(&self) -> crate::comments::shape::Line<'_>
    {
        match *self {
            Self::Unledgered { ref line, .. } | Self::Stale { ref line } => {
                crate::comments::shape::Line(line)
            },
        }
    }

    /// Whether this line is in the ledger and no longer owed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_stale(&self) -> crate::comments::shape::Yes
    {
        crate::comments::shape::Yes(matches!(*self, Self::Stale { .. }))
    }
}

impl core::fmt::Display for Discrepancy
{
    /// The gate's one-line refusal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: names the ledger key, and an unledgered finding as debt the
    ///   ledger does not hold.
    /// - provides: the line the binary prints for one disagreement.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant's line contains its key and only the
    ///   unledgered variant says the ledger does not hold it.
    /// - witness: `tests::comments::ledger::tests::each_disagreement_names_its_line`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Unledgered { ref line, .. } => {
                write!(
                    f,
                    "corpus comments FAILED: finding not in the ledger: {line}"
                )
            },
            Self::Stale { ref line } => {
                write!(f, "corpus comments FAILED: stale ledger line: {line}")
            },
        }
    }
}

/// The disagreements between `found` and the ledger text `ledger`.
///
/// Empty lines and `#` lines in the ledger are ignored. A finding whose line
/// the ledger holds is not a disagreement.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one [`Discrepancy::Unledgered`] per line a finding owes that the
///   ledger does not hold, and one [`Discrepancy::Stale`] per held line,
///   neither empty nor a `#` line, that no finding carries; ordered by line.
/// - provides: the ratchet's verdict.
/// - fails: never: every trimmed line reads as a key, a `String`'s parse being
///   infallible; the `Result` is the shared ledger's reading.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a missing line, a stale line and an exact match are three
///   observations; a blank line and the header are not a fourth finding.
/// - witness: `tests::comments::judge::tests::an_uncommented_item_is_refused_by_name`
/// - witness: `tests::comments::judge::tests::a_ledgered_item_passes`
/// - witness: `tests::comments::judge::tests::a_stale_ledger_line_is_refused`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |rows| rows.iter().zip(rows.iter().skip(1)).all(|(left, right)| left.line() <= right.line())))]
#[inline]
pub fn discrepancies(
    found: &[Finding],
    ledger: crate::comments::shape::Text<'_>,
) -> Result<Vec<Discrepancy>, LedgerError>
{
    let held = Ledger::<String>::read(gandr_workflow_ledger::Text(ledger.0))?;
    let verdict = held.check(found, |finding| finding.line().0.to_owned());
    let mut rows: Vec<Discrepancy> = verdict
        .new
        .iter()
        .map(|finding| Discrepancy::Unledgered {
            line: finding.line().0.to_owned(),
            detail: finding.detail().0.to_owned(),
        })
        .chain(
            verdict
                .stale
                .iter()
                .map(|&line| Discrepancy::Stale { line: line.clone() }),
        )
        .collect();
    rows.sort_by(|left, right| left.line().cmp(&right.line()));
    Ok(rows)
}

/// The ledger text of `found`: the header, then one sorted line per finding,
/// as `gandr_workflow_ledger::write` writes it; the bytes
/// `CORPUS_COMMENTS_WRITE_LEDGER=1` commits.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn ledger_text(found: &[Finding]) -> String
{
    gandr_workflow_ledger::write(HEADER, found.iter().map(|finding| finding.line().0))
}

#[cfg(test)]
mod tests
{
    use super::Discrepancy;

    #[test]
    fn each_disagreement_names_its_line()
    {
        let unledgered = Discrepancy::Unledgered {
            line: "sample.gandr:bare".to_owned(),
            detail: "sample.gandr: bare has no comment before its attribute block".to_owned(),
        };
        let stale = Discrepancy::Stale {
            line: "sample.gandr:gone".to_owned(),
        };
        assert!(
            unledgered.to_string().contains("sample.gandr:bare")
                && unledgered.to_string().contains("not in the ledger"),
            "an unledgered finding names its line"
        );
        assert!(
            stale.to_string().contains("sample.gandr:gone") && stale.to_string().contains("stale"),
            "a stale line names itself"
        );
        assert!(!stale.to_string().contains("not in the ledger"));
    }
}
