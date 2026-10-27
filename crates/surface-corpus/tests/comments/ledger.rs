//! The committed ledger and the difference a run owes against it.

use alloc::collections::BTreeSet;

use anodized::spec;

use crate::comments::judge::Finding;

/// The ledger's first line: the shape of every line after it.
const HEADER: &str = "# key kind. The key is path:name:digest, or path:block.member:digest for a \
                      block's member, the digest the first sixteen hex digits of BLAKE3 over the \
                      item's text with whitespace collapsed and comments and the attribute block \
                      left out; path:<file> for a source's head comment; path:comment:digest for \
                      an item comment, the digest over its text. The kind is uncommented, or \
                      unshaped:<rule> for a comment outside the shape \
                      (crates/surface-corpus/README.md § Comments)";

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
/// - ensures: one [`Discrepancy::Unledgered`] per finding whose line the ledger
///   does not hold, and one [`Discrepancy::Stale`] per ledger line, neither
///   empty nor a `#` line, that no finding carries; ordered by line.
/// - provides: the ratchet's verdict.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a missing line, a stale line and an exact match are three
///   observations; a blank line and the header are not a fourth finding.
/// - witness: `tests::comments::judge::tests::an_uncommented_item_is_refused_by_name`
/// - witness: `tests::comments::judge::tests::a_ledgered_item_passes`
/// - witness: `tests::comments::judge::tests::a_stale_ledger_line_is_refused`
/// - witness: `tests::comments::ledger::tests::a_blank_ledger_line_is_not_debt`
#[spec(ensures: |ret| ret.iter().zip(ret.iter().skip(1)).all(|(left, right)| left.line() <= right.line()))]
#[inline]
#[must_use]
pub fn discrepancies(
    found: &[Finding],
    ledger: crate::comments::shape::Text<'_>,
) -> Vec<Discrepancy>
{
    let owed: BTreeSet<&str> = found.iter().map(|finding| finding.line().0).collect();
    let held = ledger_lines(ledger);
    let mut rows = Vec::new();
    for finding in found {
        if !held.contains(finding.line().0) {
            rows.push(Discrepancy::Unledgered {
                line: finding.line().0.to_owned(),
                detail: finding.detail().0.to_owned(),
            });
        }
    }
    for line in &held {
        if !owed.contains(line.as_str()) {
            rows.push(Discrepancy::Stale { line: line.clone() });
        }
    }
    rows.sort_by(|left, right| left.line().cmp(&right.line()));
    rows
}

/// The ledger text of `found`: the header, then one sorted line per finding.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the header line, then the findings' distinct lines in order, each
///   line ended by a newline.
/// - provides: the bytes `CORPUS_COMMENTS_WRITE_LEDGER=1` commits.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, one line and two unsorted repeated lines render in
///   order under the header, each once, each terminated.
/// - witness: `tests::comments::ledger::tests::the_ledger_text_is_sorted_and_terminated`
#[spec(ensures: |ret| ret.starts_with(HEADER) && ret.ends_with('\n'))]
#[inline]
#[must_use]
pub fn ledger_text(found: &[Finding]) -> String
{
    let mut lines: Vec<&str> = found.iter().map(|finding| finding.line().0).collect();
    lines.sort_unstable();
    lines.dedup();
    let mut text = String::from(HEADER);
    text.push('\n');
    for line in lines {
        text.push_str(line);
        text.push('\n');
    }
    text
}

/// The trimmed lines of a ledger, neither empty nor a `#` line.
///
/// # Specification
/// trivial.
fn ledger_lines(ledger: crate::comments::shape::Text<'_>) -> BTreeSet<String>
{
    ledger
        .0
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(str::to_owned)
        .collect()
}

#[cfg(test)]
mod tests
{
    use super::Discrepancy;
    use super::HEADER;
    use super::discrepancies;
    use super::ledger_text;
    use crate::comments::judge::Finding;

    /// # Specification
    /// trivial.
    fn finding(line: crate::comments::shape::Text<'_>) -> Finding
    {
        Finding::from_line(line)
    }

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

    #[test]
    fn a_blank_ledger_line_is_not_debt()
    {
        let rows = discrepancies(
            &[],
            crate::comments::shape::Text(&format!("{HEADER}\n\n  \n")),
        );
        assert!(
            rows.is_empty(),
            "neither a blank ledger line nor the header is a stale finding"
        );
    }

    #[test]
    fn the_ledger_text_is_sorted_and_terminated()
    {
        assert_eq!(ledger_text(&[]), format!("{HEADER}\n"));
        let text = ledger_text(&[
            finding(crate::comments::shape::Text("b:z")),
            finding(crate::comments::shape::Text("a:m")),
            finding(crate::comments::shape::Text("b:z")),
        ]);
        assert_eq!(text, format!("{HEADER}\na:m\nb:z\n"));
    }
}
