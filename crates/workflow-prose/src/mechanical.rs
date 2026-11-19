//! The named override for a mechanical change: a pull request body's
//! `prose-override:` line, read and checked against the base.
//!
//! A mechanical change rewrites paragraphs that it did not write in the
//! prose's sense: a rename moves a word through a hundred paragraphs. The
//! body names the change, the count of paragraphs it claims and the reason:
//!
//! ```text
//! prose-override: mechanical `old` -> `new` (12 paragraphs), reason: the crate's rename
//! ```
//!
//! The check does not trust the line. It applies each substitution to each
//! paragraph the base holds in a touched document, in the order the body
//! states them. A written paragraph is admitted only when its digest is the
//! digest of a base paragraph so changed. Each admitted paragraph counts for
//! each override that changed it, and the check prints the count admitted
//! beside the count claimed. A count that differs refuses, so the signed line
//! states what the change did. The architect signs an override as a deletion
//! is signed, and `check:prose` reads the sign-off.

use std::collections::HashMap;

use crate::digest::Digest;
use crate::passage::Passage;
use crate::passage::Text;

/// One override a body states.
///
/// # Specification
/// - provides: the substitution the check applies to the base, and the count it
///   compares.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Override
{
    /// The text the change replaces.
    pub old: String,
    /// The text the change writes in its place.
    pub new: String,
    /// The paragraphs the body claims the change rewrites.
    pub claimed: usize,
    /// The paragraphs the check admitted under this override.
    pub admitted: usize,
    /// The body's line, as written.
    pub line: String,
}

/// A body's line that opens on `prose-override:` and does not read.
///
/// # Specification
/// - provides: the line the refusal names.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unread(pub String);

/// The line's opening word.
const OPENING: &str = "prose-override:";

/// The overrides `body` states, in its order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one override per line outside a fenced block that, trimmed, opens
///   on `prose-override:` and reads as `mechanical`, the old text in backticks,
///   `->`, the new text in backticks, the count in parentheses with `paragraph`
///   or `paragraphs`, a comma, and `reason:` with a reason. The old text is not
///   empty, and the count is a decimal number.
/// - provides: what [`admit`] applies.
/// - fails: [`Unread`] naming the first line that opens on `prose-override:`
///   and does not read.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the overrides and a refused line, growth within the body
///
/// # Adequacy
/// - hypothesis: L3 — a body with an override, a quoted one in a fence and
///   lines that miss each part; a fenced line read, a missing reason admitted
///   or a count misread changes the result.
/// - witness: `mechanical::tests::a_body_states_its_overrides_and_a_malformed_line_refuses`
#[inline]
pub fn read(body: Text<'_>) -> Result<Vec<Override>, Unread>
{
    let mut overrides = Vec::new();
    let mut fenced = false;
    for raw in body.0.lines() {
        let line = raw.trim();
        if line.starts_with("```") {
            fenced = !fenced;
            continue;
        }
        if fenced || !line.starts_with(OPENING) {
            continue;
        }
        overrides.push(stated(Text(line)).ok_or_else(|| Unread(line.to_owned()))?);
    }
    Ok(overrides)
}

/// The override `line` states, when it reads.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the override's texts and line, growth within the line
///
/// # Adequacy
/// - hypothesis: L3 — as [`read`].
/// - witness: `mechanical::tests::a_body_states_its_overrides_and_a_malformed_line_refuses`
fn stated(line: Text<'_>) -> Option<Override>
{
    let rest = line.0.strip_prefix(OPENING)?.trim_start();
    let rest = rest.strip_prefix("mechanical `")?;
    let (old, rest) = rest.split_once('`')?;
    let rest = rest.trim_start().strip_prefix("->")?.trim_start();
    let rest = rest.strip_prefix('`')?;
    let (new, rest) = rest.split_once('`')?;
    let rest = rest.trim_start().strip_prefix('(')?;
    let (count, rest) = rest.split_once(' ')?;
    let rest = rest
        .strip_prefix("paragraphs)")
        .or_else(|| rest.strip_prefix("paragraph)"))?;
    let reason = rest.strip_prefix(", reason:")?.trim();
    if old.is_empty() || reason.is_empty() || !count.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    Some(Override {
        old: old.to_owned(),
        new: new.to_owned(),
        claimed: count.parse().ok()?,
        admitted: 0,
        line: line.0.to_owned(),
    })
}

/// The written paragraphs the overrides do not admit.
///
/// # Specification
/// - requires: `held` is the base's paragraphs of the touched documents, and
///   `written` the head's paragraphs whose digest the base does not hold.
/// - ensures: each base paragraph takes every override whose old text it holds,
///   in order, each replacing every instance. A written paragraph whose digest
///   is a changed base paragraph's is left out of the answer, and each override
///   that changed that base paragraph counts it in [`Override::admitted`].
///   Every other written paragraph is answered, in order.
/// - provides: the paragraphs that parse.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Cost
/// - allocation: each changed base paragraph's text and the digest map, growth
///   within the touched documents
///
/// # Adequacy
/// - hypothesis: L3 — a rename in two paragraphs, a paragraph renamed and
///   reworded, and a paragraph the rename never reached; an admitted rewording,
///   a rename refused, or a miscount changes the answer or the counts.
/// - witness: `mechanical::tests::a_rename_admits_its_paragraphs_and_no_rewording`
#[inline]
pub fn admit<'head>(
    overrides: &mut [Override],
    held: &[Passage],
    written: Vec<&'head Passage>,
) -> Vec<&'head Passage>
{
    if overrides.is_empty() {
        return written;
    }
    let mut changed: HashMap<Digest, Vec<usize>> = HashMap::new();
    let mut text = String::new();
    for passage in held {
        text.clear();
        text.push_str(&passage.text);
        let mut by = Vec::new();
        for (at, stated) in overrides.iter().enumerate() {
            if text.contains(&stated.old) {
                text = text.replace(&stated.old, &stated.new);
                by.push(at);
            }
        }
        if !by.is_empty() {
            changed.entry(Digest::of(Text(&text))).or_insert(by);
        }
    }
    written
        .into_iter()
        .filter(|passage| {
            changed
                .get(&Digest::of(Text(&passage.text)))
                .is_none_or(|by| {
                    for &at in by {
                        if let Some(stated) = overrides.get_mut(at) {
                            stated.admitted = stated.admitted.saturating_add(1);
                        }
                    }
                    false
                })
        })
        .collect()
}

#[cfg(test)]
mod tests
{
    use super::Override;
    use super::Unread;
    use super::admit;
    use super::read;
    use crate::passage::Passage;
    use crate::passage::Text;
    use crate::passage::document;

    /// The one paragraph of `text`, read as a README's.
    ///
    /// # Specification
    /// trivial.
    fn paragraph(text: Text<'_>) -> Passage
    {
        document(Text("crates/a/README.md"), text)
            .into_iter()
            .next()
            .expect("one paragraph")
    }

    #[test]
    fn a_body_states_its_overrides_and_a_malformed_line_refuses()
    {
        let body = "## Summary\n\nThe rename.\n\n\
                    prose-override: mechanical `Opener` -> `Opening` (2 paragraphs), reason: the \
                    rename of #7614\n\
                    ```text\nprose-override: quoted, never read\n```\n\
                    prose-override: mechanical `a b` -> `` (1 paragraph), reason: a word leaves\n";
        let overrides = read(Text(body)).expect("both lines read");
        assert_eq!(
            overrides
                .iter()
                .map(|stated| (stated.old.as_str(), stated.new.as_str(), stated.claimed))
                .collect::<Vec<_>>(),
            [("Opener", "Opening", 2), ("a b", "", 1)]
        );
        for line in [
            "prose-override: mechanical rename (2 paragraphs), reason: a rename",
            "prose-override: mechanical `a` -> `b` (two paragraphs), reason: a rename",
            "prose-override: mechanical `a` -> `b` (2 paragraphs)",
            "prose-override: mechanical `a` -> `b` (2 paragraphs), reason:",
            "prose-override: mechanical `` -> `b` (2 paragraphs), reason: a rename",
        ] {
            assert_eq!(read(Text(line)), Err(Unread(line.to_owned())), "{line}");
        }
    }

    #[test]
    fn a_rename_admits_its_paragraphs_and_no_rewording()
    {
        let held = [
            paragraph(Text("The Opener reads the table.")),
            paragraph(Text("Each Opener keeps its slot.")),
            paragraph(Text("The arena holds the cells.")),
        ];
        let renamed = paragraph(Text("The Opening reads the table."));
        let reworded = paragraph(Text("Each Opening keeps its own slot."));
        let fresh = paragraph(Text("A new paragraph."));
        let mut overrides = vec![Override {
            old: "Opener".into(),
            new: "Opening".into(),
            claimed: 2,
            ..Override::default()
        }];
        let left = admit(&mut overrides, &held, vec![&renamed, &reworded, &fresh]);
        assert_eq!(left, [&reworded, &fresh]);
        assert_eq!(overrides[0].admitted, 1);
        assert_eq!(admit(&mut [], &held, vec![&renamed]), [&renamed]);
    }
}
