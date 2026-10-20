//! Rename: the name at a position, rewritten where it is declared and at every
//! use the workspace's documents make of it.
//!
//! A rename is about the name a request at a position means, as
//! [`found`] finds it, and its sites are the uses [`uses`](crate::uses)
//! answers for a reference request, read off each document's type table, never
//! searched for in the text. A use's span may hold more than the name — an
//! import's alias before it — so each site is narrowed to the name's spelling
//! at its end: an aliased use keeps its alias. A use whose text does not end
//! with the name's spelling refuses the rename, naming where it is, rather than
//! renaming part of something else.
//!
//! The server judges the new name before answering: the declaring source, with
//! its sites renamed, is tried beside its present text, and a rename the trial
//! ranks lower or reports more errors for is refused — a keyword, a name the
//! grammar does not read as one, or a name the source declares already.

use alloc::vec::Vec;
use core::fmt;
use std::path::Path;

use anodized::spec;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

use crate::goto::ranged;
use crate::hover::Hovering;
use crate::position::Position;
use crate::protocol::PrepareRename;
use crate::protocol::TextEdit;
use crate::uses::Written;
use crate::uses::found;
use crate::uses::spelling;

/// A use a rename cannot rewrite: its text does not end with the name's
/// spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unrenamed
{
    /// How the use is written.
    pub written: String,
    /// The name's spelling.
    pub spelled: String,
}

/// The name a rename writes in place of the one it renames.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NewName<'name>(pub &'name str);

impl fmt::Display for Unrenamed
{
    /// Say which use stops the rename.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let Self {
            ref written,
            ref spelled,
        } = *self;
        write!(
            f,
            "a use of `{spelled}` is written `{written}`, which does not end with the name; \
             nothing is renamed"
        )
    }
}

/// What a prepare-rename request at `position` of `text`, whose copy keeps
/// `hovering`, answers: the name as written at the position and its
/// spelling.
///
/// # Specification
/// - requires: `hovering` was read off `text`.
/// - ensures: for what [`found`] finds at the position's byte, the range of the
///   name's spelling at the end of what is written there, with that spelling as
///   the placeholder; none when nothing is found, the name's source is not in
///   the table, or what is written does not end with the name.
/// - provides: the answer to `textDocument/prepareRename` for a held document.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a declaring name, a use of a sibling's name and a keyword
///   are each prepared or not as a rename there is.
/// - witness: `server::tests::a_rename_rewrites_a_name_everywhere_it_is_written`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|prepared| !prepared.placeholder.is_empty()))]
#[must_use]
pub fn prepared(
    text: SourceText<'_>,
    hovering: &Hovering,
    position: Position,
) -> Option<PrepareRename>
{
    let table = hovering.table();
    let index = LineIndex::new(<&str>::from(text).into());
    let (span, referent) = found(table, ByteOffset::from(usize::from(position.byte(&index))))?;
    let source = if referent.source() == table.own_source() {
        text
    }
    else {
        table.source_text(referent.source())?
    };
    let spelled = spelling(source, referent.named())?;
    let site = narrowed(text, span, spelled).ok()?;
    Some(PrepareRename {
        range: ranged(&index, site)?,
        placeholder: String::from(<&str>::from(spelled)),
    })
}

/// Where the document `text`, whose canonical path is `own` and whose copy
/// keeps `hovering`, writes the name `written` places: its declaring name when
/// the document is the name's source, and each use, every site narrowed to the
/// name's spelling at its end.
///
/// # Specification
/// - requires: `hovering` was read off `text`.
/// - ensures: when `own` is the name's source, its declaring span, then the
///   uses of it the table reads in the document's own text, ascending by start
///   without repeats, each the trailing `written.spelled` of its span; none
///   when the document reads no such source. A use not ending with the spelling
///   is the [`Unrenamed`] naming it.
/// - provides: one document's part of a rename's edits.
/// - fails: [`Unrenamed`], as above.
/// - panics: none.
///
/// # Errors
/// [`Unrenamed`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the declaring document's name and uses, an importer's
///   uses and a document reading no such source answer their sites.
/// - witness: `server::tests::a_rename_rewrites_a_name_everywhere_it_is_written`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |sites| sites.windows(2).all(|pair| match *pair {
    [left, right] => left.end() <= right.start(),
    _ => false,
})))]
pub fn sites(
    text: SourceText<'_>,
    own: &Path,
    hovering: &Hovering,
    written: &Written,
) -> Result<Vec<ByteSpan>, Unrenamed>
{
    let table = hovering.table();
    let declaring = own == written.path;
    let source = if declaring {
        Some(table.own_source())
    }
    else {
        hovering.source_at(&written.path)
    };
    let Some(source) = source
    else {
        return Ok(Vec::new());
    };
    let declared = declaring.then_some(written.named);
    let mut sites = Vec::new();
    for span in declared
        .into_iter()
        .chain(table.uses_of(source, written.named))
    {
        sites.push(narrowed(
            text,
            span,
            SourceText::from(written.spelled.as_str()),
        )?);
    }
    sites.sort_unstable_by_key(|site| usize::from(site.start()));
    sites.dedup();
    Ok(sites)
}

/// The trailing `spelled` of what `text` writes at `span`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the span of the last bytes of `span` that spell `spelled` when
///   the text there ends with it and it is not empty; else the [`Unrenamed`]
///   naming what is written there.
/// - fails: [`Unrenamed`], as above.
/// - panics: none.
///
/// # Errors
/// [`Unrenamed`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a declaring name and uses written as the name narrow to
///   themselves; every site of a rename is one.
/// - witness: `server::tests::a_rename_rewrites_a_name_everywhere_it_is_written`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|site| site.end() == span.end()
    && usize::from(site.end()).saturating_sub(usize::from(site.start())) == <&str>::from(spelled).len()) || ret.is_err())]
fn narrowed(
    text: SourceText<'_>,
    span: ByteSpan,
    spelled: SourceText<'_>,
) -> Result<ByteSpan, Unrenamed>
{
    let written = spelling(text, span).map_or("", <&str>::from);
    let spelled = <&str>::from(spelled);
    let unrenamed = || Unrenamed {
        written: written.to_owned(),
        spelled: spelled.to_owned(),
    };
    let start = usize::from(span.end()).checked_sub(spelled.len());
    match start {
        Some(start) if written.ends_with(spelled) && !spelled.is_empty() => {
            ByteSpan::new(ByteOffset::from(start), span.end()).map_err(|_inverted| unrenamed())
        },
        Some(_) | None => Err(unrenamed()),
    }
}

/// `text` with each of `sites` replaced by `name`.
///
/// # Specification
/// - requires: `sites` ascend without overlapping, each within `text` on
///   character boundaries.
/// - ensures: the text between the sites kept in order, each site replaced by
///   `name`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a rename to a keyword and to a name already declared are
///   refused only when the spliced text reads as their trial reads it.
/// - witness: `server::tests::a_rename_rewrites_a_name_everywhere_it_is_written`
#[spec(ensures: |ret| ret.len() == <&str>::from(text).len()
    .saturating_add(sites.len().saturating_mul(name.0.len()))
    .saturating_sub(sites.iter().map(|site| usize::from(site.end()).saturating_sub(usize::from(site.start()))).sum::<usize>()))]
#[must_use]
pub fn spliced(
    text: SourceText<'_>,
    sites: &[ByteSpan],
    name: NewName<'_>,
) -> String
{
    let text = <&str>::from(text);
    let mut renamed = String::with_capacity(text.len());
    let mut kept = 0_usize;
    for site in sites {
        renamed.push_str(
            text.get(kept .. usize::from(site.start()))
                .unwrap_or_default(),
        );
        renamed.push_str(name.0);
        kept = usize::from(site.end());
    }
    renamed.push_str(text.get(kept ..).unwrap_or_default());
    renamed
}

/// The edits replacing each of `sites` of `text` with `name`, in order; a site
/// with no range in `text` is dropped.
///
/// # Specification
/// trivial.
#[must_use]
pub fn text_edits(
    text: SourceText<'_>,
    sites: &[ByteSpan],
    name: NewName<'_>,
) -> Vec<TextEdit>
{
    let index = LineIndex::new(<&str>::from(text).into());
    sites
        .iter()
        .filter_map(|&site| ranged(&index, site))
        .map(|range| TextEdit {
            range,
            new_text: name.0.to_owned(),
        })
        .collect()
}
