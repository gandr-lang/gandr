//! Shadowing binders: a code lens over each binder that hides another
//! binding, and a diagnostic there at the severity the client sets.
//!
//! Both views read the shadow index that the document's type table keeps
//! ([`TypeTable::shadows`]): each binder of the document's own text whose
//! name an enclosing binder, an opened member, a declaration, an import or a
//! builtin answers where the binder stands, with the binding it hides. No view
//! compares spellings to find a shadow. A lens is listed with no command. Its
//! resolution names the hidden binding and counts the uses that the binder
//! takes ([`TypeTable::uses_of`]), and it runs [`SHOW_REFERENCES`] over them.
//! The diagnostic names the hidden binding in the same words, and its related
//! information points at the place where the unit writes that binding
//! ([`TypeTable::hidden_site`]).
//!
//! | The hidden binding | The lens title |
//! | --- | --- |
//! | a binder | `shadows x (line 4) · 3 uses` |
//! | a declaration of the document | `shadows x (declared line 2) · 3 uses` |
//! | a declaration the printer names by a path: an opened member, a qualified import | `shadows x (Module.x) · 3 uses` |
//! | a declaration of another source, read bare | `shadows x (./sibling.gandr line 1) · 3 uses` |
//! | a constructor | `shadows Zero (Nat.Zero) · 3 uses` |
//! | a builtin | `shadows builtin x · 3 uses` |
//!
//! A line counts from one. The path of another source is its import's
//! address, as the document writes it between the quotes. A source that no
//! import of the document names, as the prelude, is named by the file name of
//! its path. The diagnostic's message is the title without its count.
//!
//! # References
//!
//! - `vault:01a178ab-2ecf-7893-afda-f14010a8acbe` — anchor: the name-modifier
//!   design — a shadow shows as a diagnostic and never as a refusal. The
//!   diagnostic is off by default.
//!
//! [`TypeTable::shadows`]: gandr_surface_dispatcher::TypeTable::shadows
//! [`TypeTable::uses_of`]: gandr_surface_dispatcher::TypeTable::uses_of
//! [`TypeTable::hidden_site`]: gandr_surface_dispatcher::TypeTable::hidden_site

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_lowering::ImportTarget;
use gandr_surface_lowering::Resolution;
use gandr_surface_lowering::Shadow;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::PositionRow;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;
use serde_json::Value;

use crate::goto::Locator;
use crate::position::ranged;
use crate::protocol::CodeLens;
use crate::protocol::Command;
use crate::protocol::Counted;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::LensData;
use crate::protocol::Location;
use crate::protocol::RelatedInformation;
use crate::protocol::SHOW_REFERENCES;
use crate::protocol::Severity;
use crate::reading::Reading;

/// The code a shadowing binder's diagnostic carries.
pub const SHADOWING_BINDER: &str = "ShadowingBinder";

/// What the shadowing views of one document read: the document, its text
/// indexed, its type table, the closure it was typed in and its reading.
#[derive(Clone, Copy)]
pub struct Seen<'seen>
{
    /// The document.
    pub uri: &'seen DocumentUri,
    /// Its text.
    pub text: SourceText<'seen>,
    /// Its text, indexed.
    pub index: &'seen LineIndex<'seen>,
    /// The type table of its text.
    pub table: &'seen TypeTable,
    /// The path each source of the table's unit was opened at, in the unit's
    /// order; empty for a text typed alone.
    pub opened: &'seen [PathBuf],
    /// What each of its path imports resolved to, in the order it writes
    /// them; empty for a text typed alone.
    pub targets: &'seen [ImportTarget],
    /// The reading of its text, which says where each import's address is
    /// written.
    pub reading: &'seen Reading,
}

/// What a shadowing binder hides, as its lens and its diagnostic name it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Hiding<'seen>
{
    /// A binder of the document, on its row.
    Binder(PositionRow),
    /// A declaration of the document under the binder's name, on its row.
    Declared(PositionRow),
    /// A declaration the printer names by a path: a member of an opened
    /// module, or a name a qualified import reads.
    Qualified(&'seen str),
    /// A declaration of another source, read bare: that source's path and
    /// the declaration's row in it.
    Imported(&'seen str, PositionRow),
    /// A constructor, of the family the printer names so.
    Constructor(&'seen str),
    /// A name the builtin namespace seeds.
    Builtin,
    /// A binding whose name or site the table does not keep.
    Unplaced,
}

/// One lens over each shadowing binder of `table`'s own text, the document at
/// `uri` whose text `index` indexes, to resolve by [`resolved`].
///
/// # Specification
/// - requires: `index` was built over the text `table` was typed from.
/// - ensures: one lens per entry of [`TypeTable::shadows`] whose binder `index`
///   ranges, in order, over the binder's name, with no command and the data of
///   `uri`, the range's start and [`Counted::Shadowed`].
/// - provides: the shadowing lenses of `textDocument/codeLens`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a pattern binder that hides a parameter lists one lens
///   over its name.
/// - witness: `server::tests::a_shadowing_binder_shows_what_it_hides_6251`
#[spec(ensures: |ret| ret.len() <= table.shadows().len()
    && ret.iter().all(|lens| lens.command.is_none() && lens.data.as_ref().is_some_and(|data|
        &data.uri == uri && data.position == lens.range.start && data.counts == Counted::Shadowed)))]
#[must_use]
pub fn lenses(
    uri: &DocumentUri,
    table: &TypeTable,
    index: &LineIndex<'_>,
) -> Vec<CodeLens>
{
    table
        .shadows()
        .iter()
        .filter_map(|shadow| {
            let range = ranged(index, shadow.binder)?;
            Some(CodeLens {
                range,
                command: None,
                data: Some(LensData {
                    uri: uri.clone(),
                    position: range.start,
                    counts: Counted::Shadowed,
                }),
            })
        })
        .collect()
}

/// The command of the lens over the shadowing binder whose name starts at
/// `offset` of `seen`'s text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for the entry of [`TypeTable::shadows`] whose binder starts at
///   `offset`, the command titled as the module's table states, with the count
///   of the uses [`TypeTable::uses_of`] answers for the binder, `1 use` or `N
///   uses`, running [`SHOW_REFERENCES`] with the document's URI, the binder's
///   position and the location of each use; none when no entry starts at
///   `offset`.
/// - provides: the answer to `codeLens/resolve` for a shadowing lens.
/// - fails: never.
/// - panics: none.
/// - intension: a binary search of the shadow index and a slice of the use
///   index, so a resolution reads one binder's uses.
///
/// # Adequacy
/// - hypothesis: L3 — a pattern binder that hides a parameter names the
///   parameter's line and counts its own uses, a parameter that hides an
///   earlier declaration names its declared line, and a `let` that hides an
///   opened member names the member's path.
/// - witness: `server::tests::a_shadowing_binder_shows_what_it_hides_6251`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|command| command.name == SHOW_REFERENCES
    && command.title.starts_with("shadows ") && command.arguments.len() == 3_usize))]
#[must_use]
pub fn resolved(
    seen: &Seen<'_>,
    offset: ByteOffset,
) -> Option<Command>
{
    let shadows = seen.table.shadows();
    let at = shadows
        .binary_search_by_key(&offset, |shadow| shadow.binder.start())
        .ok()?;
    let shadow = *shadows.get(at)?;
    let name = spelled(seen.text, shadow.binder)?;
    let position = ranged(seen.index, shadow.binder)?.start;
    let mut locator = Locator::laid((seen.table, seen.opened), seen.uri, seen.index);
    let (hiding, _) = hidden(seen, &mut locator, shadow, name);
    let uses: Vec<Location> = seen
        .table
        .uses_of(seen.table.own_source(), shadow.binder)
        .filter_map(|span| {
            Some(Location {
                uri: seen.uri.clone(),
                range: ranged(seen.index, span)?,
            })
        })
        .collect();
    let mut title = described(hiding, name);
    let _written = write!(
        title,
        " · {} {}",
        uses.len(),
        if uses.len() == 1_usize { "use" } else { "uses" }
    );
    Some(Command {
        title,
        name: SHOW_REFERENCES,
        arguments: Vec::from([
            serde_json::to_value(seen.uri).unwrap_or(Value::Null),
            serde_json::to_value(position).unwrap_or(Value::Null),
            serde_json::to_value(&uses).unwrap_or(Value::Null),
        ]),
    })
}

/// The diagnostic at each shadowing binder of `seen`'s text, at `severity`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one diagnostic per entry of [`TypeTable::shadows`] whose binder
///   `seen`'s index ranges, in order: over the binder's name, at `severity`,
///   code [`SHADOWING_BINDER`], its message the lens title without its count,
///   and one related location at the hidden binding's name where the unit
///   writes it, none for a builtin or a site outside every text the views read.
/// - provides: the diagnostics `gandr.diagnostics.shadowing` turns on.
/// - fails: never.
/// - panics: none.
/// - intension: one pass over the shadow index, each other source's text
///   indexed once.
///
/// # Adequacy
/// - hypothesis: L3 — a pattern binder that hides a parameter is published at
///   the severity set, with the parameter as its related location, and none is
///   published with the setting off.
/// - witness: `server::tests::a_shadowing_binder_shows_what_it_hides_6251`
#[spec(ensures: |ret| ret.len() <= seen.table.shadows().len()
    && ret.iter().all(|diagnostic| diagnostic.severity == severity
        && diagnostic.code.as_deref() == Some(SHADOWING_BINDER)
        && diagnostic.related_information.len() <= 1_usize))]
#[must_use]
pub fn diagnostics(
    seen: &Seen<'_>,
    severity: Severity,
) -> Vec<Diagnostic>
{
    let mut locator = Locator::laid((seen.table, seen.opened), seen.uri, seen.index);
    seen.table
        .shadows()
        .iter()
        .filter_map(|&shadow| {
            let range = ranged(seen.index, shadow.binder)?;
            let name = spelled(seen.text, shadow.binder)?;
            let (hiding, site) = hidden(seen, &mut locator, shadow, name);
            let mut diagnostic = Diagnostic::new(range, severity, described(hiding, name));
            diagnostic.code = Some(String::from(SHADOWING_BINDER));
            diagnostic.related_information = site
                .into_iter()
                .map(|location| RelatedInformation {
                    location,
                    message: format!("the `{}` it hides", <&str>::from(name)),
                })
                .collect();
            Some(diagnostic)
        })
        .collect()
}

/// What `shadow`, a binder of `seen`'s text spelled `name`, hides, and the
/// location of the hidden binding's name, as `locator` places it.
///
/// # Specification
/// trivial.
fn hidden<'seen>(
    seen: &Seen<'seen>,
    locator: &mut Locator<'seen, 'seen>,
    shadow: Shadow,
    name: SourceText<'_>,
) -> (Hiding<'seen>, Option<Location>)
{
    let site = match seen.table.hidden_site(shadow.hidden) {
        Maybe::Present(site) => Some(site),
        Maybe::Absent(_) => None,
    };
    let location = site
        .and_then(|site| locator.place(&site))
        .map(|placed| Location {
            uri: placed.uri,
            range: placed.named,
        });
    let row = |span: ByteSpan| {
        seen.index
            .row_of_byte(RenderOffset::from(usize::from(span.start())))
    };
    let hiding = match shadow.hidden {
        Resolution::Binder(span) => Hiding::Binder(row(span)),
        Resolution::Builtin => Hiding::Builtin,
        Resolution::Constructor { family, .. } => match seen.table.printer_name(family) {
            Maybe::Present(family) => Hiding::Constructor(<&str>::from(family)),
            Maybe::Absent(_) => Hiding::Unplaced,
        },
        Resolution::Declaration(constant) => {
            let printed = match seen.table.printer_name(constant) {
                Maybe::Present(printed) => Some(printed),
                Maybe::Absent(_) => None,
            };
            declaration(seen, locator, (printed, site), name)
        },
    };
    (hiding, location)
}

/// How a hidden declaration is named: by the path the printer writes,
/// `printed`, when it differs from the binder's `name`; by its row when the
/// document writes it at `site`; else by the path of the source writing it and
/// its row there.
///
/// # Specification
/// trivial.
fn declaration<'seen>(
    seen: &Seen<'seen>,
    locator: &mut Locator<'seen, 'seen>,
    (printed, site): (Option<SourceText<'seen>>, Option<Referent>),
    name: SourceText<'_>,
) -> Hiding<'seen>
{
    if let Some(printed) = printed.filter(|&printed| <&str>::from(printed) != <&str>::from(name)) {
        return Hiding::Qualified(<&str>::from(printed));
    }
    let Some(site) = site
    else {
        return Hiding::Unplaced;
    };
    if site.source() == seen.table.own_source() {
        return Hiding::Declared(
            seen.index
                .row_of_byte(RenderOffset::from(usize::from(site.named().start()))),
        );
    }
    match (written(seen, site.source()), locator.row(&site)) {
        (Some(path), Some((_, row))) => Hiding::Imported(<&str>::from(path), row),
        (Some(_) | None, _) => Hiding::Unplaced,
    }
}

/// The path of the unit's source `source`, as `seen`'s document names it: the
/// address of the import that reads it, as written between its quotes; else
/// the file name of the path it was opened at.
///
/// # Specification
/// trivial.
fn written<'seen>(
    seen: &Seen<'seen>,
    source: SourceIndex,
) -> Option<SourceText<'seen>>
{
    seen.reading
        .addresses()
        .zip(seen.targets)
        .find(|&(_, target)| matches!(*target, ImportTarget::Source(read) if read == source))
        .and_then(|(span, _)| spelled(seen.text, span))
        .or_else(|| {
            seen.opened
                .get(usize::from(source))?
                .file_name()?
                .to_str()
                .map(SourceText::from)
        })
}

/// The text `text` writes over `span`.
///
/// # Specification
/// trivial.
fn spelled(
    text: SourceText<'_>,
    span: ByteSpan,
) -> Option<SourceText<'_>>
{
    <&str>::from(text)
        .get(usize::from(span.start()) .. usize::from(span.end()))
        .map(SourceText::from)
}

/// The words naming `hiding`, at a binder spelled `name`: the lens title
/// without its count, and the diagnostic's message.
///
/// # Specification
/// trivial.
fn described(
    hiding: Hiding<'_>,
    name: SourceText<'_>,
) -> String
{
    let name = <&str>::from(name);
    match hiding {
        Hiding::Binder(row) => format!(
            "shadows {name} (line {})",
            usize::from(row).saturating_add(1)
        ),
        Hiding::Declared(row) => format!(
            "shadows {name} (declared line {})",
            usize::from(row).saturating_add(1)
        ),
        Hiding::Qualified(printed) => format!("shadows {name} ({printed})"),
        Hiding::Imported(path, row) => format!(
            "shadows {name} ({path} line {})",
            usize::from(row).saturating_add(1)
        ),
        Hiding::Constructor(family) => format!("shadows {name} ({family}.{name})"),
        Hiding::Builtin => format!("shadows builtin {name}"),
        Hiding::Unplaced => format!("shadows {name}"),
    }
}
