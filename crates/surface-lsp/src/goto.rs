//! Definitions and declarations: where what a written name refers to is
//! written, and where the families the type of a node names are declared.
//!
//! A definition or declaration request reads the referent index the
//! document's type table keeps ([`TypeTable::referent`]): every use the
//! lowering resolved, with the binder or declaration it resolved to, built
//! once per text beside the types a hover reads. A name declared in two
//! halves answers its definition half to a definition request and its
//! signature half to a declaration request ([`TypeTable::half`]), and a name
//! written once answers that form to both. A type-definition request reads the
//! families the chosen node's type names ([`TypeTable::type_referents`]). None
//! resolves a name again, and none reads the text for one.
//!
//! A referent in a sibling the document imports is answered at the sibling's
//! path, its position counted in the sibling's text as the closure laid it out.
//! A position just past a name answers the name, as a caret left at a name's
//! end means it.
//!
//! [`TypeTable::referent`]: gandr_surface_dispatcher::TypeTable::referent
//! [`TypeTable::half`]: gandr_surface_dispatcher::TypeTable::half
//! [`TypeTable::type_referents`]: gandr_surface_dispatcher::TypeTable::type_referents

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::DeclaredHalf;
use gandr_surface_dispatcher::Referent;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::hover::Hovering;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::Answer;
use crate::protocol::DocumentUri;
use crate::protocol::Linked;
use crate::protocol::Location;
use crate::protocol::LocationLink;

/// Which request a definition answers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Goto
{
    /// `textDocument/definition`: what the name at the position refers to,
    /// at its definition half.
    Definition,
    /// `textDocument/declaration`: what the name at the position refers to,
    /// at its signature half.
    Declaration,
    /// `textDocument/typeDefinition`: the families the type of the node at
    /// the position names.
    TypeDefinition,
}

/// The range `span` covers in the text `index` indexes.
///
/// # Specification
/// trivial.
pub fn ranged(
    index: &LineIndex<'_>,
    span: ByteSpan,
) -> Option<Range>
{
    Range::of_bytes(
        index,
        RenderOffset::from(usize::from(span.start())),
        RenderOffset::from(usize::from(span.end())),
    )
    .ok()
}

/// Where a referent is declared: the document holding it, the whole binder
/// or declaring form, and its name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Placed
{
    /// The document: the request's own, or a sibling's path as a `file` URI.
    pub uri: DocumentUri,
    /// The binder or declaring form, whole.
    pub whole: Range,
    /// Its name.
    pub named: Range,
}

/// The places of the referents one document's table answers, each sibling's
/// text indexed once however many referents it declares.
pub struct Locator<'held, 'text>
{
    /// What the document's copy keeps for its hovers.
    hovering: &'held Hovering,
    /// The document.
    uri: &'held DocumentUri,
    /// The document's text, indexed.
    index: &'held LineIndex<'text>,
    /// Each sibling asked about: its URI and its text indexed, or none when
    /// its source names no path or keeps no text.
    siblings: BTreeMap<SourceIndex, Option<(DocumentUri, LineIndex<'held>)>>,
}

impl<'held, 'text> Locator<'held, 'text>
{
    /// A locator over the document at `uri`, whose text `index` indexes and
    /// whose copy keeps `hovering`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub const fn new(
        hovering: &'held Hovering,
        uri: &'held DocumentUri,
        index: &'held LineIndex<'text>,
    ) -> Self
    {
        Self {
            hovering,
            uri,
            index,
            siblings: BTreeMap::new(),
        }
    }

    /// Where `referent` is declared.
    ///
    /// # Specification
    /// - requires: `referent` was answered by the table `hovering` keeps.
    /// - ensures: a referent of the document itself is placed in it, its ranges
    ///   counted in its text; one of a sibling is placed at the sibling's path
    ///   as a `file` URI, its ranges counted in the sibling's text as the
    ///   closure laid it out, that text indexed on the first referent asked of
    ///   it; none when the sibling names no path or keeps no text, or a span
    ///   falls outside its text.
    /// - provides: the targets of a definition request and the locations of an
    ///   inlay hint's label.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the ranges are counted in texts the predicate would
    ///   have to index again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name declared in the document and one a sibling
    ///   declares are each placed at their declaring form.
    /// - witness: `server::tests::definition_answers_what_a_use_refers_to_795`
    /// - witness: `tests::session::a_definition_in_a_sibling_answers_the_sibling_s_path_795`
    pub fn place(
        &mut self,
        referent: &Referent,
    ) -> Option<Placed>
    {
        let table = self.hovering.table();
        let (uri, index) = if referent.source() == table.own_source() {
            (self.uri, self.index)
        }
        else {
            let hovering = self.hovering;
            let sibling = self
                .siblings
                .entry(referent.source())
                .or_insert_with(|| {
                    let uri = hovering.path(referent).and_then(DocumentUri::of_path)?;
                    let text = hovering.table().source_text(referent.source())?;
                    Some((uri, LineIndex::new(<&str>::from(text).into())))
                })
                .as_ref()?;
            (&sibling.0, &sibling.1)
        };
        Some(Placed {
            uri: uri.clone(),
            whole: ranged(index, referent.extent())?,
            named: ranged(index, referent.named())?,
        })
    }
}

/// What a `goto` request at `position` of `text`, the document at `uri` whose
/// copy keeps `hovering`, answers to a client that takes links as `linked`
/// says.
///
/// # Specification
/// - requires: `hovering` was read off `text`.
/// - ensures: for [`Goto::Definition`] and [`Goto::Declaration`], the referent
///   of the use holding the position's byte, or else the byte before it, at its
///   definition half or its signature half respectively, as [`TypeTable::half`]
///   answers it; for [`Goto::TypeDefinition`], the declaration of each family
///   the type of the node there names, in the order the table answers them.
///   Each target is named by the request's URI when it stands in the document
///   itself, and by its source's path as a `file` URI when it stands in a
///   sibling, its ranges counted in that source's text: links from the use, or
///   from the node, to the whole binder or declaring form with its name
///   selected when `linked` holds, the name's location otherwise. A target
///   whose source names no path or no range is dropped; none is the empty
///   answer.
/// - provides: the answer to `textDocument/definition`,
///   `textDocument/declaration` and `textDocument/typeDefinition` for a held
///   document.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter's use, a declaration's use and a constructor
///   in a pattern answer their sites, as links and as locations; a caret just
///   past a name answers it; a keyword answers nothing; a use's type answers
///   its family; a name a sibling declares answers the sibling's path; a name
///   declared in two halves answers its definition to a definition request and
///   its signature to a declaration request.
/// - witness: `server::tests::definition_answers_what_a_use_refers_to_795`
/// - witness: `server::tests::a_two_half_name_answers_each_half_and_renames_both_1034`
/// - witness: `server::tests::type_definition_answers_the_family_a_use_s_type_names_795`
/// - witness: `tests::session::a_definition_in_a_sibling_answers_the_sibling_s_path_795`
///
/// [`TypeTable::half`]: gandr_surface_dispatcher::TypeTable::half
#[spec(ensures: |ret| matches!(ret, Answer::Links(_) | Answer::Locations(_))
    && matches!(ret, Answer::Links(_)) == linked.0)]
#[must_use]
pub fn targets(
    text: SourceText<'_>,
    uri: &DocumentUri,
    hovering: &Hovering,
    position: Position,
    goto: Goto,
    linked: Linked,
) -> Answer
{
    let table = hovering.table();
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    let before = usize::from(at).checked_sub(1_usize).map(ByteOffset::from);
    let (origin, referents): (Option<ByteSpan>, Vec<Referent>) = match goto {
        Goto::Definition | Goto::Declaration => {
            let found = match table.referent(at) {
                Maybe::Present(found) => Some(found),
                Maybe::Absent(_) => before.and_then(|before| match table.referent(before) {
                    Maybe::Present(found) => Some(found),
                    Maybe::Absent(_) => None,
                }),
            };
            let half = match goto {
                Goto::Declaration => DeclaredHalf::Signature,
                Goto::Definition | Goto::TypeDefinition => DeclaredHalf::Definition,
            };
            match found {
                Some((span, referent)) => (Some(span), Vec::from([table.half(referent, half)])),
                None => (None, Vec::new()),
            }
        },
        Goto::TypeDefinition => {
            let probe = if table.answering(at).is_some() {
                Some(at)
            }
            else {
                before.filter(|&before| table.answering(before).is_some())
            };
            probe.map_or_else(
                || (None, Vec::new()),
                |probe| (table.answering(probe), table.type_referents(probe)),
            )
        },
    };
    let origin = origin.and_then(|span| ranged(&index, span));
    let mut locator = Locator::new(hovering, uri, &index);
    let mut links = Vec::with_capacity(referents.len());
    for referent in referents {
        if let (Some(origin), Some(placed)) = (origin, locator.place(&referent)) {
            links.push(LocationLink {
                origin_selection_range: origin,
                target_uri: placed.uri,
                target_range: placed.whole,
                target_selection_range: placed.named,
            });
        }
    }
    if linked.0 {
        Answer::Links(links)
    }
    else {
        Answer::Locations(
            links
                .into_iter()
                .map(|link| Location {
                    uri: link.target_uri,
                    range: link.target_selection_range,
                })
                .collect(),
        )
    }
}
