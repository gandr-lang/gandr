//! World declarations and a site's offer, as the collection pass reads them.
//!
//! `world w ;` takes a slot like any top-level name, its definition half
//! [`Operand::World`](super::Operand::World): the declaration lowers to no core
//! term, and its admission position is the world's identity, which a handle
//! type `A at w`, a migration `migrate [w] { … }` and an entry `@[ entry(…) ]`
//! name. The name enters the module's namespace, so every position that reads a
//! world resolves it as it resolves any earlier declaration, and a world
//! declared twice is the duplicate definition any name declared twice is.
//!
//! `world w requires [ … ] ;` files the row's entries beside the slot
//! ([`super::Collected::requirements`]), as a labelled row writes them: what a
//! role placed at `w` needs, which a deployment holds each site placing `w` to
//! answer. The entries are resolved once every name is collected, as a row's
//! are.
//!
//! `offers [ … ] ;` takes no slot: it is a site's answer to the rows of the
//! worlds placed at it, filed by its source ([`super::Collected::offers`]),
//! each host interface by its name and each label with the module answering
//! it. A name no host declares, a label or an interface written twice and a
//! second offer in one source are refused as it is read; a module its source
//! does not declare, once the source is collected. Each is the offer's own
//! refusal, filed as a stray.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::host::HostSignatures;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Collector;
use super::Container;
use super::Stray;
use super::Tail;
use super::labelled;
use super::misplaced_in;
use super::strayed;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::resolve::HeadArity;
use crate::resolve::SurfaceName;
use crate::unit::SourceIndex;

/// One entry of a world's requirement row as it is written, `store : Store
/// with sort V = String`, read once every name is collected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RequiredEntry
{
    /// The operand before the `:`, the label code at the world performs
    /// through; none for an interface named whole.
    pub label: Maybe<Placed, labelled::Absent>,
    /// The interface's name.
    pub interface: Placed,
    /// Each sort the entry fixes, beside the operand it fixes it to.
    pub manifest: Vec<(Placed, NodeIndex)>,
    /// The bytes from the interface's name to the entry's end.
    pub written: ByteSpan,
}

/// A site's offer as it is written, `offers [ Console, store = Echo ] ;`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SiteOffer
{
    /// The declaration.
    pub declaration: Placed,
    /// Each host interface the site grants, by its name.
    pub granted: Vec<Placed>,
    /// Each label the site answers, beside the name of the module answering
    /// it.
    pub answered: Vec<(Placed, Placed)>,
    /// The attribute blocks standing before the declaration, which state what
    /// a refusal of it is expected to be.
    pub decorations: Vec<Placed>,
}

impl<'source> Collector<'_, 'source>
{
    /// Collect the deployment declaration `declaration`, a world's or a site's
    /// offer, decorated by the attribute blocks `decorations` standing before
    /// it.
    ///
    /// # Specification
    /// - requires: `declaration` is a world declaration or an offers form and
    ///   every entry of `decorations` an attribute block standing on its own
    ///   before it.
    /// - ensures: a world's name takes its slot in the declaration's source,
    ///   which owns the declaration and its decorations; a clean form files its
    ///   definition half, [`super::Operand::World`], its attributes and its
    ///   requirement row's entries; the form's first fault is offered to the
    ///   slot instead. An offer whose entries read is filed by its source with
    ///   its decorations, and its first fault otherwise is the inner refusal,
    ///   for the caller to file as a stray.
    /// - provides: the deployment half of [`super::collect_source`].
    /// - fails: when a world has no name to file a refusal under, or a form's
    ///   pieces do not read.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a nameless world and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declared world, a world declared twice and a world
    ///   named where none is declared separate filing from refusal; an offer
    ///   that reads is filed and each entry out of place refused by name.
    /// - witness: `lower::world::tests::a_world_declaration_names_its_world`
    /// - witness: `lower::world::tests::a_world_declared_twice_is_refused`
    /// - witness: `lower::world::tests::a_site_s_offer_answers_by_label_and_by_name_3523`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ret| ret.is_err() || self.collected.slots.len() >= before,
    )]
    pub(super) fn world(
        &mut self,
        declaration: Placed,
        decorations: &[Placed],
    ) -> Result<Result<(), LoweringRefusal<'source>>, LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        let outcome =
            read_pieces(self.pbg, self.tree, declaration.node, &mut pieces).and_then(|()| {
                if let Maybe::Present(_) =
                    Cursor::new(&pieces.pieces, declaration.span).at(TileName::OFFERS)
                {
                    Ok(self.read_offers(declaration, &pieces, decorations))
                }
                else {
                    self.read_world(declaration, &pieces, decorations).map(Ok)
                }
            });
        self.pieces = pieces;

        outcome
    }

    /// Read the world declaration `declaration` over its pieces.
    ///
    /// # Specification
    /// - requires: as [`Self::world`]; `pieces` is the declaration's reading.
    /// - ensures: as [`Self::world`].
    /// - fails: as [`Self::world`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::world`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::world`].
    /// - witness: `lower::world::tests::a_world_declaration_names_its_world`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.collected.owner_of(declaration.node), Maybe::Present(_)))]
    fn read_world(
        &mut self,
        declaration: Placed,
        pieces: &Pieces,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, declaration.span);
        let _world = cursor.tile(TileName::WORLD);
        let Maybe::Present(named) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(misplaced_in(FormName::WORLD_DECLARATION, cursor.here()));
        };
        let name = self.name_of(named);
        let slot = self.admit(
            self.collected.top(declaration.span.start()),
            name,
            declaration,
            named,
        );
        self.collected.own(declaration.node, slot);
        for &block in decorations {
            self.document(slot, block.node, block.span.end(), declaration.node);
        }
        self.document(slot, declaration.node, named.span.start(), declaration.node);
        let mut attributes = Vec::new();
        let mut attributed = Ok(());
        for &block in decorations {
            self.collected.own(block.node, slot);
            if attributed.is_ok() {
                attributed = self.decoration(block, declaration.node, &mut attributes);
            }
        }
        let (entries, read) = match read_requirement(&mut cursor) {
            Ok(entries) => (entries, Ok(())),
            Err(refusal) => (Vec::new(), Err(refusal)),
        };
        let closed = matches!(cursor.tile(TileName::SEMICOLON), Maybe::Present(_))
            && matches!(cursor.peek(), Maybe::Absent(_));
        let tail = if let Maybe::Present(repaired) = pieces.repair {
            Tail::Refused(repaired.refusal(FormName::WORLD_DECLARATION))
        }
        else if let Err(refusal) = attributed {
            Tail::Refused(refusal)
        }
        else if let Err(refusal) = read {
            Tail::Refused(refusal)
        }
        else if !closed {
            Tail::Refused(misplaced_in(FormName::WORLD_DECLARATION, cursor.here()))
        }
        else {
            Tail::World
        };
        if matches!(tail, Tail::World) && !entries.is_empty() {
            let _first = self.collected.requirements.insert(slot, entries);
        }
        self.file(slot, declaration, named, tail, attributes);

        Ok(())
    }

    /// Read the offer `declaration` over its pieces, filing it by its source.
    ///
    /// # Specification
    /// - requires: `declaration` is an offers form; `pieces` is its reading.
    /// - ensures: when every entry reads, the offer filed under its source, its
    ///   host interfaces and its labels with their modules in written order;
    ///   nothing filed otherwise.
    /// - fails: the form's repair; a misplaced tile; a host interface no host
    ///   declares; a label or an interface written twice; a second offer in the
    ///   source.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`],
    /// [`LoweringRefusal::UnresolvedTypeHead`] at a name no host declares,
    /// [`LoweringRefusal::DuplicateDefinition`] at a name written again or at
    /// the second offer, and [`LoweringRefusal::HostConflict`] for a host
    /// table that does not mint.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an offer of a host interface and a label settles; a
    ///   name no host declares, a label written twice and a second offer are
    ///   each refused by name.
    /// - witness: `lower::world::tests::a_site_s_offer_answers_by_label_and_by_name_3523`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.collected.offers.get(&self.collected.unit.source_at(declaration.span.start())), Some(offer) if offer.declaration == declaration))]
    fn read_offers(
        &mut self,
        declaration: Placed,
        pieces: &Pieces,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(FormName::OFFERS_DECLARATION));
        }
        let mut cursor = Cursor::new(&pieces.pieces, declaration.span);
        let _offers = cursor.tile(TileName::OFFERS);
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACKET_OPEN) {
            return Err(misplaced_in(FormName::OFFERS_DECLARATION, cursor.here()));
        }
        let table = HostSignatures::new(&mut CoreArena::new()).map_err(|_conflict| {
            LoweringRefusal::HostConflict {
                span: declaration.span,
            }
        })?;
        let mut granted = Vec::new();
        let mut answered = Vec::new();
        let mut written: BTreeMap<SurfaceName<'_>, ByteSpan> = BTreeMap::new();
        loop {
            let named = if let Maybe::Present(interface) = cursor.tile(TileName::TYPE_IDENTIFIER) {
                let name = self.name_of(interface);
                if let Maybe::Absent(_) = table.named(&EffectName::from(name.as_ref())) {
                    return Err(LoweringRefusal::UnresolvedTypeHead {
                        span: interface.span,
                        name,
                        arity: HeadArity::Nullary,
                    });
                }
                granted.push(interface);
                interface
            }
            else {
                let (Maybe::Present(label), Maybe::Present(_), Maybe::Present(module)) = (
                    cursor.tile(TileName::IDENTIFIER),
                    cursor.tile(TileName::EQUALS),
                    cursor.tile(TileName::TYPE_IDENTIFIER),
                )
                else {
                    return Err(misplaced_in(FormName::OFFERS_DECLARATION, cursor.here()));
                };
                answered.push((label, module));
                label
            };
            let name = self.name_of(named);
            if let Some(&first) = written.get(&name) {
                return Err(LoweringRefusal::DuplicateDefinition {
                    span: named.span,
                    name,
                    first,
                });
            }
            let _first = written.insert(name, named.span);
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                break;
            }
        }
        let closed = matches!(cursor.tile(TileName::BRACKET_CLOSE), Maybe::Present(_))
            && matches!(cursor.tile(TileName::SEMICOLON), Maybe::Present(_))
            && matches!(cursor.peek(), Maybe::Absent(_));
        if !closed {
            return Err(misplaced_in(FormName::OFFERS_DECLARATION, cursor.here()));
        }
        let source = self.collected.unit.source_at(declaration.span.start());
        if let Some(first) = self.collected.offers.get(&source) {
            return Err(LoweringRefusal::DuplicateDefinition {
                span: declaration.span,
                name: SurfaceName::from("offers"),
                first: first.declaration.span,
            });
        }
        let _first = self.collected.offers.insert(source, SiteOffer {
            declaration,
            granted,
            answered,
            decorations: decorations.to_vec(),
        });

        Ok(())
    }

    /// Withdraw the offer of the source `source` when a label names a module
    /// the source does not declare at its top level, filing its refusal as a
    /// stray onto `strays`.
    ///
    /// # Specification
    /// - requires: every module of `source` is collected.
    /// - ensures: the offer kept, when each module it names is one `source`
    ///   declares at its top level, and the first attribute block before it
    ///   filed as a stray decorating nothing; otherwise the offer withdrawn and
    ///   a stray filed at it, refused [`LoweringRefusal::UnresolvedName`] at
    ///   the first module the source does not declare and decorated by the
    ///   offer's attribute blocks, which state what it is expected to be.
    /// - fails: a fault reading an attribute block that is no stray's own.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`super::strayed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a label answered by a module of the source settles,
    ///   and one answered by a name the source declares no module under is
    ///   refused at the name.
    /// - witness: `lower::world::tests::a_site_s_offer_answers_by_label_and_by_name_3523`
    #[spec(
        captures: before = strays.len(),
        ensures: |ret| ret.is_err() || strays.len() <= before.saturating_add(1),
    )]
    pub(super) fn answered(
        &mut self,
        source: SourceIndex,
        strays: &mut Vec<Stray<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(offer) = self.collected.offers.get(&source)
        else {
            return Ok(());
        };
        let unanswered = offer.answered.iter().find_map(|&(_, module)| {
            let name = self.name_of(module);
            (!self
                .collected
                .modules
                .contains_key(&(Container::TopLevel(source), name)))
            .then_some((module, name))
        });
        let first = offer.decorations.first().copied();
        if let Some((module, name)) = unanswered {
            if let Some(withdrawn) = self.collected.offers.remove(&source) {
                strays.push(Stray::of(
                    withdrawn.declaration,
                    LoweringRefusal::UnresolvedName {
                        span: module.span,
                        name,
                    },
                    withdrawn.decorations,
                ));
            }
            return Ok(());
        }
        if let Some(block) = first
            && let Some(refusal) = strayed(self.module_child(block))?
        {
            strays.push(Stray::of(block, refusal, Vec::new()));
        }

        Ok(())
    }
}

/// The row after `requires`, read off `cursor` where it stands: each entry's
/// label, interface, fixed sorts and bytes; none when no `requires` follows.
///
/// # Specification
/// - requires: `cursor` stands after a world declaration's name.
/// - ensures: empty, the cursor unmoved, when the next tile is no `requires`;
///   otherwise one entry per comma-separated entry between the brackets, in
///   written order, the cursor past the `]`.
/// - fails: a tile out of its place in the row.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`] at the tile that stands out of place.
///
/// # Adequacy
/// - hypothesis: L3 — a world requiring a host interface and a labelled theory
///   files both entries; one written with none files nothing.
/// - witness: `lower::world::tests::a_world_s_requirement_is_a_row_3523`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.is_sorted_by_key(|entry| entry.written.start())))]
fn read_requirement(cursor: &mut Cursor<'_>)
-> Result<Vec<RequiredEntry>, LoweringRefusal<'static>>
{
    let mut entries = Vec::new();
    if let Maybe::Absent(_) = cursor.tile(TileName::REQUIRES) {
        return Ok(entries);
    }
    let misplaced = |cursor: &Cursor<'_>| misplaced_in(FormName::WORLD_DECLARATION, cursor.here());
    if let Maybe::Absent(_) = cursor.tile(TileName::BRACKET_OPEN) {
        return Err(misplaced(cursor));
    }
    loop {
        let label = match cursor.peek() {
            Maybe::Present(Piece::Operand(written)) => {
                let _label = cursor.read();
                if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
                    return Err(misplaced(cursor));
                }
                Maybe::Present(written)
            },
            Maybe::Present(Piece::Tile { .. }) | Maybe::Absent(_) => {
                Maybe::Absent(labelled::Absent::Whole)
            },
        };
        let Maybe::Present(interface) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(misplaced(cursor));
        };
        let mut manifest = Vec::new();
        let mut end = interface.span.end();
        while let Maybe::Present(_) = cursor.tile(TileName::WITH) {
            let Maybe::Present(_) = cursor.tile(TileName::SORT)
            else {
                return Err(misplaced(cursor));
            };
            let Maybe::Present(sort) = cursor.tile(TileName::TYPE_IDENTIFIER)
            else {
                return Err(misplaced(cursor));
            };
            let Maybe::Present(_) = cursor.tile(TileName::EQUALS)
            else {
                return Err(misplaced(cursor));
            };
            let Maybe::Present(Piece::Operand(ty)) = cursor.read()
            else {
                return Err(misplaced(cursor));
            };
            manifest.push((sort, ty.node));
            end = ty.span.end();
        }
        let Ok(written) = ByteSpan::new(interface.span.start(), end)
        else {
            return Err(misplaced(cursor));
        };
        entries.push(RequiredEntry {
            label,
            interface,
            manifest,
            written,
        });
        if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
            break;
        }
    }
    if let Maybe::Absent(_) = cursor.tile(TileName::BRACKET_CLOSE) {
        return Err(misplaced(cursor));
    }

    Ok(entries)
}
