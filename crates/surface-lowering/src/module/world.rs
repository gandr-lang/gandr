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
//! it. A label's module may be read through a translation: `via f` names a
//! flow, which resolves as an import's `via` does, and `renaming { a as b }`
//! names a renaming of the module's members. A name no host declares, a label
//! or an interface written twice, a name a renaming gives twice and a second
//! offer in one source are refused as it is read; a module its source does not
//! declare, a flow that does not resolve and a renaming its module refuses,
//! once the source is collected. Each is the offer's own refusal, filed as a
//! stray.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::host::HostSignatures;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use super::Collector;
use super::Container;
use super::Member;
use super::Stray;
use super::Tail;
use super::labelled;
use super::misplaced_in;
use super::read_translation;
use super::strayed;
use super::written_translation;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::WrittenPath;
use crate::form::entry_path;
use crate::form::read_pieces;
use crate::import::ImportResolution;
use crate::import::RenamingFault;
use crate::import::WrittenTranslation;
use crate::import::direct;
use crate::resolve::HeadArity;
use crate::resolve::SurfaceName;
use crate::unit::ImportTarget;
use crate::unit::SourceIndex;

/// One entry of a world's requirement row as it is written, `store : Store
/// with sort V = String`, read once every name is collected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RequiredEntry
{
    /// The operand before the `:`, the label code at the world performs
    /// through; none for an interface named whole.
    pub label: Maybe<Placed, labelled::Absent>,
    /// The interface's path.
    pub interface: WrittenPath,
    /// Each sort the entry fixes, beside the operand it fixes it to.
    pub manifest: Vec<(Placed, NodeIndex)>,
    /// The bytes from the interface's path to the entry's end.
    pub written: ByteSpan,
}

/// A site's offer as it is written, `offers [ Console, store = Echo ] ;`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SiteOffer
{
    /// The declaration.
    pub declaration: Placed,
    /// Each host interface the site grants, by its path.
    pub granted: Vec<WrittenPath>,
    /// Each label the site answers, in written order.
    pub answered: Vec<AnsweredEntry>,
    /// The attribute blocks standing before the declaration, which state what
    /// a refusal of it is expected to be.
    pub decorations: Vec<Placed>,
}

/// One label a site's offer answers, as it is written, `store = Echo`,
/// `store = Echo via downgrade` or `store = Echo renaming { fetch as get }`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AnsweredEntry
{
    /// The label's tile.
    pub label: Placed,
    /// The name tile of the module answering it.
    pub module: Placed,
    /// The translation the module is read through, as its tiles spell it.
    pub translation: Maybe<WrittenTranslation, direct::Absent>,
    /// The name tiles of the members of the flow `via` names that do more
    /// than rename one member, once the source is collected; empty for an
    /// entry with no flow.
    pub rewritten: Vec<Placed>,
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
        for &block in decorations {
            self.collected.own(block.node, slot);
        }
        let mut attributes = Vec::new();
        let attributed = self
            .decorations(decorations, declaration.node, &mut attributes)
            .map_err(|(_block, refusal)| refusal);
        let (entries, read) = match read_requirement(self.pbg, self.tree, &mut cursor) {
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
    ///   host interfaces and its labels with their modules in written order,
    ///   each label with the translation written after its module, as
    ///   [`read_translation`] reads it; nothing filed otherwise.
    /// - fails: the form's repair; a misplaced tile; a host interface no host
    ///   declares; a label or an interface written twice; a member a renaming
    ///   reads twice or a name it gives twice; a second offer in the source.
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
    ///   each refused by name; a label read via a flow and one read through a
    ///   renaming keep their translations.
    /// - witness: `lower::world::tests::a_site_s_offer_answers_by_label_and_by_name_3523`
    /// - witness: `lower::world::tests::an_offer_names_the_translation_it_answers_a_label_through_3461`
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
            let named = if let Maybe::Present((interface, fixed)) =
                entry_path(self.pbg, self.tree, &mut cursor)?
            {
                // An offer grants a host interface whole, fixing no sort.
                if let Some(&(sort, _)) = fixed.first() {
                    return Err(misplaced_in(FormName::OFFERS_DECLARATION, sort.span));
                }
                let name = interface.name(self.tree);
                if let Maybe::Absent(_) = table.named(&EffectName::from(name.as_ref())) {
                    return Err(LoweringRefusal::UnresolvedTypeHead {
                        span: interface.span(),
                        name,
                        arity: HeadArity::Nullary,
                    });
                }
                let named = (interface.span(), name);
                granted.push(interface);
                named
            }
            else {
                let mut named = Pieces::new();
                let label = match cursor.read() {
                    Maybe::Present(Piece::Operand(label)) => {
                        self.lone_name(label.node, &mut named)?
                    },
                    Maybe::Present(Piece::Tile { .. }) | Maybe::Absent(_) => None,
                };
                let (Some(label), Maybe::Present(_), Maybe::Present(module)) = (
                    label,
                    cursor.tile(TileName::EQUALS),
                    cursor.tile(TileName::TYPE_IDENTIFIER),
                )
                else {
                    return Err(misplaced_in(FormName::OFFERS_DECLARATION, cursor.here()));
                };
                let translation = match read_translation(&mut cursor) {
                    Maybe::Present(WrittenTranslation::Renaming(pairs)) => {
                        let _named = self.renaming_of(&pairs)?;
                        Maybe::Present(WrittenTranslation::Renaming(pairs))
                    },
                    Maybe::Present(via) => Maybe::Present(via),
                    Maybe::Absent(written_translation::Absent::Unwritten) => {
                        Maybe::Absent(direct::Absent::Unwritten)
                    },
                    Maybe::Absent(written_translation::Absent::Misplaced) => {
                        return Err(misplaced_in(FormName::OFFERS_DECLARATION, cursor.here()));
                    },
                };
                answered.push(AnsweredEntry {
                    label,
                    module,
                    translation,
                    rewritten: Vec::new(),
                });
                (label.span, self.name_of(label))
            };
            let (span, name) = named;
            if let Some(&first) = written.get(&name) {
                return Err(LoweringRefusal::DuplicateDefinition { span, name, first });
            }
            let _first = written.insert(name, span);
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

    /// Withdraw the offer of the source `source` when it grants a host
    /// interface whose module the source does not import, a label names a
    /// module the source does not declare at its top level, or a label's
    /// translation does not hold, filing its refusal as a stray onto
    /// `strays`.
    ///
    /// # Specification
    /// - requires: every module and import of `source` is collected.
    /// - ensures: the offer kept, when the source reaches each host interface
    ///   it grants, each module it names is one `source` declares at its top
    ///   level and each translation holds as [`Self::translated`] reads it,
    ///   each flow's rewritten members filed with its label, and the first
    ///   attribute block before it filed as a stray decorating nothing;
    ///   otherwise the offer withdrawn and a stray filed at it, refused
    ///   [`LoweringRefusal::UnresolvedTypeHead`] at the first interface the
    ///   source does not reach, or else [`LoweringRefusal::UnresolvedName`] at
    ///   the first module the source does not declare, or else the first
    ///   refusal of a translation, and decorated by the offer's attribute
    ///   blocks, which state what it is expected to be.
    /// - fails: a fault reading an attribute block that is no stray's own.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`super::strayed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a label answered by a module of the source settles,
    ///   and one answered by a name the source declares no module under is
    ///   refused at the name; an interface whose module the source imports
    ///   after the offer settles, and one it does not import is refused; a
    ///   label read via a flow and through a renaming settle, and a flow that
    ///   does not resolve is refused at its name.
    /// - witness: `lower::world::tests::a_site_s_offer_answers_by_label_and_by_name_3523`
    /// - witness: `lower::world::tests::an_offer_names_the_translation_it_answers_a_label_through_3461`
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
        // A host interface is reached through an import the source may write
        // after its offer, so the offer's interfaces are read once the source
        // is collected (#4523).
        let unreached = offer.granted.iter().find_map(|interface| {
            let name = interface.name(self.tree);
            (!self
                .collected
                .reaches(interface.span().start(), &EffectName::from(name.as_ref()))
                .0)
                .then_some(LoweringRefusal::UnresolvedTypeHead {
                    span: interface.span(),
                    name,
                    arity: HeadArity::Nullary,
                })
        });
        let unanswered = || {
            offer.answered.iter().find_map(|entry| {
                let name = self.name_of(entry.module);
                (!self
                    .collected
                    .modules
                    .contains_key(&(Container::TopLevel(source), name)))
                .then_some(LoweringRefusal::UnresolvedName {
                    span: entry.module.span,
                    name,
                })
            })
        };
        let first = offer.decorations.first().copied();
        let granted: Vec<_> = offer
            .granted
            .iter()
            .map(|interface| {
                (
                    interface.span().start(),
                    EffectName::from(interface.name(self.tree).as_ref()),
                )
            })
            .collect();
        let refused = unreached.or_else(unanswered).map_or_else(
            || {
                offer
                    .answered
                    .iter()
                    .map(|entry| self.translated(source, offer.declaration, entry))
                    .collect::<Result<Vec<_>, _>>()
            },
            Err,
        );
        let rewritten = match refused {
            Ok(rewritten) => rewritten,
            Err(refusal) => {
                if let Some(withdrawn) = self.collected.offers.remove(&source) {
                    strays.push(Stray::of(
                        withdrawn.declaration,
                        refusal,
                        withdrawn.decorations,
                    ));
                }
                return Ok(());
            },
        };
        if let Some(offer) = self.collected.offers.get_mut(&source) {
            for (entry, members) in offer.answered.iter_mut().zip(rewritten) {
                entry.rewritten = members;
            }
        }
        for (at, named) in granted {
            self.collected.reach_host(at, &named);
        }
        if let Some(block) = first
            && let Some(refusal) = strayed(self.module_child(block))?
        {
            strays.push(Stray::of(block, refusal, Vec::new()));
        }

        Ok(())
    }

    /// The name tiles of the members of the flow the label `entry` of the
    /// offer `declaration`, in `source`, is read through, when its
    /// translation holds.
    ///
    /// # Specification
    /// - requires: every module and import of `source` is collected, and
    ///   `entry`'s module is one `source` declares at its top level.
    /// - ensures: for `via f`, the members of the flow `f` resolves to that do
    ///   more than rename one member ([`Self::rewritten`]), `f` resolving as
    ///   [`super::Collected::translation_flow`] resolves it before the offer, a
    ///   source `source` imports publishing it; none for a renaming that holds
    ///   or an entry with no translation.
    /// - fails: a flow that does not resolve; a renaming the module refuses.
    /// - panics: none.
    /// - executable: none — the clause restates the flow's resolution and the
    ///   walk over the module's exports.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnresolvedName`] at a flow's name that resolves to
    /// no flow; [`LoweringRefusal::UnknownMember`] at a renaming's member the
    /// module does not export; [`LoweringRefusal::DuplicateDefinition`] at a
    /// renaming's name the module keeps for a member of its own.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::answered`].
    /// - witness: `lower::world::tests::an_offer_names_the_translation_it_answers_a_label_through_3461`
    fn translated(
        &self,
        source: SourceIndex,
        declaration: Placed,
        entry: &AnsweredEntry,
    ) -> Result<Vec<Placed>, LoweringRefusal<'source>>
    {
        let pairs = match entry.translation {
            Maybe::Present(WrittenTranslation::Via(flow)) => {
                let name = self.name_of(flow);
                let imports = &self.collected.imports;
                let published = |at: SourceIndex| {
                    imports.of(source).any(|import| {
                        import.resolution() == ImportResolution::Path(ImportTarget::Source(at))
                    })
                };
                return match self.collected.translation_flow(
                    source,
                    declaration.span.start(),
                    name,
                    published,
                ) {
                    Maybe::Present(index) => Ok(self.rewritten(index)),
                    Maybe::Absent(_) => Err(LoweringRefusal::UnresolvedName {
                        span: flow.span,
                        name,
                    }),
                };
            },
            Maybe::Present(WrittenTranslation::Renaming(ref pairs)) => pairs,
            Maybe::Absent(_) => return Ok(Vec::new()),
        };
        let module = self.name_of(entry.module);
        let Some(structure) = self
            .collected
            .modules
            .get(&(Container::TopLevel(source), module))
            .and_then(|&index| self.collected.structures.get(usize::from(index)))
        else {
            return Ok(Vec::new());
        };
        // Each member the module exports, by name, beside the bytes of its
        // first declaration.
        let mut exported: BTreeMap<SurfaceName<'source>, ByteSpan> = BTreeMap::new();
        for &export in &structure.exports {
            let member = match export {
                Member::Slot(slot) => self
                    .collected
                    .slots
                    .get(usize::from(slot))
                    .map(|member| (member.name, member.named.span)),
                Member::Module(nested) => self
                    .collected
                    .structures
                    .get(usize::from(nested))
                    .map(|member| (member.name, member.declared_by.span)),
            };
            if let Some((name, span)) = member {
                exported.entry(name).or_insert(span);
            }
        }
        for component in structure.exported_types() {
            exported
                .entry(component.name)
                .or_insert(structure.declared_by.span);
        }
        let members: Vec<SurfaceName<'source>> = exported.keys().copied().collect();
        let renaming = self.renaming_of(pairs)?;
        let Maybe::Present((at, fault)) = renaming.unrenamable(&members)
        else {
            return Ok(Vec::new());
        };
        let (Some(&(read, given)), Some(&(member, named))) = (
            pairs.get(usize::from(at)),
            renaming.pairs().get(usize::from(at)),
        )
        else {
            return Ok(Vec::new());
        };
        Err(match fault {
            RenamingFault::Missing => LoweringRefusal::UnknownMember {
                span: read.span,
                module,
                member,
            },
            RenamingFault::Clash => LoweringRefusal::DuplicateDefinition {
                span: given.span,
                name: named,
                first: exported
                    .get(&named)
                    .copied()
                    .unwrap_or(structure.declared_by.span),
            },
        })
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
/// - fails: a tile out of its place in the row; a form fault reading an entry's
///   links.
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
fn read_requirement<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    cursor: &mut Cursor<'_>,
) -> Result<Vec<RequiredEntry>, LoweringRefusal<'source>>
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
        // An operand the `:` follows is the entry's label; one alone spells a
        // package's path, `std.fs.Eff`.
        let mut label = Maybe::Absent(labelled::Absent::Whole);
        if let Maybe::Present(Piece::Operand(written)) = cursor.peek() {
            let mut ahead = cursor.clone();
            let _label = ahead.read();
            if let Maybe::Present(_) = ahead.tile(TileName::COLON) {
                *cursor = ahead;
                label = Maybe::Present(written);
            }
        }
        let Maybe::Present((interface, fixed)) = entry_path(pbg, tree, cursor)?
        else {
            return Err(misplaced(cursor));
        };
        let mut end = fixed
            .last()
            .map_or_else(|| interface.last.span.end(), |&(_, ty)| ty.span.end());
        let mut manifest: Vec<(Placed, NodeIndex)> = fixed
            .into_iter()
            .map(|(sort, ty)| (sort, ty.node))
            .collect();
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
        let Ok(written) = ByteSpan::new(interface.span().start(), end)
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
