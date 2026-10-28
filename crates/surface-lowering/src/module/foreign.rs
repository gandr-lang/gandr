//! Extern blocks, as the collection pass reads them.
//!
//! `extern "rust" from "library" as Name { def f(x : u32, …) -> u32 ; … }`
//! declares one effect interface, named by its alias or else its library, each
//! bodiless member an operation whose payload is its arguments and whose reply
//! is its result. A row names the interface, `[Name]`, and a call performs one
//! of its operations, `Name.f(…)`; no handler the source writes answers it, so
//! the run offers it to its host, which the program's Rust caller supplies. A
//! block declares no name in the source's namespace, and its interface is read
//! in the source declaring it alone.
//!
//! A source reads an interface name through one table. The host's interfaces
//! seed the table. Each block of the source goes in over them. A block thus
//! shadows the host's interface of its name. A source with no block reads the
//! seed itself.
//!
//! Three forms read the host's interfaces alone: the operations of a
//! capability type, the label of an instance in a row, and the interfaces of a
//! world's offer.
//!
//! A block carrying `@[ boundary(rows) ]` takes one slot, entered in no name
//! table: the check that each member realises the row the attribute names for
//! it, in written order ([`BoundarySlot`]). The lowering mints its body, a call
//! of `std.boundary`'s `admitBlock` on the members' codes and the rows. Any
//! other block takes no slot, like an import.
//!
//! A member's types are the four fixed-width atoms, `u32`, `u64`, `i32` and
//! `i64`, each crossing as itself. A member beyond them (another type, a mode,
//! an untyped parameter, no result) and a `type T ;` member are out of the
//! form, refused at the piece, as a block of another language is refused
//! whole: the lowering does not reach them yet (#327).
//!
//! # References
//!
//! - `vault:01a178aa-a7bd-7d03-a728-feae5af9d1a8` — background: a block
//!   declares one effect signature named by its library namespace, each
//!   bodiless member an operation, and a declared namespace shadows a host
//!   interface of its name.

use alloc::collections::BTreeMap;
use alloc::collections::btree_map::Entry;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::host::INTERFACES;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerWidth;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use super::Collected;
use super::Collector;
use super::DeclarationSlot;
use super::Half;
use super::Operand;
use super::Payload;
use super::Role;
use super::SlotIndex;
use super::declaration_half;
use super::misplaced_in;
use super::quoted;
use super::slot_refusal;
use crate::attribute::RegisteredAttribute;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::resolve::SurfaceName;
use crate::unbuilt::Unbuilt;
use crate::unit::SourceIndex;

/// The language whose blocks the collection reads.
const RUST: &str = "rust";

/// The widths a member's type may name, each by its own spelling.
const WIDTHS: [IntegerWidth; 4] = [
    IntegerWidth::U32,
    IntegerWidth::U64,
    IntegerWidth::I32,
    IntegerWidth::I64,
];

/// An interface an extern block declares: its name, where it is named, and
/// its operations in the order the block writes them.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: no two operations share a name.
/// - executable: none — the collection builds the record and refuses a repeated
///   member before it is kept.
///
/// # Adequacy
/// - hypothesis: L3 — a block of two members declares both, in order, and a
///   member written twice is refused at the second.
/// - witness: `lower::capability::tests::an_extern_block_declares_an_interface_its_callers_perform_2901`
/// - witness: `lower::capability::tests::an_extern_block_beyond_the_form_is_refused_at_the_piece_2901`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignInterface
{
    /// The interface's name: the block's alias, or else its library.
    pub name: EffectName,
    /// The bytes naming it: the alias, or else the library's quotes.
    pub named: ByteSpan,
    /// One operation per member, in written order.
    pub operations: Vec<ForeignOperation>,
}

/// A member of an extern block, as the operation it declares: its name, its
/// parameters in order, and its result's type.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignOperation
{
    /// The member's name.
    pub name: OperationName,
    /// Where the member's name is written.
    pub named: Placed,
    /// Each parameter, in written order.
    pub parameters: Vec<ForeignParameter>,
    /// The result's type.
    pub result: ForeignType,
}

/// A parameter of a member: where its name is written, and its type.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ForeignParameter
{
    /// The parameter's name tile.
    pub named: Placed,
    /// Its type.
    pub ty: ForeignType,
}

/// A type a member writes: the width it spells and where it is written.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ForeignType
{
    /// The width the type spells.
    pub width: IntegerWidth,
    /// Where the type is written.
    pub written: Placed,
}

/// What the collection makes of an extern block.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub(super) enum Foreign<'source>
{
    /// A block of another language, which the lowering refuses whole as it
    /// refuses any form standing where a declaration does.
    Other,
    /// A block whose interface the collection keeps.
    Declared(Arc<ForeignInterface>),
    /// A block refused at its first piece beyond the form.
    Refused(LoweringRefusal<'source>),
}

/// The check an extern block carrying `boundary` takes a slot for: the
/// interface it declares, and the attribute's payload, which names one row
/// per member in written order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoundarySlot
{
    /// The interface the block declares.
    pub interface: Arc<ForeignInterface>,
    /// The attribute's payload.
    pub rows: Payload,
}

/// Whether an extern block took the slot its `boundary` attribute asks for.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub(super) struct Bounded(pub bool);

/// Where an interface a source reads by name comes from.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Provider
{
    /// The host's interface of the name.
    Host,
    /// The interface an extern block of the source declares under the name.
    Block(Arc<ForeignInterface>),
}

/// The interface names each source reads.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Interfaces
{
    /// What a source with no block reads: the host's interfaces alone.
    seed: BTreeMap<EffectName, Provider>,
    /// What each source with a block reads: the seed with each block over it.
    sources: BTreeMap<SourceIndex, BTreeMap<EffectName, Provider>>,
}

impl Default for Interfaces
{
    /// The host's interfaces, before any block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            seed: INTERFACES
                .into_iter()
                .map(|name| (EffectName::from(name), Provider::Host))
                .collect(),
            sources: BTreeMap::new(),
        }
    }
}

impl Interfaces
{
    /// Declare `interface`, the interface of an extern block of `source`,
    /// under its name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `source` reads the name as the block. Every other source
    ///   reads the name as before.
    /// - fails: when a block of `source` already holds the name. What any
    ///   source reads then stays as it was.
    /// - panics: none.
    ///
    /// # Errors
    /// The bytes naming the block that holds the name first.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block over a fresh name, and a second block over
    ///   one name.
    /// - witness: `lower::capability::tests::an_extern_block_declares_an_interface_its_callers_perform_2901`
    /// - witness: `lower::capability::tests::an_extern_block_beyond_the_form_is_refused_at_the_piece_2901`
    #[spec(ensures: |ref ret| ret.as_ref().ok().is_none_or(|block|
        matches!(self.named(source, &block.name), Some(&Provider::Block(ref held)) if Arc::ptr_eq(held, block))))]
    pub(super) fn declare(
        &mut self,
        source: SourceIndex,
        interface: ForeignInterface,
    ) -> Result<Arc<ForeignInterface>, ByteSpan>
    {
        let read = self
            .sources
            .entry(source)
            .or_insert_with(|| self.seed.clone());
        match read.entry(interface.name.clone()) {
            Entry::Occupied(mut held) => {
                if let Provider::Block(ref first) = *held.get() {
                    return Err(first.named);
                }
                let block = Arc::new(interface);
                let _host = held.insert(Provider::Block(Arc::clone(&block)));
                Ok(block)
            },
            Entry::Vacant(vacant) => {
                let block = Arc::new(interface);
                let _fresh = vacant.insert(Provider::Block(Arc::clone(&block)));
                Ok(block)
            },
        }
    }

    /// What `source` reads the interface `name` as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the block of `source` declared under `name`, or else the
    ///   host's interface of the name. A name neither holds reads as none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row and a call in a block's source read its
    ///   interface, and a scope handling `Proc` reads the host's.
    /// - witness: `lower::capability::tests::an_extern_block_declares_an_interface_its_callers_perform_2901`
    /// - witness: `lower::capability::tests::a_capability_at_a_scope_lives_in_its_region`
    #[spec(ensures: |ret| ret.is_none_or(|found| match *found {
        Provider::Block(ref block) => block.name == *name,
        Provider::Host => INTERFACES.contains(&name.as_ref()),
    }))]
    pub(crate) fn named(
        &self,
        source: SourceIndex,
        name: &EffectName,
    ) -> Option<&Provider>
    {
        self.sources.get(&source).unwrap_or(&self.seed).get(name)
    }

    /// The interfaces the extern blocks of `source` declare, in name order.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn blocks(
        &self,
        source: SourceIndex,
    ) -> impl Iterator<Item = &Arc<ForeignInterface>>
    {
        self.sources
            .get(&source)
            .into_iter()
            .flat_map(BTreeMap::values)
            .filter_map(|provider| match *provider {
                Provider::Block(ref block) => Some(block),
                Provider::Host => None,
            })
    }
}

impl Collected<'_>
{
    /// What the source holding `at` reads the interface `name` as.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn interface(
        &self,
        at: ByteOffset,
        name: &EffectName,
    ) -> Option<&Provider>
    {
        self.interfaces.named(self.unit.source_at(at), name)
    }
}

impl<'source> Collector<'_, 'source>
{
    /// Collect the extern block `block`.
    ///
    /// # Specification
    /// - requires: `block` is an extern block form at a source's top level.
    /// - ensures: a block in a language other than `rust` is [`Foreign::Other`]
    ///   and changes nothing. A `rust` block the parser repaired is refused
    ///   malformed; one with a tile out of place is refused misplaced there;
    ///   one naming an interface an earlier block of its source names, or a
    ///   member an earlier member names, is refused as a duplicate at the
    ///   second. A member beyond the form is refused out of the fragment at the
    ///   piece: a `type T ;` member, an untyped parameter, a mode, a type no
    ///   fixed width spells, or no result. Any other `rust` block is
    ///   [`Foreign::Declared`], and its source reads the interface's name as
    ///   it. No slot is taken either way.
    /// - provides: the extern half of [`super::collect_source`].
    /// - fails: the mold refusals of [`read_pieces`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block of two members declares its interface; a C
    ///   block is left to its refusal; a member taking `Integer`, a `type`
    ///   member, a member with no result and a second block of one name are
    ///   each refused at the piece.
    /// - witness: `lower::capability::tests::an_extern_block_declares_an_interface_its_callers_perform_2901`
    /// - witness: `lower::capability::tests::an_extern_block_beyond_the_form_is_refused_at_the_piece_2901`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ref ret| self.collected.slots.len() == before
            && match *ret {
                Ok(Foreign::Declared(ref interface)) => matches!(self.collected.interface(block.span.start(), &interface.name), Some(&Provider::Block(ref held)) if Arc::ptr_eq(held, interface)),
                Ok(Foreign::Other | Foreign::Refused(_)) | Err(_) => true,
            },
    )]
    pub(super) fn foreign(
        &mut self,
        block: Placed,
    ) -> Result<Foreign<'source>, LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        let outcome = read_pieces(self.pbg, self.tree, block.node, &mut pieces)
            .map(|()| self.read_foreign(block, &pieces));
        self.pieces = pieces;

        outcome
    }

    /// Read the extern block `block` over its pieces.
    ///
    /// # Specification
    /// - requires: as [`Self::foreign`]; `pieces` is the block's reading.
    /// - ensures: as [`Self::foreign`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::foreign`].
    /// - witness: `lower::capability::tests::an_extern_block_beyond_the_form_is_refused_at_the_piece_2901`
    #[spec(ensures: |ref ret| match *ret {
        Foreign::Declared(ref interface) => matches!(self.collected.interface(block.span.start(), &interface.name), Some(&Provider::Block(ref held)) if Arc::ptr_eq(held, interface)),
        Foreign::Other | Foreign::Refused(_) => true,
    })]
    fn read_foreign(
        &mut self,
        block: Placed,
        pieces: &Pieces,
    ) -> Foreign<'source>
    {
        let mut cursor = Cursor::new(&pieces.pieces, block.span);
        let _extern = cursor.tile(TileName::EXTERN);
        let Maybe::Present((language, _)) = quoted(self.tree, &mut cursor)
        else {
            return Foreign::Other;
        };
        if language != RUST {
            return Foreign::Other;
        }
        if let Maybe::Present(repaired) = pieces.repair {
            return Foreign::Refused(repaired.refusal(FormName::EXTERN_BLOCK));
        }
        match self.interface(&mut cursor) {
            Ok(interface) => {
                let source = self.collected.unit.source_at(block.span.start());
                let named = interface.named;
                match self.collected.interfaces.declare(source, interface) {
                    Ok(declared) => Foreign::Declared(declared),
                    Err(first) => Foreign::Refused(LoweringRefusal::DuplicateDefinition {
                        span: named,
                        name: self.spelled(named),
                        first,
                    }),
                }
            },
            Err(refusal) => Foreign::Refused(refusal),
        }
    }

    /// The interface the rest of a `rust` block declares, the cursor past its
    /// language.
    ///
    /// # Specification
    /// - requires: `cursor` stands past the block's language.
    /// - ensures: the interface named by the alias, or else the library, with
    ///   one operation per member, in order.
    /// - fails: as [`Self::foreign`], but for the duplicate interface.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::foreign`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::foreign`].
    /// - witness: `lower::capability::tests::an_extern_block_beyond_the_form_is_refused_at_the_piece_2901`
    #[spec(ensures: |ref ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|interface| interface.operations.iter().enumerate().all(|(at, operation)| interface.operations.iter().skip(at.saturating_add(1)).all(|later| later.name != operation.name))))]
    fn interface(
        &self,
        cursor: &mut Cursor<'_>,
    ) -> Result<ForeignInterface, LoweringRefusal<'source>>
    {
        let misplaced = |cursor: &Cursor<'_>| misplaced_in(FormName::EXTERN_BLOCK, cursor.here());
        if let Maybe::Absent(_) = cursor.tile(TileName::FROM) {
            return Err(misplaced(cursor));
        }
        let Maybe::Present((library, quotes)) = quoted(self.tree, cursor)
        else {
            return Err(misplaced(cursor));
        };
        let (name, named) = if let Maybe::Present(_) = cursor.tile(TileName::AS) {
            let alias = match cursor.tile(TileName::TYPE_IDENTIFIER) {
                Maybe::Present(alias) => alias,
                Maybe::Absent(_) => match cursor.tile(TileName::IDENTIFIER) {
                    Maybe::Present(alias) => alias,
                    Maybe::Absent(_) => return Err(misplaced(cursor)),
                },
            };
            (EffectName::from(self.name_of(alias).as_ref()), alias.span)
        }
        else {
            (EffectName::from(library.as_str()), quotes)
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACE_OPEN) {
            return Err(misplaced(cursor));
        }
        let mut operations: Vec<ForeignOperation> = Vec::new();
        let mut seen: BTreeMap<OperationName, ByteSpan> = BTreeMap::new();
        loop {
            match cursor.read() {
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::BRACE_CLOSE => {
                    break;
                },
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::DEF => {
                    let operation = self.operation(cursor)?;
                    if let Some(&first) = seen.get(&operation.name) {
                        return Err(LoweringRefusal::DuplicateDefinition {
                            span: operation.named.span,
                            name: self.spelled(operation.named.span),
                            first,
                        });
                    }
                    let _first = seen.insert(operation.name.clone(), operation.named.span);
                    operations.push(operation);
                },
                Maybe::Present(Piece::Tile { label, at }) if label == TileName::TYPE => {
                    return Err(beyond(at.span));
                },
                Maybe::Present(_) | Maybe::Absent(_) => return Err(misplaced(cursor)),
            }
        }
        if let Maybe::Present(_) = cursor.peek() {
            return Err(misplaced(cursor));
        }

        Ok(ForeignInterface {
            name,
            named,
            operations,
        })
    }

    /// The operation one member declares, the cursor past its `def`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past a member's `def`.
    /// - ensures: the member's name, each parameter's type in order and the
    ///   result's, the cursor past its `;`.
    /// - fails: a misplaced-tile refusal for a tile out of place; out of the
    ///   fragment at an untyped parameter, a mode, a type no fixed width
    ///   spells, or a member with no result.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::foreign`].
    /// - witness: `lower::capability::tests::an_extern_block_beyond_the_form_is_refused_at_the_piece_2901`
    #[spec(ensures: |ref ret| ret.as_ref().is_ok() || matches!(*ret, Err(LoweringRefusal::OutOfFragment { .. } | LoweringRefusal::MalformedForm { .. })))]
    fn operation(
        &self,
        cursor: &mut Cursor<'_>,
    ) -> Result<ForeignOperation, LoweringRefusal<'source>>
    {
        let misplaced = |cursor: &Cursor<'_>| misplaced_in(FormName::EXTERN_BLOCK, cursor.here());
        let Maybe::Present(named) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(misplaced(cursor));
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
            return Err(misplaced(cursor));
        }
        let mut parameters = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::PAREN_CLOSE) {
            let parameter = [
                TileName::IDENTIFIER,
                TileName::TYPE_VARIABLE,
                TileName::TYPE_IDENTIFIER,
            ]
            .into_iter()
            .find_map(|label| match cursor.tile(label) {
                Maybe::Present(parameter) => Some(parameter),
                Maybe::Absent(_) => None,
            });
            let Some(parameter) = parameter
            else {
                return Err(misplaced(cursor));
            };
            if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
                return Err(beyond(parameter.span));
            }
            for mode in [TileName::SHARED, TileName::CONSUMED] {
                if let Maybe::Present(written) = cursor.tile(mode) {
                    return Err(beyond(written.span));
                }
            }
            parameters.push(ForeignParameter {
                named: parameter,
                ty: self.width(cursor)?,
            });
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
            {
                return Err(misplaced(cursor));
            }
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::ARROW) {
            return Err(beyond(named.span));
        }
        let result = self.width(cursor)?;
        if let Maybe::Absent(_) = cursor.tile(TileName::SEMICOLON) {
            return Err(misplaced(cursor));
        }

        Ok(ForeignOperation {
            name: OperationName::from(self.name_of(named).as_ref()),
            named,
            parameters,
            result,
        })
    }

    /// The type at the cursor, the cursor past it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the width whose name the operand's bytes are, layout aside,
    ///   and where the operand is written.
    /// - fails: a misplaced-tile refusal where no operand stands; out of the
    ///   fragment at an operand no fixed width spells.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `u32` and `u64` are read, and `Integer` is refused at
    ///   its bytes.
    /// - witness: `lower::capability::tests::an_extern_block_beyond_the_form_is_refused_at_the_piece_2901`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |ty| WIDTHS.contains(&ty.width)))]
    fn width(
        &self,
        cursor: &mut Cursor<'_>,
    ) -> Result<ForeignType, LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Operand(written)) = cursor.read()
        else {
            return Err(misplaced_in(FormName::EXTERN_BLOCK, cursor.here()));
        };
        let spelled = self.tree.spanned(written.span);
        WIDTHS
            .into_iter()
            .find(|width| spelled.is_some_and(|text| text.as_ref().trim() == width.as_ref()))
            .map(|width| ForeignType { width, written })
            .ok_or_else(|| beyond(written.span))
    }

    /// File the extern block `block`, which declares `interface`, as the slot
    /// its check takes, when one of the attribute blocks `decorations`
    /// standing before it writes `boundary`.
    ///
    /// # Specification
    /// - requires: `block` is a `rust` extern block the collection declared
    ///   `interface` from; each entry of `decorations` is an attribute block
    ///   standing on its own before it.
    /// - ensures: when the attributes read from `decorations` include
    ///   `boundary`, one [`Role::Derived`] slot under the interface's name,
    ///   entered in no name table, its definition [`Operand::Derived`]; it owns
    ///   the block and its decorations, carries their attributes and
    ///   documentation, and [`super::Collected::boundaries`] keeps the
    ///   interface and the attribute's payload under it; a decoration that does
    ///   not read refuses the slot at the block. Otherwise nothing is filed,
    ///   and the blocks before it decorate nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block carrying `boundary` takes one slot holding
    ///   its attributes; a block carrying another attribute takes none.
    /// - witness: `lower::boundary::tests::a_boundary_block_takes_the_slot_its_check_runs_in_2901`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.by_name.len()),
        ensures: |ret| self.collected.by_name.len() == before.1
            && self.collected.slots.len() == before.0.saturating_add(usize::from(ret.0)),
    )]
    pub(super) fn boundary(
        &mut self,
        block: Placed,
        decorations: &[Placed],
        interface: &Arc<ForeignInterface>,
    ) -> Bounded
    {
        let mut attributes = Vec::new();
        let mut attributed = Ok(());
        for &decoration in decorations {
            if attributed.is_ok() {
                attributed = self.decoration(decoration, block.node, &mut attributes);
            }
        }
        let Some(rows) = attributes
            .iter()
            .find(|written| written.name.as_ref() == RegisteredAttribute::BOUNDARY.as_ref())
            .map(|written| written.payload)
        else {
            return Bounded(false);
        };
        let slot = SlotIndex(self.collected.slots.len());
        let named = Placed {
            node: block.node,
            span: interface.named,
        };
        self.collected.slots.push(DeclarationSlot {
            name: self.spelled(interface.named),
            container: self.collected.top(block.span.start()),
            role: Role::Derived,
            constant: ConstantIndex::from(slot.0),
            introduced_by: block,
            named,
            signature: Maybe::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Present(Half {
                declaration: block,
                named,
                operand: Operand::Derived,
            }),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });
        let _fresh = self.collected.boundaries.insert(slot, BoundarySlot {
            interface: Arc::clone(interface),
            rows,
        });
        self.collected.own(block.node, slot);
        for &decoration in decorations {
            self.collected.own(decoration.node, slot);
            self.document(slot, decoration.node, decoration.span.end(), block.node);
        }
        self.document(slot, block.node, interface.named.start(), block.node);
        if let Some(entry) = self.collected.slots.get_mut(slot.0) {
            entry.attributes.extend(attributes);
            if let Err(refusal) = attributed {
                entry.refuse(block.node, refusal);
            }
        }
        Bounded(true)
    }

    /// The bytes `span` covers, as a name.
    ///
    /// # Specification
    /// trivial.
    fn spelled(
        &self,
        span: ByteSpan,
    ) -> SurfaceName<'source>
    {
        self.tree
            .spanned(span)
            .map_or_else(|| SurfaceName::from(""), SurfaceName::from)
    }
}

/// The refusal of a piece of an extern block beyond the form: the lowering
/// does not reach it yet.
///
/// # Specification
/// trivial.
const fn beyond<'source>(span: ByteSpan) -> LoweringRefusal<'source>
{
    LoweringRefusal::OutOfFragment {
        span,
        form: FormName::EXTERN_BLOCK,
        sort: FragmentSort::Declaration,
        boundary: FragmentBoundary::Unadmitted(Unbuilt::ExternBlock),
    }
}
