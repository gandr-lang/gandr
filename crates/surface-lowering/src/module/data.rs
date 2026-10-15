//! Data declarations, as the collection pass reads them.
//!
//! `data T(a : A, …) : U { C : (x : B, …) --> T(a, …) ; … }` is read into a
//! [`DataForm`]: the parameter telescope, the universe and each generator's
//! fields, every type kept as the syntax node the lowering reads later. A
//! generator's result is checked here and dropped: the family applied to its
//! own parameters, in order, is the only result a nominal family without
//! indices has, so a result that applies it to anything else is an indexed
//! family and is declined by name. The declined constructor-block spelling is
//! declined by its own name. The operation and rule members a data block
//! parses — `oper`, `rule` and the retired `op` — are passed over: the
//! description route reads them into cells and holds each member's refusal at
//! its own span, so the family's generators stay native. An `oper` member's
//! name is kept, and once the family is read each operation whose rules
//! compile is admitted as a declaration of its own (`crate::operation`).
//!
//! # A cell between terms
//!
//! A member whose arrow stands between two closed terms of the family, `loop
//! : Base <-> Base`, is a cell between them. The single-shaft arrows build
//! data — `-->` a constructor between types, or a directed cell between terms,
//! `<->` an invertible cell — and the double-shaft arrows compute: `==>` a
//! rule run as conversion, `<=>` an invertible rule. This fragment admits one
//! of the four places: an invertible cell from a point to itself, a loop. Each
//! loop of a family without parameters is read into a [`CellForm`], and the
//! loops at one point mint their words: a declaration of their own,
//! [`Role::Words`], entered in no namespace, whose constructors are the empty
//! word, then each loop's letter and its inverse consing onto a word, and
//! whose rules are the two cancellations per loop. The checkers and the kernel
//! read `Path(T, a, a)` at the point as those words; each loop is bound at it
//! as the word of its one letter.
//!
//! - **Refusals.** A directed cell, `-->` between terms, is
//!   `LoweringRefusal::DirectedCell`; a cell between distinct terms is
//!   `LoweringRefusal::CellNotALoop` — the free groupoid on a graph, whose
//!   words are indexed by their endpoints. A rule arrow between terms, a cell
//!   of a parameterised family and a side that is no closed term of the
//!   family's generators are declined by the cell member's name. A cell's fault
//!   refuses the family once its form is filed, as a fault of its rules does,
//!   so the attributes stating what the family is expected to do stay with it.
//! - **Alternatives.** The words could have been the family's own presentation,
//!   the loop a term constructor with a written inverse and written
//!   cancellations; that lowers the book's circle one stratum down, where the
//!   equivalence it computes is the type's with the integers rather than its
//!   loop space's. The words could have been a surface name of their own
//!   (`Circle.Loops`), which the path type would then convert to; reading the
//!   path type as them needs no name a reader writes.
//! - **Reversal.** A cell between distinct points needs its words indexed by
//!   both endpoints, which a declaration of words per point cannot hold; a
//!   family with parameters needs its words at each instance.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ConstructorTag;
use gandr_core_term::RuleNode;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermView;
use gandr_theory_spec_combinators::Mark;
use gandr_theory_spec_combinators::appended;
use quenchant_shape::shape::Maybe;

use super::Collector;
use super::Container;
use super::DeclarationSlot;
use super::Half;
use super::Operand;
use super::Role;
use super::Tail;
use super::declaration_half;
use super::extra_operand;
use super::misplaced_in;
use super::one_in;
use super::slot_refusal;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::module::SlotIndex;
use crate::module::WrittenAttribute;
use crate::operation::RouteConstructor;
use crate::operation::RouteTable;
use crate::operation::Width;
use crate::operation::plan_operation;
use crate::resolve::SurfaceName;

quenchant_shape::reason_enum! {
    /// Why a data declaration states no universe.
    pub mod data_kind {
        /// The source wrote none.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `: U` follows the name or the parameters.
            Unwritten,
        }
    }
}

/// One parameter of a data declaration: its name's tile and its classifier.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: both coordinates name nodes of the tree the declaration was read
///   from.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a two-parameter family keeps both in telescope order.
/// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DataParameter
{
    /// The parameter's name.
    pub named: Placed,
    /// The type the parameter was written with.
    pub classifier: Placed,
}

/// One generator of a data declaration: its name's tile and its fields' types.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the fields keep source order, which is the constructor's field
///   order; a generator with none is a nullary constructor.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — nullary, unary and three-field generators keep their
///   field counts and order.
/// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct GeneratorForm
{
    /// The constructor's name.
    pub named: Placed,
    /// Each field's type, in order.
    pub fields: Vec<Placed>,
}

/// One data declaration, as the collection pass read it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the parameters keep telescope order and the generators tag order;
///   every result was the family over its parameters.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — parameterless and parameterized families, and an indexed
///   generator declined, separate the read form from the refusal.
/// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
/// - witness: `lower::native::tests::an_indexed_generator_is_declined`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DataForm
{
    /// The declaration form.
    pub declaration: Placed,
    /// The slot the family's name takes.
    pub slot: SlotIndex,
    /// The parameters, in telescope order.
    pub parameters: Vec<DataParameter>,
    /// The universe written after the parameters.
    pub kind: Maybe<Placed, data_kind::Absent>,
    /// The generators, in tag order.
    pub generators: Vec<GeneratorForm>,
    /// The name tile of each `oper` member, in source order: the operations
    /// the description route reads and the module may call.
    pub operations: Vec<Placed>,
    /// The loops the block declares, `name : a <-> a`, in source order.
    pub cells: Vec<CellForm>,
}

/// One loop of a data declaration, `name : a <-> a`: a free invertible cell
/// from the closed term `a` to itself.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the point is a closed constructor term of the declaration's own
///   generators, in pre-order, which both sides of the cell spelled.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a loop at a point keeps its name and point; a cell
///   between distinct terms and a directed one never become a cell form.
/// - witness: `lower::native::tests::a_loop_mints_the_words_at_its_point`
/// - witness: `lower::native::tests::a_cell_between_terms_is_a_loop_or_refused_by_name`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CellForm
{
    /// The cell's name tile, its node the binding's own and its span the
    /// whole member.
    pub at: Placed,
    /// The cell's name tile.
    pub named: Placed,
    /// The point the cell loops at, over the declaration's generators.
    pub point: Box<[RuleNode]>,
    /// Each written node of the cell's two sides, in pre-order, the source's
    /// first: no core node holds them, so each answers at the family.
    pub sides: Vec<ByteSpan>,
}

/// The words of the loops a data declaration declares at one point: the
/// presented type a path at that point reads as.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: every loop is the declaration's, at the point, in the order its
///   letters take their tags.
/// - executable: none — the indices hold no list to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`CellForm`].
/// - witness: `lower::native::tests::a_loop_mints_the_words_at_its_point`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct WordsForm
{
    /// The declaration's position in the collection's data list.
    pub family: usize,
    /// The slot the words take, entered in no namespace.
    pub slot: SlotIndex,
    /// The point, over the declaration's generators.
    pub point: Box<[RuleNode]>,
    /// Each loop's slot, the binding its name declares, in generator order.
    pub loops: Vec<SlotIndex>,
}

/// A data declaration's form as [`Collector::data_form`] reads it, and the
/// first fault among its cell members.
///
/// A cell's fault refuses the declaration only once its form is filed, as a
/// fault of the family's rules does, so the attributes stating what the
/// declaration is expected to do stay with it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the form holds no cell when a cell member is faulted.
/// - executable: none — the fault holds no form to check it against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`CellForm`].
/// - witness: `lower::native::tests::a_cell_between_terms_is_a_loop_or_refused_by_name`
#[derive(Clone, Debug)]
struct Formed<'source>
{
    /// The declaration's form.
    form: DataForm,
    /// The first cell member's fault, offered to the declaration's slot once
    /// the form is filed.
    cells: Result<(), LoweringRefusal<'source>>,
}

/// Where the generators of a constructor's family are read from.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a written family names its position in the collection's data
///   list; `Sig` names the presentation code the collection mints; words name
///   their position in the collection's words list.
/// - executable: none — the tag holds no list to check its position against.
///
/// # Adequacy
/// - hypothesis: L3 — a constructor of a written family and one of `Sig` each
///   apply and match through their own generators.
/// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
/// - witness: `description::sign::tests::a_sign_block_defines_its_presentation`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Generators
{
    /// The data declaration at this position of the collection's data list.
    Written(usize),
    /// `Sig`, the presentation code, minted from its description.
    Presentation,
    /// The words at this position of the collection's words list: the empty
    /// word, then each loop's letter and its inverse.
    Words(usize),
}

/// A constructor, as a term or a pattern naming it resolves it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `form` names the family's generators, `tag` one of them, and
///   `arity` is that generator's field count.
/// - executable: none — the entry holds no list to check its indices against.
///
/// # Adequacy
/// - hypothesis: L3 — two families' constructors resolve to their own family,
///   tag and arity; a second constructor of one name is refused.
/// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
/// - witness: `lower::native::tests::a_constructor_named_twice_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Constructor
{
    /// The family's slot.
    pub family: SlotIndex,
    /// Where the family's generators are read from.
    pub form: Generators,
    /// The constructor's tag: its generator's position.
    pub tag: usize,
    /// How many fields the constructor takes.
    pub arity: usize,
    /// The generator's name tile; for a constructor of `Sig`, the name tile of
    /// the `sign` block that minted it.
    pub named: Placed,
}

impl<'source> Collector<'_, 'source>
{
    /// The former of the root child `child`; a child that is no form reads as
    /// [`Former::Unadmitted`].
    ///
    /// # Specification
    /// - requires: `child` is a written child of the root.
    /// - ensures: a form's former as the dispatch table reads it.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a data declaration, an attribute block and a
    ///   definition each reach their own reading.
    /// - witness: `lower::native::tests::an_attribute_block_decorates_the_data_declaration_after_it`
    #[spec(ensures: |ret| ret.is_err() || self.tree.node(child.node).is_some() || ret == Ok(Former::Unadmitted))]
    pub(super) fn root_former(
        &self,
        child: Placed,
    ) -> Result<Former, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(child.node)
        else {
            return Ok(Former::Unadmitted);
        };
        Ok(match shape_of(self.pbg, node)? {
            Shape::Form { former, .. } => former,
            Shape::Root | Shape::Repair(_) | Shape::Layout => Former::Unadmitted,
        })
    }

    /// Collect the data declaration `declaration`, decorated by the attribute
    /// blocks `decorations` standing before it.
    ///
    /// # Specification
    /// - requires: `declaration` is a data declaration form and every entry of
    ///   `decorations` an attribute block standing on its own before it.
    /// - ensures: the family's name takes its slot, which owns the declaration
    ///   and its decorations; a clean form is pushed onto the data list, its
    ///   constructors entered by name, and its definition half and attributes
    ///   filed; the form's first fault is offered to the slot instead. A cell
    ///   member's fault refuses the slot once the form is filed, so the
    ///   attributes stating what the declaration expects stay with it.
    /// - provides: the data half of [`super::collect`].
    /// - fails: when the form has no name to file a refusal under.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a nameless declaration and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decorated family, a family named twice and a
    ///   constructor named twice separate filing from refusal.
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    /// - witness: `lower::native::tests::an_attribute_block_decorates_the_data_declaration_after_it`
    /// - witness: `lower::native::tests::a_constructor_named_twice_is_refused`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ret| ret.is_err() || (self.collected.slots.len() >= before
            && matches!(self.collected.owner_of(declaration.node), Maybe::Present(_))),
    )]
    pub(super) fn data(
        &mut self,
        declaration: Placed,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        let outcome = read_pieces(self.pbg, self.tree, declaration.node, &mut pieces)
            .and_then(|()| self.read_data(declaration, &pieces, decorations));
        self.pieces = pieces;

        outcome
    }

    /// Read the data declaration `declaration` over its pieces.
    ///
    /// # Specification
    /// - requires: as [`Self::data`]; `pieces` is the declaration's reading.
    /// - ensures: as [`Self::data`].
    /// - fails: as [`Self::data`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::data`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::data`].
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.collected.owner_of(declaration.node), Maybe::Present(_)))]
    fn read_data(
        &mut self,
        declaration: Placed,
        pieces: &Pieces,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, declaration.span);
        let _data = cursor.tile(TileName::DATA);
        let Maybe::Present(named) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(misplaced_in(FormName::DATA, cursor.here()));
        };
        let name = self.name_of(named);
        let slot = self.admit(Container::TopLevel, name, declaration, named);
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
        let mut cells = Ok(());
        let tail = if let Maybe::Present(repaired) = pieces.repair {
            Tail::Refused(repaired.refusal(FormName::DATA))
        }
        else if let Err(refusal) = attributed {
            Tail::Refused(refusal)
        }
        else {
            match self.data_form(declaration, slot, &mut cursor) {
                Ok(formed) => match self
                    .collected
                    .slots
                    .get(slot.0)
                    .map(|entry| entry.definition)
                {
                    Some(Maybe::Present(first)) => {
                        Tail::Refused(LoweringRefusal::DuplicateDefinition {
                            span: declaration.span,
                            name,
                            first: first.declaration.span,
                        })
                    },
                    Some(Maybe::Absent(_)) | None => {
                        cells = formed.cells;
                        self.enter(formed.form)
                    },
                },
                Err(refusal) => Tail::Refused(refusal),
            }
        };
        self.file(slot, declaration, tail, attributes);
        match (tail, cells) {
            (Tail::Data(_), Ok(())) => self.mint_words(declaration),
            (Tail::Data(_), Err(refusal)) => {
                if let Some(entry) = self.collected.slots.get_mut(slot.0) {
                    entry.refuse(declaration.node, refusal);
                }
            },
            _ => {},
        }

        Ok(())
    }

    /// Read the attribute block `block` standing before the declaration at
    /// `declaration`, pushing its attributes onto `attributes`.
    ///
    /// # Specification
    /// - requires: `block` is an attribute block standing on its own.
    /// - ensures: each attribute is pushed decorating `declaration`.
    /// - fails: the block's repair, and the attribute reader's refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] and [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block of two attributes decorates the family after
    ///   it, each filed under the family's content identity. The predicate
    ///   reads only the attributes this call appended.
    /// - witness: `lower::native::tests::an_attribute_block_decorates_the_data_declaration_after_it`
    #[spec(
        captures: before = attributes.len(),
        ensures: |ret| ret.is_err() || attributes.get(before ..).is_some_and(|appended| {
            appended.iter().all(|entry| entry.decorates == declaration)
        }),
    )]
    pub(super) fn decoration(
        &self,
        block: Placed,
        declaration: NodeIndex,
        attributes: &mut Vec<WrittenAttribute<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, block.node, &mut pieces)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(FormName::ATTRIBUTE));
        }
        self.read_attributes(
            Cursor::new(&pieces.pieces, block.span),
            declaration,
            attributes,
        )
    }

    /// Push `form` onto the data list and enter its constructors by name.
    ///
    /// # Specification
    /// - requires: `form`'s slot is live.
    /// - ensures: the data tail at the form's position when every constructor's
    ///   name is fresh, each entered with its family, tag and arity; otherwise
    ///   the refusal of the first constructor this or an earlier declaration
    ///   already named, and nothing entered.
    /// - fails: never; a second name is a refused tail.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two families with distinct constructors, and a second
    ///   family reusing a name, separate entry from refusal.
    /// - witness: `lower::native::tests::a_constructor_named_twice_is_refused`
    #[spec(
        captures: before = (self.collected.data.len(), self.collected.constructors.len()),
        ensures: |ret| match ret {
            | Tail::Data(position) => position == before.0 && self.collected.data.len() == before.0.saturating_add(1),
            | _ => self.collected.data.len() == before.0 && self.collected.constructors.len() == before.1,
        },
    )]
    fn enter(
        &mut self,
        form: DataForm,
    ) -> Tail<'source>
    {
        for (index, generator) in form.generators.iter().enumerate() {
            let name = self.name_of(generator.named);
            let earlier = form
                .generators
                .iter()
                .take(index)
                .find(|prior| self.name_of(prior.named) == name)
                .map(|prior| prior.named.span);
            let entered = self
                .collected
                .constructors
                .get(&name)
                .map(|entry| entry.named.span);
            if let Some(first) = entered.or(earlier) {
                return Tail::Refused(LoweringRefusal::DuplicateDefinition {
                    span: generator.named.span,
                    name,
                    first,
                });
            }
        }
        let position = self.collected.data.len();
        for (tag, generator) in form.generators.iter().enumerate() {
            let _fresh =
                self.collected
                    .constructors
                    .insert(self.name_of(generator.named), Constructor {
                        family: form.slot,
                        form: Generators::Written(position),
                        tag,
                        arity: generator.fields.len(),
                        named: generator.named,
                    });
        }
        self.collected.data.push(form);

        Tail::Data(position)
    }

    /// Admit the words of the loops the data declaration entered last
    /// declares, one words slot per point, and a binding per loop.
    ///
    /// # Specification
    /// - requires: the declaration `declaration` was the last one entered on
    ///   the data list.
    /// - ensures: for each point a loop of the declaration is at, in the order
    ///   its first loop is written, one [`Role::Words`] slot entered in no
    ///   namespace and, after it, one declared slot per loop at the point,
    ///   named by the loop and entered in the top level's name table, whose
    ///   definition is the loop's letter; one [`WordsForm`] per point. A
    ///   declaration without loops changes nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block with a loop mints its words and binds the
    ///   loop by name; a block without one mints nothing.
    /// - witness: `lower::native::tests::a_loop_mints_the_words_at_its_point`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.words.len()),
        ensures: self.collected.slots.len().saturating_sub(before.0)
            == self.collected.data.last().map_or(0, |form| form.cells.len())
                .saturating_add(self.collected.words.len().saturating_sub(before.1)),
    )]
    fn mint_words(
        &mut self,
        declaration: Placed,
    )
    {
        let position = self.collected.data.len().saturating_sub(1);
        let Some(form) = self.collected.data.get(position)
        else {
            return;
        };
        let family = form.slot;
        let mut points: Vec<(Box<[RuleNode]>, Vec<CellForm>)> = Vec::new();
        for cell in &form.cells {
            match points
                .iter_mut()
                .find(|&&mut (ref point, _)| *point == cell.point)
            {
                Some(&mut (_, ref mut loops)) => loops.push(cell.clone()),
                None => points.push((cell.point.clone(), Vec::from([cell.clone()]))),
            }
        }
        let name = self
            .collected
            .slots
            .get(family.0)
            .map_or_else(|| SurfaceName::from(""), |slot| slot.name);
        for (point, cells) in points {
            let index = self.collected.words.len();
            let words = SlotIndex(self.collected.slots.len());
            self.collected.slots.push(DeclarationSlot {
                name,
                container: Container::TopLevel,
                role: Role::Words,
                constant: ConstantIndex::from(words.0),
                introduced_by: declaration,
                named: cells.first().map_or(declaration, |cell| cell.named),
                signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                definition: Maybe::Present(Half {
                    declaration,
                    operand: Operand::Words(index),
                }),
                attributes: Vec::new(),
                docs: Vec::new(),
                refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
            });
            let mut loops = Vec::with_capacity(cells.len());
            for (generator, cell) in cells.iter().enumerate() {
                let bound = SlotIndex(self.collected.slots.len());
                let named = self.name_of(cell.named);
                self.collected.slots.push(DeclarationSlot {
                    name: named,
                    container: Container::TopLevel,
                    role: Role::Declared,
                    constant: ConstantIndex::from(bound.0),
                    introduced_by: cell.at,
                    named: cell.named,
                    signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                    definition: Maybe::Present(Half {
                        declaration: cell.at,
                        operand: Operand::Loop {
                            words: index,
                            generator,
                        },
                    }),
                    attributes: Vec::new(),
                    docs: Vec::new(),
                    refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
                });
                let _fresh = self
                    .collected
                    .by_name
                    .insert((Container::TopLevel, named), bound);
                loops.push(bound);
            }
            self.collected.words.push(WordsForm {
                family: position,
                slot: words,
                point,
                loops,
            });
        }
    }

    /// Read a data declaration's parameters, universe, generators and cells,
    /// the cursor standing just past the family's name.
    ///
    /// # Specification
    /// - requires: `cursor` stands past the name tile of the declaration at
    ///   `declaration`.
    /// - ensures: the parameters in order, the universe when one is written,
    ///   every generator and every loop, the cursor exhausted; the first cell
    ///   member's fault, as [`cell`] and [`Self::loops`] state them, kept
    ///   beside a form with no cell, the member passed over.
    /// - fails: a tile out of place or an operand missing or extra; a generator
    ///   whose result is not the family over its parameters.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] and
    /// [`LoweringRefusal::OutOfFragment`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses below read each member shape the
    ///   pending corpus writes, pass over the description route's members,
    ///   decline an indexed generator and keep a cell's fault beside the form.
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    /// - witness: `lower::native::tests::an_indexed_generator_is_declined`
    /// - witness: `lower::native::tests::operation_and_rule_members_are_left_to_the_description_route`
    /// - witness: `lower::native::tests::a_cell_between_terms_is_a_loop_or_refused_by_name`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |formed| formed.form.declaration == declaration
        && formed.form.slot == slot
        && (formed.cells.is_ok() || formed.form.cells.is_empty())))]
    fn data_form(
        &self,
        declaration: Placed,
        slot: SlotIndex,
        cursor: &mut Cursor<'_>,
    ) -> Result<Formed<'source>, LoweringRefusal<'source>>
    {
        let mut parameters = Vec::new();
        if let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN) {
            loop {
                let named = match cursor.peek() {
                    Maybe::Present(Piece::Tile { label, at })
                        if label == TileName::TYPE_VARIABLE || label == TileName::IDENTIFIER =>
                    {
                        let _named = cursor.tile(label);
                        at
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => {
                        return Err(misplaced_in(FormName::PARAMETER, cursor.here()));
                    },
                };
                if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
                    return Err(misplaced_in(FormName::PARAMETER, cursor.here()));
                }
                let classifier = one_in(FormName::PARAMETER, cursor.operands())?;
                parameters.push(DataParameter { named, classifier });
                if let Maybe::Present(_) = cursor.tile(TileName::COMMA)
                    && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
                {
                    continue;
                }
                if let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE) {
                    break;
                }
                return Err(misplaced_in(FormName::PARAMETERS, cursor.here()));
            }
        }
        let kind = match cursor.tile(TileName::COLON) {
            Maybe::Present(_) => Maybe::Present(one_in(FormName::DATA, cursor.operands())?),
            Maybe::Absent(_) => Maybe::Absent(data_kind::Absent::Unwritten),
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACE_OPEN) {
            return Err(misplaced_in(FormName::DATA, cursor.here()));
        }
        let mut generators = Vec::new();
        let mut operations = Vec::new();
        let mut written = Vec::new();
        let mut faulted = Ok(());
        loop {
            match cursor.read() {
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::BRACE_CLOSE => {
                    break;
                },
                Maybe::Present(Piece::Tile { label, at }) if label == TileName::CONSTRUCTOR => {
                    generators.push(self.generator(at, cursor, &parameters)?);
                },
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::OPER => {
                    if let Maybe::Present(named) = cursor.tile(TileName::IDENTIFIER) {
                        operations.push(named);
                    }
                    pass_over_member(cursor);
                    continue;
                },
                Maybe::Present(Piece::Tile { label, .. })
                    if label == TileName::OP || label == TileName::RULE =>
                {
                    pass_over_member(cursor);
                    continue;
                },
                Maybe::Present(Piece::Tile { label, at }) if label == TileName::IDENTIFIER => {
                    match cell(at, cursor) {
                        Ok(member) => written.push(member),
                        Err(refusal) => {
                            if faulted.is_ok() {
                                faulted = Err(refusal);
                            }
                            pass_over_member(cursor);
                            continue;
                        },
                    }
                },
                Maybe::Present(Piece::Tile { at, .. }) => {
                    return Err(misplaced_in(FormName::DATA, at.span));
                },
                Maybe::Present(Piece::Operand(operand)) => {
                    return Err(extra_operand(FormName::DATA, operand));
                },
                Maybe::Absent(_) => return Err(misplaced_in(FormName::DATA, cursor.here())),
            }
            if let Maybe::Absent(_) = cursor.tile(TileName::SEMICOLON) {
                let _comma = cursor.tile(TileName::COMMA);
            }
        }
        if let Maybe::Present(piece) = cursor.peek() {
            return Err(misplaced_in(FormName::DATA, piece.placed().span));
        }
        let (cells, faulted) =
            match faulted.and_then(|()| self.loops(&written, &generators, &parameters)) {
                Ok(cells) => (cells, Ok(())),
                Err(refusal) => (Vec::new(), Err(refusal)),
            };
        Ok(Formed {
            form: DataForm {
                declaration,
                slot,
                parameters,
                kind,
                generators,
                operations,
                cells,
            },
            cells: faulted,
        })
    }

    /// Read each written cell `written` as a loop of the declaration whose
    /// generators are `generators` and parameters `parameters`.
    ///
    /// # Specification
    /// - requires: `generators` are every generator of the declaration.
    /// - ensures: one loop per cell, in order, its point the closed term both
    ///   its sides spell over `generators`.
    /// - fails: a cell of a parameterised declaration, and a side that is no
    ///   closed term of the declaration's generators, as outside the fragment
    ///   by the cell member's name; a cell named as an earlier cell or an
    ///   earlier declaration is; [`LoweringRefusal::CellNotALoop`] for sides
    ///   that spell distinct terms.
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a loop, a cell between distinct terms and a cell at
    ///   an open side separate the loop from the refusals.
    /// - witness: `lower::native::tests::a_cell_between_terms_is_a_loop_or_refused_by_name`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |cells| cells.len() == written.len()))]
    fn loops(
        &self,
        written: &[WrittenCell],
        generators: &[GeneratorForm],
        parameters: &[DataParameter],
    ) -> Result<Vec<CellForm>, LoweringRefusal<'source>>
    {
        let names: Vec<SurfaceName<'source>> = generators
            .iter()
            .map(|generator| self.name_of(generator.named))
            .collect();
        let tag_of = |name: SourceFragment<'source>| {
            let tag = names
                .iter()
                .position(|&written| written.as_ref() == name.as_ref())?;
            Some((tag, generators.get(tag)?.fields.len()))
        };
        let mut cells = Vec::with_capacity(written.len());
        for (index, cell) in written.iter().enumerate() {
            if !parameters.is_empty() {
                return Err(declined(cell.named, FormName::CELL_MEMBER));
            }
            let name = self.name_of(cell.named);
            let earlier = written
                .iter()
                .take(index)
                .find(|prior| self.name_of(prior.named) == name)
                .map(|prior| prior.named.span);
            let declared = self
                .collected
                .by_name
                .get(&(Container::TopLevel, name))
                .and_then(|&slot| self.collected.slots.get(slot.0))
                .map(|slot| slot.named.span);
            if let Some(first) = declared.or(earlier) {
                return Err(LoweringRefusal::DuplicateDefinition {
                    span: cell.named.span,
                    name,
                    first,
                });
            }
            let side = |at: Placed| -> Result<ClosedTerm, LoweringRefusal<'source>> {
                match closed_term(self.pbg, self.tree, at, &tag_of)? {
                    Maybe::Present(term) => Ok(term),
                    Maybe::Absent(_) => Err(declined(at, FormName::CELL_MEMBER)),
                }
            };
            let (source, target) = (side(cell.source)?, side(cell.target)?);
            if source.nodes != target.nodes {
                return Err(LoweringRefusal::CellNotALoop { span: cell.at.span });
            }
            cells.push(CellForm {
                at: cell.at,
                named: cell.named,
                sides: source
                    .written
                    .iter()
                    .chain(&target.written)
                    .map(|written| written.span)
                    .collect(),
                point: source.nodes,
            });
        }

        Ok(cells)
    }

    /// Read one generator, `C : (x : B, …) --> T(a, …)` or `C : T(a, …)`, its
    /// name tile `named` already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the generator's name tile.
    /// - ensures: the generator's fields, named or bare, in order; the cursor
    ///   stands past its result.
    /// - fails: the declined constructor-block spelling and an attribute slot
    ///   by name; a grade prefix by name; a telescope with no result; a result
    ///   other than the family over its parameters, as an indexed family.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] and
    /// [`LoweringRefusal::OutOfFragment`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nullary, single-port and telescoped generators read
    ///   their fields; an indexed result, a declined spelling and a missing
    ///   result each refuse.
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    /// - witness: `lower::native::tests::an_indexed_generator_is_declined`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |generator| generator.named == named))]
    fn generator(
        &self,
        named: Placed,
        cursor: &mut Cursor<'_>,
        parameters: &[DataParameter],
    ) -> Result<GeneratorForm, LoweringRefusal<'source>>
    {
        if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
            return Err(declined(named, FormName::CONSTRUCTOR_BLOCK_MEMBER));
        }
        let mut fields = Vec::new();
        let result = if let Maybe::Present(open) = cursor.tile(TileName::PAREN_OPEN) {
            loop {
                if let Maybe::Present(Piece::Tile { label, .. }) = cursor.peek()
                    && label == TileName::IDENTIFIER
                {
                    let _binder = cursor.tile(label);
                    if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
                        return Err(misplaced_in(FormName::DATA_GENERATOR, cursor.here()));
                    }
                }
                else if let Maybe::Present(Piece::Tile { at, .. }) = cursor.peek() {
                    return Err(declined(at, FormName::GRADE));
                }
                fields.push(one_in(FormName::DATA_GENERATOR, cursor.operands())?);
                if let Maybe::Present(_) = cursor.tile(TileName::COMMA)
                    && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
                {
                    continue;
                }
                if let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE) {
                    break;
                }
                return Err(misplaced_in(FormName::DATA_GENERATOR, cursor.here()));
            }
            if let Maybe::Absent(_) = cursor.tile(TileName::GENERATOR) {
                return Err(LoweringRefusal::MalformedForm {
                    span: open.span.join(cursor.here()),
                    form: FormName::DATA_GENERATOR,
                    fault: FormFault::MissingOperand,
                });
            }
            one_in(FormName::DATA_GENERATOR, cursor.operands())?
        }
        else {
            let side = one_in(FormName::DATA_GENERATOR, cursor.operands())?;
            if let Maybe::Present(_) = cursor.tile(TileName::GENERATOR) {
                fields.push(side);
                one_in(FormName::DATA_GENERATOR, cursor.operands())?
            }
            else {
                side
            }
        };
        if let Maybe::Present(attributes) = cursor.tile(TileName::ATTRIBUTES) {
            return Err(declined(attributes, FormName::ATTRIBUTE));
        }
        self.uniform(result, parameters)?;

        Ok(GeneratorForm { named, fields })
    }

    /// Require `result` to be the family over `parameters`: the family's name
    /// alone for a family without parameters, and otherwise the family's name
    /// applied to each parameter's name, in order.
    ///
    /// # Specification
    /// - requires: `result` is a generator's result operand.
    /// - ensures: succeeds exactly for the uniform spellings above, the family
    ///   named by the declaration whose generator this is; the head's name is
    ///   not compared, a foreign head failing later as the type it names.
    /// - fails: any other result as an indexed family, declined at the result;
    ///   [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] with the indexed boundary, and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the family over its parameters, over a literal type
    ///   and over its parameters reordered separate uniform from indexed.
    /// - witness: `lower::native::tests::an_indexed_generator_is_declined`
    #[spec(ensures: |ret| ret.is_ok()
        || matches!(ret, Err(LoweringRefusal::UnknownMold { .. }))
        || matches!(ret, Err(LoweringRefusal::OutOfFragment {
            form: FormName::DATA_GENERATOR,
            boundary: FragmentBoundary::Indexed,
            ..
        })))]
    fn uniform(
        &self,
        result: Placed,
        parameters: &[DataParameter],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let indexed = LoweringRefusal::OutOfFragment {
            span: result.span,
            form: FormName::DATA_GENERATOR,
            sort: FragmentSort::Declaration,
            boundary: FragmentBoundary::Indexed,
        };
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, result.node, &mut pieces)?;
        let mut arguments = pieces.pieces.iter().filter_map(|piece| match *piece {
            Piece::Operand(operand) => Some(operand),
            Piece::Tile { .. } => None,
        });
        for parameter in parameters {
            let Some(argument) = arguments.next()
            else {
                return Err(indexed);
            };
            if self.name_of(argument) != self.name_of(parameter.named) {
                return Err(indexed);
            }
        }
        let headed = matches!(pieces.pieces.first(), Some(&Piece::Tile { label, .. }) if label == TileName::TYPE_IDENTIFIER);
        if arguments.next().is_some() || !headed {
            return Err(indexed);
        }

        Ok(())
    }

    /// Plan each operation the data declaration at `declaration` writes, and
    /// admit each one that runs as a declaration of its own.
    ///
    /// # Specification
    /// - requires: the declaration was collected by [`Self::data`].
    /// - ensures: one [`Role::Operation`] slot per operation with a route, in
    ///   source order after the family's slots, each with its plan and, when no
    ///   earlier operation took its name, its name; an operation without a
    ///   route, a parameterised family, a refused declaration and a family
    ///   whose rules the coincidence check refused change nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-output operation over a helper is admitted with
    ///   its helper, an operation missing a constructor is not, and an
    ///   operation calling a later one is not.
    /// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
    /// - witness: `operation::tests::an_operation_whose_rules_miss_a_constructor_is_not_callable`
    /// - witness: `operation::tests::an_operation_calling_a_later_one_is_not_callable`
    #[spec(
        captures: before = (Mark::of(&self.collected.slots), self.collected.operations.len()),
        ensures: self.collected.slots.len().saturating_sub(usize::from(before.0))
            == self.collected.operations.len().saturating_sub(before.1)
            && appended(&self.collected.slots, before.0).iter().all(|slot| slot.role == Role::Operation),
    )]
    pub(super) fn route_operations(
        &mut self,
        declaration: Placed,
    )
    {
        let mut routed = Vec::new();
        {
            let collected = &self.collected;
            let Some(form) = collected
                .data
                .iter()
                .find(|form| form.declaration.node == declaration.node)
            else {
                return;
            };
            let (Some(described), Some(cells)) = (
                collected.descriptions.get(&declaration.node),
                collected
                    .cells
                    .declarations
                    .iter()
                    .find(|cells| cells.at.node == declaration.node),
            )
            else {
                return;
            };
            if !form.parameters.is_empty()
                || described.description.polarity != DeclPolarity::Data
                || matches!(cells.coincidence, crate::coincide::Coincidence::Refused(_))
            {
                return;
            }
            let mut table = self.route_table();
            for &named in &form.operations {
                let name = self.name_of(named);
                let Some((position, operation)) = described
                    .description
                    .opers
                    .iter()
                    .enumerate()
                    .find(|&(_, operation)| operation.name.as_ref() == name.as_ref())
                else {
                    continue;
                };
                if table.callees.contains_key(&operation.name)
                    || collected.operation_names.contains_key(&name)
                    || !cells
                        .operations
                        .iter()
                        .any(|frame| frame.op.as_ref() == name.as_ref())
                {
                    continue;
                }
                let mut faces = Vec::new();
                let mut declined = false;
                let written = if cells.oriented.is_empty() {
                    described.description.rules.as_ref()
                }
                else {
                    cells.oriented.as_slice()
                };
                for (rule, face) in written.iter().enumerate() {
                    if matches!(face.lhs.view(), TermView::Op { name: head, .. } if *head == operation.name)
                    {
                        declined |= cells
                            .declined_faces
                            .iter()
                            .any(|&index| usize::from(index) == rule);
                        faces.push(face);
                    }
                }
                if declined {
                    continue;
                }
                let Ok(plan) = plan_operation(operation, &faces, &table)
                else {
                    continue;
                };
                let constant =
                    ConstantIndex::from(collected.slots.len().saturating_add(routed.len()));
                let _fresh = table.callees.insert(operation.name.clone(), constant);
                let span = described
                    .operation_spans
                    .get(position)
                    .copied()
                    .unwrap_or(named.span);
                routed.push((name, named, span, plan));
            }
        }
        for (name, named, span, plan) in routed {
            let minted = SlotIndex(self.collected.slots.len());
            self.collected.slots.push(DeclarationSlot {
                name,
                container: Container::TopLevel,
                role: Role::Operation,
                constant: ConstantIndex::from(minted.0),
                introduced_by: Placed {
                    node: declaration.node,
                    span,
                },
                named,
                signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                definition: Maybe::Present(Half {
                    declaration,
                    operand: Operand::Operation,
                }),
                attributes: Vec::new(),
                docs: Vec::new(),
                refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
            });
            let _plan = self.collected.operations.insert(minted, plan);
            let _name = self.collected.operation_names.insert(name, minted);
        }
    }

    /// What the module's families offer an operation's rules so far: every
    /// unparameterised family with its constructors, and the operations
    /// already planned.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one family entry per unparameterised data form, its
    ///   constructors in tag order, and each planned operation's constant by
    ///   name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::route_operations`].
    /// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
    #[spec(ensures: |ret| ret.families.len() <= self.collected.data.len() && ret.callees.len() == self.collected.operation_names.len())]
    fn route_table(&self) -> RouteTable
    {
        let mut table = RouteTable::default();
        for form in &self.collected.data {
            let Some(slot) = self.collected.slots.get(form.slot.0)
            else {
                continue;
            };
            if !form.parameters.is_empty() {
                continue;
            }
            let family = slot.constant;
            let _fresh = table
                .families
                .insert(Name::from(slot.name.as_ref()), family);
            let mut generators = Vec::with_capacity(form.generators.len());
            for (tag, generator) in form.generators.iter().enumerate() {
                let fields = Width::from(generator.fields.len());
                generators.push(fields);
                let _constructor = table.constructors.insert(
                    Name::from(self.name_of(generator.named).as_ref()),
                    RouteConstructor {
                        family,
                        tag: ConstructorTag::from(tag),
                        fields,
                    },
                );
            }
            let _generators = table.generators.insert(family, generators);
        }
        for (name, &slot) in &self.collected.operation_names {
            if let Some(entry) = self.collected.slots.get(slot.0) {
                let _callee = table
                    .callees
                    .insert(Name::from(name.as_ref()), entry.constant);
            }
        }

        table
    }
}

/// Pass over the rest of a member the description route reads: every piece up
/// to and including its `;`, stopping before the block's `}`.
///
/// # Specification
/// - requires: `cursor` stands just past the member's leading tile.
/// - ensures: the cursor stands past the member's `;`, or at the block's `}` or
///   its end when the member has no `;`.
/// - panics: none.
/// - executable: none — the cursor exposes no position to compare before and
///   after.
///
/// # Adequacy
/// - hypothesis: L3 — a family with an operation and a rule member between its
///   generators keeps both generators.
/// - witness: `lower::native::tests::operation_and_rule_members_are_left_to_the_description_route`
fn pass_over_member(cursor: &mut Cursor<'_>)
{
    loop {
        match cursor.peek() {
            Maybe::Present(Piece::Tile { label, .. }) if label == TileName::BRACE_CLOSE => return,
            Maybe::Present(Piece::Tile { label, .. }) if label == TileName::SEMICOLON => {
                let _end = cursor.tile(label);
                return;
            },
            Maybe::Present(_) => {
                let _skipped = cursor.read();
            },
            Maybe::Absent(_) => return,
        }
    }
}

/// One cell member as written, `name : a <-> b`, before its sides are read
/// as terms.
#[derive(Clone, Copy, Debug)]
struct WrittenCell
{
    /// The cell's name tile, spanning the whole member.
    at: Placed,
    /// The cell's name tile.
    named: Placed,
    /// The side before the arrow.
    source: Placed,
    /// The side after the arrow.
    target: Placed,
}

/// Read one cell member, `name : a <-> b`, its name tile `named` already
/// read.
///
/// # Specification
/// - requires: `cursor` stands just past the cell's name tile.
/// - ensures: the cell's two sides, the cursor past the second.
/// - fails: [`LoweringRefusal::DirectedCell`] for the arrow `-->`; the rule
///   arrows `==>` and `<=>` as outside the fragment by the cell member's name;
///   a tile out of place or an operand missing or extra.
/// - panics: none.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — the invertible arrow reads, the directed one and a rule
///   arrow are each refused by name.
/// - witness: `lower::native::tests::a_cell_between_terms_is_a_loop_or_refused_by_name`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |cell| cell.named == named && cell.at.node == named.node))]
fn cell<'source>(
    named: Placed,
    cursor: &mut Cursor<'_>,
) -> Result<WrittenCell, LoweringRefusal<'source>>
{
    if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
        return Err(misplaced_in(FormName::CELL_MEMBER, cursor.here()));
    }
    let source = one_in(FormName::CELL_MEMBER, cursor.operands())?;
    let arrow = match cursor.read() {
        Maybe::Present(Piece::Tile { label, at }) => (label, at),
        Maybe::Present(Piece::Operand(operand)) => {
            return Err(extra_operand(FormName::CELL_MEMBER, operand));
        },
        Maybe::Absent(_) => return Err(misplaced_in(FormName::CELL_MEMBER, cursor.here())),
    };
    match arrow {
        (label, _) if label == TileName::INVERTIBLE => {},
        (label, at) if label == TileName::GENERATOR => {
            return Err(LoweringRefusal::DirectedCell { span: at.span });
        },
        (label, at) if label == TileName::REWRITE || label == TileName::REVERSIBLE => {
            return Err(declined(at, FormName::CELL_MEMBER));
        },
        (_, at) => return Err(misplaced_in(FormName::CELL_MEMBER, at.span)),
    }
    let target = one_in(FormName::CELL_MEMBER, cursor.operands())?;
    let span = ByteSpan::new(named.span.start(), target.span.end()).unwrap_or(named.span);

    Ok(WrittenCell {
        at: Placed {
            node: named.node,
            span,
        },
        named,
        source,
        target,
    })
}

quenchant_shape::reason_enum! {
    /// Why a written term is no closed term over a family's generators.
    pub mod closed_term {
        /// The reason the term spells no closed constructor term.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A node of the term is no constructor `tag_of` reads, or a
            /// constructor applied to other than its field count.
            Foreign,
        }
    }
}

/// A closed constructor term as written: its nodes over the family's tags,
/// and the written node each spells.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one written node per term node, both in pre-order.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`closed_term()`].
/// - witness: `lower::native::tests::a_loop_mints_the_words_at_its_point`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosedTerm
{
    /// The term's nodes, in pre-order.
    pub nodes: Box<[RuleNode]>,
    /// The written node each spells, in the same order.
    pub written: Vec<Placed>,
}

/// The closed constructor term written at `at`, in pre-order, each
/// constructor's tag and field count read by `tag_of` off its name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one node per constructor written, in pre-order, beside the
///   written node it spells: a nullary constructor is its bare name, an applied
///   one a call headed by its name with one argument per field.
/// - fails: [`closed_term::Absent::Foreign`] for a node that is no such
///   constructor, a call at other than its field count, and a repaired call;
///   the shape refusals of a mold the grammar does not hold.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::UnknownMold`].
///
/// # Termination
/// - reason: the `while let` worklist, not recursion.
/// - measure: the written nodes still to visit, each a strict subterm of the
///   one that queued it.
///
/// # Adequacy
/// - hypothesis: L3 — a nullary point and a call at its point read, an open
///   side does not.
/// - witness: `lower::native::tests::a_cell_between_terms_is_a_loop_or_refused_by_name`
/// - witness: `lower::native::tests::a_loop_mints_the_words_at_its_point`
#[spec(ensures: |ret| match ret {
    Ok(Maybe::Present(ref term)) => !term.nodes.is_empty() && term.nodes.len() == term.written.len(),
    _ => true,
})]
pub fn closed_term<'source, F>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    at: Placed,
    tag_of: &F,
) -> Result<Maybe<ClosedTerm, closed_term::Absent>, LoweringRefusal<'source>>
where
    F: Fn(SourceFragment<'source>) -> Option<(usize, usize)>,
{
    let foreign = Ok(Maybe::Absent(closed_term::Absent::Foreign));
    let mut nodes = Vec::new();
    let mut visited = Vec::new();
    let mut pending = Vec::from([at]);
    let mut pieces = Pieces::new();
    while let Some(written) = pending.pop() {
        let Some(node) = tree.node(written.node)
        else {
            return foreign;
        };
        let (head, fields) = match shape_of(pbg, node)? {
            Shape::Form {
                former: Former::Constructor,
                ..
            } => (written, Vec::new()),
            Shape::Form {
                former: Former::Call,
                ..
            } => {
                read_pieces(pbg, tree, written.node, &mut pieces)?;
                if let Maybe::Present(_) = pieces.repair {
                    return foreign;
                }
                let mut operands = pieces.pieces.iter().filter_map(|piece| match *piece {
                    Piece::Operand(operand) => Some(operand),
                    Piece::Tile { .. } => None,
                });
                let Some(head) = operands.next()
                else {
                    return foreign;
                };
                let fields: Vec<Placed> = operands.collect();
                let Some(headed) = tree.node(head.node)
                else {
                    return foreign;
                };
                let Shape::Form {
                    former: Former::Constructor,
                    ..
                } = shape_of(pbg, headed)?
                else {
                    return foreign;
                };
                (head, fields)
            },
            Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                return foreign;
            },
        };
        let Some((tag, arity)) = tree.fragment(head.node).and_then(tag_of)
        else {
            return foreign;
        };
        if arity != fields.len() {
            return foreign;
        }
        nodes.push(RuleNode::Constructor(ConstructorTag::from(tag)));
        visited.push(written);
        pending.extend(fields.into_iter().rev());
    }

    Ok(Maybe::Present(ClosedTerm {
        nodes: nodes.into_boxed_slice(),
        written: visited,
    }))
}

/// The refusal a member the fragment does not read earns, by its own name.
///
/// # Specification
/// trivial.
const fn declined<'source>(
    at: Placed,
    form: FormName,
) -> LoweringRefusal<'source>
{
    LoweringRefusal::OutOfFragment {
        span: at.span,
        form,
        sort: FragmentSort::Declaration,
        boundary: FragmentBoundary::Unadmitted,
    }
}
