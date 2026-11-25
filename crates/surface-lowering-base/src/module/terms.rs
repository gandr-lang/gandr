//! The terms of a theory, as the collection pass reads them.
//!
//! A source asks for the terms of a theory in a type. `Terms S` asks for the
//! terms of a theory `S` of one plain sort. `Terms S s` asks for the terms of
//! the sort `s` of `S`, and `Terms S s i` asks for them at the index `i` of an
//! indexed sort.
//!
//! The terms of one sort are a presented type. Each operation into the sort is
//! a constructor that takes its inputs as terms, and each rule of the sort is
//! a rule over those constructors. The terms of an indexed sort are a family
//! over the terms of each index sort, and each constructor stands at the
//! closed index that its operation states.
//!
//! The first type of the unit that asks for the terms of a sort takes one
//! [`Role::Terms`] slot before the top-level form that writes it. The
//! definition of the slot is the half [`Operand::Terms`], which the lowering
//! mints from the presentation ([`TermsForm`]). The slot takes the text of the
//! type as its name, from `Terms` to the name of the sort, and no name table
//! holds it. `S.op` names a constructor. The terms of an index sort take their
//! slot before the family that stands over them.
//!
//! A sort outside the slice takes no slot, and the lowering refuses the type
//! where it reads it ([`term_generators`]).

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::cmp::Reverse;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::NodeLabel;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

use super::Collector;
use super::DeclarationSlot;
use super::Half;
use super::Operand;
use super::Role;
use super::SlotIndex;
use super::declaration_half;
use super::slot_refusal;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::model::Port;
use crate::model::Presentation;
use crate::model::PresentedOperation;
use crate::resolve::SurfaceName;
use crate::unbuilt::Unbuilt;

/// The head a source writes a theory's terms under, `Terms(S)`.
pub const TERMS: &str = "Terms";

quenchant_shape::reason_enum! {
    /// Why a terms type names no sort.
    pub mod asked_sort {
        /// The type holds no name of a sort.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The type writes the theory alone, `Terms S`.
            Unwritten,
        }
    }
}

/// The sort of a theory that a terms type asks for.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `At` holds the name tile of a sort in the block of its theory.
/// - executable: none — the choice is data that [`term_generators`] reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`term_generators`].
/// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AskedSort
{
    /// The one sort of the theory, `Terms S`.
    Only,
    /// The sort whose name tile this is, `Terms S s`.
    At(Placed),
}

/// One node of a closed term of an index sort.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `tag` is the place of the node's operation among the operations
///   into the index sort, and `arity` is the count of its arguments.
/// - executable: none — the record is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`term_generators`].
/// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IndexNode
{
    /// The constructor of the terms of the index sort.
    pub tag: ConstructorTag,
    /// The count of the node's arguments, which follow it.
    pub arity: usize,
}

/// A closed term of an index sort: its nodes in pre-order.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the nodes spell one term, each node before its arguments.
/// - executable: none — the record is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`term_generators`].
/// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosedIndex
{
    /// The nodes of the term, in pre-order.
    pub nodes: Vec<IndexNode>,
}

/// The terms of one sort of a theory: the slot they take and the generators
/// the theory's operations give them.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `theory` is the slot of a `theory` block and `sort` the name tile
///   of a sort of it. `operations`, `arities` and `stated` are parallel, one
///   entry per operation into the sort, in the presentation's order. `indices`
///   holds one entry of the unit's terms per index of the sort, and each row of
///   `stated` holds one closed term per index for each input and then for the
///   result.
/// - executable: none — the record is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — a unital magma's terms take one slot whose generators are
///   its unit and its product. The terms of a sort of widths and of a sort over
///   it take two slots, the widths first.
/// - witness: `gandr-surface-lowering::tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
/// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermsForm
{
    /// The theory's slot.
    pub theory: SlotIndex,
    /// The slot the terms take, entered in no namespace.
    pub slot: SlotIndex,
    /// The name tile of the sort, in the block of the theory.
    pub sort: Placed,
    /// Each operation's name tile, in the presentation's order: the name its
    /// constructor answers to.
    pub operations: Vec<Placed>,
    /// Each operation's input count, parallel to `operations`.
    pub arities: Vec<usize>,
    /// The entry of the terms of each index sort, in the order of the sort's
    /// indices. A plain sort holds none.
    pub indices: Vec<usize>,
    /// The closed indices that each operation states, parallel to
    /// `operations`: one term per index for each input, then for the result.
    pub stated: Vec<Vec<ClosedIndex>>,
}

/// The generators a presentation gives the terms of one sort: each operation's
/// name tile, its input count and the indices it states, in the presentation's
/// order.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `operations`, `arities` and `stated` are parallel when
///   [`term_generators`] builds the record, and `indices` holds the name tile
///   of each index sort.
/// - executable: none — the record is data the collector reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`term_generators`].
/// - witness: `gandr-surface-lowering::tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
/// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermGenerators
{
    /// The name tile of the sort, in the block of the theory.
    pub sort: Placed,
    /// Each operation's name tile, in the presentation's order.
    pub operations: Vec<Placed>,
    /// Each operation's input count, parallel to `operations`.
    pub arities: Vec<usize>,
    /// The name tile of each index sort, in the order of the sort's indices.
    pub indices: Vec<Placed>,
    /// The closed indices that each operation states, parallel to
    /// `operations`: one term per index for each input, then for the result.
    pub stated: Vec<Vec<ClosedIndex>>,
}

/// The closed term `term` of the sort `sort`, over the operations of
/// `operations` into that sort.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one node per node of `term`, in pre-order, when each node applies
///   an operation of one result at `sort`. The tag of a node is the place of
///   its operation among those operations.
/// - fails: nothing is answered for a term that holds a variable or any other
///   head.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` loop over the pending stack, not recursion.
/// - measure: the nodes of the term still to read.
///
/// # Cost
/// - allocation: the pending stack and the nodes, growth within the term
///
/// # Adequacy
/// - hypothesis: L3 — the index `bit` of an operation into the terms at a width
///   reads as the first constructor of the widths, and an index variable reads
///   as nothing.
/// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|closed| !closed.nodes.is_empty()))]
fn closed_index<N>(
    operations: &[PresentedOperation<N>],
    sort: &N,
    term: &FreeTerm<N>,
) -> Option<ClosedIndex>
where
    N: PartialEq,
{
    let mut nodes = Vec::new();
    let mut pending = Vec::from([term.to_node()]);
    while let Some(node) = pending.pop() {
        let TermView::Op { name, args } = node.view()
        else {
            return None;
        };
        let tag = operations
            .iter()
            .filter(
                |operation| matches!(*operation.outputs, [ref output] if output.sort.sort == *sort),
            )
            .position(|operation| operation.name == *name)?;
        let mark = pending.len();
        pending.extend(args);
        let arity = pending.len().saturating_sub(mark);
        if let Some(arguments) = pending.get_mut(mark ..) {
            arguments.reverse();
        }
        nodes.push(IndexNode {
            tag: ConstructorTag::from(tag),
            arity,
        });
    }

    Some(ClosedIndex { nodes })
}

/// The generators `presentation` gives the terms of the sort `asked`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one name tile, one count and one row of indices per operation of
///   one result at the sort, when the slice below holds. The sort lands in
///   values. Each index of the sort is at another sort of the theory, and that
///   sort has no index. Each input of such an operation is at the sort, each
///   port binds and abstracts nothing, and each index that a port states is a
///   closed term of its index sort. No rule is wired as a circuit, and no law
///   is stated. [`AskedSort::Only`] reads the sort of a theory of one sort.
/// - fails: [`Unbuilt::LawTerms`] for a stated law; [`Unbuilt::TermsType`] for
///   any other presentation outside that slice, or one whose members do not
///   read.
/// - panics: none.
///
/// # Errors
/// As the fails clause.
///
/// # Cost
/// - allocation: the members on ids, setup
/// - allocation: the generators, durable by the terms type
///
/// # Adequacy
/// - hypothesis: L3 — a unital magma gives its unit and its product, a
///   two-sorted theory read at no sort and a law-bearing one are refused by
///   their features. A sort of widths gives its two constants, and a sort over
///   it gives each operation with the width of each port.
/// - witness: `gandr-surface-lowering::tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
/// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_theory_outside_one_plain_sort_are_refused_4143`
/// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |generators| generators.operations.len() == generators.arities.len() && generators.operations.len() == generators.stated.len()))]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: `sorts` holds the sorts of one theory"
    )
)]
#[inline]
pub fn term_generators(
    presentation: &Presentation,
    asked: AskedSort,
) -> Result<TermGenerators, Unbuilt>
{
    if !presentation.laws.is_empty() {
        return Err(Unbuilt::LawTerms);
    }
    let outside = Err(Unbuilt::TermsType);
    if presentation.wired().next().is_some() {
        return outside;
    }
    let Ok(members) = presentation.members()
    else {
        return outside;
    };
    let sort = match asked {
        AskedSort::Only => match *members.sorts {
            [ref only] => only,
            _ => return outside,
        },
        AskedSort::At(named) => match members.sorts.iter().find(|sort| sort.named == named) {
            Some(found) => found,
            None => return outside,
        },
    };
    if sort.ground != GroundSort::Value {
        return outside;
    }
    let bare = |port: &Port<_>| port.binders.is_empty() && port.abstractions.is_empty();
    // Each index of the sort is at a plain sort of the theory.
    let mut over = Vec::with_capacity(sort.indices.len());
    for index in &sort.indices {
        let Some(at) = members
            .sorts
            .iter()
            .find(|other| other.name == index.sort.sort)
        else {
            return outside;
        };
        if at.name == sort.name
            || !at.indices.is_empty()
            || !index.sort.indices.is_empty()
            || !bare(index)
        {
            return outside;
        }
        over.push(at);
    }
    let mut operations = Vec::new();
    let mut arities = Vec::new();
    let mut stated = Vec::new();
    for operation in &members.operations {
        let [ref output] = *operation.outputs
        else {
            return outside;
        };
        if output.sort.sort != sort.name {
            // An operation into another sort of the theory is a constructor
            // of the terms of that sort.
            if members
                .sorts
                .iter()
                .any(|other| other.name == output.sort.sort)
            {
                continue;
            }
            return outside;
        }
        let mut row = Vec::with_capacity(
            operation
                .inputs
                .len()
                .saturating_add(1)
                .saturating_mul(over.len()),
        );
        for port in operation.inputs.iter().chain([output]) {
            if port.sort.sort != sort.name || !bare(port) || port.sort.indices.len() != over.len() {
                return outside;
            }
            for (term, at) in port.sort.indices.iter().zip(&over) {
                let Some(closed) = closed_index(&members.operations, &at.name, term)
                else {
                    return outside;
                };
                row.push(closed);
            }
        }
        operations.push(operation.named);
        arities.push(operation.inputs.len());
        stated.push(row);
    }

    Ok(TermGenerators {
        sort: sort.named,
        operations,
        arities,
        indices: over.iter().map(|at| at.named).collect(),
        stated,
    })
}

/// One terms type of a source: where it stands and what it names.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `theory` is the name tile of the theory, and `sort` the name tile
///   of the sort where the type writes one.
/// - executable: none — the record is data the collector reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Collector::terms`].
/// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct AskedTerms
{
    /// The type application.
    at: Placed,
    /// The name tile of the theory, in the type.
    theory: Placed,
    /// The name tile of the sort, in the type.
    sort: Maybe<Placed, asked_sort::Absent>,
}

impl AskedTerms
{
    /// The type application.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn at(&self) -> Placed
    {
        self.at
    }
}

impl<'source> Collector<'_, 'source>
{
    /// The theory and the sort that the terms type `applied` writes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the name tile of `S`, and of `s` where it is written, when
    ///   `applied` reads `Terms ( S` and then `, s`. `pieces` is overwritten.
    /// - panics: none.
    /// - executable: none — the classification is the grammar's, which a
    ///   predicate would read again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::terms`].
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    /// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
    fn asked_terms(
        &self,
        applied: Placed,
        pieces: &mut Pieces,
    ) -> Option<AskedTerms>
    {
        read_pieces(self.pbg, self.tree, applied.node, pieces).ok()?;
        let mut cursor = Cursor::new(&pieces.pieces, applied.span);
        let Maybe::Present(written) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return None;
        };
        if self.name_of(written).as_ref() != TERMS {
            return None;
        }
        let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN)
        else {
            return None;
        };
        let Run::One(theory) = cursor.operands()
        else {
            return None;
        };
        let sort = match cursor.tile(TileName::COMMA) {
            Maybe::Present(_) => match cursor.operands() {
                Run::One(sort) => Some(sort),
                Run::Empty(_) | Run::Several { .. } => return None,
            },
            Maybe::Absent(_) => None,
        };
        let theory = self.named_operand(theory, pieces)?;
        let sort = match sort {
            Some(sort) => Maybe::Present(self.named_operand(sort, pieces)?),
            None => Maybe::Absent(asked_sort::Absent::Unwritten),
        };

        Some(AskedTerms {
            at: applied,
            theory,
            sort,
        })
    }

    /// The terms types of the source, each with the names it writes, in the
    /// order their text starts.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every type application of the source's tree that
    ///   [`Self::asked_terms`] reads, once, ascending by the start of its span.
    ///   A type written by juxtaposition nests one application for each
    ///   operand, and the outermost one alone is answered.
    /// - panics: none.
    /// - executable: none — the classification is the grammar's, which a
    ///   predicate would read again.
    ///
    /// # Cost
    /// - allocation: the class of each mold and the list of the types, growth
    ///   within the forms of the source
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::terms`].
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    /// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
    pub(super) fn terms_types(&mut self) -> Vec<AskedTerms>
    {
        // A form's mold decides its former, so each mold is classified once.
        let mut applied_molds = BTreeMap::new();
        let mut pieces = core::mem::take(&mut self.pieces);
        let mut found = Vec::new();
        for position in self.tree.positions() {
            let Some(node) = self.tree.node(position)
            else {
                continue;
            };
            let NodeLabel::Meld(mold) = node.label()
            else {
                continue;
            };
            let applied = *applied_molds.entry(mold).or_insert_with(|| {
                matches!(
                    shape_of(self.pbg, node),
                    Ok(Shape::Form {
                        former: Former::TypeApplication,
                        ..
                    })
                )
            });
            if !applied {
                continue;
            }
            if let Some(asked) = self.asked_terms(Placed::of(position, node), &mut pieces) {
                found.push(asked);
            }
        }
        self.pieces = pieces;
        // The applications of one juxtaposed type start at one byte: the
        // longest one is the type.
        found.sort_by_key(|asked| (asked.at.span.start(), Reverse(asked.at.span.end())));
        found.dedup_by_key(|asked| asked.at.span.start());

        found
    }

    /// The name of the slot of the terms that `asked` writes: its text from
    /// `Terms` to the name of the sort, or the whole type where it names no
    /// sort.
    ///
    /// # Specification
    /// trivial.
    fn terms_name(
        &self,
        asked: AskedTerms,
    ) -> Option<SurfaceName<'source>>
    {
        let fragment = self.tree.fragment(asked.at.node)?;
        match asked.sort {
            Maybe::Present(sort) => {
                let length =
                    usize::from(sort.span.end()).checked_sub(usize::from(asked.at.span.start()))?;
                <&str>::from(fragment).get(.. length).map(SurfaceName::from)
            },
            Maybe::Absent(_) => Some(SurfaceName::from(fragment)),
        }
    }

    /// The theory that `asked` names and the generators of the sort it asks
    /// for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot that
    ///   [`Collected::presented_theory`](super::Collected::presented_theory)
    ///   resolves the theory to where the type stands, and what
    ///   [`term_generators`] reads at the sort of that theory whose name the
    ///   type writes; nothing for a name that no sort of the theory has, or a
    ///   sort outside the slice.
    /// - panics: none.
    /// - executable: none — the answer is a reading of the presentation.
    ///
    /// # Cost
    /// - allocation: the generators, durable by the terms type
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::terms`].
    /// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
    fn asked_generators(
        &self,
        asked: AskedTerms,
    ) -> Option<(SlotIndex, TermGenerators)>
    {
        let (theory, presentation) = self
            .collected
            .presented_theory(
                asked.theory.span.start(),
                asked.theory.span,
                self.name_of(asked.theory),
            )
            .ok()?;
        let which = match asked.sort {
            Maybe::Present(written) => {
                let name = self.name_of(written);
                let named = presentation
                    .placement
                    .sorts
                    .iter()
                    .copied()
                    .find(|&sort| self.name_of(sort) == name)?;
                AskedSort::At(named)
            },
            Maybe::Absent(_) => AskedSort::Only,
        };
        let generators = term_generators(presentation, which).ok()?;

        Some((theory, generators))
    }

    /// Take the slot of the terms `form`, for the type that `asked` writes,
    /// under the name `name`.
    ///
    /// # Specification
    /// - requires: no entry of the unit's terms holds the sort of `form` in its
    ///   theory, and `form.slot` is the next slot of the unit.
    /// - ensures: one [`Role::Terms`] slot named `name` at the type, its
    ///   definition the terms the lowering mints, and `form` as the last entry
    ///   of the unit's terms.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the slot and the entry, durable by the unit
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::terms`].
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.terms.len()),
        ensures: self.collected.slots.len() == before.0.saturating_add(1)
            && self.collected.terms.len() == before.1.saturating_add(1),
    )]
    fn take_terms(
        &mut self,
        asked: AskedTerms,
        name: SurfaceName<'source>,
        form: TermsForm,
    )
    {
        let AskedTerms {
            at, theory: named, ..
        } = asked;
        let index = self.collected.terms.len();
        self.collected.slots.push(DeclarationSlot {
            name,
            container: self.collected.top(at.span.start()),
            role: Role::Terms,
            constant: ConstantIndex::from(form.slot.0),
            introduced_by: at,
            named,
            signature: Maybe::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Present(Half {
                declaration: at,
                named,
                operand: Operand::Terms(index),
            }),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });
        self.collected.terms.push(form);
    }

    /// Collect the terms that the type `asked` asks for.
    ///
    /// # Specification
    /// - requires: `asked` is a terms type of the source.
    /// - ensures: when [`Self::asked_generators`] reads the sort that `asked`
    ///   names, no terms slot of the unit is for that sort and each index sort
    ///   has its slot, one [`Role::Terms`] slot named by the text of `asked`,
    ///   and one [`TermsForm`] for it. Nothing where the sort does not read, or
    ///   where an index sort has no slot yet: the lowering refuses the type
    ///   where it reads it.
    /// - provides: the terms half of the theory collection.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance, before any slot is taken.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Cost
    /// - allocation: the entries of the index sorts, growth within the indices
    ///   of the sort
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a unital magma's terms written twice take one slot; a
    ///   two-sorted theory's read at no sort take none. The terms of a sort
    ///   over the widths take their slot after the slot of the widths, and a
    ///   unit that writes the terms of the widths nowhere takes no slot.
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    /// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_theory_outside_one_plain_sort_are_refused_4143`
    /// - witness: `gandr-surface-lowering::tests::modules::models::the_terms_of_a_sort_are_a_type_and_of_an_indexed_sort_a_family_8358`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.terms.len()),
        ensures: |ret| self.collected.slots.len().saturating_sub(before.0)
            == self.collected.terms.len().saturating_sub(before.1)
            && self.collected.terms.len() <= before.1.saturating_add(1)
            && (ret.is_ok() || self.collected.slots.len() == before.0),
    )]
    pub(super) fn terms(
        &mut self,
        asked: AskedTerms,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.fuel.spend()?;
        let Some((theory, generators)) = self.asked_generators(asked)
        else {
            return Ok(());
        };
        let held = |collector: &Self, sort: Placed| {
            collector
                .collected
                .terms
                .iter()
                .position(|terms| terms.theory == theory && terms.sort == sort)
        };
        if held(self, generators.sort).is_some() {
            return Ok(());
        }
        let Some(name) = self.terms_name(asked)
        else {
            return Ok(());
        };
        // An index of a type is a term of the index sort, so a type of the
        // unit writes the terms of that sort before this one.
        let mut indices = Vec::with_capacity(generators.indices.len());
        for &index in &generators.indices {
            let Some(entry) = held(self, index)
            else {
                return Ok(());
            };
            indices.push(entry);
        }
        let form = TermsForm {
            theory,
            slot: SlotIndex(self.collected.slots.len()),
            sort: generators.sort,
            operations: generators.operations,
            arities: generators.arities,
            indices,
            stated: generators.stated,
        };
        self.take_terms(asked, name, form);

        Ok(())
    }
}
