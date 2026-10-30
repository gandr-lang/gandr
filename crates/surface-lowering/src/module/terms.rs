//! The terms of a theory, as the collection pass reads them.
//!
//! A type a source writes as `Terms(S)`, `S` a theory of one plain sort, asks
//! for the theory's terms: a presented type whose constructors are `S`'s
//! operations, each taking its inputs as terms, and whose rules are `S`'s
//! rules read over those constructors. The first such type the unit writes
//! for `S` takes one [`Role::Terms`] slot before the top-level form writing it,
//! as a manifest model type's forgetting map does, its definition the half
//! [`Operand::Terms`] the lowering mints from the presentation
//! ([`TermsForm`]). The slot is named by the type as first written, the name
//! the terms print by, and is entered in no name table; `S.op` names its
//! constructors. A theory outside the slice takes
//! no slot, and the lowering refuses the type where it reads it
//! ([`term_generators`]).

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::NodeLabel;
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
use crate::form::Former;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::shape_of;
use crate::model::Port;
use crate::model::Presentation;
use crate::resolve::SurfaceName;
use crate::unbuilt::Unbuilt;

/// The head a source writes a theory's terms under, `Terms(S)`.
pub const TERMS: &str = "Terms";

/// The terms of one theory: the slot they take and the generators the
/// theory's operations give them.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `theory` is the slot of a `theory` block of one plain sort;
///   `operations` and `arities` are parallel, one entry per operation of its
///   presentation, in its order.
/// - executable: none — the record is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — a unital magma's terms take one slot whose generators are
///   its unit and its product.
/// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermsForm
{
    /// The theory's slot.
    pub theory: SlotIndex,
    /// The slot the terms take, entered in no namespace.
    pub slot: SlotIndex,
    /// Each operation's name tile, in the presentation's order: the name its
    /// constructor answers to.
    pub operations: Vec<Placed>,
    /// Each operation's input count, parallel to `operations`.
    pub arities: Vec<usize>,
}

/// The generators a presentation gives its terms: each operation's name tile
/// and its input count, in the presentation's order.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `operations` and `arities` are parallel when [`term_generators`]
///   builds the record.
/// - executable: none — the record is data the collector reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`term_generators`].
/// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermGenerators
{
    /// Each operation's name tile, in the presentation's order.
    pub operations: Vec<Placed>,
    /// Each operation's input count, parallel to `operations`.
    pub arities: Vec<usize>,
}

/// The generators `presentation` gives its terms.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one name tile and one count per operation when the presentation
///   declares one sort, of no indices and landing in values, every operation
///   returns one result of it and takes each input at it, binding and
///   abstracting nothing, no rule is wired as a circuit, and no law is stated.
/// - fails: [`Unbuilt::LawTerms`] for a stated law; [`Unbuilt::TermsType`] for
///   any other presentation outside that slice, or one whose members do not
///   read.
/// - panics: none.
///
/// # Errors
/// As the fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — a unital magma gives its unit and its product, a
///   two-sorted theory and a law-bearing one are refused by their features.
/// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
/// - witness: `tests::modules::models::the_terms_of_a_theory_outside_one_plain_sort_are_refused_4143`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |generators| generators.operations.len() == generators.arities.len()))]
pub fn term_generators(presentation: &Presentation) -> Result<TermGenerators, Unbuilt>
{
    if !presentation.laws.is_empty() {
        return Err(Unbuilt::LawTerms);
    }
    let outside = Err(Unbuilt::TermsType);
    if !presentation.circuits.is_empty() {
        return outside;
    }
    let Ok(members) = presentation.members()
    else {
        return outside;
    };
    let [ref sort] = *members.sorts
    else {
        return outside;
    };
    if !sort.indices.is_empty() || sort.ground != GroundSort::Value {
        return outside;
    }
    let plain = |port: &Port| {
        port.sort.sort == sort.name
            && port.sort.indices.is_empty()
            && port.binders.is_empty()
            && port.abstractions.is_empty()
    };
    let mut operations = Vec::with_capacity(members.operations.len());
    let mut arities = Vec::with_capacity(members.operations.len());
    for operation in &members.operations {
        let [ref output] = *operation.outputs
        else {
            return outside;
        };
        if !plain(output) || !operation.inputs.iter().all(plain) {
            return outside;
        }
        operations.push(operation.named);
        arities.push(operation.inputs.len());
    }

    Ok(TermGenerators {
        operations,
        arities,
    })
}

impl<'source> Collector<'_, 'source>
{
    /// The terms types of the source, `Terms(S)` with `S` one name, each beside
    /// the theory's name tile, in the order their text starts.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every type application of the source's tree that reads `Terms
    ///   ( S )`, once, beside the name tile of `S`, ascending by the start of
    ///   its span.
    /// - panics: none.
    /// - executable: none — the classification is the grammar's, which a
    ///   predicate would read again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::terms`].
    /// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    pub(super) fn terms_types(&mut self) -> Vec<(Placed, Placed)>
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
            let at = Placed::of(position, node);
            if let Some(named) = self.applied_operand(at, SurfaceName::from(TERMS), &mut pieces) {
                found.push((at, named));
            }
        }
        self.pieces = pieces;
        found.sort_by_key(|&(at, _)| at.span.start());

        found
    }

    /// Collect the terms the type `at`, `Terms(S)`, asks for, `named` the name
    /// tile of `S`.
    ///
    /// # Specification
    /// - requires: `at` is a terms type of the source, `named` its theory's
    ///   name tile.
    /// - ensures: when
    ///   [`Collected::presented_theory`](super::Collected::presented_theory)
    ///   resolves `S` where it is written to a theory no terms slot of the unit
    ///   is for, and [`term_generators`] reads its generators, one
    ///   [`Role::Terms`] slot named by `at`'s text and at `named`, its
    ///   definition the terms the lowering mints, and one [`TermsForm`] for it;
    ///   nothing otherwise, a type of another theory being the lowering's to
    ///   refuse where it reads it.
    /// - provides: the terms half of the theory collection.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance, before any slot is taken.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a unital magma's terms written twice take one slot; a
    ///   two-sorted theory's take none.
    /// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    /// - witness: `tests::modules::models::the_terms_of_a_theory_outside_one_plain_sort_are_refused_4143`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.terms.len()),
        ensures: |ret| self.collected.slots.len().saturating_sub(before.0)
            == self.collected.terms.len().saturating_sub(before.1)
            && self.collected.terms.len() <= before.1.saturating_add(1)
            && (ret.is_ok() || self.collected.slots.len() == before.0),
    )]
    pub(super) fn terms(
        &mut self,
        at: Placed,
        named: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.fuel.spend()?;
        let Ok((theory, presentation)) =
            self.collected
                .presented_theory(named.span.start(), named.span, self.name_of(named))
        else {
            return Ok(());
        };
        if self
            .collected
            .terms
            .iter()
            .any(|terms| terms.theory == theory)
        {
            return Ok(());
        }
        let Ok(TermGenerators {
            operations,
            arities,
        }) = term_generators(presentation)
        else {
            return Ok(());
        };
        // The terms print as the type that asked for them, `Terms(S)`.
        let Some(name) = self.tree.fragment(at.node).map(SurfaceName::from)
        else {
            return Ok(());
        };
        let index = self.collected.terms.len();
        let slot = SlotIndex(self.collected.slots.len());
        self.collected.slots.push(DeclarationSlot {
            name,
            container: self.collected.top(at.span.start()),
            role: Role::Terms,
            constant: ConstantIndex::from(slot.0),
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
        self.collected.terms.push(TermsForm {
            theory,
            slot,
            operations,
            arities,
        });

        Ok(())
    }
}
