//! Derived rules, as the collection pass reads them.
//!
//! `derive r : l <=> r in T` reads its statement
//! ([`crate::description::derive`]), finds the theory `T` names as the model
//! type `Model(T)` finds it, and plans the proof the theory's completed rules
//! give ([`crate::derive::plan`]). Each lemma of the plan takes a slot, in the
//! plan's order, [`Role::Derived`] with the definition half
//! [`Operand::Derived`], entered in no name table. The last is the statement's
//! own: it owns the declaration and its decorations, and the lowering enters
//! it under the theory's path, `T.r`. A statement the theory does not derive is
//! refused [`LoweringRefusal::UnderivedRule`] on a held slot under the rule's
//! name.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::Collector;
use super::DeclarationSlot;
use super::Half;
use super::Operand;
use super::Role;
use super::SlotIndex;
use super::declaration_half;
use super::slot_refusal;
use crate::derive::DeriveFault;
use crate::derive::Lemma;
use crate::derive::plan;
use crate::description::derive::derived_statement;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::shape_of;

/// A slot a `derive` declaration takes: the theory its rule holds in and the
/// lemma the slot states and proves.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `presented` is the slot of the `theory` block `theory` names
///   where the declaration starts, at `at`; `run` is the declaration's first
///   slot, which a lemma the proof fires counts its place from.
/// - executable: none — the record is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — a group's inverse of a product takes one slot per lemma
///   its proof rests on, then its own.
/// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DerivedSlot
{
    /// The theory's name tile.
    pub theory: Placed,
    /// Where the declaration starts.
    pub at: ByteOffset,
    /// The theory's slot.
    pub presented: SlotIndex,
    /// The lemma the slot states and proves.
    pub lemma: Lemma,
    /// The declaration's first slot.
    pub run: SlotIndex,
}

/// Whether a root child is a `derive` declaration.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub(super) struct Derives(pub bool);

impl<'source> Collector<'_, 'source>
{
    /// Whether the root child `child` is a `derive` declaration.
    ///
    /// # Specification
    /// - requires: `child` is a root child.
    /// - ensures: whether its node is the form the grammar names
    ///   [`FormName::DERIVE_DECLARATION`].
    /// - fails: when the node's mold is unknown to the grammar.
    /// - panics: none.
    /// - executable: none — the result is the grammar's reading of the node.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::derive`].
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    pub(super) fn derives(
        &self,
        child: Placed,
    ) -> Result<Derives, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(child.node)
        else {
            return Ok(Derives(false));
        };

        Ok(Derives(matches!(
            shape_of(self.pbg, node)?,
            Shape::Form { name, .. } if name == FormName::DERIVE_DECLARATION
        )))
    }

    /// Collect the `derive` declaration `declaration`, decorated by the
    /// attribute blocks `decorations` standing before it.
    ///
    /// # Specification
    /// - requires: `declaration` is a derive declaration form and every entry
    ///   of `decorations` an attribute block standing on its own before it.
    /// - ensures: a statement its theory's completed rules derive takes one
    ///   [`Role::Derived`] slot per lemma of its plan, in order, the last the
    ///   statement's; a statement the plan refuses, or whose theory no `theory`
    ///   block defines, takes one held slot under the rule's name carrying the
    ///   refusal, the declaration its definition, so its expectation is read;
    ///   either way the last slot owns the declaration and its decorations and
    ///   carries their attributes; no slot enters the name table; the sides, as
    ///   written, join the members of the theory's description, when a `theory`
    ///   block defines it.
    /// - provides: the derive half of [`super::collect_source`].
    /// - fails: when the form is malformed: the parser repaired it, or a piece
    ///   of it is out of place.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] and the mold refusals of
    /// [`crate::form::read_pieces`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a derived rule takes its slots, and a statement the
    ///   completion keeps apart is refused by name.
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    /// - witness: `tests::modules::models::a_rule_the_theory_does_not_derive_is_refused`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.by_name.len()),
        ensures: |ret| ret.is_err() || (self.collected.slots.len() > before.0
            && self.collected.by_name.len() == before.1),
    )]
    pub(super) fn derive(
        &mut self,
        declaration: Placed,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let statement =
            derived_statement(self.pbg, self.tree, declaration)?.map_err(|diagnostic| {
                LoweringRefusal::MalformedForm {
                    span: diagnostic.span,
                    form: FormName::DERIVE_DECLARATION,
                    fault: FormFault::MisplacedTile,
                }
            })?;
        let name = self.name_of(statement.named);
        let theory = self.name_of(statement.theory);
        let at = declaration.span.start();
        let container = self.collected.top(at);
        let planned = self
            .collected
            .presented_theory(at, statement.theory.span, theory)
            .and_then(|(presented, presentation)| {
                let node = self
                    .collected
                    .slots
                    .get(presented.0)
                    .map(|slot| slot.introduced_by.node);
                let rule = Name::from(name.as_ref());
                self.collected
                    .cells
                    .declarations
                    .iter()
                    .find(|cells| Some(cells.at.node) == node)
                    .map_or(Err(DeriveFault::Incoherent), |cells| {
                        plan(
                            (&rule, statement.named),
                            (&statement.sides.left.0, &statement.sides.right.0),
                            presentation,
                            cells,
                        )
                    })
                    .map(|lemmas| (presented, lemmas))
                    .map_err(|fault| LoweringRefusal::UnderivedRule {
                        span: declaration.span,
                        rule: name,
                        theory,
                        fault,
                    })
            });
        let slot = match planned {
            Ok((presented, lemmas)) => {
                let run = SlotIndex(self.collected.slots.len());
                for lemma in lemmas {
                    let minted = SlotIndex(self.collected.slots.len());
                    self.collected.slots.push(DeclarationSlot {
                        name,
                        container,
                        role: Role::Derived,
                        constant: ConstantIndex::from(minted.0),
                        introduced_by: declaration,
                        named: statement.named,
                        signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                        definition: Maybe::Present(Half {
                            declaration,
                            named: statement.named,
                            operand: Operand::Derived,
                        }),
                        attributes: Vec::new(),
                        docs: Vec::new(),
                        refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
                    });
                    let _fresh = self.collected.derived.insert(minted, DerivedSlot {
                        theory: statement.theory,
                        at,
                        presented,
                        lemma,
                        run,
                    });
                }
                SlotIndex(self.collected.slots.len().saturating_sub(1))
            },
            Err(refusal) => {
                let held = self.refuse_held(container, name, declaration, statement.named, refusal);
                if let Some(entry) = self.collected.slots.get_mut(held.0) {
                    entry.definition = Maybe::Present(Half {
                        declaration,
                        named: statement.named,
                        operand: Operand::Derived,
                    });
                }
                held
            },
        };
        // The sides are the theory's terms: its description answers each node
        // at its sort, as it answers its own rules' nodes.
        let described = self
            .collected
            .presented_theory(at, statement.theory.span, theory)
            .ok()
            .and_then(|(presented, _)| self.collected.slots.get(presented.0))
            .map(|slot| slot.introduced_by.node);
        if let Some(node) = described
            && let Maybe::Present(entry) = self.collected.descriptions.get_mut(&node)
        {
            entry.written.derived.push(statement.sides);
        }
        self.collected.own(declaration.node, slot);
        let mut attributes = Vec::new();
        let mut attributed = Ok(());
        for &block in decorations {
            self.collected.own(block.node, slot);
            if attributed.is_ok() {
                attributed = self.decoration(block, declaration.node, &mut attributes);
            }
        }
        for &block in decorations {
            self.document(slot, block.node, block.span.end(), declaration.node);
        }
        self.document(
            slot,
            declaration.node,
            statement.named.span.start(),
            declaration.node,
        );
        if let Some(entry) = self.collected.slots.get_mut(slot.0) {
            entry.attributes.extend(attributes);
            if let Err(refusal) = attributed {
                entry.refuse(declaration.node, refusal);
            }
        }

        Ok(())
    }
}
