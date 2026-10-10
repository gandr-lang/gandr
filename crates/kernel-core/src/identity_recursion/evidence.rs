//! Derived diagonal evidence and transport for the first-order identity family.

use alloc::vec::Vec;

use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompType;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::Fiber;
use super::Fibers;
use super::Identity;
use super::Mode;
use super::Proof;
use super::Relation;
use super::RelationError;
use super::check_value;
use super::same_type;
use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::encoding::ContentTable;
use crate::rewrite::substitute_comp_type;

impl Identity
{
    /// Expose computed evidence without granting a checking capability.
    ///
    /// # Specification
    /// - ensures: returns the native fibre inhabitant carried by this identity.
    /// - fails: `NeutralFiber` for a suspended diagonal program.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::NeutralFiber`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — higher replay consumes computed evidence, while a
    ///   suspended sum diagonal cannot become an invented native value.
    /// - witness: `higher_field::tests::higher_fibres_preserve_boundaries`
    #[inline]
    pub fn native_evidence(self) -> Result<ValueId, RelationError>
    {
        match self.proof {
            | Proof::Native(value) => Ok(value),
            | Proof::Diagonal => Err(RelationError::NeutralFiber),
        }
    }
}

/// A dependent transport computation in the experimental rule language.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Transport
{
    /// Transport reduced to this value at the instantiated target fibre.
    Return(ValueId),
    /// A neutral identity cannot yet reduce a dependent transport.
    /// Re-evaluation after substituting its indices computes its next step.
    Neutral
    {
        /// The source fibre checked for the argument.
        source: ValueTypeId,
        /// The target fibre of the suspended computation.
        target: ValueTypeId,
        /// The value supplied at the source.
        value: ValueId,
        /// The checked identity whose action remains suspended.
        identity: Identity,
        /// The family body, still scoped under the identity index.
        motive: ValueTypeId,
    },
}

impl Relation
{
    /// Derive the diagonal inhabitant of an identity relation.
    ///
    /// # Specification
    /// - ensures: interprets the relation at `(value, value)` and constructs
    ///   Unit/pair evidence when computed. A neutral sum retains the structural
    ///   diagonal program: case on the index, then the corresponding payload
    ///   diagonal. This operation never installs a relation at an abstract
    ///   type.
    /// - fails: `NonFibrant` for a bridge, `HigherEvaluationRequired` at a
    ///   function fibre, or an index-checking error. Function reflexivity uses
    ///   `function_reflexivity` with a producer-supplied higher introduction.
    /// - panics: none.
    ///
    /// # Errors
    /// `NonFibrant`, `Typing`, `Arena`, or `Evidence` for an impossible empty
    /// diagonal; `HigherEvaluationRequired` at a function fibre.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Unit, Base and Product diagonals compute; a neutral
    ///   sum retains a diagonal without treating its unknown tag as a
    ///   constructor.
    /// - witness: `identity_recursion::tests::reflexivity_and_transport_compute`
    /// - witness: `identity_recursion::function::tests::lambda_reflexivity_replays_higher_evaluation`
    #[inline]
    pub fn reflexivity(
        &self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
        value: ValueId,
    ) -> Result<Identity, RelationError>
    {
        self.fibrant()?;
        let fiber = self.fiber(arena, context, value, value)?;
        let proof = match fiber.inhabitant(arena) {
            | Ok(value) => Proof::Native(value),
            | Err(RelationError::NeutralFiber) => Proof::Diagonal,
            | Err(error) => return Err(error),
        };
        let root = self.node(self.root)?;
        let domain = root.source;
        Ok(Identity {
            domain,
            left: value,
            right: value,
            proof,
        })
    }

    /// Check supplied evidence at the computed element-identity fibre.
    ///
    /// # Specification
    /// - ensures: both endpoints check and `proof : Rel(left, right)` in the
    ///   context; cross-injection or unequal-base evidence cannot be
    ///   fabricated.
    /// - fails: `NonFibrant`, `NeutralFiber`, or a fibre/type-checking error.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Unit cannot inhabit Empty; product evidence must
    ///   satisfy both coordinates, including a mismatched second coordinate.
    /// - witness: `identity_recursion::tests::identity_evidence_refuses_false_fibres`
    #[inline]
    pub fn witness(
        &self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
        left: ValueId,
        right: ValueId,
        proof: ValueId,
    ) -> Result<Identity, RelationError>
    {
        self.fibrant()?;
        let fiber = self.fiber(arena, context, left, right)?;
        let ty = fiber.native(arena)?;
        check_value(arena, context, proof, ty)?;
        let root = self.node(self.root)?;
        let domain = root.source;
        Ok(Identity {
            domain,
            left,
            right,
            proof: Proof::Native(proof),
        })
    }

    /// Transport identity evidence in the family `z -> Rel(left, z)`.
    ///
    /// # Specification
    /// - ensures: checks both identities and their middle boundary, then gives
    ///   evidence at the composite endpoints. Product fibres compose through
    ///   both component fibres; sum fibres keep their common injection. Base
    ///   fibres compose discrete equality. A diagonal supplies either unit law.
    /// - fails: `Boundary` for a wrong middle endpoint; `NonFibrant` for
    ///   bridges; an evidence-checking error for invalid proofs.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`, including `Evidence` or `NeutralFiber` if no computed
    /// composite exists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — composition checks the middle boundary and both
    ///   product coordinates; its result inhabits the independently computed
    ///   fibre.
    /// - witness: `identity_recursion::tests::product_transport_composes_componentwise`
    #[inline]
    pub fn compose(
        &self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
        first: &Identity,
        second: &Identity,
    ) -> Result<Identity, RelationError>
    {
        self.validate(arena, context, first)?;
        self.validate(arena, context, second)?;
        if equal_values(arena, first.right, second.left) != Convertibility::Convertible {
            return Err(RelationError::Boundary);
        }
        if matches!(first.proof, Proof::Diagonal) {
            return Ok(second.clone());
        }
        if matches!(second.proof, Proof::Diagonal) {
            return Ok(first.clone());
        }
        let fiber = self.fiber(arena, context, first.left, second.right)?;
        let proof = fiber.inhabitant(arena)?;
        self.witness(arena, context, first.left, second.right, proof)
    }

    /// Transport in a native level-zero value family scoped under one index.
    ///
    /// # Specification
    /// - ensures: forms `motive` under the identity's element binder, checks
    ///   the source argument, and instantiates both fibres by capture-free
    ///   substitution. Reflexive endpoint syntax returns the exact supplied
    ///   value. Otherwise the dependent elimination remains a typed neutral,
    ///   not a guessed value.
    /// - fails: `NonFibrant` or a proof, family, or argument typing failure.
    /// - panics: none.
    ///
    /// # Errors
    /// `NonFibrant`, `Boundary`, `Typing`, `NeutralFiber`, `Arena`, `Evidence`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — base and product reflexivity transport open values
    ///   unchanged; ill-typed arguments refuse; neutral Unit indices do not
    ///   license unchecked conversion of a dependent family.
    /// - witness: `identity_recursion::tests::reflexivity_and_transport_compute`
    #[inline]
    pub fn transport(
        &self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
        identity: &Identity,
        motive: ValueTypeId,
        value: ValueId,
    ) -> Result<Transport, RelationError>
    {
        self.validate(arena, context, identity)?;
        let mut extended = Vec::with_capacity(context.len().saturating_add(1));
        extended.extend_from_slice(context);
        extended.push(identity.domain);
        let quote = arena.value_quote(motive);
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        check_value(arena, &extended, quote, universe)?;
        let mut table = ContentTable::new();
        let family = arena.comp_type_returner(motive);
        let source = substitute_comp_type(arena, &mut table, &mut NullMemo, family, identity.left);
        let target = substitute_comp_type(arena, &mut table, &mut NullMemo, family, identity.right);
        let source = return_type(arena, source)?;
        let target = return_type(arena, target)?;
        check_value(arena, context, value, source)?;
        if equal_values(arena, identity.left, identity.right) == Convertibility::Convertible {
            check_value(arena, context, value, target)?;
            Ok(Transport::Return(value))
        }
        else {
            Ok(Transport::Neutral {
                source,
                target,
                value,
                identity: identity.clone(),
                motive,
            })
        }
    }

    /// Require the identity reading before exposing fibrant operations.
    ///
    /// # Specification
    /// - ensures: only code-derived identity programs pass.
    /// - fails: `NonFibrant` for every bridge program.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::NonFibrant`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — arbitrary bridge families cannot acquire transport.
    /// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
    pub(super) fn fibrant(&self) -> Result<(), RelationError>
    {
        match self.mode {
            | Mode::Identity => Ok(()),
            | Mode::Bridge => Err(RelationError::NonFibrant),
        }
    }

    /// Recheck arena-relative evidence in the current context.
    ///
    /// # Specification
    /// - ensures: the identity belongs to this relation and its evidence
    ///   checks; the suspended diagonal is permitted only at reflexive
    ///   endpoints.
    /// - fails: `NonFibrant`, `Boundary`, or evidence/index checking errors.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — changing the context or relation cannot reuse
    ///   evidence as an unchecked judgement.
    /// - witness: `identity_recursion::tests::identity_evidence_refuses_false_fibres`
    pub(super) fn validate(
        &self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
        identity: &Identity,
    ) -> Result<(), RelationError>
    {
        self.fibrant()?;
        let root = self.node(self.root)?;
        same_type(arena, root.source, identity.domain)?;
        match identity.proof {
            | Proof::Native(proof) => {
                self.witness(arena, context, identity.left, identity.right, proof)?;
            },
            | Proof::Diagonal => {
                if equal_values(arena, identity.left, identity.right) != Convertibility::Convertible
                {
                    return Err(RelationError::Boundary);
                }
                self.reflexivity(arena, context, identity.left)?;
            },
            | Proof::HigherEvaluation(ref evidence) => {
                self.check_higher(
                    arena,
                    (identity.left, identity.right),
                    evidence,
                    crate::replay::ReplayBudget::DEFAULT,
                )?;
            },
        }
        Ok(())
    }
}

impl Fibers
{
    /// Construct evidence for Unit/product fibres, preserving every coordinate.
    ///
    /// # Specification
    /// - ensures: a native inhabitant constructed from Unit and pairing.
    /// - fails: `Evidence` on Empty, `NeutralFiber` on a residual, `Arena` on
    ///   an invalid local address.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composition witness has the computed product
    ///   fibre and cannot erase an empty coordinate.
    /// - witness: `identity_recursion::tests::product_transport_composes_componentwise`
    pub(super) fn inhabitant(
        &self,
        arena: &mut TermArena,
    ) -> Result<ValueId, RelationError>
    {
        /// Pending proof-construction work.
        enum Task
        {
            /// Construct the evidence of this fibre.
            Visit(super::FiberId),
            /// Pair both component inhabitants.
            Pair,
            /// Reuse the completed proof for a shared fibre.
            Remember(super::FiberId),
        }
        let mut pending = Vec::from([Task::Visit(self.root())]);
        let mut values = Vec::new();
        let mut completed = alloc::collections::BTreeMap::new();
        while let Some(task) = pending.pop() {
            let value = match task {
                | Task::Remember(id) => {
                    let value = *values.last().ok_or(RelationError::Arena)?;
                    completed.insert(id, value);
                    continue;
                },
                | Task::Pair => {
                    let right = values.pop().ok_or(RelationError::Arena)?;
                    let left = values.pop().ok_or(RelationError::Arena)?;
                    arena.value_pair(left, right)
                },
                | Task::Visit(id) => {
                    if let Some(&value) = completed.get(&id) {
                        values.push(value);
                        continue;
                    }
                    pending.push(Task::Remember(id));
                    let fiber = self.get(id)?;
                    match fiber {
                        | Fiber::Unit => arena.value_unit(),
                        | Fiber::Product(left, right) => {
                            pending.push(Task::Pair);
                            pending.push(Task::Visit(right));
                            pending.push(Task::Visit(left));
                            continue;
                        },
                        | Fiber::Empty => return Err(RelationError::Evidence),
                        | Fiber::Function { .. } => {
                            return Err(RelationError::HigherEvaluationRequired);
                        },
                        | Fiber::Discrete(..) | Fiber::Suspended(..) => {
                            return Err(RelationError::NeutralFiber);
                        },
                    }
                },
            };
            values.push(value);
        }
        values.pop().ok_or(RelationError::Arena)
    }
}

/// Extract the value type of a substituted returner family.
///
/// # Specification
/// - ensures: returns the returner's child without interpreting another former.
/// - fails: `Arena` if substitution did not preserve its returner wrapper.
/// - panics: none.
///
/// # Errors
/// `RelationError::Arena`.
///
/// # Adequacy
/// - hypothesis: L3 — dependent transport uses the correctly instantiated
///   fibre.
/// - witness: `identity_recursion::tests::reflexivity_and_transport_compute`
fn return_type(
    arena: &TermArena,
    ty: gandr_kernel_term::CompTypeId,
) -> Result<ValueTypeId, RelationError>
{
    match arena.comp_type(ty) {
        | Some(&CompType::Returner(value)) => Ok(value),
        | _ => Err(RelationError::Arena),
    }
}
