//! Pointwise translator identities and higher coherence of replayed round
//! trips.

use alloc::boxed::Box;
use alloc::vec::Vec;

use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::Cell;
use super::Codata;
use super::HigherError;
use super::ObservationBudget;
use super::Prefix;
use super::relation;
use crate::check::check_closed_value;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::identity_recursion::RelationError;
use crate::path_universe::Dialogue;
use crate::path_universe::endpoints;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::replay::replay;

/// The unfolded type of identity between two equivalence records.
///
/// Fields describe obligations, not their inhabitants. Observing a field at a
/// point establishes only that instance and the stated higher depth. Exhaustive
/// Bool observations cover both constructors; finite Base samples do not prove
/// a universally quantified field.
#[derive(Clone, Copy, Debug)]
pub struct CertificateIdentity
{
    /// Pointwise identity of forward translators.
    pub forward: Pointwise,
    /// Pointwise identity of backward translators.
    pub backward: Pointwise,
    /// Identity between the source round trips reflected from replay.
    pub source_coherence: Coherence,
    /// Identity between the target round trips reflected from replay.
    pub target_coherence: Coherence,
}

/// A point-indexed identity of two closed translators.
#[derive(Clone, Copy, Debug)]
pub struct Pointwise
{
    /// The input type.
    domain: ValueTypeId,
    /// The result type.
    codomain: ValueTypeId,
    /// The left translator.
    left: ValueId,
    /// The right translator.
    right: ValueId,
}

/// A point-indexed higher identity between two computational round trips.
#[derive(Clone, Copy, Debug)]
pub struct Coherence
{
    /// The first legs of the compared round trips.
    first: Pointwise,
    /// The second legs, with reversed source and target types.
    second: Pointwise,
}

/// A proposed returned value, with an untrusted reduction dialogue.
#[derive(Clone, Debug)]
pub struct Reduction
{
    /// The claimed normal result; replay checks this exact value.
    pub value: ValueId,
    /// Evidence for the kernel-built computation against `return value`.
    pub dialogue: Dialogue,
}

/// Evidence at one input of a pointwise translator identity.
#[derive(Clone, Debug)]
pub struct PointwiseEvidence
{
    /// Proposed result of the left translator.
    pub left: Reduction,
    /// Proposed result of the right translator.
    pub right: Reduction,
    /// Evidence relating those two results in the code-derived identity.
    pub identity: ValueId,
    /// Guarded higher evidence for that identity's diagonal.
    pub higher: Codata,
}

/// Evidence at one input of a round-trip coherence field.
#[derive(Clone, Debug)]
pub struct CoherenceEvidence
{
    /// Replay of the left round trip to its input.
    pub left: Dialogue,
    /// Replay of the right round trip to its input.
    pub right: Dialogue,
    /// Identity between the reflected round-trip witnesses, observed lazily.
    pub higher: Codata,
}

/// Unfold identity of equivalence certificates into its four record fields.
///
/// # Specification
/// - requires: all arena nodes remain live without address reuse.
/// - ensures: both certificates form independently at the same endpoints;
///   returns forward and backward pointwise identities and the two higher
///   round-trip coherence obligations. No certificate comparison is performed.
/// - provides: an identity type's record view, not a universal inhabitant.
/// - fails: `Relation(Typing(..))` for native checking, `Path` for endpoint
///   decoding, `Boundary` for mismatched endpoints, or `ExpectedEquivalence`
///   for a non-record introduction.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — negation and case-inlined triple negation unfold to
///   independently replayable fields despite non-convertible certificates.
/// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
#[inline]
pub fn unfold(
    arena: &mut TermArena,
    left: ValueId,
    right: ValueId,
    budget: ReplayBudget,
) -> Result<CertificateIdentity, HigherError>
{
    let first = crate::check::synth_closed_value(arena, left)
        .map_err(|error| RelationError::Typing(Box::new(error)))?;
    let first = endpoints(arena, first, budget)?;
    let second = crate::check::synth_closed_value(arena, right)
        .map_err(|error| RelationError::Typing(Box::new(error)))?;
    let second = endpoints(arena, second, budget)?;
    if convertible_value_types(arena, first.source, second.source) != Convertibility::Convertible
        || convertible_value_types(arena, first.target, second.target)
            != Convertibility::Convertible
    {
        return Err(HigherError::Boundary);
    }
    let left = arena.value(left).ok_or(HigherError::ExpectedEquivalence)?;
    let right = arena.value(right).ok_or(HigherError::ExpectedEquivalence)?;
    let (
        &Value::PathEquiv {
            forward: left_forward,
            backward: left_backward,
            ..
        },
        &Value::PathEquiv {
            forward: right_forward,
            backward: right_backward,
            ..
        },
    ) = (left, right)
    else {
        return Err(HigherError::ExpectedEquivalence);
    };
    let forward = Pointwise {
        domain: first.source,
        codomain: first.target,
        left: left_forward,
        right: right_forward,
    };
    let backward = Pointwise {
        domain: first.target,
        codomain: first.source,
        left: left_backward,
        right: right_backward,
    };
    Ok(CertificateIdentity {
        forward,
        backward,
        source_coherence: Coherence {
            first: forward,
            second: backward,
        },
        target_coherence: Coherence {
            first: backward,
            second: forward,
        },
    })
}

impl Pointwise
{
    /// Replay both translator outputs, then observe their identity's higher
    /// field.
    ///
    /// # Specification
    /// - ensures: input, maps and outputs typecheck; both reductions replay;
    ///   their results inhabit the stated identity fibre and its higher prefix.
    /// - provides: evidence only at `input`, never a sampled universal verdict.
    /// - fails: `Relation`, `Replay`, or a higher observation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both Bool points and both translator directions
    ///   compute; a swapped output or a corrupt dialogue refuses.
    /// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
    #[inline]
    pub fn observe(
        self,
        arena: &mut TermArena,
        input: ValueId,
        evidence: &PointwiseEvidence,
        budget: ObservationBudget,
    ) -> Result<Prefix, HigherError>
    {
        self.check(arena, input)?;
        for (translator, output) in [(self.left, &evidence.left), (self.right, &evidence.right)] {
            check(arena, output.value, self.codomain)?;
            let computation = apply(arena, translator, input);
            let expected = arena.computation_return(output.value);
            reduce(
                arena,
                computation,
                expected,
                &output.dialogue,
                budget.replay,
            )?;
        }
        let code = arena.value_quote(self.codomain);
        let cell = Cell {
            code,
            left: evidence.left.value,
            right: evidence.right.value,
            evidence: evidence.identity,
        };
        evidence.higher.observe(arena, &[], cell, cell, budget)
    }

    /// Check the point and both maps in their closed telescope.
    ///
    /// # Specification
    /// - ensures: both maps have the exact `U (domain -> F codomain)` type.
    /// - fails: `Relation` for ordinary kernel typing failure.
    /// - panics: none.
    ///
    /// # Errors
    /// `HigherError::Relation`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a Unit argument cannot enter a Bool field.
    /// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
    fn check(
        self,
        arena: &mut TermArena,
        input: ValueId,
    ) -> Result<(), HigherError>
    {
        check(arena, input, self.domain)?;
        let returner = arena.comp_type_returner(self.codomain);
        let arrow = arena.comp_type_arrow(self.domain, returner);
        let thunk = arena.value_type_thunk(arrow);
        check(arena, self.left, thunk)?;
        check(arena, self.right, thunk)
    }
}

impl Coherence
{
    /// Observe identity between the two round-trip witnesses at one point.
    ///
    /// # Specification
    /// - ensures: both typed composites replay to the input; their conversion
    ///   proofs reflect to native diagonal witnesses, whose identity is checked
    ///   through the higher field. Round-trip dialogue syntax is not compared.
    /// - provides: coherence of computational round trips in this first-order
    ///   fragment, with a stated finite higher depth.
    /// - fails: `Relation`, `Replay`, or a higher observation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both round-trip directions replay at both Bool
    ///   constructors; a corrupt or non-productive coherence is refused.
    /// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
    #[inline]
    pub fn observe(
        self,
        arena: &mut TermArena,
        input: ValueId,
        evidence: &CoherenceEvidence,
        budget: ObservationBudget,
    ) -> Result<Prefix, HigherError>
    {
        self.first.check(arena, input)?;
        // Check second-leg maps directly: the intermediate need not be given
        // by the producer or evaluated before constructing the composite.
        let returner = arena.comp_type_returner(self.second.codomain);
        let arrow = arena.comp_type_arrow(self.second.domain, returner);
        let thunk = arena.value_type_thunk(arrow);
        check(arena, self.second.left, thunk)?;
        check(arena, self.second.right, thunk)?;
        let expected = arena.computation_return(input);
        for (first, second, dialogue) in [
            (self.first.left, self.second.left, &evidence.left),
            (self.first.right, self.second.right, &evidence.right),
        ] {
            let first = apply(arena, first, input);
            let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
            let second = apply(arena, second, variable);
            let computation = arena.computation_bind(first, second);
            reduce(arena, computation, expected, dialogue, budget.replay)?;
        }
        let code = arena.value_quote(self.first.domain);
        let relation = relation(arena, code)?;
        let diagonal = relation.reflexivity(arena, &[], input)?;
        let diagonal = diagonal.native_evidence()?;
        let cell = Cell {
            code,
            left: input,
            right: input,
            evidence: diagonal,
        };
        evidence.higher.observe(arena, &[], cell, cell, budget)
    }
}

/// Preserve ordinary closed-value checking failures.
///
/// # Specification
/// - ensures: succeeds exactly when the closed value checks at its type.
/// - fails: `Relation(Typing)` carrying the kernel diagnostic.
/// - panics: none.
///
/// # Errors
/// `HigherError::Relation`.
///
/// # Adequacy
/// - hypothesis: L3 — invalid field arguments refuse before replay.
/// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
fn check(
    arena: &mut TermArena,
    value: ValueId,
    ty: ValueTypeId,
) -> Result<(), HigherError>
{
    check_closed_value(arena, value, ty)
        .map_err(|error| HigherError::Relation(RelationError::Typing(Box::new(error))))
}

/// Construct a forced application of a closed translator.
///
/// # Specification
/// trivial.
fn apply(
    arena: &mut TermArena,
    translator: ValueId,
    input: ValueId,
) -> ComputationId
{
    let force = arena.computation_force(translator);
    arena.computation_application(force, input)
}

/// Replay a positive reduction claim built at the checking boundary.
///
/// # Specification
/// - requires: computations have been constructed from typed maps and values.
/// - ensures: only the existing kernel's positive replay verdict passes.
/// - fails: `Replay` preserves every non-positive verdict, including
///   exhaustion.
/// - panics: none.
///
/// # Errors
/// `HigherError::Replay`.
///
/// # Adequacy
/// - hypothesis: L3 — relabeling a wrong-output trace cannot prove equality.
/// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
fn reduce(
    arena: &mut TermArena,
    computation: ComputationId,
    expected: ComputationId,
    dialogue: &Dialogue,
    budget: ReplayBudget,
) -> Result<(), HigherError>
{
    let verdict = replay(
        arena,
        &Unfoldings::new(Vec::new()),
        ReplaySides::Computations(computation, expected),
        EngineClaim::Convertible,
        dialogue.0.iter().copied(),
        budget,
    );
    match verdict {
        | KernelVerdict::Convertible => Ok(()),
        | verdict => Err(HigherError::Replay(verdict)),
    }
}
