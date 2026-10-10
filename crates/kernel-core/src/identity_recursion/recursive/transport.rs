//! The list functor lifts a certified element equivalence constructorwise.

use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::Constructor;
use super::Cursor;
use super::Meter;
use super::Progress;
use super::Refusal;
use crate::higher_field::Codata;
use crate::higher_field::HigherError;
use crate::identity_recursion::Interpretation;
use crate::identity_recursion::RelationError;
use crate::path_universe;
use crate::path_universe::Dialogue;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;

/// A checked constructorwise lift, retaining raw element-path syntax only.
///
/// # Specification
/// - provides: List(source) ≃ List(target) from a checked source ≃ target.
/// - ensures: Nil maps to Nil, Cons maps its head and delays its tail. Round
///   trips follow by finite-spine induction from the element round trips; no
///   samples of lists or infinite coherence are certified at formation.
///
/// # Adequacy
/// - hypothesis: L1/L3 — invalid element certificates refuse at formation;
///   replay checks every observed head and preserves list shape.
/// - witness: `path_universe::tests::recursive_transport_tests::negation_transport_computes`
#[derive(Clone, Copy, Debug)]
pub struct ListEquivalence
{
    /// The raw path, rechecked by every consumer.
    element: ValueId,
    /// Native source list code, never an admission capability.
    source: ValueTypeId,
    /// Native target list code.
    target: ValueTypeId,
}

/// Untrusted output and one replay dialogue per observed Cons constructor.
#[derive(Clone, Copy, Debug)]
pub struct TransportEvidence<'evidence>
{
    /// The claimed constructorwise output.
    pub output: &'evidence Codata,
    /// The element transport claims, in spine order; Nil owes none.
    pub heads: &'evidence [Dialogue],
}

impl ListEquivalence
{
    /// Certify the element path before lifting its two maps to lists.
    ///
    /// # Specification
    /// - ensures: source and target are native List codes over checked element
    ///   endpoints. Inverses and both round trips come from path formation.
    /// - fails: existing path formation errors, without a list certificate.
    /// - panics: none.
    ///
    /// # Errors
    /// Native typing or endpoint decoding errors, retaining their cause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — constant Bool maps cannot become list equivalences.
    /// - witness: `path_universe::tests::recursive_transport_tests::negation_transport_computes`
    #[inline]
    pub fn form(
        arena: &mut TermArena,
        element: ValueId,
        budget: ReplayBudget,
    ) -> Result<Self, HigherError>
    {
        let endpoints = Interpretation::UniverseIdentity.path(arena, element, budget)?;
        Ok(Self {
            element,
            source: arena.value_type_list(endpoints.source),
            target: arena.value_type_list(endpoints.target),
        })
    }

    /// Expose the two native code roots, without exposing admission authority.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn endpoints(self) -> (ValueTypeId, ValueTypeId)
    {
        (self.source, self.target)
    }

    /// Replay the lifted forward map, one constructor at a time.
    ///
    /// # Specification
    /// - requires: all roots remain live in their original arenas.
    /// - ensures: success only at paired Nil, after all Cons head transports
    ///   replay positively and all supplied dialogues are consumed exactly.
    ///   Shape mismatch, wrong output and corrupt evidence never certify.
    /// - fails: existing named path, relation, replay, productivity or budget
    ///   refusals, retaining completed list depth and visited instructions.
    /// - panics: none.
    /// - intension: a shared budget counts both graphs' Guard/Redirect visits;
    ///   each element transport independently receives the finite replay cap.
    ///
    /// # Errors
    /// Refusal with precise higher verdict and progress; Boundary for wrong
    /// constructor shape or incomplete/excess head evidence.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — three list lengths exercise the same rule; wrong
    ///   output, corrupt or missing traces, shape and exact budgets refuse.
    /// - witness: `path_universe::tests::recursive_transport_tests::negation_transport_computes`
    #[inline]
    pub fn replay(
        &self,
        arena: &mut TermArena,
        input: &Codata,
        evidence: TransportEvidence<'_>,
        budget: ReplayBudget,
    ) -> Result<Progress, Refusal>
    {
        let mut meter = Meter::new(budget);
        let endpoints = Interpretation::UniverseIdentity
            .path(arena, self.element, budget)
            .map_err(|error| meter.refuse(error.into()))?;
        let mut input = Cursor::new(input);
        let mut output = Cursor::new(evidence.output);
        let mut heads = evidence.heads.iter();
        loop {
            let source = input.next(arena, endpoints.source, &mut meter)?;
            let target = output.next(arena, endpoints.target, &mut meter)?;
            match (source, target) {
                | (Constructor::Nil, Constructor::Nil) => {
                    if heads.next().is_some() {
                        return Err(meter.refuse(HigherError::Boundary));
                    }
                    meter.progress.depth.0 = meter.progress.depth.0.saturating_add(1);
                    return Ok(meter.progress);
                },
                | (Constructor::Cons(value), Constructor::Cons(expected)) => {
                    let dialogue = heads
                        .next()
                        .ok_or_else(|| meter.refuse(HigherError::Boundary))?;
                    let expected = arena.computation_return(expected);
                    let verdict = path_universe::replay_transport(
                        arena,
                        path_universe::Transport {
                            path: self.element,
                            value,
                        },
                        expected,
                        EngineClaim::Convertible,
                        dialogue,
                        budget,
                    )
                    .map_err(|error| {
                        meter.refuse(RelationError::Typing(alloc::boxed::Box::new(error)).into())
                    })?;
                    if verdict != KernelVerdict::Convertible {
                        return Err(meter.refuse(HigherError::Replay(verdict)));
                    }
                    meter.progress.depth.0 = meter.progress.depth.0.saturating_add(1);
                },
                | _ => return Err(meter.refuse(HigherError::Boundary)),
            }
        }
    }
}
