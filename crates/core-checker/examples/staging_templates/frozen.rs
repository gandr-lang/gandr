//! Replay of the captured pre-interning equation occurrences, selected with
//! `GANDR_INPUT=frozen`.
//!
//! The capture recorded every classifier, term and selected equation
//! occurrence of 15 paying families with append-only coordinates. Loading
//! remaps them through the current canonical allocator before any timing,
//! preserving occurrence multiplicity and exact equation content.

#[path = "frozen_data.rs"]
mod data;

use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Child;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Step;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;
use quenchant_shape::shape::Maybe;

use crate::Case;

quenchant_shape::reason_enum! {
    /// Why a family has no captured occurrences.
    pub mod uncaptured {
        /// The reason nothing is loaded.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The capture recorded no family under this case and index.
            Uncaptured,
        }
    }
}

/// Resolve a captured classifier coordinate to its remapped identity.
///
/// # Specification
/// - ensures: returns the identity the captured coordinate was remapped to.
/// - fails: `UnknownType` for a coordinate not yet remapped.
/// - panics: none.
///
/// # Errors
/// Returns `UnknownType`.
fn classifier(
    remapped: &[TypeId],
    id: TypeId,
) -> Result<TypeId, StageError>
{
    remapped
        .get(id.0)
        .copied()
        .ok_or(StageError::UnknownType(id))
}

/// Resolve a captured term coordinate to its remapped identity.
///
/// # Specification
/// - ensures: returns the identity the captured coordinate was remapped to.
/// - fails: `UnknownTerm` for a coordinate not yet remapped.
/// - panics: none.
///
/// # Errors
/// Returns `UnknownTerm`.
fn term(
    remapped: &[TermId],
    id: TermId,
) -> Result<TermId, StageError>
{
    remapped
        .get(id.0)
        .copied()
        .ok_or(StageError::UnknownTerm(id))
}

/// Import one family's captured coordinates through the current allocator.
///
/// # Specification
/// - ensures: every captured classifier and term is interned in capture order;
///   every occurrence keeps its multiplicity and exact content.
/// - provides: `uncaptured::Absent::Uncaptured` for an unrecorded family.
/// - fails: a forward or absent captured edge.
/// - panics: none.
///
/// # Errors
/// Returns the originating staging refusal.
pub(super) fn load(
    case: Case,
    index: Natural,
) -> Result<Maybe<(Arena, Vec<Step>), uncaptured::Absent>, StageError>
{
    let (types, terms, steps) = match data::data(case, index) {
        | Maybe::Present(captured) => captured,
        | Maybe::Absent(reason) => return Ok(Maybe::Absent(reason)),
    };
    let mut arena = Arena::default();
    let mut classifiers = Vec::with_capacity(types.len());
    for ty in types {
        let ty = match ty {
            | Type::Arrow(a, b) => {
                Type::Arrow(classifier(&classifiers, a)?, classifier(&classifiers, b)?)
            },
            | Type::Lift(inner) => Type::Lift(classifier(&classifiers, inner)?),
            | leaf => leaf,
        };
        classifiers.push(arena.alloc_type(ty)?);
    }
    let mut coordinates = Vec::with_capacity(terms.len());
    for captured in terms {
        let captured = match captured {
            | Term::Code(ty) => Term::Code(classifier(&classifiers, ty)?),
            | Term::Lambda(ty, body) => Term::Lambda(classifier(&classifiers, ty)?, body),
            | Term::Eliminate(body, ty) => Term::Eliminate(body, classifier(&classifiers, ty)?),
            | other => other,
        };
        let mut children = [Child::Vacant; 3];
        for (child, output) in captured.children().into_iter().zip(&mut children) {
            if let Child::Present(child) = child {
                *output = Child::Present(term(&coordinates, child)?);
            }
        }
        coordinates.push(arena.alloc(captured.rebuild(children)?)?);
    }
    let steps = steps
        .into_iter()
        .map(|step| {
            Ok(Step {
                source: term(&coordinates, step.source)?,
                target: term(&coordinates, step.target)?,
                rule: step.rule,
            })
        })
        .collect::<Result<Vec<_>, StageError>>()?;
    Ok(Maybe::Present((arena, steps)))
}
