//! Contravariant fibre action and its checked square in the computed fragment.

use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueTypeId;

use super::Cell;
use super::Codata;
use super::HigherError;
use super::ObservationBudget;
use super::Prefix;
use super::relation;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::identity_recursion::Transport;

/// A square whose upper and right faces compute a path followed by its inverse.
///
/// The bottom and left faces are the source diagonal. The filler relates the
/// upper-then-right composite to the left-then-bottom composite.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Square
{
    /// The supplied `a -> b` identity.
    pub top: Cell,
    /// The computed `b -> a` symmetry.
    pub right: Cell,
    /// The `a -> a` diagonal.
    pub bottom: Cell,
    /// The `a -> a` diagonal.
    pub left: Cell,
    /// Observed coherence between the two boundary composites.
    pub filler: Prefix,
}

/// Derive symmetry by transport in the computed identity fibre.
///
/// # Specification
/// - ensures: checks `p : Rel(code, a, b)` and higher identity from reindexed
///   diagonal evidence to its proof; transports the source diagonal in the
///   constant inverse fibre; checks all square faces and their higher filler.
/// - provides: symmetry for native computed first-order fibres. The equality of
///   diagonal and inverse fibre types is checked before the action; no reversed
///   path or inverse evidence is supplied by the caller.
/// - fails: relation or higher observation refusals, `Boundary` if the fibre is
///   not structurally constant, or `NeutralTransport` if the action is stuck.
/// - panics: none.
///
/// # Errors
/// `HigherError::Relation`, `Boundary`, `NeutralTransport`, or an `observe`
/// error.
///
/// # Adequacy
/// - hypothesis: L3 — a Bool path with distinct neutral Unit payloads computes
///   an inverse, with all four boundaries and the higher filler checked;
///   corrupt higher evidence cannot manufacture that inverse.
/// - witness: `higher_field::tests::symmetry_on_a_boolean_square_computes`
#[inline]
pub fn symmetry(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    path: Cell,
    higher: &Codata,
    budget: ObservationBudget,
) -> Result<Square, HigherError>
{
    let relation = relation(arena, path.code)?;
    let forward = path.check(arena, context)?;
    let diagonal = relation.reflexivity(arena, context, path.left)?;
    let evidence = diagonal.native_evidence()?;
    let diagonal = Cell {
        left: path.left,
        right: path.left,
        evidence,
        ..path
    };
    let source = relation.fiber(arena, context, path.left, path.left)?;
    let source = source.native(arena)?;
    let target = relation.fiber(arena, context, path.right, path.left)?;
    let target = target.native(arena)?;
    if convertible_value_types(arena, source, target) != Convertibility::Convertible {
        return Err(HigherError::Boundary);
    }
    // In this fragment the fibre family has a constant native reduct. Its
    // action is ordinary transport in the next identity relation, not a new
    // inverse constructor or a guessed inhabitant of the target.
    let observed = higher.observe(arena, context, Cell { evidence, ..path }, path, budget)?;
    let identity = observed.head.check(arena, context)?;
    let higher_relation = super::relation(arena, observed.head.code)?;
    let result = higher_relation.transport(arena, context, identity, target, evidence)?;
    let evidence = match result {
        | Transport::Return(value) => value,
        | Transport::Neutral { .. } => return Err(HigherError::NeutralTransport),
    };
    let inverse = Cell {
        left: path.right,
        right: path.left,
        evidence,
        ..path
    };
    let backward = inverse.check(arena, context)?;
    let left = diagonal.check(arena, context)?;
    let bottom = diagonal.check(arena, context)?;
    let upper = relation.compose(arena, context, forward, backward)?;
    let lower = relation.compose(arena, context, left, bottom)?;
    let upper = upper.native_evidence()?;
    let lower = lower.native_evidence()?;
    let filler = higher.observe(
        arena,
        context,
        Cell {
            evidence: upper,
            ..diagonal
        },
        Cell {
            evidence: lower,
            ..diagonal
        },
        budget,
    )?;
    Ok(Square {
        top: path,
        right: inverse,
        bottom: diagonal,
        left: diagonal,
        filler,
    })
}
