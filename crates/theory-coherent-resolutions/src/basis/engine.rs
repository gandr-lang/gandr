//! The engine of the basis: a step fired along its cell or against it, the
//! positions that a move reads, and the replay of a homotopy move by move.
//!
//! A step against its cell matches the right-hand side and puts the
//! left-hand side in its place. The basis admits only cells whose two sides
//! hold each metavariable once, so the step back is determined, and a
//! forward firing checks it. Two forward steps commute when one fires in a
//! metavariable of the other's left-hand side, or when they stand apart. The
//! residual of the inner step then follows the metavariable to the other
//! side.

use alloc::vec::Vec;

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use quenchant_shape::shape::Maybe;

use super::BasisFault;
use super::Move;
use super::PathStep;
use super::RewritePath;
use super::Sense;
use crate::boundary::MovePlace;
use crate::boundary::StepPlace;
use crate::rewrite::CellApp;
use crate::rewrite::rewrite_at;
use crate::tracelet::Tracelet;

/// The step of `app` along its cell.
///
/// # Specification
/// trivial.
pub(super) fn forward<A>(app: CellApp<A>) -> PathStep<A>
where
    A: CellAlphabet,
{
    PathStep {
        app,
        sense: Sense::Forward,
    }
}

/// `cell` with both sides renamed apart from `term`, so that a binding of
/// its metavariables never names a metavariable of `term`.
///
/// # Specification
/// trivial.
fn renamed<A>(
    cell: &Cell<A>,
    term: &A::Cmd,
) -> Cell<A>
where
    A: CellAlphabet,
{
    let (lhs, rhs) = A::rename_apart((term, term), (cell.lhs(), cell.rhs()));
    Cell::new(lhs, rhs, cell.orient(), cell.provenance())
}

/// The term that `step` reaches from `term`, or nothing where it does not
/// fire. The cell fires renamed apart from `term`.
///
/// # Specification
/// trivial.
pub(super) fn fire<A>(
    store: &CellStore<A>,
    term: &A::Cmd,
    step: &PathStep<A>,
) -> Option<A::Cmd>
where
    A: CellAlphabet,
{
    let Maybe::Present(cell) = store.get(step.app.cell)
    else {
        return None;
    };
    let cell = renamed(cell, term);
    match step.sense {
        Sense::Forward => match rewrite_at(&cell, term, &step.app.at) {
            Maybe::Present(next) => Some(next),
            Maybe::Absent(_) => None,
        },
        Sense::Backward => unfire(&cell, term, &step.app.at),
    }
}

/// The term from which `cell`, fired at `at`, reaches `term`, or nothing
/// where its right-hand side does not match there.
///
/// # Specification
/// trivial.
fn unfire<A>(
    cell: &Cell<A>,
    term: &A::Cmd,
    at: &A::Pos,
) -> Option<A::Cmd>
where
    A: CellAlphabet,
{
    let Maybe::Present(redex) = A::subterm_cmd_at(term, at)
    else {
        return None;
    };
    let mut subst = A::Subst::default();
    if !bool::from(A::match_cmd(cell.rhs(), &redex, &mut subst)) {
        return None;
    }
    let before = A::splice_cmd_at(term, at, A::apply_subst(&subst, cell.lhs())).ok()?;
    match rewrite_at(cell, &before, at) {
        Maybe::Present(ref after) if after == term => Some(before),
        Maybe::Present(_) | Maybe::Absent(_) => None,
    }
}

/// The term that `steps` reach from `start`, or nothing where a step does
/// not fire.
///
/// # Specification
/// trivial.
pub(super) fn reach<A>(
    store: &CellStore<A>,
    start: &A::Cmd,
    steps: &[PathStep<A>],
) -> Option<A::Cmd>
where
    A: CellAlphabet,
{
    let mut term = start.clone();
    for step in steps {
        term = fire(store, &term, step)?;
    }
    Some(term)
}

/// The steps of `word` reversed, each one against its sense.
///
/// # Specification
/// trivial.
pub(super) fn word_inverse<A>(word: &[PathStep<A>]) -> impl Iterator<Item = PathStep<A>> + '_
where
    A: CellAlphabet,
{
    word.iter().rev().map(|step| PathStep {
        app: step.app.clone(),
        sense: step.sense.flipped(),
    })
}

/// The moves of `moves` reversed, each one inverted.
///
/// # Specification
/// trivial.
pub(super) fn inverted<A>(moves: &[Move<A>]) -> Vec<Move<A>>
where
    A: CellAlphabet,
{
    moves.iter().rev().map(Move::inverse).collect()
}

/// The moves of `moves`, each one past `offset` more steps.
///
/// # Specification
/// trivial.
pub(super) fn shifted<A>(
    moves: &[Move<A>],
    offset: StepPlace,
) -> Vec<Move<A>>
where
    A: CellAlphabet,
{
    moves.iter().map(|each| each.shifted(offset)).collect()
}

/// The position `inner`, read below `outer`.
///
/// # Specification
/// trivial.
pub(super) fn below<A>(
    outer: &A::Pos,
    inner: &A::Pos,
) -> A::Pos
where
    A: CellAlphabet,
{
    joined::<A>(&[A::position_steps(outer), A::position_steps(inner)])
}

/// The position whose steps are the steps of `parts`, in order.
///
/// # Specification
/// trivial.
fn joined<A>(parts: &[&[PositionStep]]) -> A::Pos
where
    A: CellAlphabet,
{
    let mut steps = Vec::with_capacity(parts.iter().map(|part| part.len()).sum());
    for part in parts {
        steps.extend_from_slice(part);
    }
    A::position_at_path(&steps)
}

/// The metavariable that `term` is, or nothing where it is no lone
/// metavariable.
///
/// # Specification
/// trivial.
pub(super) fn lone_variable<A>(term: &A::Cmd) -> Option<A::Var>
where
    A: CellAlphabet,
{
    if usize::from(A::cmd_size(term)) != 1 {
        return None;
    }
    let mut variables = A::metavariables(term);
    if variables.len() == 1 {
        variables.pop()
    }
    else {
        None
    }
}

/// The metavariable of `pattern` on the way along `rest`, with the steps of
/// `rest` below it, or nothing where `rest` meets no metavariable.
///
/// # Specification
/// trivial.
fn variable_place<'rest, A>(
    pattern: &A::Cmd,
    rest: &'rest [PositionStep],
) -> Option<(A::Var, &'rest [PositionStep])>
where
    A: CellAlphabet,
{
    for split in 0 ..= rest.len() {
        let (head, tail) = rest.split_at_checked(split)?;
        let Maybe::Present(sub) = A::subterm_cmd_at(pattern, &A::position_at_path(head))
        else {
            return None;
        };
        if let Some(variable) = lone_variable::<A>(&sub) {
            return Some((variable, tail));
        }
    }
    None
}

/// The position of the metavariable `variable` in `pattern`, or nothing
/// where `pattern` does not hold it.
///
/// # Specification
/// trivial.
fn variable_position<A>(
    pattern: &A::Cmd,
    variable: &A::Var,
) -> Option<A::Pos>
where
    A: CellAlphabet,
{
    A::command_positions(pattern).into_iter().find(|at| {
        matches!(A::subterm_cmd_at(pattern, at), Maybe::Present(ref sub)
            if lone_variable::<A>(sub).as_ref() == Some(variable))
    })
}

/// The position below `base` that follows `rest` from the side `from` of a
/// cell to the side `to`, through the metavariable that `rest` meets, or
/// nothing where `rest` meets none.
///
/// # Specification
/// trivial.
fn carried<A>(
    from: &A::Cmd,
    to: &A::Cmd,
    base: &A::Pos,
    rest: &[PositionStep],
) -> Option<A::Pos>
where
    A: CellAlphabet,
{
    let (variable, tail) = variable_place::<A>(from, rest)?;
    let place = variable_position::<A>(to, &variable)?;
    Some(joined::<A>(&[
        A::position_steps(base),
        A::position_steps(&place),
        tail,
    ]))
}

/// How two forward steps on one term meet.
#[derive(Clone, Debug)]
pub(super) enum Meeting<A>
where
    A: CellAlphabet,
{
    /// The steps commute: the first step after the second, and the second
    /// after the first.
    Apart
    {
        /// The first step, after the second fired.
        first: CellApp<A>,
        /// The second step, after the first fired.
        second: CellApp<A>,
    },
    /// The left-hand sides overlap.
    Overlap
    {
        /// The step at the higher position, or the first step at one position.
        outer: CellApp<A>,
        /// The other step.
        inner: CellApp<A>,
        /// The position of the inner step below the outer one.
        seam: A::Pos,
    },
}

/// How the forward steps `first` and `second` on one term meet, or nothing
/// where a step names no cell of `store`.
///
/// # Specification
/// trivial.
pub(super) fn meeting<A>(
    store: &CellStore<A>,
    first: &CellApp<A>,
    second: &CellApp<A>,
) -> Option<Meeting<A>>
where
    A: CellAlphabet,
{
    let Maybe::Present(first_cell) = store.get(first.cell)
    else {
        return None;
    };
    let Maybe::Present(second_cell) = store.get(second.cell)
    else {
        return None;
    };
    Some(match A::position_order(&first.at, &second.at) {
        PositionOrder::Incomparable => Meeting::Apart {
            first: first.clone(),
            second: second.clone(),
        },
        PositionOrder::Same => Meeting::Overlap {
            outer: first.clone(),
            inner: second.clone(),
            seam: A::root_position(),
        },
        PositionOrder::Encloses => {
            let rest = A::position_steps(&second.at).strip_prefix(A::position_steps(&first.at))?;
            carried::<A>(first_cell.lhs(), first_cell.rhs(), &first.at, rest).map_or_else(
                || Meeting::Overlap {
                    outer: first.clone(),
                    inner: second.clone(),
                    seam: A::position_at_path(rest),
                },
                |at| Meeting::Apart {
                    first: first.clone(),
                    second: CellApp {
                        at,
                        ..second.clone()
                    },
                },
            )
        },
        PositionOrder::EnclosedBy => {
            let rest = A::position_steps(&first.at).strip_prefix(A::position_steps(&second.at))?;
            carried::<A>(second_cell.lhs(), second_cell.rhs(), &second.at, rest).map_or_else(
                || Meeting::Overlap {
                    outer: second.clone(),
                    inner: first.clone(),
                    seam: A::position_at_path(rest),
                },
                |at| Meeting::Apart {
                    first: CellApp {
                        at,
                        ..first.clone()
                    },
                    second: second.clone(),
                },
            )
        },
    })
}

/// The forward steps `first` and then `second` from `term`, swapped: the
/// second before the first, then the first after it. Nothing where the
/// steps do not commute.
///
/// # Specification
/// trivial.
pub(super) fn exchange<A>(
    store: &CellStore<A>,
    term: &A::Cmd,
    first: &CellApp<A>,
    second: &CellApp<A>,
) -> Option<[CellApp<A>; 2]>
where
    A: CellAlphabet,
{
    let Maybe::Present(first_cell) = store.get(first.cell)
    else {
        return None;
    };
    let Maybe::Present(second_cell) = store.get(second.cell)
    else {
        return None;
    };
    let swapped = match A::position_order(&first.at, &second.at) {
        PositionOrder::Incomparable => [second.clone(), first.clone()],
        PositionOrder::Same => return None,
        PositionOrder::Encloses => {
            let rest = A::position_steps(&second.at).strip_prefix(A::position_steps(&first.at))?;
            let at = carried::<A>(first_cell.rhs(), first_cell.lhs(), &first.at, rest)?;
            [
                CellApp {
                    at,
                    ..second.clone()
                },
                first.clone(),
            ]
        },
        PositionOrder::EnclosedBy => {
            let rest = A::position_steps(&first.at).strip_prefix(A::position_steps(&second.at))?;
            let at = carried::<A>(second_cell.lhs(), second_cell.rhs(), &second.at, rest)?;
            [second.clone(), CellApp {
                at,
                ..first.clone()
            }]
        },
    };
    let one = reach(store, term, &[
        forward(first.clone()),
        forward(second.clone()),
    ])?;
    let [ref before, ref after] = swapped;
    let other = reach(store, term, &[
        forward(before.clone()),
        forward(after.clone()),
    ])?;
    (one == other).then_some(swapped)
}

/// The path that `moves` reach from `source`. Each move is checked against
/// the path it reads, and the term at the offset of each move is pushed onto
/// `trace`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// - [`BasisFault::Unfired`]: a step of the source does not fire.
/// - [`BasisFault::Inapplicable`]: a move does not apply to the path it reads.
pub(super) fn run<A>(
    store: &CellStore<A>,
    certificates: &[Tracelet<A>],
    source: &RewritePath<A>,
    moves: &[Move<A>],
    trace: &mut Vec<A::Cmd>,
) -> Result<Vec<PathStep<A>>, BasisFault>
where
    A: CellAlphabet,
{
    let start = &source.start;
    if reach(store, start, &source.steps).is_none() {
        return Err(BasisFault::Unfired);
    }
    let mut steps = source.steps.clone();
    let mut factor = Vec::new();
    for (place, each) in moves.iter().enumerate() {
        let refused = BasisFault::Inapplicable(MovePlace::from(place));
        let offset = usize::from(each.offset());
        let term = steps
            .get(.. offset)
            .and_then(|head| reach(store, start, head))
            .ok_or(refused)?;
        factor.clear();
        match *each {
            Move::Confluence {
                certificate,
                sense,
                ref at,
                ..
            } => {
                let tracelet = certificates.get(usize::from(certificate)).ok_or(refused)?;
                let (from, to) = match sense {
                    Sense::Forward => (&tracelet.path_a, &tracelet.path_b),
                    Sense::Backward => (&tracelet.path_b, &tracelet.path_a),
                };
                let moved = |app: &CellApp<A>| {
                    forward(CellApp {
                        at: below::<A>(at, &app.at),
                        ..app.clone()
                    })
                };
                factor.extend(from.iter().map(moved));
                let end = offset.saturating_add(factor.len());
                if steps.get(offset .. end) != Some(factor.as_slice()) {
                    return Err(refused);
                }
                let Maybe::Present(redex) = A::subterm_cmd_at(&term, at)
                else {
                    return Err(refused);
                };
                if !bool::from(A::match_cmd(
                    &tracelet.overlap.peak,
                    &redex,
                    &mut A::Subst::default(),
                )) {
                    return Err(refused);
                }
                drop(steps.splice(offset .. end, to.iter().map(moved)));
            },
            Move::Exchange { .. } => {
                let next = offset.saturating_add(1);
                let (Some(first), Some(second)) = (steps.get(offset), steps.get(next))
                else {
                    return Err(refused);
                };
                if first.sense != Sense::Forward || second.sense != Sense::Forward {
                    return Err(refused);
                }
                let swapped = exchange(store, &term, &first.app, &second.app).ok_or(refused)?;
                for (slot, app) in steps.iter_mut().skip(offset).zip(swapped) {
                    slot.app = app;
                }
            },
            Move::Expand { ref word, .. } => {
                if offset > steps.len() || reach(store, &term, word).is_none() {
                    return Err(refused);
                }
                drop(steps.splice(
                    offset .. offset,
                    word.iter().cloned().chain(word_inverse(word)),
                ));
            },
            Move::Contract { ref word, .. } => {
                factor.extend(word.iter().cloned());
                factor.extend(word_inverse(word));
                let end = offset.saturating_add(factor.len());
                if steps.get(offset .. end) != Some(factor.as_slice()) {
                    return Err(refused);
                }
                drop(steps.drain(offset .. end));
            },
        }
        trace.push(term);
    }
    Ok(steps)
}
