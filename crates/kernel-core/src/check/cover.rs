//! The replay of a definition's cover derivations.
//!
//! A match lowers to a tree of cases, and the lowering records beside it the
//! derivation `{arms} ◁ Ξ` that states why the arms cover the scrutinee. The
//! kernel does not take that reason on trust. It replays each derivation
//! against the admitted environment and against the tree its root names:
//!
//! - every step names only steps minted before it, and every split holds one
//!   branch for each of its cases;
//! - a data split lists its family's constructors once each, in tag order, with
//!   their field counts, and then either no loop or every loop a case over the
//!   family owes, in the order it owes them;
//! - a data split meets a data case with one branch for each constructor and
//!   loop, each constructor's branch binding its fields, the case's index
//!   equations and the binders the checker generalised the case over, which it
//!   stands applied to, and each branch goes on with the branch's step;
//! - an absurd split meets a data case with no branch.
//!
//! The other splits are checked as steps. Their nodes are read where their
//! own formers check them, and the replay does not descend under them.
//!
//! The data case's own check reads the case's family from its scrutinee's
//! type, and the replay reads it from the step, so a case and its step agree
//! on the constructors each names.
//!
//! # References
//!
//! - `vault:01a1567c-2c32-7ed3-a102-45e54f702b4f` — anchor: Eremondi and
//!   Kammar's coverage semantics, § 5 — `var`, `split` and `compose` as the
//!   closure operations of a coverage.
//! - `vault:01a1567c-2c32-7ed3-a102-45dc5330206a` — anchor: coverage and
//!   unification, § coverage-evidence-form — the derivation replayed by the
//!   kernel step by step.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::CellIndex;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::cover::ArmCount;
use gandr_kernel_term::cover::Cases;
use gandr_kernel_term::cover::CoverRefusal;
use gandr_kernel_term::cover::Covered;
use gandr_kernel_term::cover::Loop;
use gandr_kernel_term::cover::Step;
use gandr_kernel_term::cover::StepId;

use super::former::signature;
use crate::env::Entries;
use crate::error::KernelError;
use crate::presented::Presentations;

/// Replay each of `covers` against the admitted environment and its tree.
///
/// # Specification
/// - requires: each root names a computation of `arena`.
/// - ensures: `Ok` exactly when every derivation is well formed, every data
///   split lists its family's constructors and owed loops, and every step meets
///   its own node of the tree, as the module states.
/// - fails: [`KernelError::CoverDisagrees`] naming the first step that does not
///   replay.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a derivation that follows its tree is admitted, and one
///   mutated in each rule is refused by that rule's name.
/// - witness: `tests::cover::a_derivation_that_follows_its_tree_is_admitted_5104`
/// - witness: `tests::cover::every_broken_derivation_is_refused_by_its_rule_5104`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(KernelError::CoverDisagrees(_))))]
pub(super) fn admit(
    arena: &TermArena,
    (entries, presentations): (&Entries, &Presentations),
    covers: &[Covered],
) -> Result<(), KernelError>
{
    for covered in covers {
        replay(arena, (entries, presentations), covered).map_err(KernelError::CoverDisagrees)?;
    }
    Ok(())
}

/// Replay one derivation against its tree.
///
/// # Specification
/// - requires: as [`admit`].
/// - ensures: as [`admit`], for one derivation.
/// - fails: the [`CoverRefusal`] of the first step that does not replay.
/// - panics: none.
///
/// # Termination
/// Each step is read once: a step's parts are minted before it, which the
/// check refuses otherwise, so the walk descends the derivation.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`admit`].
/// - witness: `tests::cover::every_broken_derivation_is_refused_by_its_rule_5104`
#[spec(ensures: |ret| ret.is_err() || covered.cover.steps().next().is_some())]
fn replay(
    arena: &TermArena,
    (entries, presentations): (&Entries, &Presentations),
    covered: &Covered,
) -> Result<(), CoverRefusal>
{
    let cover = &covered.cover;
    // The kernel holds no arm list, so a `var`'s arm is bounded by nothing
    // here: the arm a leaf runs is the tree's, which the replay follows.
    cover.check(ArmCount::from(usize::MAX), |family| {
        signature(entries, family).ok().map(|declared| {
            declared
                .constructors
                .iter()
                .map(|fields| FieldCount::from(fields.len()))
        })
    })?;
    let Some((root, _step)) = cover.steps().last()
    else {
        return Err(CoverRefusal::Empty);
    };
    // The walk pushes each step of a tree-shaped derivation once, so one
    // allocation of the step count holds the whole stack.
    let mut pending: Vec<(StepId, ComputationId)> = Vec::with_capacity(cover.steps().size_hint().0);
    pending.push((root, covered.root));
    let mut owed: Vec<Loop> = Vec::new();
    while let Some((id, at)) = pending.pop() {
        match *cover.step(id).ok_or(CoverRefusal::Dangling(id))? {
            // A leaf runs its arm, and a split the replay does not descend
            // under is checked as a step.
            Step::Var(_)
            | Step::Split {
                cases:
                    Cases::Boolean
                    | Cases::Integer(_)
                    | Cases::Tuple(_)
                    | Cases::Record(_)
                    | Cases::Sum(_)
                    | Cases::List
                    | Cases::Guard,
                ..
            } => {},
            Step::Compose(inner) => pending.push((inner, at)),
            Step::Split {
                cases:
                    Cases::Data {
                        family,
                        ref constructors,
                        ref loops,
                    },
                ref branches,
            } => {
                // A case over a sort with loops carries either no loop branch,
                // its loops then owed by the case's own check, or one branch
                // for each cell the sort owes, loops and cells above dimension
                // one alike, in the order it owes them.
                if !loops.is_empty() {
                    owed.clear();
                    for (words, cells) in presentations.looping(family) {
                        owed.extend(
                            (0 .. cells.cells().len())
                                .map(|cell| Loop::new(words, CellIndex::from(cell))),
                        );
                    }
                    if owed != *loops {
                        return Err(CoverRefusal::Loops(id));
                    }
                }
                // A case the checker generalised over later binders stands
                // applied to each, and each of its branches binds them after
                // its fields.
                let mut head = at;
                let mut generalised = 0_usize;
                while let Some(&Computation::Application(applied, _argument)) =
                    arena.computation(head)
                {
                    head = applied;
                    generalised = generalised.saturating_add(1);
                }
                let Some(&Computation::DataCase {
                    branches: ref held,
                    equations,
                    ..
                }) = arena.computation(head)
                else {
                    return Err(CoverRefusal::Tree(id));
                };
                if held.len() != branches.len() {
                    return Err(CoverRefusal::Tree(id));
                }
                // A constructor's branch binds its fields, which the check
                // read against the signature, then the case's equations, then
                // the binders it is generalised over; a loop's binds nothing.
                for (place, (&branch, &child)) in branches.iter().zip(held).enumerate() {
                    let binders = constructors.get(place).map_or(0, |&(_tag, fields)| {
                        usize::from(fields)
                            .saturating_add(usize::from(equations))
                            .saturating_add(generalised)
                    });
                    pending.push((
                        branch,
                        opened(arena, child, Bound(binders)).ok_or(CoverRefusal::Tree(id))?,
                    ));
                }
            },
            Step::Split {
                cases: Cases::Absurd,
                ..
            } => match arena.computation(at) {
                Some(&Computation::DataCase { ref branches, .. }) if branches.is_empty() => {},
                Some(_) | None => return Err(CoverRefusal::Tree(id)),
            },
        }
    }
    Ok(())
}

/// How many lambdas a branch binds before its body.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Bound(usize);

/// The body under `binders` lambdas of `branch`, or nothing when the branch
/// binds fewer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the computation `binders` lambdas below `branch`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a branch binding one lambda too few is refused as a tree
///   that is not the step's.
/// - witness: `tests::cover::every_broken_derivation_is_refused_by_its_rule_5104`
#[spec(ensures: |ret| binders.0 > 0 || ret == Some(branch))]
fn opened(
    arena: &TermArena,
    branch: ComputationId,
    binders: Bound,
) -> Option<ComputationId>
{
    let mut inner = branch;
    for _binder in 0 .. binders.0 {
        let &Computation::Lambda(body) = arena.computation(inner)?
        else {
            return None;
        };
        inner = body;
    }
    Some(inner)
}
