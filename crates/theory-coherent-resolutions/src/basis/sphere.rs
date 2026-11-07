//! The boundary of the 4-cell of a critical triple, built from the
//! confluences and the normal forms, and the definition of a confluence that
//! occurs once in it.
//!
//! The normal form of a term is the path that [`apply_once`] takes, outermost
//! first. For a step `s` on a term `u`, the homotopy `ρ(s)` runs from `s`
//! followed by the normal form of its target to the normal form of `u`. It is
//! empty when `s` is the first step of that normal form. Otherwise `s` and that
//! first step make a branching, and `ρ(s)` resolves it. A branching of two
//! steps that commute resolves through an exchange, and a branching whose
//! left-hand sides overlap resolves through its confluence in context. Each
//! side is then normalised again, at a term below `u`. A worklist holds the
//! branchings still to resolve, each with the shift and the sense that its
//! place gives its moves. The rewriting terminates, so the worklist empties,
//! and the normalization budget bounds the depth of nested branchings.
//!
//! The boundary of a triple `(f, g, h)` resolves its three branchings in
//! turn: `(f, g)`, then `(g, h)`, then `(h, f)`. It is a loop of homotopies
//! from `f` followed by a normal form back to the same path. This is the
//! construction of the coherent presentation of a convergent presentation
//! through a normalisation strategy (Ara and others, Theorem 7.3.5, and the
//! 4-cells of § 7.5.6).

use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use quenchant_shape::shape::Maybe;

use super::Homotopy;
use super::Move;
use super::PathStep;
use super::RewritePath;
use super::Sense;
use super::engine::Meeting;
use super::engine::below;
use super::engine::fire;
use super::engine::forward;
use super::engine::inverted;
use super::engine::meeting;
use super::engine::shifted;
use super::engine::word_inverse;
use crate::boundary::CertificateIndex;
use crate::boundary::MovePlace;
use crate::boundary::NormalizationBudget;
use crate::boundary::StepPlace;
use crate::overlap::OverlapKind;
use crate::rewrite::CellApp;
use crate::rewrite::apply_once;
use crate::tracelet::Tracelet;
use crate::triple::CriticalTriple;

/// Why the boundary of a triple is not built.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Unbuilt
{
    /// A normal form or the depth of nested branchings passes the budget.
    Exhausted,
    /// No certificate joins a branching that the boundary resolves.
    Unjoined,
    /// A step that the construction takes does not fire.
    Unfired,
}

/// The construction of the boundaries over one store and its certificates.
#[derive(Clone, Copy, Debug)]
pub(super) struct Builder<'basis, A>
where
    A: CellAlphabet,
{
    /// The cells.
    store: &'basis CellStore<A>,
    /// The confluences.
    certificates: &'basis [Tracelet<A>],
    /// The bound on each normal form and on the depth of nested branchings.
    budget: NormalizationBudget,
}

/// The place one step further.
///
/// # Specification
/// trivial.
fn one() -> StepPlace
{
    StepPlace::from(1_usize)
}

/// The shift and the sense that the place of a task gives its moves.
#[derive(Clone, Copy, Debug)]
struct Frame
{
    /// The steps before the path that the task reads.
    shift: StepPlace,
    /// [`Sense::Backward`] when the task's moves run inverted.
    sense: Sense,
}

impl Frame
{
    /// The frame of the root: no shift, forward.
    ///
    /// # Specification
    /// trivial.
    fn root() -> Self
    {
        Self {
            shift: StepPlace::default(),
            sense: Sense::Forward,
        }
    }

    /// The frame `by` more steps further.
    ///
    /// # Specification
    /// trivial.
    fn further(
        self,
        by: StepPlace,
    ) -> Self
    {
        Self {
            shift: StepPlace::from(usize::from(self.shift).saturating_add(usize::from(by))),
            sense: self.sense,
        }
    }

    /// The frame with its sense flipped.
    ///
    /// # Specification
    /// trivial.
    const fn flipped(self) -> Self
    {
        Self {
            shift: self.shift,
            sense: self.sense.flipped(),
        }
    }

    /// `each` in this frame: shifted, then inverted when the frame runs
    /// backward. A shift and an inversion commute.
    ///
    /// # Specification
    /// trivial.
    fn placed<A>(
        self,
        each: &Move<A>,
    ) -> Move<A>
    where
        A: CellAlphabet,
    {
        let moved = each.shifted(self.shift);
        match self.sense {
            Sense::Forward => moved,
            Sense::Backward => moved.inverse(),
        }
    }

    /// Put `pieces`, pushed in the order of a forward frame, in the order
    /// that the worklist pops them: the last piece first when the frame runs
    /// forward, as pushed when it runs backward.
    ///
    /// # Specification
    /// trivial.
    fn order<T>(
        self,
        pieces: &mut [T],
    )
    {
        if self.sense == Sense::Forward {
            pieces.reverse();
        }
    }
}

/// A piece of a boundary still to build.
#[derive(Clone, Debug)]
enum Task<A>
where
    A: CellAlphabet,
{
    /// A move, already in its frame.
    Emit(Move<A>),
    /// The homotopy `ρ(step)` on `term`.
    Normalising
    {
        /// The step.
        step: CellApp<A>,
        /// The term that it fires on.
        term: A::Cmd,
        /// The depth of nested branchings left.
        depth: NormalizationBudget,
        /// The place of the task.
        frame: Frame,
    },
    /// The homotopy `ρ` of each step of `path` from `start`, whiskered.
    NormalisingPath
    {
        /// The steps.
        path: Vec<CellApp<A>>,
        /// The term that the first step fires on.
        start: A::Cmd,
        /// The depth of nested branchings left.
        depth: NormalizationBudget,
        /// The place of the task.
        frame: Frame,
    },
    /// The branching of `first` and `second` on `term`.
    Branch
    {
        /// The step on the source side.
        first: CellApp<A>,
        /// The step on the target side.
        second: CellApp<A>,
        /// The term that both fire on.
        term: A::Cmd,
        /// The depth of nested branchings left.
        depth: NormalizationBudget,
        /// The place of the task.
        frame: Frame,
    },
}

impl<'basis, A> Builder<'basis, A>
where
    A: CellAlphabet,
{
    /// The construction over `store` and `certificates`, within `budget`.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn new(
        store: &'basis CellStore<A>,
        certificates: &'basis [Tracelet<A>],
        budget: NormalizationBudget,
    ) -> Self
    {
        Self {
            store,
            certificates,
            budget,
        }
    }
}

impl<A> Builder<'_, A>
where
    A: CellAlphabet,
{
    /// The term that `app` reaches from `term` along its cell.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Unbuilt::Unfired`]: the step does not fire.
    fn fire(
        &self,
        term: &A::Cmd,
        app: &CellApp<A>,
    ) -> Result<A::Cmd, Unbuilt>
    {
        fire(self.store, term, &forward(app.clone())).ok_or(Unbuilt::Unfired)
    }

    /// Push the steps of the normal form of `term` onto `steps`: the step
    /// that [`apply_once`] chooses, outermost first, fired renamed apart.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Unbuilt::Exhausted`]: the normal form passes the budget.
    /// - [`Unbuilt::Unfired`]: a chosen step does not fire.
    fn normal_path(
        &self,
        term: &A::Cmd,
        steps: &mut Vec<PathStep<A>>,
    ) -> Result<(), Unbuilt>
    {
        let mut term = term.clone();
        for _ in 0 ..= usize::from(self.budget) {
            let Maybe::Present(rewrite) = apply_once(self.store, &term)
            else {
                return Ok(());
            };
            term = self.fire(&term, &rewrite.step)?;
            steps.push(forward(rewrite.step));
        }
        Err(Unbuilt::Exhausted)
    }

    /// Push the homotopy `ρ(step)` on `term` onto `tasks`: from `step`
    /// followed by the normal form of its target to the normal form of
    /// `term`. It is empty when `step` is the first step of that normal form,
    /// and otherwise the branching of the two.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Unbuilt::Unfired`]: `term` takes no step.
    fn normalising(
        &self,
        step: CellApp<A>,
        term: A::Cmd,
        depth: NormalizationBudget,
        frame: Frame,
        tasks: &mut Vec<Task<A>>,
    ) -> Result<(), Unbuilt>
    {
        let Maybe::Present(first) = apply_once(self.store, &term)
        else {
            return Err(Unbuilt::Unfired);
        };
        if first.step != step {
            tasks.push(Task::Branch {
                first: step,
                second: first.step,
                term,
                depth,
                frame,
            });
        }
        Ok(())
    }

    /// Push the homotopy `ρ` of each step of `path` from `start` onto
    /// `tasks`, whiskered by the steps before it: from `path` followed by the
    /// normal form of its end to the normal form of `start`. The last step
    /// comes first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Unbuilt::Unfired`]: a step of `path` does not fire.
    fn normalising_path(
        &self,
        path: &[CellApp<A>],
        start: &A::Cmd,
        depth: NormalizationBudget,
        frame: Frame,
        tasks: &mut Vec<Task<A>>,
    ) -> Result<(), Unbuilt>
    {
        let mark = tasks.len();
        let mut term = start.clone();
        for (place, app) in path.iter().enumerate() {
            let next = self.fire(&term, app)?;
            tasks.push(Task::Normalising {
                step: app.clone(),
                term,
                depth,
                frame: frame.further(StepPlace::from(place)),
            });
            term = next;
        }
        // The pieces stand first step first: the reverse of the order of a
        // forward frame, which puts the last step first.
        if let Some(pieces) = tasks.get_mut(mark ..) {
            frame.flipped().order(pieces);
        }
        Ok(())
    }

    /// Push the homotopy that resolves the branching of the steps `first`
    /// and `second` on `term` onto `tasks`: from `first` followed by a normal
    /// form to `second` followed by a normal form.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Unbuilt::Exhausted`]: the depth of nested branchings passes the
    ///   budget.
    /// - [`Unbuilt::Unjoined`]: no certificate joins an overlap.
    /// - [`Unbuilt::Unfired`]: a step does not fire.
    fn branch(
        &self,
        first: &CellApp<A>,
        second: &CellApp<A>,
        term: &A::Cmd,
        depth: NormalizationBudget,
        frame: Frame,
        tasks: &mut Vec<Task<A>>,
    ) -> Result<(), Unbuilt>
    {
        let depth = NormalizationBudget::from(
            usize::from(depth)
                .checked_sub(1)
                .ok_or(Unbuilt::Exhausted)?,
        );
        let after_first = self.fire(term, first)?;
        let after_second = self.fire(term, second)?;
        let deeper = frame.further(one());
        let mark = tasks.len();
        match meeting(self.store, first, second).ok_or(Unbuilt::Unfired)? {
            Meeting::Apart {
                first: first_after,
                second: second_after,
            } => {
                tasks.push(Task::Normalising {
                    step: second_after,
                    term: after_first,
                    depth,
                    frame: deeper.flipped(),
                });
                tasks.push(Task::Emit(frame.placed(&Move::Exchange {
                    offset: StepPlace::default(),
                })));
                tasks.push(Task::Normalising {
                    step: first_after,
                    term: after_second,
                    depth,
                    frame: deeper,
                });
            },
            Meeting::Overlap { outer, inner, seam } => {
                let (certificate, tracelet) = self.joining(&outer, &inner, &seam, term)?;
                let moved = |app: &CellApp<A>| CellApp {
                    cell: app.cell,
                    at: below::<A>(&outer.at, &app.at),
                };
                let (Some(a_first), Some(b_first)) =
                    (tracelet.path_a.first(), tracelet.path_b.first())
                else {
                    return Err(Unbuilt::Unjoined);
                };
                let (a_first, b_first) = (moved(a_first), moved(b_first));
                let (own, other, sense, own_first, other_first) = if a_first == *first {
                    (
                        &tracelet.path_a,
                        &tracelet.path_b,
                        Sense::Forward,
                        a_first,
                        b_first,
                    )
                }
                else {
                    (
                        &tracelet.path_b,
                        &tracelet.path_a,
                        Sense::Backward,
                        b_first,
                        a_first,
                    )
                };
                if own_first != *first || other_first != *second {
                    return Err(Unbuilt::Unjoined);
                }
                tasks.push(Task::NormalisingPath {
                    path: own.iter().skip(1).map(moved).collect(),
                    start: after_first,
                    depth,
                    frame: deeper.flipped(),
                });
                tasks.push(Task::Emit(frame.placed(&Move::Confluence {
                    certificate,
                    sense,
                    offset: StepPlace::default(),
                    at: outer.at.clone(),
                })));
                tasks.push(Task::NormalisingPath {
                    path: other.iter().skip(1).map(moved).collect(),
                    start: after_second,
                    depth,
                    frame: deeper,
                });
            },
        }
        if let Some(pieces) = tasks.get_mut(mark ..) {
            frame.order(pieces);
        }
        Ok(())
    }

    /// The certificate that joins the overlap of `outer` and `inner` at
    /// `seam`, where `term` holds an instance of its peak at the position of
    /// `outer`. A pair at one position may stand in either order.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Unbuilt::Unfired`]: the position of `outer` addresses no command.
    /// - [`Unbuilt::Unjoined`]: no certificate joins the overlap.
    fn joining(
        &self,
        outer: &CellApp<A>,
        inner: &CellApp<A>,
        seam: &A::Pos,
        term: &A::Cmd,
    ) -> Result<(CertificateIndex, &Tracelet<A>), Unbuilt>
    {
        let Maybe::Present(redex) = A::subterm_cmd_at(term, &outer.at)
        else {
            return Err(Unbuilt::Unfired);
        };
        let root = A::root_position();
        self.certificates
            .iter()
            .enumerate()
            .find(|&(_, tracelet)| {
                let overlap = &tracelet.overlap;
                let pair = (overlap.left, overlap.right);
                let oriented = pair == (outer.cell, inner.cell) && overlap.seam == *seam;
                let mirrored =
                    *seam == root && pair == (inner.cell, outer.cell) && overlap.seam == root;
                overlap.kind == OverlapKind::Confluence
                    && (oriented || mirrored)
                    && bool::from(A::match_cmd(
                        &overlap.peak,
                        &redex,
                        &mut A::Subst::default(),
                    ))
            })
            .map(|(place, tracelet)| (CertificateIndex::from(place), tracelet))
            .ok_or(Unbuilt::Unjoined)
    }

    /// The boundary of the 4-cell of `triple`: its three branchings resolved
    /// in turn, a loop from its first step followed by a normal form.
    ///
    /// The worklist pops each task in the order of its moves in the
    /// boundary, so each move it emits goes to the end.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Builder::branch`], and [`Unbuilt::Exhausted`] for a normal form
    /// past the budget.
    pub(super) fn sphere(
        &self,
        triple: &CriticalTriple<A>,
    ) -> Result<Homotopy<A>, Unbuilt>
    {
        let [ref first, ref second, ref third] = triple.steps;
        let peak = &triple.peak;
        let after = self.fire(peak, first)?;
        let mut steps = vec![forward(first.clone())];
        self.normal_path(&after, &mut steps)?;
        let mut tasks = Vec::new();
        for (one_side, other_side) in [(third, first), (second, third), (first, second)] {
            tasks.push(Task::Branch {
                first: one_side.clone(),
                second: other_side.clone(),
                term: peak.clone(),
                depth: self.budget,
                frame: Frame::root(),
            });
        }
        let mut moves = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Emit(each) => moves.push(each),
                Task::Normalising {
                    step,
                    term,
                    depth,
                    frame,
                } => self.normalising(step, term, depth, frame, &mut tasks)?,
                Task::NormalisingPath {
                    path,
                    start,
                    depth,
                    frame,
                } => self.normalising_path(&path, &start, depth, frame, &mut tasks)?,
                Task::Branch {
                    first,
                    second,
                    term,
                    depth,
                    frame,
                } => self.branch(&first, &second, &term, depth, frame, &mut tasks)?,
            }
        }
        Ok(Homotopy {
            source: RewritePath {
                start: peak.clone(),
                steps,
            },
            moves,
        })
    }
}

/// The definition of the confluence at the move `place` of `sphere` by the
/// rest of the loop: a homotopy from the confluence's first path to its
/// second, each at the root of its peak. `path` is the path that the move
/// reads.
///
/// The rest of the loop runs between the two paths whiskered by the steps
/// before the confluence and after it. The definition puts each whisker and
/// its inverse in place first, and takes them out last.
///
/// # Specification
/// trivial.
pub(super) fn cut<A>(
    sphere: &Homotopy<A>,
    place: MovePlace,
    path: &[PathStep<A>],
    tracelet: &Tracelet<A>,
) -> Option<Homotopy<A>>
where
    A: CellAlphabet,
{
    let at = usize::from(place);
    let Some(&Move::Confluence { sense, offset, .. }) = sphere.moves.get(at)
    else {
        return None;
    };
    let offset = usize::from(offset);
    let own = match sense {
        Sense::Forward => tracelet.path_a.len(),
        Sense::Backward => tracelet.path_b.len(),
    };
    let (prefix, rest) = path.split_at_checked(offset)?;
    let suffix = rest.get(own ..)?;
    let (before, after) = (
        sphere.moves.get(.. at)?,
        sphere.moves.get(at.saturating_add(1) ..)?,
    );
    let mut loop_rest = Vec::with_capacity(sphere.moves.len());
    loop_rest.extend(after.iter().cloned());
    loop_rest.extend(before.iter().cloned());
    let middle = match sense {
        Sense::Forward => inverted(&loop_rest),
        Sense::Backward => loop_rest,
    };
    let back: Vec<PathStep<A>> = word_inverse(prefix).collect();
    let twice = offset.saturating_mul(2);
    let mut moves = Vec::with_capacity(middle.len().saturating_add(4));
    if !back.is_empty() {
        moves.push(Move::Expand {
            offset: StepPlace::default(),
            word: back.clone(),
        });
    }
    if !suffix.is_empty() {
        moves.push(Move::Expand {
            offset: StepPlace::from(twice.saturating_add(tracelet.path_a.len())),
            word: suffix.to_vec(),
        });
    }
    moves.extend(shifted(&middle, StepPlace::from(offset)));
    if !suffix.is_empty() {
        moves.push(Move::Contract {
            offset: StepPlace::from(twice.saturating_add(tracelet.path_b.len())),
            word: suffix.to_vec(),
        });
    }
    if !back.is_empty() {
        moves.push(Move::Contract {
            offset: StepPlace::default(),
            word: back,
        });
    }
    Some(Homotopy {
        source: RewritePath {
            start: tracelet.overlap.peak.clone(),
            steps: tracelet.path_a.iter().cloned().map(forward).collect(),
        },
        moves,
    })
}
