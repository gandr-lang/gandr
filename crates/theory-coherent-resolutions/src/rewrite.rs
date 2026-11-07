//! Firing a cell and budgeted normalization, generic over the
//! [`CellAlphabet`].
//!
//! A cell fires at a command position when the alphabet's firing discipline
//! permits it there ([`CellAlphabet::may_fire`]) and its left-hand side matches
//! the command: the matched substitution instantiates the right-hand side,
//! which is spliced back in place of the redex. [`rewrite_at`] is that one
//! step; [`apply_once`] fires the first cell that fires anywhere, outermost
//! position first and store order within a position; [`normalize`] repeats it
//! until no cell fires or the budget is spent, and reports which of the two
//! stopped it. A budget is the guard against a store that does not terminate,
//! so normalization declines with a report rather than diverging.
//!
//! The discipline is consulted before matching, so a cell the alphabet
//! confines to one polarity — the sequent alphabet's η cells — is refused at
//! the other however well its left-hand side matches.
//!
//! # Firing and normalization
//!
//! A cell fires at a command position when the alphabet's firing discipline
//! permits it there and its left-hand side matches the command; the discipline
//! is asked first, so the sequent alphabet's η cells are refused at the wrong
//! polarity however well they match. `apply_once` tries positions in the
//! alphabet's order, outermost first, and cells in store order within a
//! position, so normalization is deterministic for a fixed store.
//!
//! A wire is a metavariable that a cell's right-hand side holds and its
//! left-hand side does not bind ([`Cell::wires`]). A wire is a scoped name, so
//! a cell with a wire fires with its faces renamed apart from the term. Each
//! firing thus writes each wire under a name that the term does not hold, and
//! two firings of one cell write two wires.
//!
//! `normalize` stops at a normal form or after its budget, and
//! `Normalization::exhausted` says which: a spent budget with a redex pending
//! is reported, never mistaken for a normal form. The budget is the guard
//! against a store that does not terminate, the same decline-and-report posture
//! completion takes.
//!
//! # Recorded substitution
//!
//! A step records the substitution that matched the cell's own left-hand side
//! ([`CellApp::subst`]). [`fire_at`] fires a cell and records its step.
//! [`replay_at`] replays a step: it instantiates the left-hand side by the
//! recorded substitution and compares the instance with the command at the
//! step's position, in place of a match. A substitution that does not give
//! that command is refused as [`firing::Absent::ForgedSubstitution`]. The
//! replay then contracts the step as [`rewrite_at`] does.

use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::RootAgreement;
use gandr_theory_cell_complexes::SequentAlphabet;
use quenchant_shape::shape::Maybe;

use crate::boundary::BudgetExhaustion;
use crate::boundary::NormalizationBudget;

/// One rewrite step: which cell fired, where, and the substitution that matched
/// it there.
///
/// The substitution binds each variable of the cell's left-hand side, as the
/// store holds the cell, to its subterm of the command at [`CellApp::at`].
/// Replay instantiates the left-hand side by it and compares the instance with
/// that command, in place of a match ([`replay_at`]). Replay then contracts the
/// step, so a certificate is re-executed and never trusted. A step holds the
/// substitution of the term that its holder fires it on: a certificate records
/// each step on the skolemized replay of its peak ([`crate::record_path`]).
///
/// # Identity
///
/// Equality and hashing read the cell and the position, not the substitution.
/// The substitution is the evidence of the step, which replay checks, and the
/// term that a holder fires the step on determines it. So one step that two
/// holders record on two terms is one step, and a path that a homotopy moves
/// into a context compares with the path it meets there.
#[derive(Clone, Debug)]
pub struct CellApp<A: CellAlphabet = SequentAlphabet>
{
    /// The cell that fired.
    pub cell: CellId,
    /// The command position it fired at.
    pub at: A::Pos,
    /// The substitution of the cell's left-hand side that matched the command
    /// at [`CellApp::at`].
    pub subst: A::Subst,
}

impl<A: CellAlphabet> CellApp<A>
{
    /// A step of `cell` at `at` that records no substitution yet.
    ///
    /// A reader that fires each step by a match, such as an event order, a
    /// flow or a footprint, reads the cell and the position alone. Replay
    /// refuses the step until [`crate::record_path`] records its substitution.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unrecorded(
        cell: CellId,
        at: A::Pos,
    ) -> Self
    {
        Self {
            cell,
            at,
            subst: A::Subst::default(),
        }
    }
}

impl<A: CellAlphabet> PartialEq for CellApp<A>
{
    /// Whether the two steps fire one cell at one position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.cell == other.cell && self.at == other.at
    }
}

impl<A: CellAlphabet> Eq for CellApp<A>
{
}

impl<A: CellAlphabet> core::hash::Hash for CellApp<A>
{
    /// The cell and the position, as [`PartialEq`] reads them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hash<H>(
        &self,
        state: &mut H,
    ) where
        H: core::hash::Hasher,
    {
        self.cell.hash(state);
        self.at.hash(state);
    }
}

/// One successful rewrite: the step, and the whole term after it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rewrite<A: CellAlphabet = SequentAlphabet>
{
    /// The step that fired.
    pub step: CellApp<A>,
    /// The whole term after the contraction.
    pub result: A::Cmd,
}

/// The outcome of [`normalize`]: the term reached, the steps that reached it,
/// and whether the budget stopped it short of a normal form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Normalization<A: CellAlphabet = SequentAlphabet>
{
    /// The term reached: a normal form unless [`Normalization::exhausted`]
    /// says otherwise.
    pub normal: A::Cmd,
    /// Every step taken from the input to [`Normalization::normal`], in order.
    pub path: Vec<CellApp<A>>,
    /// Whether the budget ran out with a redex still pending.
    pub exhausted: BudgetExhaustion,
}

quenchant_shape::reason_enum! {
    /// Why a cell does not fire at a position.
    pub mod firing {
        /// The reason the step does not happen.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The position addresses no command of the term.
            NoCommand(gandr_theory_cell_complexes::command_subterm::Absent),
            /// The alphabet's firing discipline refuses the cell at that
            /// command.
            Refused,
            /// The cell's left-hand side does not match the command.
            NoMatch,
            /// The step's substitution does not instantiate the cell's
            /// left-hand side to the command at the position: the substitution
            /// is forged.
            ForgedSubstitution,
            /// The alphabet refused to splice the contractum back where the
            /// redex was read, which an alphabet keeping the splice law never
            /// does.
            SpliceRefused(gandr_theory_cell_complexes::CommandSpliceRefusal),
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no cell of a store fires anywhere in a term.
    pub mod redex_search {
        /// The reason no rewrite is found.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No cell fires at any command position: the term is a normal
            /// form of the store.
            NormalForm,
        }
    }
}

/// Normalize `term` under `store`, taking at most `budget` steps.
///
/// # Specification
/// - requires: every cell's left-hand side binds every metavariable of its
///   right-hand side when it matches, so a contractum carries no hole the redex
///   did not.
/// - ensures: [`Normalization::path`] lists every step taken, in order, and
///   re-firing it from `term` reproduces [`Normalization::normal`]; at most
///   `budget` steps are taken.
/// - ensures: [`Normalization::exhausted`] is negative exactly when
///   [`Normalization::normal`] is a normal form of `store`; a positive answer
///   means the budget was spent with a redex pending.
/// - panics: none.
/// - intension: one redex search per step taken and one more to tell a normal
///   form from a spent budget.
///
/// # Adequacy
/// - hypothesis: L3 — a frame-defining cell reduces a sequent configuration in
///   one step to a normal form, a zero budget reports the pending redex without
///   firing it, and the same loop drives the toy alphabet through two cells to
///   a normal form below the root. Zero, exact and excess budgets separate a
///   pending redex from a normal form; changed step counts, premature
///   exhaustion and lost contractions change those observations.
/// - witness: `rewrite::tests::a_frame_defining_cell_fires_at_the_root`
/// - witness: `rewrite::tests::a_budget_of_zero_reports_a_pending_redex`
/// - witness: `tests::second_inhabitant::the_normalizer_runs_over_the_toy_alphabet`
/// - witness: `rewrite::tests::normalization_and_first_redex_respect_both_orders`
#[inline]
#[must_use]
#[spec(ensures: |output| output.path.len() <= usize::from(budget)
    && (!bool::from(output.exhausted) || output.path.len() == usize::from(budget))
    && (!output.path.is_empty() || output.normal == *term)
    && bool::from(output.exhausted) == matches!(apply_once(store, &output.normal), Maybe::Present(_)))]
#[cfg_attr(feature = "hotpath", hotpath::measure)]
pub fn normalize<A>(
    store: &CellStore<A>,
    term: &A::Cmd,
    budget: NormalizationBudget,
) -> Normalization<A>
where
    A: CellAlphabet,
{
    let mut normal = term.clone();
    let mut path = Vec::new();
    let mut remaining = usize::from(budget);
    loop {
        let Maybe::Present(rewrite) = apply_once(store, &normal)
        else {
            return Normalization {
                normal,
                path,
                exhausted: BudgetExhaustion::from(false),
            };
        };
        if remaining == 0 {
            return Normalization {
                normal,
                path,
                exhausted: BudgetExhaustion::from(true),
            };
        }
        path.push(rewrite.step);
        normal = rewrite.result;
        remaining = remaining.saturating_sub(1);
    }
}

/// Fire the first cell that fires anywhere in `term`.
///
/// # Specification
/// - ensures: the rewrite of the first `(position, cell)` pair whose
///   [`rewrite_at`] fires, positions in the alphabet's
///   [`CellAlphabet::command_positions`] order (outermost first) and cells in
///   store order within a position.
/// - provides: [`redex_search::Absent::NormalForm`] when no cell fires at any
///   command position.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the frame-defining cell is found at the root of a sequent
///   configuration, and a normal form is told from a spent budget by this
///   search. Competing root cells and a later root match above an earlier child
///   match separate cell order from position order; swapping either priority
///   changes the chosen application.
/// - witness: `rewrite::tests::a_frame_defining_cell_fires_at_the_root`
/// - witness: `rewrite::tests::a_budget_of_zero_reports_a_pending_redex`
/// - witness: `rewrite::tests::normalization_and_first_redex_respect_both_orders`
#[inline]
#[spec(ensures: |output| {
    let positions = A::command_positions(term);
    match output {
        Maybe::Present(ref rewrite) => positions.contains(&rewrite.step.at) && match store.get(rewrite.step.cell) {
            Maybe::Present(cell) => match rewrite_at(cell, term, &rewrite.step.at) {
                Maybe::Present(expected) => expected == rewrite.result,
                Maybe::Absent(_) => false,
            },
            Maybe::Absent(_) => false,
        },
        Maybe::Absent(redex_search::Absent::NormalForm) => positions.iter().all(|pos| store.iter().all(|(_, cell)| matches!(rewrite_at(cell, term, pos), Maybe::Absent(_)))),
    }
})]
pub fn apply_once<A>(
    store: &CellStore<A>,
    term: &A::Cmd,
) -> Maybe<Rewrite<A>, redex_search::Absent>
where
    A: CellAlphabet,
{
    for at in A::command_positions(term) {
        let Maybe::Present(redex) = A::subterm_cmd_at(term, &at)
        else {
            continue;
        };
        for (cell_id, cell) in store.iter() {
            if let Maybe::Present((result, subst)) = contract(cell, term, &at, &redex) {
                return Maybe::Present(Rewrite {
                    step: CellApp {
                        cell: cell_id,
                        at,
                        subst,
                    },
                    result,
                });
            }
        }
    }
    Maybe::Absent(redex_search::Absent::NormalForm)
}

/// Fire `cell` at `pos` in `term`.
///
/// # Specification
/// - ensures: `term` with the command at `pos` replaced by the cell's
///   right-hand side under the substitution that matches its left-hand side to
///   that command. A cell with wires ([`Cell::wires`]) fires with both faces
///   renamed apart from `term` ([`CellAlphabet::rename_apart`]), so each wire
///   that it writes takes a name that `term` does not hold.
/// - provides: [`firing::Absent::NoCommand`] when `pos` addresses no command;
///   [`firing::Absent::Refused`] when the alphabet's firing discipline refuses
///   the cell there, which is decided before matching;
///   [`firing::Absent::NoMatch`] when the left-hand side does not match;
///   [`firing::Absent::SpliceRefused`] when the alphabet refuses the splice
///   back.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a data η cell matching a negative cut is refused there, a
///   codata η cell fires at it, and the frame-defining cell fires at a root. An
///   off-term path, a failed match and a refused splice retain distinct
///   reasons. Failure precedence and any recorded step after refusal change the
///   observation.
/// - witness: `rewrite::tests::an_eta_cell_is_rejected_at_the_wrong_polarity`
/// - witness: `rewrite::tests::a_frame_defining_cell_fires_at_the_root`
/// - witness: `tests::differential::eta_at_the_wrong_polarity_is_rejected`
/// - witness: `rewrite::tests::refusal_boundaries_do_not_record_a_step`
/// - witness: `rewrite::tests::each_firing_writes_its_wire_under_a_name_the_term_does_not_hold`
#[inline]
#[spec(ensures: |output| match A::subterm_cmd_at(term, pos) {
    Maybe::Absent(reason) => output == Maybe::Absent(firing::Absent::NoCommand(reason)),
    Maybe::Present(ref redex) => if bool::from(A::may_fire(&cell.provenance(), redex)) {
        let renamed = renamed(cell, term);
        let (lhs, rhs) = renamed.as_ref().map_or_else(|| (cell.lhs(), cell.rhs()), |&(ref lhs, ref rhs)| (lhs, rhs));
        let mut subst = A::Subst::default();
        if bool::from(A::match_cmd(lhs, redex, &mut subst)) {
            match A::splice_cmd_at(term, pos, A::apply_subst(&subst, rhs)) {
                Ok(expected) => output == Maybe::Present(expected),
                Err(reason) => output == Maybe::Absent(firing::Absent::SpliceRefused(reason)),
            }
        } else {
            output == Maybe::Absent(firing::Absent::NoMatch)
        }
    } else {
        output == Maybe::Absent(firing::Absent::Refused)
    },
})]
pub fn rewrite_at<A>(
    cell: &Cell<A>,
    term: &A::Cmd,
    pos: &A::Pos,
) -> Maybe<A::Cmd, firing::Absent>
where
    A: CellAlphabet,
{
    match fire(cell, term, pos) {
        Maybe::Present((result, _subst)) => Maybe::Present(result),
        Maybe::Absent(reason) => Maybe::Absent(reason),
    }
}

/// Fire `cell` at `pos` in `term`, with the substitution that matched the
/// cell's own left-hand side: [`rewrite_at`] that keeps the substitution.
///
/// # Specification
/// - ensures: the result that [`rewrite_at`] gives, with a substitution that
///   instantiates the cell's left-hand side to the command at `pos`.
/// - provides: the reasons that [`rewrite_at`] provides.
/// - panics: none.
/// - executable: none — [`rewrite_at`] fires through this function, so a clause
///   that calls it recurses without end.
///
/// # Adequacy
/// - hypothesis: L3 — as [`fire_at`], which records its step through it.
/// - witness: `rewrite::tests::a_replayed_step_refuses_a_forged_substitution_by_name`
pub fn fire<A>(
    cell: &Cell<A>,
    term: &A::Cmd,
    pos: &A::Pos,
) -> Maybe<(A::Cmd, A::Subst), firing::Absent>
where
    A: CellAlphabet,
{
    match A::subterm_cmd_at(term, pos) {
        Maybe::Present(redex) => contract(cell, term, pos, &redex),
        Maybe::Absent(reason) => Maybe::Absent(firing::Absent::NoCommand(reason)),
    }
}

/// Fire `cell`, which a store holds under `id`, at `at` in `term`, and record
/// the step: [`rewrite_at`] with the substitution that matched.
///
/// # Specification
/// - ensures: the result that [`rewrite_at`] gives, with the step of `id` at
///   `at` whose substitution instantiates the cell's left-hand side to the
///   command at `at`.
/// - provides: the reasons that [`rewrite_at`] provides.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded step replays to the result of its firing, and
///   the same step with a changed substitution is refused. A substitution of
///   another redex or a dropped binding changes the replay.
/// - witness: `rewrite::tests::a_replayed_step_refuses_a_forged_substitution_by_name`
#[inline]
#[spec(captures: expected = rewrite_at(cell, term, &at), ensures: |output| match output {
    Maybe::Present(ref fired) => expected == Maybe::Present(fired.result.clone()) && fired.step.cell == id
        && matches!(A::subterm_cmd_at(term, &fired.step.at), Maybe::Present(ref redex)
            if A::apply_images(cell.lhs(), |var| A::image(&fired.step.subst, var)) == *redex),
    Maybe::Absent(reason) => expected == Maybe::Absent(reason),
})]
pub fn fire_at<A>(
    id: CellId,
    cell: &Cell<A>,
    term: &A::Cmd,
    at: A::Pos,
) -> Maybe<Rewrite<A>, firing::Absent>
where
    A: CellAlphabet,
{
    match fire(cell, term, &at) {
        Maybe::Present((result, subst)) => Maybe::Present(Rewrite {
            step: CellApp {
                cell: id,
                at,
                subst,
            },
            result,
        }),
        Maybe::Absent(reason) => Maybe::Absent(reason),
    }
}

/// Replay `step` of `cell` in `term`: instantiate the cell's left-hand side by
/// the step's substitution, compare the instance with the command at the
/// step's position, and contract.
///
/// The comparison takes the place of a match. The contraction is the one that
/// [`rewrite_at`] makes, so a replayed step is re-executed and never trusted.
/// Only the bindings of the left-hand side's variables are read, so a binding
/// of another variable changes nothing.
///
/// # Specification
/// - ensures: when the substitution instantiates the left-hand side to the
///   command at `step.at`, the result that [`rewrite_at`] gives there.
/// - provides: [`firing::Absent::NoCommand`] when the position addresses no
///   command; [`firing::Absent::Refused`] when the alphabet's firing discipline
///   refuses the cell there; [`firing::Absent::NoMatch`] when the instance
///   differs from the command and the left-hand side matches it under no
///   substitution; [`firing::Absent::ForgedSubstitution`] when the instance
///   differs from a command that the left-hand side matches;
///   [`firing::Absent::SpliceRefused`] when the alphabet refuses the splice.
/// - panics: none.
/// - intension: one instantiation and one comparison in place of a match, then
///   one instantiation of the right-hand side. A refused instance costs one
///   match, which names the refusal. A cell with a wire also matches its faces
///   renamed apart from `term`, as [`rewrite_at`] does.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded step replays to the result of its firing. A
///   substitution of another redex, a dropped binding, an extra binding of
///   another variable and a command that the cell does not match are replayed.
///   The first two are refused as forged, the third replays alike, and the
///   fourth is refused as no match. Accepting a forged substitution or refusing
///   the honest one changes the outcome.
/// - witness: `rewrite::tests::a_replayed_step_refuses_a_forged_substitution_by_name`
#[inline]
#[spec(ensures: |output| match A::subterm_cmd_at(term, &step.at) {
    Maybe::Absent(reason) => output == Maybe::Absent(firing::Absent::NoCommand(reason)),
    Maybe::Present(ref redex) => if !bool::from(A::may_fire(&cell.provenance(), redex)) {
        output == Maybe::Absent(firing::Absent::Refused)
    } else if A::apply_images(cell.lhs(), |var| A::image(&step.subst, var)) == *redex {
        output == rewrite_at(cell, term, &step.at)
    } else if bool::from(A::match_cmd(cell.lhs(), redex, &mut A::Subst::default())) {
        output == Maybe::Absent(firing::Absent::ForgedSubstitution)
    } else {
        output == Maybe::Absent(firing::Absent::NoMatch)
    },
})]
pub fn replay_at<A>(
    cell: &Cell<A>,
    term: &A::Cmd,
    step: &CellApp<A>,
) -> Maybe<A::Cmd, firing::Absent>
where
    A: CellAlphabet,
{
    let redex = match A::subterm_cmd_at(term, &step.at) {
        Maybe::Present(redex) => redex,
        Maybe::Absent(reason) => return Maybe::Absent(firing::Absent::NoCommand(reason)),
    };
    if !bool::from(A::may_fire(&cell.provenance(), &redex)) {
        return Maybe::Absent(firing::Absent::Refused);
    }
    let image_of = |var: &A::Var| A::image(&step.subst, var);
    if A::apply_images(cell.lhs(), image_of) != redex {
        let matches = A::match_cmd(cell.lhs(), &redex, &mut A::Subst::default());
        return Maybe::Absent(if bool::from(matches) {
            firing::Absent::ForgedSubstitution
        }
        else {
            firing::Absent::NoMatch
        });
    }
    let contractum = match renamed(cell, term) {
        None => A::apply_images(cell.rhs(), image_of),
        Some(ref faces) => match wired_contractum::<A>(faces, &redex) {
            Maybe::Present(contractum) => contractum,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        },
    };
    match A::splice_cmd_at(term, &step.at, contractum) {
        Ok(result) => Maybe::Present(result),
        Err(refusal) => Maybe::Absent(firing::Absent::SpliceRefused(refusal)),
    }
}

/// Fire `cell` at `pos` in `term`, where `redex` is the command `pos`
/// addresses: [`rewrite_at`] after its read of the redex, so a search that
/// tries every cell at one position reads the redex once. The substitution
/// that matched the cell's own left-hand side comes with the result.
///
/// # Specification
/// - requires: `redex` is the command of `term` at `pos`.
/// - ensures: the answer [`rewrite_at`] gives for `cell`, `term` and `pos`: the
///   splice of the instantiated right-hand side when the discipline permits the
///   cell and its left-hand side matches `redex`, so a root check that refuses
///   a cell which matches breaks it. A cell with wires instantiates its faces
///   renamed apart from `term`. The substitution instantiates the cell's own
///   left-hand side to `redex`.
/// - provides: [`firing::Absent::Refused`] when the alphabet's firing
///   discipline refuses the cell there; [`firing::Absent::NoMatch`] when the
///   roots clash or the left-hand side does not match;
///   [`firing::Absent::SpliceRefused`] when the alphabet refuses the splice.
/// - panics: none.
/// - intension: the roots are compared before the left-hand side is matched, so
///   a cell whose root cannot meet the redex costs one comparison. A cell with
///   no wire fires with its own faces and builds no renamed copy; a cell with a
///   wire matches its own left-hand side for the substitution and its renamed
///   one for the contraction.
///
/// # Adequacy
/// - hypothesis: L3 — [`rewrite_at`]'s witnesses run through it, and the redex
///   search's order witness tries cells whose roots clash with the redex before
///   the one that fires. Skipping a cell that matches, or firing one that does
///   not, changes the observed rewrite.
/// - witness: `rewrite::tests::an_eta_cell_is_rejected_at_the_wrong_polarity`
/// - witness: `rewrite::tests::a_frame_defining_cell_fires_at_the_root`
/// - witness: `rewrite::tests::normalization_and_first_redex_respect_both_orders`
/// - witness: `rewrite::tests::refusal_boundaries_do_not_record_a_step`
/// - witness: `rewrite::tests::each_firing_writes_its_wire_under_a_name_the_term_does_not_hold`
#[spec(ensures: |output| if bool::from(A::may_fire(&cell.provenance(), redex)) {
    let renamed = renamed(cell, term);
    let (lhs, rhs) = renamed.as_ref().map_or_else(|| (cell.lhs(), cell.rhs()), |&(ref lhs, ref rhs)| (lhs, rhs));
    let mut subst = A::Subst::default();
    if bool::from(A::match_cmd(lhs, redex, &mut subst)) {
        match A::splice_cmd_at(term, pos, A::apply_subst(&subst, rhs)) {
            Ok(expected) => matches!(output, Maybe::Present((ref result, ref own)) if *result == expected
                && A::apply_images(cell.lhs(), |var| A::image(own, var)) == *redex),
            Err(reason) => output == Maybe::Absent(firing::Absent::SpliceRefused(reason)),
        }
    } else {
        output == Maybe::Absent(firing::Absent::NoMatch)
    }
} else {
    output == Maybe::Absent(firing::Absent::Refused)
})]
fn contract<A>(
    cell: &Cell<A>,
    term: &A::Cmd,
    pos: &A::Pos,
    redex: &A::Cmd,
) -> Maybe<(A::Cmd, A::Subst), firing::Absent>
where
    A: CellAlphabet,
{
    if !bool::from(A::may_fire(&cell.provenance(), redex)) {
        return Maybe::Absent(firing::Absent::Refused);
    }
    if A::root_agreement(cell.lhs(), redex) == RootAgreement::Clash {
        return Maybe::Absent(firing::Absent::NoMatch);
    }
    let mut subst = A::Subst::default();
    if !bool::from(A::match_cmd(cell.lhs(), redex, &mut subst)) {
        return Maybe::Absent(firing::Absent::NoMatch);
    }
    let contractum = match renamed(cell, term) {
        None => A::apply_subst(&subst, cell.rhs()),
        Some(ref faces) => match wired_contractum::<A>(faces, redex) {
            Maybe::Present(contractum) => contractum,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        },
    };
    match A::splice_cmd_at(term, pos, contractum) {
        Ok(result) => Maybe::Present((result, subst)),
        Err(refusal) => Maybe::Absent(firing::Absent::SpliceRefused(refusal)),
    }
}

/// The contractum of a cell with a wire at `redex`: its right-hand side
/// `faces.1` under the match of its left-hand side `faces.0`, both renamed
/// apart from the term, so that each wire takes a name the term does not hold.
///
/// # Specification
/// - ensures: the right-hand side under the substitution that matches the
///   left-hand side to `redex`.
/// - provides: [`firing::Absent::NoMatch`] when the left-hand side does not
///   match, which a renaming of a left-hand side that matches never gives.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `cong1` fired twice from a ground term writes `x′` and
///   then `x′'`. A wire written under a held name changes the terms.
/// - witness: `rewrite::tests::each_firing_writes_its_wire_under_a_name_the_term_does_not_hold`
#[spec(ensures: |output| {
    let mut subst = A::Subst::default();
    if bool::from(A::match_cmd(&faces.0, redex, &mut subst)) {
        output == Maybe::Present(A::apply_subst(&subst, &faces.1))
    } else {
        output == Maybe::Absent(firing::Absent::NoMatch)
    }
})]
fn wired_contractum<A>(
    faces: &(A::Cmd, A::Cmd),
    redex: &A::Cmd,
) -> Maybe<A::Cmd, firing::Absent>
where
    A: CellAlphabet,
{
    let mut renamed = A::Subst::default();
    if !bool::from(A::match_cmd(&faces.0, redex, &mut renamed)) {
        return Maybe::Absent(firing::Absent::NoMatch);
    }
    Maybe::Present(A::apply_subst(&renamed, &faces.1))
}

/// The faces of `cell` renamed apart from `term`, when the cell has a wire: a
/// wire is a scoped name, and each firing introduces a fresh one.
///
/// # Specification
/// - ensures: nothing for a cell with no wire; otherwise its two faces renamed
///   apart from the metavariables of `term` ([`CellAlphabet::rename_apart`]). A
///   name absent from `term` stays, and a name that `term` holds takes primes
///   until it is absent.
/// - panics: none.
/// - intension: a cell with no wire costs one length read, and a cell with a
///   wire builds one renamed copy of its two faces.
///
/// # Adequacy
/// - hypothesis: L3 — `cong1` fired twice from a ground term writes `x′` and
///   then `x′'`, and a cell with no wire fires with its own faces. A firing
///   that keeps a held name, or renames a cell with no wire, changes the terms.
/// - witness: `rewrite::tests::each_firing_writes_its_wire_under_a_name_the_term_does_not_hold`
#[spec(ensures: |output| if cell.wires().is_empty() {
    output.is_none()
} else {
    output == Some(A::rename_apart((term, term), (cell.lhs(), cell.rhs())))
})]
fn renamed<A>(
    cell: &Cell<A>,
    term: &A::Cmd,
) -> Option<(A::Cmd, A::Cmd)>
where
    A: CellAlphabet,
{
    if cell.wires().is_empty() {
        return None;
    }
    Some(A::rename_apart((term, term), (cell.lhs(), cell.rhs())))
}

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::EtaKind;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::Pos;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::Sym;
    use gandr_theory_cell_complexes::frame_defining_cell;

    use super::*;

    #[test]
    fn normalization_and_first_redex_respect_both_orders()
    {
        use gandr_theory_cell_complexes_tools::Toy;
        use gandr_theory_cell_complexes_tools::ToyAlphabet;
        use gandr_theory_cell_complexes_tools::toy_cell;
        let root = ToyAlphabet::root_position();
        let mut store = CellStore::new();
        let peel = store.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::var("x")));
        let two = Toy::succ(Toy::succ(Toy::zero()));
        for (budget, expected, steps, exhausted) in [
            (0_usize, two.clone(), 0_usize, true),
            (1, Toy::succ(Toy::zero()), 1, true),
            (2, Toy::zero(), 2, false),
            (3, Toy::zero(), 2, false),
        ] {
            let result = normalize(&store, &two, NormalizationBudget::from(budget));
            assert_eq!(expected, result.normal);
            assert_eq!(exhausted, bool::from(result.exhausted));
            assert_eq!(
                alloc::vec![(peel, root.clone()); steps],
                result
                    .path
                    .iter()
                    .map(|step| (step.cell, step.at.clone()))
                    .collect::<Vec<_>>()
            );
        }
        let normal = normalize(&store, &Toy::zero(), NormalizationBudget::from(0_usize));
        assert_eq!(Toy::zero(), normal.normal);
        assert!(normal.path.is_empty());
        assert!(!bool::from(normal.exhausted));
        let root_rule = store.insert(toy_cell(
            Toy::add(Toy::var("x"), Toy::var("y")),
            Toy::var("x"),
        ));
        let term = Toy::add(Toy::succ(Toy::zero()), two.clone());
        let placed = |rewrite: Maybe<Rewrite<ToyAlphabet>, redex_search::Absent>| match rewrite {
            Maybe::Present(rewrite) => (rewrite.step.cell, rewrite.step.at, rewrite.result),
            Maybe::Absent(reason) => panic!("a cell fires: {reason:?}"),
        };
        assert_eq!(
            (root_rule, root.clone(), Toy::succ(Toy::zero())),
            placed(apply_once(&store, &term))
        );
        let mut competing = CellStore::new();
        let first = competing.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::zero()));
        competing.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::var("x")));
        assert_eq!(
            (first, root.clone(), Toy::zero()),
            placed(apply_once(&competing, &two))
        );
        let mut looping = CellStore::new();
        let loop_id = looping.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::succ(Toy::var("x"))));
        let bounded = normalize(&looping, &two, NormalizationBudget::from(2_usize));
        assert_eq!(two, bounded.normal);
        assert!(bool::from(bounded.exhausted));
        assert_eq!(
            alloc::vec![(loop_id, root); 2],
            bounded
                .path
                .iter()
                .map(|step| (step.cell, step.at.clone()))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn a_replayed_step_refuses_a_forged_substitution_by_name()
    {
        use gandr_theory_cell_complexes_tools::Toy;
        use gandr_theory_cell_complexes_tools::ToyAlphabet;
        use gandr_theory_cell_complexes_tools::ToyVar;
        use gandr_theory_cell_complexes_tools::toy_cell;
        let root = ToyAlphabet::root_position();
        let mut store = CellStore::new();
        let id = store.insert(toy_cell(
            Toy::add(Toy::var("x"), Toy::var("y")),
            Toy::var("x"),
        ));
        let Maybe::Present(cell) = store.get(id)
        else {
            panic!("the store holds the cell");
        };
        let fire = |term: &Toy| match fire_at(id, cell, term, root.clone()) {
            Maybe::Present(fired) => fired,
            Maybe::Absent(reason) => panic!("the cell fires at the root: {reason:?}"),
        };
        let term = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
        let fired = fire(&term);
        assert_eq!(Toy::succ(Toy::zero()), fired.result);
        assert_eq!(
            Maybe::Present(fired.result.clone()),
            replay_at(cell, &term, &fired.step),
            "the recorded step replays to the result of its firing"
        );
        let forged = |subst| CellApp {
            subst,
            ..fired.step.clone()
        };
        let other = fire(&Toy::add(Toy::zero(), Toy::zero())).step.subst;
        let dropped = ToyAlphabet::restrict_subst(&fired.step.subst, &[ToyVar::from("x")]);
        for (label, subst) in [("another redex's", other), ("a dropped binding's", dropped)] {
            assert_eq!(
                Maybe::Absent(firing::Absent::ForgedSubstitution),
                replay_at(cell, &term, &forged(subst)),
                "{label} substitution is refused by name"
            );
        }
        assert_eq!(
            Maybe::Absent(firing::Absent::NoMatch),
            replay_at(cell, &Toy::succ(Toy::zero()), &fired.step),
            "a step replayed on a command that its cell does not match is no match"
        );
        let mut extended = fired.step.subst.clone();
        assert!(bool::from(ToyAlphabet::match_cmd(
            &Toy::var("z"),
            &Toy::zero(),
            &mut extended
        )));
        assert_eq!(
            Maybe::Present(fired.result.clone()),
            replay_at(cell, &term, &forged(extended)),
            "a binding of a variable the left-hand side does not hold is not read"
        );
    }

    /// Rejects the final splice after a successful read and match.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    struct RefusingSplice;

    impl gandr_theory_cell_complexes_tools::AlphabetLie for RefusingSplice
    {
        /// Refuses every otherwise valid splice to expose the firing boundary.
        ///
        /// # Specification
        /// - fails: always returns the non-command refusal.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — valid matching, mismatching and off-term inputs
        ///   separate the splice refusal from earlier failures. A refused
        ///   splice never becomes a normalization step.
        /// - witness: `rewrite::tests::refusal_boundaries_do_not_record_a_step`
        #[spec(ensures: |output| matches!(output, Err(gandr_theory_cell_complexes::CommandSpliceRefusal::NotACommand)))]
        fn splice_cmd_at(
            _cmd: &gandr_theory_cell_complexes_tools::Toy,
            _pos: &gandr_theory_cell_complexes_tools::ToyPos,
            _replacement: gandr_theory_cell_complexes_tools::Toy,
        ) -> Result<
            gandr_theory_cell_complexes_tools::Toy,
            gandr_theory_cell_complexes::CommandSpliceRefusal,
        >
        {
            Err(gandr_theory_cell_complexes::CommandSpliceRefusal::NotACommand)
        }
    }

    #[test]
    fn refusal_boundaries_do_not_record_a_step()
    {
        use gandr_theory_cell_complexes::CommandSpliceRefusal;
        use gandr_theory_cell_complexes::PositionStep;
        use gandr_theory_cell_complexes::command_subterm;
        use gandr_theory_cell_complexes_tools::Lying;
        use gandr_theory_cell_complexes_tools::Toy;
        use gandr_theory_cell_complexes_tools::ToyAlphabet;
        use gandr_theory_cell_complexes_tools::lying_cell;
        let cell = lying_cell::<RefusingSplice>(Toy::succ(Toy::var("x")), Toy::var("x"));
        let root = ToyAlphabet::root_position();
        let redex = Toy::succ(Toy::zero());
        assert_eq!(
            Maybe::Absent(firing::Absent::SpliceRefused(
                CommandSpliceRefusal::NotACommand
            )),
            rewrite_at(&cell, &redex, &root)
        );
        assert_eq!(
            Maybe::Absent(firing::Absent::NoMatch),
            rewrite_at(&cell, &Toy::zero(), &root)
        );
        let outside = ToyAlphabet::position_at_path(&[PositionStep::from(1_usize)]);
        assert_eq!(
            Maybe::Absent(firing::Absent::NoCommand(command_subterm::Absent::OffTerm)),
            rewrite_at(&cell, &redex, &outside)
        );
        let mut store = CellStore::<Lying<RefusingSplice>>::new();
        store.insert(cell);
        let result = normalize(&store, &redex, NormalizationBudget::from(2_usize));
        assert_eq!(redex, result.normal);
        assert!(result.path.is_empty());
        assert!(!bool::from(result.exhausted));
    }

    /// `⟨Zero | Succ⁻(★)⟩`, the frame-defining cell's redex at `Zero`.
    ///
    /// # Specification
    /// trivial.
    fn framed_zero() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::frame("Succ", ConsPat::top()),
        )
    }

    #[test]
    fn a_frame_defining_cell_fires_at_the_root()
    {
        // ⟨Zero | Succ⁻(★)⟩ ~> ⟨Succ(Zero) | ★⟩.
        let mut store = CellStore::new();
        store.insert(frame_defining_cell(&Sym::new("Succ")));
        let out = normalize(&store, &framed_zero(), NormalizationBudget::from(16_usize));
        let expected = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]),
            ConsPat::top(),
        );
        assert_eq!(expected, out.normal, "the μ̃ reduction wrapped Zero in Succ");
        assert_eq!(1_usize, out.path.len(), "exactly one step");
        assert!(!bool::from(out.exhausted), "a normal form was reached");
    }

    #[test]
    fn an_eta_cell_is_rejected_at_the_wrong_polarity()
    {
        // A data-η cell, which requires a positive cut, built over a negative
        // one: its left-hand side matches the target, and the discipline
        // refuses it anyway.
        let lhs = CmdPat::cut(Polarity::Negative, ProdPat::meta("x"), ConsPat::meta("a"));
        let eta: Cell = Cell::new(
            lhs.clone(),
            lhs.clone(),
            Orientation::PolarityDerived,
            CellProvenance::Eta(EtaKind::Data),
        );
        assert_eq!(
            Maybe::Absent(firing::Absent::Refused),
            rewrite_at(&eta, &lhs, &Pos::root()),
            "data-η must not fire at a negative cut"
        );
        let positive = CmdPat::cut(Polarity::Positive, ProdPat::meta("x"), ConsPat::meta("a"));
        let data_eta: Cell = Cell::new(
            positive.clone(),
            positive.clone(),
            Orientation::PolarityDerived,
            CellProvenance::Eta(EtaKind::Data),
        );
        assert!(
            matches!(
                rewrite_at(&data_eta, &positive, &Pos::root()),
                Maybe::Present(_)
            ),
            "at a positive cut it fires"
        );
    }

    #[test]
    fn each_firing_writes_its_wire_under_a_name_the_term_does_not_hold()
    {
        let wired = |lhs, rhs| -> Cell {
            Cell::new(
                lhs,
                rhs,
                Orientation::PolarityDerived,
                CellProvenance::SurfaceRule,
            )
        };
        let fire = |cell: &Cell, term: &CmdPat| match rewrite_at(cell, term, &Pos::root()) {
            Maybe::Present(result) => result,
            Maybe::Absent(reason) => panic!("the cell fires at the root: {reason:?}"),
        };
        // `cong1` of `theory NatSum`, ⟨x | add(y; k)⟩ ~> ⟨x′ | add(y; k)⟩: the
        // second firing consumes the first wire and writes another.
        let add = || ConsPat::op("add", [ProdPat::meta("y")], ConsPat::meta("k"));
        let cong = wired(
            CmdPat::cut(Polarity::Positive, ProdPat::meta("x"), add()),
            CmdPat::cut(Polarity::Positive, ProdPat::meta("x′"), add()),
        );
        let ground = SequentAlphabet::skolemize(cong.lhs());
        let once = fire(&cong, &ground);
        let twice = fire(&cong, &once);
        assert_eq!(
            (&ProdPat::meta("x′"), &ProdPat::meta("x′'")),
            (once.producer(), twice.producer()),
            "the second firing writes a name that the term does not hold"
        );
        // ⟨x | k⟩ ~> ⟨Pair(x, w) | k⟩ keeps the first wire, so one term holds
        // two wires with two names.
        let pair = wired(
            CmdPat::cut(Polarity::Positive, ProdPat::meta("x"), ConsPat::meta("k")),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("w")]),
                ConsPat::meta("k"),
            ),
        );
        let ground = SequentAlphabet::skolemize(pair.lhs());
        let twice = fire(&pair, &fire(&pair, &ground));
        let held = ProdPat::ctor("Pair", [ProdPat::ctor("$k$x", []), ProdPat::meta("w")]);
        assert_eq!(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Pair", [held, ProdPat::meta("w'")]),
                ground.consumer().clone(),
            ),
            twice,
            "two firings write two wires"
        );
    }

    #[test]
    fn a_budget_of_zero_reports_a_pending_redex()
    {
        let mut store = CellStore::new();
        store.insert(frame_defining_cell(&Sym::new("Succ")));
        let out = normalize(&store, &framed_zero(), NormalizationBudget::from(0_usize));
        assert!(
            bool::from(out.exhausted),
            "a redex remained but the budget was zero"
        );
        assert_eq!(0_usize, out.path.len(), "no step was taken");
        assert_eq!(
            framed_zero(),
            out.normal,
            "and the term is returned as it came"
        );
    }
}
