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

use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::SequentAlphabet;
use quenchant_shape::shape::Maybe;

use crate::boundary::BudgetExhaustion;
use crate::boundary::NormalizationBudget;

/// One rewrite step: which cell fired, and where.
///
/// A step records no substitution. Replay re-matches and re-contracts every
/// step, so a certificate is re-executed rather than trusted.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CellApp<A: CellAlphabet = SequentAlphabet>
{
    /// The cell that fired.
    pub cell: CellId,
    /// The command position it fired at.
    pub at: A::Pos,
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
        for (cell_id, cell) in store.iter() {
            if let Maybe::Present(result) = rewrite_at(cell, term, &at) {
                return Maybe::Present(Rewrite {
                    step: CellApp { cell: cell_id, at },
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
///   that command.
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
#[inline]
#[spec(ensures: |output| match A::subterm_cmd_at(term, pos) {
    Maybe::Absent(reason) => output == Maybe::Absent(firing::Absent::NoCommand(reason)),
    Maybe::Present(ref redex) => if bool::from(A::may_fire(&cell.provenance(), redex)) {
        let mut subst = A::Subst::default();
        if bool::from(A::match_cmd(cell.lhs(), redex, &mut subst)) {
            match A::splice_cmd_at(term, pos, A::apply_subst(&subst, cell.rhs())) {
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
    let redex = match A::subterm_cmd_at(term, pos) {
        | Maybe::Present(redex) => redex,
        | Maybe::Absent(reason) => return Maybe::Absent(firing::Absent::NoCommand(reason)),
    };
    if !bool::from(A::may_fire(&cell.provenance(), &redex)) {
        return Maybe::Absent(firing::Absent::Refused);
    }
    let mut subst = A::Subst::default();
    if !bool::from(A::match_cmd(cell.lhs(), &redex, &mut subst)) {
        return Maybe::Absent(firing::Absent::NoMatch);
    }
    let contractum = A::apply_subst(&subst, cell.rhs());
    match A::splice_cmd_at(term, pos, contractum) {
        | Ok(result) => Maybe::Present(result),
        | Err(refusal) => Maybe::Absent(firing::Absent::SpliceRefused(refusal)),
    }
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
                alloc::vec![CellApp { cell: peel, at: root.clone() }; steps],
                result.path
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
        assert_eq!(
            Maybe::Present(Rewrite {
                step: CellApp {
                    cell: root_rule,
                    at: root.clone()
                },
                result: Toy::succ(Toy::zero())
            }),
            apply_once(&store, &term)
        );
        let mut competing = CellStore::new();
        let first = competing.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::zero()));
        competing.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::var("x")));
        assert_eq!(
            Maybe::Present(Rewrite {
                step: CellApp {
                    cell: first,
                    at: root.clone()
                },
                result: Toy::zero()
            }),
            apply_once(&competing, &two)
        );
        let mut looping = CellStore::new();
        let loop_id = looping.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::succ(Toy::var("x"))));
        let bounded = normalize(&looping, &two, NormalizationBudget::from(2_usize));
        assert_eq!(two, bounded.normal);
        assert!(bool::from(bounded.exhausted));
        assert_eq!(
            alloc::vec![CellApp { cell: loop_id, at: root }; 2],
            bounded.path
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
