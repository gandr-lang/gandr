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
///   a normal form below the root.
/// - witness: `rewrite::tests::a_frame_defining_cell_fires_at_the_root`
/// - witness: `rewrite::tests::a_budget_of_zero_reports_a_pending_redex`
/// - witness: `tests::second_inhabitant::the_normalizer_runs_over_the_toy_alphabet`
#[inline]
#[must_use]
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
///   search.
/// - witness: `rewrite::tests::a_frame_defining_cell_fires_at_the_root`
/// - witness: `rewrite::tests::a_budget_of_zero_reports_a_pending_redex`
#[inline]
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
///   codata η cell fires at it, and the frame-defining cell fires at a root.
/// - witness: `rewrite::tests::an_eta_cell_is_rejected_at_the_wrong_polarity`
/// - witness: `rewrite::tests::a_frame_defining_cell_fires_at_the_root`
/// - witness: `tests::differential::eta_at_the_wrong_polarity_is_rejected`
#[inline]
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
