//! The symmetries of the constructors of a block, as the reading of its
//! commands holds them.
//!
//! The symmetry of a constructor is a rule between two constructor terms. It
//! is a cell of the reading over terms, and the store of the commands has no
//! cell of it. The reading of the commands still decides each pair of two
//! rules of one operation. Two normal forms of such a pair that differ by the
//! order of the two arguments of a constructor with a symmetry are one term.
//! The reading over terms decides the same pair with the symmetry as an idle
//! cell, and it keeps the certificate.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_coherent_resolutions::Beside;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::PairClass;
use gandr_theory_coherent_resolutions::PairScheme;
use gandr_theory_computads::read_command;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::RuleReading;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TheoryDesc;
use quenchant_shape::shape::Maybe;

/// The head of one node of a term, with the name that it states.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Head<'term>
{
    /// A pattern variable.
    Var(&'term Name),
    /// A constructor.
    Ctor(&'term Name),
    /// An operation.
    Op(&'term Name),
    /// A results tuple.
    Results,
    /// An instantiation of a metavariable.
    Inst(&'term Name),
    /// An abstraction of an atom.
    Abs(&'term Name),
    /// An atom.
    Atom(&'term Name),
    /// A binding field.
    Lam(&'term Name),
    /// A bound variable.
    Bound(&'term Name),
}

/// One node of a term in pre-order: its head and the count of its arguments.
type Flat<'term> = (Head<'term>, usize);

/// The scheme of the reading of a block's commands. It gives no pair a class.
/// It holds two normal forms as one term where they differ by the order of the
/// two arguments of a constructor with a symmetry.
///
/// # Specification
/// - ensures: the name of each constructor whose two arguments a symmetry of
///   the block swaps.
/// - executable: none — a datum; [`PairScheme::beside`] carries the predicate.
///
/// # Adequacy
/// - hypothesis: L3 — as [`super::decide`]: two rules of an operation of a
///   `data` block that give the two orders of one constructor term join beside
///   the symmetry of the constructor.
/// - witness: `tests::coincide::two_rules_that_give_the_two_orders_of_one_term_join_beside_a_symmetry`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct TurnedConstructors
{
    /// Each constructor with a symmetry.
    symmetric: BTreeSet<Name>,
}

impl TurnedConstructors
{
    /// The constructors of `description` with a symmetry.
    ///
    /// # Specification
    /// - ensures: the head of the left side of each rule of `description` that
    ///   reads as [`RuleReading::Symmetry`] and whose left side a constructor
    ///   heads, and no other name. A symmetry of an operation is a cell of the
    ///   store, so the scheme does not hold it.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: one name for each such symmetry, growth within the rules
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TurnedConstructors`]; the same two rules beside
    ///   no symmetry part.
    /// - witness: `tests::coincide::two_rules_that_give_the_two_orders_of_one_term_join_beside_a_symmetry`
    /// - witness: `tests::coincide::an_overlap_that_joins_is_certified_and_runs_either_way`
    pub(super) fn of<G>(description: &TheoryDesc<G>) -> Self
    {
        Self {
            symmetric: description
                .rules
                .iter()
                .filter(|face| face.reading() == RuleReading::Symmetry)
                .filter_map(|face| match face.lhs.view() {
                    TermView::Ctor { name, .. } => Some(name.clone()),
                    TermView::Var(_)
                    | TermView::Op { .. }
                    | TermView::Results { .. }
                    | TermView::Inst { .. }
                    | TermView::Abs { .. }
                    | TermView::Atom(_)
                    | TermView::Lam { .. }
                    | TermView::Bound(_) => None,
                })
                .collect(),
        }
    }
}

impl PairScheme<SequentAlphabet> for TurnedConstructors
{
    /// No class for each pair: the reading of the commands fires a cell at the
    /// root of a command only.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn class(
        &mut self,
        _store: &CellStore<SequentAlphabet>,
        _overlap: &Overlap<SequentAlphabet>,
    ) -> PairClass<SequentAlphabet>
    {
        PairClass::Unclassed
    }

    /// Whether `left` and `right` are one term under the symmetries of the
    /// constructors.
    ///
    /// # Specification
    /// - ensures: [`Beside::One`] exactly when the scheme holds a constructor,
    ///   the two commands have one polarity and one consumer, each reads as a
    ///   term ([`read_command`]), and the two terms have one representative
    ///   ([`representative`]). The two normal forms of one pair share their
    ///   variables, so two terms with one representative differ by swaps of the
    ///   two arguments of such constructors alone.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the two terms that the commands read as and the nodes of
    ///   each, growth within the two commands
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TurnedConstructors`].
    /// - witness: `tests::coincide::two_rules_that_give_the_two_orders_of_one_term_join_beside_a_symmetry`
    fn beside(
        &mut self,
        _store: &CellStore<SequentAlphabet>,
        left: &CmdPat,
        right: &CmdPat,
    ) -> Beside
    {
        if self.symmetric.is_empty()
            || left.polarity() != right.polarity()
            || left.consumer() != right.consumer()
        {
            return Beside::Apart;
        }
        let (Maybe::Present(left), Maybe::Present(right)) =
            (read_command(left), read_command(right))
        else {
            return Beside::Apart;
        };
        if representative(&left, &self.symmetric) == representative(&right, &self.symmetric) {
            Beside::One
        }
        else {
            Beside::Apart
        }
    }
}

/// The nodes of `term` in pre-order, with the two arguments of each node of a
/// constructor of `symmetric` in ascending order.
///
/// # Specification
/// - ensures: one node for each node of `term`, a node before its arguments.
///   Each node of a constructor of `symmetric` over two arguments holds them in
///   ascending order of their sequences, each argument itself so arranged. A
///   term is a pre-order sequence with its argument counts, so the order of two
///   sequences is a total order of terms. Thus two terms that share their
///   variables have one result exactly when swaps of the two arguments of such
///   constructors take one to the other.
/// - panics: none.
/// - measure: the nodes of `term` not yet written, then the positions of the
///   sequence from the last; a stack holds the nodes still to write, and no
///   step recurses.
/// - executable: none — the sequence is the body's own construction.
///
/// # Cost
/// - allocation: one node for each node of `term` and the stack of its walk,
///   growth within the term
///
/// # Adequacy
/// - hypothesis: L3 — as [`TurnedConstructors`]: `Pair(y, x)` and `Pair(x, y)`
///   have one representative beside the symmetry of `Pair`, and two beside no
///   symmetry.
/// - witness: `tests::coincide::two_rules_that_give_the_two_orders_of_one_term_join_beside_a_symmetry`
fn representative<'term>(
    term: &'term FreeTerm,
    symmetric: &BTreeSet<Name>,
) -> Vec<Flat<'term>>
{
    let mut flat: Vec<Flat<'term>> = Vec::new();
    let mut pending = Vec::from([term.view()]);
    while let Some(view) = pending.pop() {
        let (head, arguments) = match view {
            TermView::Var(name) => (Head::Var(name), None),
            TermView::Ctor { name, args } => (Head::Ctor(name), Some(args)),
            TermView::Op { name, args } => (Head::Op(name), Some(args)),
            TermView::Results { args } => (Head::Results, Some(args)),
            TermView::Inst { name, args } => (Head::Inst(name), Some(args)),
            TermView::Abs { atom, args } => (Head::Abs(atom), Some(args)),
            TermView::Atom(name) => (Head::Atom(name), None),
            TermView::Lam { var, args } => (Head::Lam(var), Some(args)),
            TermView::Bound(name) => (Head::Bound(name), None),
        };
        let first = pending.len();
        pending.extend(arguments.into_iter().flatten().map(TermNode::view));
        // The stack gives the view pushed last first.
        if let Some(pushed) = pending.get_mut(first ..) {
            pushed.reverse();
        }
        flat.push((head, pending.len().saturating_sub(first)));
    }
    for at in (0 .. flat.len()).rev() {
        let turns = matches!(
            flat.get(at),
            Some(&(Head::Ctor(name), 2)) if symmetric.contains(name)
        );
        if !turns {
            continue;
        }
        let first = at.saturating_add(1);
        let second = flat_end(&flat, first);
        let end = flat_end(&flat, second);
        let turned = matches!(
            (flat.get(first .. second), flat.get(second .. end)),
            (Some(one), Some(other)) if other < one
        );
        if turned && let Some(arguments) = flat.get_mut(first .. end) {
            arguments.rotate_left(second.saturating_sub(first));
        }
    }
    flat
}

/// One past the end of the subterm of `flat` that starts at `start`; the end
/// of `flat` when it runs out first.
///
/// # Specification
/// trivial.
fn flat_end(
    flat: &[Flat<'_>],
    start: usize,
) -> usize
{
    let (mut at, mut owed) = (start, 1_usize);
    while let Some(next) = owed.checked_sub(1) {
        let Some(&(_, count)) = flat.get(at)
        else {
            return flat.len();
        };
        owed = next.saturating_add(count);
        at = at.saturating_add(1);
    }
    at
}
