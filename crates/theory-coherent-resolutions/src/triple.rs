//! The critical triples of a store: three rewriting steps on one peak, which
//! the overlaps of their left-hand sides connect.
//!
//! A triple branching is three steps on one term. It is critical when the
//! three left-hand sides cover the term and their overlaps connect the three
//! steps. Thus one step stands at the root of the peak. Each other step stands
//! at a command position that a left-hand side of the other steps covers. Two
//! steps of a triple can stand apart. On the word `LULU`, the outer left sides
//! share no letter, and the middle one overlaps both. A triple counts once over
//! the orders of its steps, as a critical pair counts once over its two orders.
//!
//! On a string rewriting system, these triples are the critical cells of
//! dimension three of Squier's resolution, the overlaps of three rules.
//!
//! # References
//!
//! - `Guiraud-2019-convergent_presentations_polygraphic_resolutions_associative_algebras`
//!   — dependency: § 6.2, Definition 6.2.2 — the critical cells of the
//!   standard resolution, each entry the shortest factor that ends the
//!   rightmost step so far. A critical cell of dimension three is a chain of
//!   three left sides, each overlapping the one before.
//! - `Malbos-2021-completion_operads_essential_syzygies` — background: § 3 — a
//!   critical branching counts once over its orders.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::RootAgreement;
use gandr_theory_cell_complexes::SequentAlphabet;
use quenchant_shape::shape::Maybe;

use crate::overlap::Overlap;
use crate::overlap::interior_overlaps_between;
use crate::overlap::overlap_command;
use crate::overlap::root_overlaps_between;
use crate::rewrite::CellApp;

/// A critical triple: three steps on one peak, which the overlaps of their
/// left-hand sides connect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CriticalTriple<A: CellAlphabet = SequentAlphabet>
{
    /// The term that the three left-hand sides cover.
    pub peak: A::Cmd,
    /// The three steps, in the order of the peak's command positions, and in
    /// the order of their cells at one position. The first stands at the root.
    pub steps: [CellApp<A>; 3],
}

/// The place of a step's position among the command positions of a peak.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Place(usize);

/// The place of each step of a triple among the command positions of its
/// peak, with its cell: the identity of the triple over the orders of its
/// steps.
type TripleKey = [(Place, CellId); 3];

/// The critical triples of `store`, each once.
///
/// The walk takes each critical pair whose left cell stands at the root: a
/// root pair once, with the earlier cell on the left, and each interior pair.
/// It unifies each cell, renamed apart, with each command subterm of the
/// pair's peak that is no lone metavariable. Each unifier gives a triple,
/// unless its third step repeats a step of the pair. The walk skips a triple
/// that an earlier pair gives.
///
/// # Specification
/// - ensures: the first step of each triple stands at the root, its three steps
///   are distinct, and the cell of each step matches the peak at the step's
///   position. No two triples hold the same steps.
/// - panics: none.
/// - intension: the walk unifies each cell with each command subterm of each
///   pair's peak once. The work is cubic in the cells.
///
/// # Adequacy
/// - hypothesis: L3 — three rules at one root give one triple and not six. A
///   rule that overlaps itself twice gives one chain whose outer steps share no
///   node. Two steps apart under one rule give one triple. A triple counted
///   twice, a lost chain or a step at a metavariable changes these counts.
/// - witness: `tests::triple::three_rules_at_one_root_make_one_triple_over_all_orders`
/// - witness: `tests::triple::a_rule_that_overlaps_itself_twice_makes_one_chain`
/// - witness: `tests::triple::two_steps_apart_under_one_rule_make_one_triple`
#[inline]
#[must_use]
#[spec(ensures: |output| output.iter().all(|triple| matches!(triple.steps, [ref first, ref second, ref third]
        if first.at == A::root_position() && first != second && second != third && first != third)
        && triple.steps.iter().all(|step| matches!((store.get(step.cell), A::subterm_cmd_at(&triple.peak, &step.at)),
            (Maybe::Present(cell), Maybe::Present(ref sub)) if bool::from(A::match_cmd(cell.lhs(), sub, &mut A::Subst::default())))))
    && output.iter().enumerate().all(|(index, triple)| output.iter().skip(index.saturating_add(1)).all(|later| later.steps != triple.steps)))]
#[cfg_attr(feature = "hotpath", hotpath::measure)]
pub fn critical_triples<A>(store: &CellStore<A>) -> Vec<CriticalTriple<A>>
where
    A: CellAlphabet,
{
    let cells: Vec<(CellId, &Cell<A>)> = store.iter().collect();
    let mut seen: BTreeSet<TripleKey> = BTreeSet::new();
    let mut out = Vec::new();
    for &left in &cells {
        for &right in &cells {
            let mut pairs = interior_overlaps_between(left, right);
            if left.0 < right.0 {
                pairs.extend(root_overlaps_between(left, right));
            }
            for pair in &pairs {
                for &third in &cells {
                    extend(pair, third, &mut seen, &mut out);
                }
            }
        }
    }
    out
}

/// Each triple that `third` adds to the critical pair `pair`, pushed onto
/// `out` unless `seen` holds its key.
///
/// # Specification
/// trivial.
fn extend<A>(
    pair: &Overlap<A>,
    third: (CellId, &Cell<A>),
    seen: &mut BTreeSet<TripleKey>,
    out: &mut Vec<CriticalTriple<A>>,
) where
    A: CellAlphabet,
{
    let (third_id, third_cell) = third;
    let held = [
        CellApp {
            cell: pair.left,
            at: A::root_position(),
        },
        CellApp {
            cell: pair.right,
            at: pair.seam.clone(),
        },
    ];
    let (lhs, _) = A::rename_apart(
        (&pair.peak, &pair.peak),
        (third_cell.lhs(), third_cell.rhs()),
    );
    for at in A::command_positions(&pair.peak) {
        if held
            .iter()
            .any(|step| step.cell == third_id && step.at == at)
        {
            continue;
        }
        let Some(sub) = overlap_command::<A>(&pair.peak, &at)
        else {
            continue;
        };
        if A::root_agreement(&sub, &lhs) == RootAgreement::Clash {
            continue;
        }
        let mut unifier = A::Subst::default();
        if !bool::from(A::unify_cmd(&sub, &lhs, &mut unifier)) {
            continue;
        }
        let peak = A::apply_subst(&unifier, &pair.peak);
        let positions = A::command_positions(&peak);
        let place = |step: &CellApp<A>| {
            Place(
                positions
                    .iter()
                    .position(|held_at| *held_at == step.at)
                    .unwrap_or(positions.len()),
            )
        };
        let [ref first, ref second] = held;
        let mut steps = [first.clone(), second.clone(), CellApp {
            cell: third_id,
            at,
        }];
        steps.sort_by_key(|step| (place(step), step.cell));
        if seen.insert(steps.each_ref().map(|step| (place(step), step.cell))) {
            out.push(CriticalTriple { peak, steps });
        }
    }
}
