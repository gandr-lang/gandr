//! One coinductive engine for equivalence and directional subtyping.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use crate::Label;
use crate::Node;
use crate::NodeId;
use crate::Session;
use crate::TypeError;

/// The relation imposed on each pair of endpoint states.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Relation
{
    /// Bisimilarity up to recursive unfolding.
    Equivalent,
    /// Left endpoint substitutes for right: fewer selections, more offers.
    Subtype,
}

/// Whether all reachable coinductive obligations hold.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Decision
{
    /// The root pair belongs to the greatest fixpoint.
    Related,
    /// Some required reachable action, payload, or branch disagrees.
    Unrelated,
}

/// Decide equivalence or left-to-right subtyping with one visited-pair engine.
///
/// # Specification
/// - ensures: equivalence matches actions, payload identities, label sets, and
///   continuations up to unfolding; subtyping admits fewer selections and more
///   offers on the left, with invariant opaque payload identities.
/// - provides: a decision, not a replayable kernel certificate.
/// - fails: broken internal arena references retain their construction error.
/// - panics: none.
///
/// # Errors
/// Returns [`TypeError`] only for a broken internal session invariant.
///
/// # Adequacy
/// - hypothesis: L2 bounded generated protocols are checked against independent
///   finite greatest-fixpoint elimination; L3 width, continuation, payload, and
///   one-unfold near-misses distinguish directional and recursive errors.
/// - witness: `tests::relations::generated_relations_match_finite_oracle`
/// - witness: `tests::relations::unfolded_recursive_types_are_equivalent`
/// - witness: `tests::relations::choice_width_and_continuations_are_directional`
#[inline]
pub fn decide(
    left: &Session,
    right: &Session,
    relation: Relation,
) -> Result<Decision, TypeError>
{
    let result = relate(left, right, relation)?;
    Ok(match result {
        | RelationResult::Related(_) => Decision::Related,
        | RelationResult::Unrelated => Decision::Unrelated,
    })
}

/// The engine's untrusted finite witness or its negative decision.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RelationResult
{
    /// Candidate data; only independent kernel replay establishes evidence.
    Related(gandr_kernel_term::session::Evidence),
    /// Some required local obligation fails.
    Unrelated,
}

/// Produce the finite root-reachable relation used by the decision engine.
///
/// # Specification
/// - ensures: Related contains every visited observable pair and preserves the
///   chosen width direction; no kernel verdict is carried.
/// - fails: broken session references retain their construction error.
/// - panics: none.
///
/// # Errors
/// An internal `TypeError`.
///
/// # Adequacy
/// - hypothesis: L1 independent kernel replay accepts generated pairs and
///   refuses deleted pairs, wrong orientation and inequivalent codes.
/// - witness: `tests::certified::seat_and_generator_identity_witnesses`
#[inline]
pub fn relate(
    left: &Session,
    right: &Session,
    relation: Relation,
) -> Result<RelationResult, TypeError>
{
    let mut visited = BTreeSet::new();
    let mut pending = alloc::vec![(left.root(), right.root())];
    while let Some((left_id, right_id)) = pending.pop() {
        let (left_id, left_node) = left.head(left_id)?;
        let (right_id, right_node) = right.head(right_id)?;
        if !visited.insert(gandr_kernel_term::session::StatePair {
            source: gandr_kernel_term::session::State(left_id.0),
            target: gandr_kernel_term::session::State(right_id.0),
        }) {
            continue;
        }
        match (left_node, right_node) {
            | (&Node::End, &Node::End) => {},
            | (&Node::Send(a, next_a), &Node::Send(b, next_b))
            | (&Node::Receive(a, next_a), &Node::Receive(b, next_b))
                if a == b =>
            {
                pending.push((next_a, next_b));
            },
            | (&Node::Select(ref a), &Node::Select(ref b)) => {
                if branches(a, b, relation, Orientation::Forward, &mut pending)
                    == Decision::Unrelated
                {
                    return Ok(RelationResult::Unrelated);
                }
            },
            | (&Node::Offer(ref a), &Node::Offer(ref b)) => {
                if branches(b, a, relation, Orientation::Reverse, &mut pending)
                    == Decision::Unrelated
                {
                    return Ok(RelationResult::Unrelated);
                }
            },
            | _ => return Ok(RelationResult::Unrelated),
        }
    }
    Ok(RelationResult::Related(
        gandr_kernel_term::session::Evidence {
            pairs: visited,
            payloads: Vec::new(),
        },
    ))
}

/// Decide duality by comparing against exactly one dual transformation.
///
/// # Specification
/// - ensures: returns equivalence of `left` and `right.dual()`.
/// - fails: broken internal arena references retain their construction error.
/// - panics: none.
///
/// # Errors
/// Returns [`TypeError`] only for a broken internal session invariant.
///
/// # Adequacy
/// - hypothesis: L2 separately authored generator and seat duals distinguish
///   directional mistakes; generated L3 payload mismatches reject false duals.
/// - witness: `tests::protocols::generator_duality_and_two_yields`
/// - witness: `tests::protocols::seat_duality_report_and_handoff`
/// - witness: `tests::relations::generated_relations_match_finite_oracle`
#[inline]
pub fn duality(
    left: &Session,
    right: &Session,
) -> Result<Decision, TypeError>
{
    decide(left, &right.dual(), Relation::Equivalent)
}

/// Restore the original endpoint ordering after checking label inclusion.
#[derive(Clone, Copy, Debug)]
enum Orientation
{
    /// The subset belongs to the left endpoint.
    Forward,
    /// The subset belongs to the right endpoint.
    Reverse,
}

/// Check label inclusion and enqueue continuations in endpoint order.
///
/// # Specification
/// - ensures: every subset label exists in the superset; equivalence also
///   requires equal cardinality; continuations retain left-to-right direction.
/// - provides: `Unrelated` on missing labels or unequal equivalence widths.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 nested choices distinguish width reversal from the separate
///   obligation to preserve direction inside matched continuations.
/// - witness: `tests::relations::choice_width_and_continuations_are_directional`
fn branches(
    subset: &BTreeMap<Label, NodeId>,
    superset: &BTreeMap<Label, NodeId>,
    relation: Relation,
    orientation: Orientation,
    pending: &mut Vec<(NodeId, NodeId)>,
) -> Decision
{
    if relation == Relation::Equivalent && subset.len() != superset.len() {
        return Decision::Unrelated;
    }
    for (label, &sub) in subset {
        let Some(&sup) = superset.get(label)
        else {
            return Decision::Unrelated;
        };
        pending.push(match orientation {
            | Orientation::Forward => (sub, sup),
            | Orientation::Reverse => (sup, sub),
        });
    }
    Decision::Related
}
