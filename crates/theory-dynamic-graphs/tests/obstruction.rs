//! The potential maintenance's verdicts read as tropical gluing.
//!
//! A system of constraints `value(target) >= value(source) + offset` asks for
//! one value at each node that meets every constraint. The constraint graph is
//! the site of that question. Its nodes are its cells of dimension zero, and
//! its constraints are its cells of dimension one. The coefficients are the
//! max-plus semiring. Two parallel constraints combine by their maximum, and a
//! path combines its offsets by their sum. A valuation that meets every
//! constraint is a global section.
//!
//! A cycle whose max-plus weight is above zero is the obstruction to a global
//! section, because along it a value must exceed itself. The maintenance
//! refuses an offer with such a cycle as its witness. The witness names the
//! cells of the cycle and not their offsets. Thus the weight comes from the
//! constraints that the caller holds.
//!
//! [`glued`] maps each verdict into this reading. An admission maps to a
//! section. A refusal maps to an obstruction, which borrows the cycle of the
//! refusal and copies nothing. The three-offer differential of the standing
//! suite reads every verdict through this map.

use anodized::spec;
use gandr_theory_dynamic_graphs::ConstraintVerdict;
use gandr_theory_dynamic_graphs::Offset;
use gandr_theory_dynamic_graphs::PotentialMaintenance;
use gandr_theory_graphs::CycleWitness;
use gandr_theory_graphs::EdgeId;
use gandr_theory_graphs::NodeId;

/// The max-plus weight of a cycle: along the cycle, the sum of the greatest
/// offset on each edge.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Weight(i64);

impl Weight
{
    /// The unit of the max-plus product: the weight of an empty path.
    pub const UNIT: Self = Self(0);
}

/// An obstruction to a global section: the cells it lives on, and its witness
/// in the coefficients.
#[derive(Debug)]
pub struct Obstruction<'verdict>
{
    /// The cycle of the refusal. Its nodes are cells of dimension zero, and
    /// its edges are cells of dimension one.
    pub cells: &'verdict CycleWitness,
    /// The max-plus weight of the cycle.
    pub weight: Weight,
}

/// The gluing reading of one verdict.
#[derive(Debug)]
pub enum Gluing<'verdict>
{
    /// The constraints glue, and the standing valuation is a global section.
    Section,
    /// The offer closes a cycle, and no global section exists.
    Obstructed(Obstruction<'verdict>),
}

/// The gluing reading of `verdict` over the constraints `held`.
///
/// # Specification
/// - requires: `held` holds every constraint that the maintenance admitted, and
///   the offer it judged.
/// - ensures: an admission maps to a section. A refusal maps to an obstruction
///   whose cells equal the refusal's own cycle. The lifetime `'verdict` makes
///   the obstruction borrow that cycle.
/// - panics: when an edge of the cycle carries no constraint of `held`, or when
///   the weight leaves the range of `i64`.
/// - intension: one scan of `held` for each edge of the cycle. The obstruction
///   copies nothing of the cycle.
///
/// # Adequacy
/// - hypothesis: L2 — the three-offer differential checks each obstruction
///   against an independent relaxation, and each section against every admitted
///   constraint. L3 — two parallel constraints decide the weight by their
///   maximum, so a weight read by the minimum is not above zero there.
/// - witness: `tests::standing::three_offer_systems_agree_with_independent_relaxation`
/// - witness: `tests::obstruction::parallel_constraints_weigh_by_their_maximum`
#[spec(ensures: |output| match *verdict {
    ConstraintVerdict::Satisfied | ConstraintVerdict::SatisfiedAfterRaise => matches!(output, Gluing::Section),
    ConstraintVerdict::Refuted(ref cycle) => matches!(output, Gluing::Obstructed(ref obstruction) if obstruction.cells == cycle),
})]
pub fn glued<'verdict>(
    verdict: &'verdict ConstraintVerdict,
    held: &[(EdgeId, Offset)],
) -> Gluing<'verdict>
{
    match *verdict {
        ConstraintVerdict::Satisfied | ConstraintVerdict::SatisfiedAfterRaise => Gluing::Section,
        ConstraintVerdict::Refuted(ref cycle) => {
            let mut weight = Weight::UNIT;
            for edge in &cycle.edges {
                let greatest = held
                    .iter()
                    .filter(|&&(candidate, _)| candidate == *edge)
                    .map(|&(_, offset)| i64::from(offset))
                    .max()
                    .expect("each edge of the cycle carries a held constraint");
                weight = Weight(
                    weight
                        .0
                        .checked_add(greatest)
                        .expect("the weight stays in range"),
                );
            }
            Gluing::Obstructed(Obstruction {
                cells: cycle,
                weight,
            })
        },
    }
}

#[test]
fn parallel_constraints_weigh_by_their_maximum()
{
    let [first, second] = [0_u32, 1].map(NodeId::from);
    let mut system = PotentialMaintenance::new();
    let mut held = Vec::new();
    for (edge, offset) in [
        (EdgeId::new(first, second), Offset::from(1_i64)),
        (EdgeId::new(first, second), Offset::from(-1_i64)),
        (EdgeId::new(second, first), Offset::from(0_i64)),
    ] {
        held.push((edge, offset));
        let verdict = system
            .insert_constraint(edge, offset)
            .expect("small offsets fit");
        if let Gluing::Obstructed(obstruction) = glued(&verdict, &held) {
            assert_eq!(
                obstruction.weight,
                Weight(1),
                "the cycle reads the greater of the two parallel offsets"
            );
            return;
        }
    }
    panic!("the third offer closes a cycle of weight one")
}
