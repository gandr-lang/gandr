//! The level solver's refusal on the diagnostics model's obstruction shape.
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
//! section, because along it a value must exceed itself. The potential
//! maintenance refuses an offer with such a cycle as its witness. The witness
//! names the cells of the cycle and not their offsets. Thus the weight comes
//! from the constraints that the caller holds.
//!
//! [`glued`] maps each verdict into this reading. An admission maps to a
//! section. A refusal fills the model's [`Obstruction`]: its cells are the
//! refused cycle, borrowed, and its witness is the cycle's weight. A parting
//! pair of completion fills the same shape, so one shape serves two analyses.
//! No checker path runs the potential maintenance, so this suite holds the
//! filling.

use anodized::spec;
use gandr_surface_diagnostics::Obstruction;
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

/// The level solver's obstruction: the refused cycle as its cells, and the
/// cycle's max-plus weight as its witness.
pub type PositiveCycle<'verdict> = Obstruction<&'verdict CycleWitness, Weight>;

/// The gluing reading of one verdict.
#[derive(Debug)]
pub enum Gluing<'verdict>
{
    /// The constraints glue, and the standing valuation is a global section.
    Section,
    /// The offer closes a cycle, and no global section exists.
    Obstructed(PositiveCycle<'verdict>),
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
/// - hypothesis: L2 — every refusal of every three-offer system fills the shape
///   with its own cycle and a weight above zero, and every admission reads as a
///   section. L3 — two parallel constraints decide the weight by their maximum,
///   so a weight read by the minimum is not above zero there.
/// - witness: `tests::obstruction::every_three_offer_refusal_fills_the_shape_with_its_cycle`
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
                witness: weight,
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
                obstruction.witness,
                Weight(1),
                "the cycle reads the greater of the two parallel offsets"
            );
            return;
        }
    }
    panic!("the third offer closes a cycle of weight one")
}

#[test]
fn every_three_offer_refusal_fills_the_shape_with_its_cycle()
{
    let nodes = [0_u32, 1, 2].map(NodeId::from);
    let mut catalog = Vec::new();
    for source in nodes {
        for target in nodes {
            for offset in [-1_i64, 0, 1] {
                catalog.push((EdgeId::new(source, target), Offset::from(offset)));
            }
        }
    }
    let mut admitted = Vec::with_capacity(3);
    for &first in &catalog {
        for &second in &catalog {
            for &third in &catalog {
                let mut system = PotentialMaintenance::new();
                system
                    .insert_constraint(EdgeId::new(nodes[2], nodes[2]), Offset::from(0_i64))
                    .expect("create the complete fixture domain");
                admitted.clear();
                for offer in [first, second, third] {
                    admitted.push(offer);
                    let verdict = system
                        .insert_constraint(offer.0, offer.1)
                        .expect("bounded fixture values fit");
                    match (&verdict, glued(&verdict, &admitted)) {
                        (
                            &ConstraintVerdict::Refuted(ref cycle),
                            Gluing::Obstructed(obstruction),
                        ) => {
                            assert!(
                                core::ptr::eq(
                                    core::ptr::from_ref(obstruction.cells),
                                    core::ptr::from_ref(cycle)
                                ),
                                "{admitted:?}: the shape borrows the refusal's own cycle"
                            );
                            assert!(
                                obstruction.witness > Weight::UNIT,
                                "{admitted:?}: {cycle:?} weighs above zero"
                            );
                            admitted.pop();
                        },
                        (
                            &(ConstraintVerdict::Satisfied
                            | ConstraintVerdict::SatisfiedAfterRaise),
                            Gluing::Section,
                        ) => {},
                        (_, gluing) => {
                            panic!("{admitted:?}: {verdict:?} reads as {gluing:?}")
                        },
                    }
                }
            }
        }
    }
}
