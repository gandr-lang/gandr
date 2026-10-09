//! The convexity supply point, driven by a store that withholds its
//! discharge.
//!
//! The adversary alphabet is the toy one with its convexity discharge
//! withheld, so the shift guard refuses every pair it cannot cover and the
//! instantiation site must ask the caller's re-check. The cells and the body
//! are the `cong2` ones the discharged suites earn a witness with, so the only
//! thing that changed is who answers the third conjunct.
//!
//! - `a_withheld_discharge_is_rechecked_by_the_supply_point` is the grant: the
//!   supply point is asked about exactly the record's pair, and its warrant
//!   comes back beside a witness that still names the store's withheld
//!   discharge.
//! - `a_refused_recheck_refuses_the_instantiation_with_its_evidence` is the
//!   refusal, carried verbatim.
//! - `the_supply_point_is_asked_only_after_the_positions_and_overlap_conjuncts`
//!   pins the order: a nested pair and an overlapping pair are refused by the
//!   guard before a refusing supply point could answer.

use core::convert::Infallible;

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes_tools::Lying;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::WithheldConvexity;
use gandr_theory_cell_complexes_tools::lying_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_computads::CircuitShiftObstruction;
use gandr_theory_computads::ConvexityGrant;
use gandr_theory_computads::ConvexitySupply;
use gandr_theory_computads::RewriteBinding;
use gandr_theory_computads::instantiate_two_redex_rule;
use gandr_theory_deep_inference::ShiftObstruction;

use crate::fixture::Asked;
use crate::fixture::RefusingSupply;
use crate::fixture::add_s_faces;
use crate::fixture::add_z_faces;
use crate::fixture::cong2_peak;
use crate::fixture::cong2_rule;
use crate::fixture::f_faces;
use crate::fixture::g_faces;
use crate::fixture::run;
use crate::fixture::sequential_rule;

/// The adversary alphabet: the toy alphabet with its discharge withheld.
type Withheld = Lying<WithheldConvexity>;

/// A supply point that grants every pair, with the pair it was asked about as
/// its warrant.
struct GrantingSupply;

/// The warrant `GrantingSupply` answers with: the pair it swept.
#[derive(Clone, Debug, Eq, PartialEq)]
struct SweptPair<A>
where
    A: CellAlphabet,
{
    /// The first application it was asked about.
    first: CellApp<A>,
    /// The second application it was asked about.
    second: CellApp<A>,
}

impl<A> ConvexitySupply<A> for GrantingSupply
where
    A: CellAlphabet,
{
    type Refusal = Infallible;
    type Warrant = SweptPair<A>;

    /// Grants, naming the pair.
    ///
    /// # Specification
    /// trivial.
    fn recheck(
        &self,
        _store: &CellStore<A>,
        _peak: &A::Cmd,
        first: &CellApp<A>,
        second: &CellApp<A>,
    ) -> Result<SweptPair<A>, Infallible>
    {
        Ok(SweptPair {
            first: first.clone(),
            second: second.clone(),
        })
    }
}

/// A withheld store holding `f` and `g`, with their identifiers.
///
/// # Specification
/// trivial.
fn withheld_cong2_store() -> (
    CellStore<Withheld>,
    gandr_theory_cell_complexes::CellId,
    gandr_theory_cell_complexes::CellId,
)
{
    let (f_lhs, f_rhs) = f_faces();
    let (g_lhs, g_rhs) = g_faces();
    let mut store = CellStore::new();
    let f = store.insert(lying_cell(f_lhs, f_rhs));
    let g = store.insert(lying_cell(g_lhs, g_rhs));
    (store, f, g)
}

#[test]
fn a_withheld_discharge_is_rechecked_by_the_supply_point()
{
    let (store, f, g) = withheld_cong2_store();
    let shift = instantiate_two_redex_rule(
        &store,
        &cong2_rule(),
        &[RewriteBinding::new("p", f), RewriteBinding::new("q", g)],
        &cong2_peak(),
        &GrantingSupply,
    )
    .expect("the supply point grants the conjunct the store withheld");
    assert_eq!(
        ConvexityGrant::Rechecked(SweptPair {
            first: CellApp {
                cell: f,
                at: at![0],
            },
            second: CellApp {
                cell: g,
                at: at![1],
            },
        }),
        shift.convexity,
        "the supply point was asked about exactly the record's pair, and its warrant came back"
    );
    assert_eq!(
        ConvexityDischarge::ReCheckRequired,
        shift.witness.convexity,
        "the witness still names the store's own discharge, which was withheld"
    );
    assert_eq!(
        Toy::add(Toy::zero(), Toy::zero()),
        shift.witness.joins_at,
        "both sequentializations reach one composite"
    );
    assert_eq!(
        (
            shift.witness.joins_at.clone(),
            shift.witness.joins_at.clone()
        ),
        (
            run(&store, &cong2_peak(), &shift.witness.first_then_second()),
            run(&store, &cong2_peak(), &shift.witness.second_then_first())
        ),
        "and running either order by hand lands on it"
    );
}

#[test]
fn a_refused_recheck_refuses_the_instantiation_with_its_evidence()
{
    let (store, f, g) = withheld_cong2_store();
    assert_eq!(
        Err(CircuitShiftObstruction::NotConvex(Asked)),
        instantiate_two_redex_rule(
            &store,
            &cong2_rule(),
            &[RewriteBinding::new("p", f), RewriteBinding::new("q", g)],
            &cong2_peak(),
            &RefusingSupply,
        ),
        "the supply point's refusal is the instantiation's, carried verbatim"
    );
}

#[test]
fn the_supply_point_is_asked_only_after_the_positions_and_overlap_conjuncts()
{
    let (store, f, g) = withheld_cong2_store();
    assert_eq!(
        Err(CircuitShiftObstruction::Refused(Box::new(
            ShiftObstruction::ComparablePositions {
                order: PositionOrder::Same,
            }
        ))),
        instantiate_two_redex_rule(
            &store,
            &sequential_rule(),
            &[RewriteBinding::new("p", f), RewriteBinding::new("q", g)],
            &cong2_peak(),
            &RefusingSupply,
        ),
        "a nested pair is refused its positions before the supply point is asked"
    );

    let (z_lhs, z_rhs) = add_z_faces();
    let (s_lhs, s_rhs) = add_s_faces();
    let mut overlapping: CellStore<Withheld> = CellStore::new();
    let z = overlapping.insert(lying_cell(z_lhs, z_rhs));
    let s = overlapping.insert(lying_cell(s_lhs, s_rhs));
    let peak = Toy::add(
        Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
        Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
    );
    let refusal = instantiate_two_redex_rule(
        &overlapping,
        &cong2_rule(),
        &[RewriteBinding::new("p", z), RewriteBinding::new("q", s)],
        &peak,
        &RefusingSupply,
    )
    .expect_err("an overlapping pair is refused");
    assert!(
        matches!(
            refusal,
            CircuitShiftObstruction::Refused(ref obstruction)
                if matches!(**obstruction, ShiftObstruction::GenuineOverlap { .. })
        ),
        "and an overlapping pair its overlap, before the supply point is asked: {refusal:?}"
    );
}
