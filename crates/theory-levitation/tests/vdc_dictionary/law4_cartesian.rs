//! Law 4, cartesian structure in the split form.
//!
//! The local `⊤` and `∧` strict laws are Law 3's. Here: the pairing and
//! projection bijection up to replay (`⋄` is replay-level composition), a
//! uniqueness spot-check bounded to pair-shaped cells, the unique cell into
//! `⊤`, and products preserved by restriction (strictly, plus a replay
//! spot-check).

use quenchant_shape::shape::Maybe;

use crate::support::DescriptorFactorIndex;
use crate::support::NumeralCount;
use crate::vdc_dictionary::fixtures::gen_x;
use crate::vdc_dictionary::fixtures::loose_of;
use crate::vdc_dictionary::fixtures::nat;
use crate::vdc_dictionary::fixtures::nat_sig;
use crate::vdc_dictionary::fixtures::relabel_cell;
use crate::vdc_dictionary::fixtures::single_input_corpus;
use crate::vdc_dictionary::fixtures::succ;
use crate::vdc_dictionary::fixtures::unary_relation;
use crate::vdc_dictionary::fixtures::var;
use crate::vdc_dictionary::harness::Cell;
use crate::vdc_dictionary::harness::CellKind;
use crate::vdc_dictionary::harness::LooseArrow;
use crate::vdc_dictionary::harness::LooseInstance;
use crate::vdc_dictionary::harness::SigMorphism;
use crate::vdc_dictionary::harness::cells_equal;
use crate::vdc_dictionary::harness::loose_instance_eq;
use crate::vdc_dictionary::harness::replay;
use crate::vdc_dictionary::harness::replay_compose;
use crate::vdc_dictionary::harness::restrict;

/// The pair `μ : R⇒S`, `ν : R⇒T`, and `⟨μ, ν⟩ : R⇒S∧T`.
///
/// # Specification
/// trivial.
fn pair_fixture() -> (Cell, Cell, Cell)
{
    let r = unary_relation("R".into());
    let mu = relabel_cell(
        alloc::sync::Arc::clone(&r),
        unary_relation("S".into()),
        var("p0.x".into()),
    );
    let nu = relabel_cell(r, unary_relation("T".into()), succ(var("p0.x".into())));
    let paired = Cell {
        dom: mu.dom.clone(),
        cod: LooseArrow::meet(&mu.cod, &nu.cod),
        left_frame: SigMorphism::identity(&nat_sig()),
        right_frame: SigMorphism::identity(&nat_sig()),
        kind: CellKind::pair(&mu, &nu),
    };
    (mu, nu, paired)
}

/// A projection cell onto codomain factor `idx`.
///
/// # Specification
/// trivial.
fn proj_cell(
    loose: LooseArrow,
    idx: DescriptorFactorIndex,
) -> Cell
{
    Cell {
        dom: vec![loose.clone()],
        cod: loose,
        left_frame: SigMorphism::identity(&nat_sig()),
        right_frame: SigMorphism::identity(&nat_sig()),
        kind: CellKind::proj(idx),
    }
}

#[test]
fn pairing_is_unique_up_to_replay_on_pair_shaped_cells()
{
    // A ρ built as a pair whose projections replay-equal μ and ν is
    // replay-equal to ⟨μ, ν⟩. The scope is bounded to pair-shaped ρ.
    let (mu, nu, paired) = pair_fixture();
    let rho = Cell {
        dom: mu.dom.clone(),
        cod: paired.cod.clone(),
        left_frame: SigMorphism::identity(&nat_sig()),
        right_frame: SigMorphism::identity(&nat_sig()),
        kind: CellKind::pair(&mu, &nu),
    };
    let proj0 = proj_cell(paired.cod.clone(), DescriptorFactorIndex::from(0_usize));
    let proj1 = proj_cell(paired.cod.clone(), DescriptorFactorIndex::from(1_usize));
    let corpus = single_input_corpus();
    // Premises: the projections of ρ match μ and ν.
    for input in &corpus {
        let p0 = replay_compose(&proj0, &[&rho], core::slice::from_ref(input));
        assert_eq!(p0, replay(&mu, input), "π₀ ⋄ ρ = μ");
        let p1 = replay_compose(&proj1, &[&rho], core::slice::from_ref(input));
        assert_eq!(p1, replay(&nu, input), "π₁ ⋄ ρ = ν");
    }
    // Conclusion.
    assert!(
        bool::from(cells_equal(&rho, &paired, &corpus)),
        "ρ ≡ ⟨μ, ν⟩ up to replay"
    );
}

#[test]
fn projection_pairing_bijection_holds_up_to_replay()
{
    let (mu, nu, paired) = pair_fixture();
    let proj0 = proj_cell(paired.cod.clone(), DescriptorFactorIndex::from(0_usize));
    let proj1 = proj_cell(paired.cod.clone(), DescriptorFactorIndex::from(1_usize));
    for k in 0 ..= 5_usize {
        let input = vec![gen_x(nat(NumeralCount::from(k)))];
        // π₀ ⋄ ⟨μ, ν⟩ ≡ μ
        let left0 = replay_compose(&proj0, &[&paired], core::slice::from_ref(&input));
        let right0 = replay(&mu, &input);
        assert_eq!(left0, right0, "π₀ ⋄ ⟨μ, ν⟩ = μ at input {k}");
        // π₁ ⋄ ⟨μ, ν⟩ ≡ ν
        let left1 = replay_compose(&proj1, &[&paired], core::slice::from_ref(&input));
        let right1 = replay(&nu, &input);
        assert_eq!(left1, right1, "π₁ ⋄ ⟨μ, ν⟩ = ν at input {k}");
    }
}

#[test]
fn products_are_preserved_by_restriction()
{
    let (_mu, _nu, paired) = pair_fixture();
    // Strict: restriction maps over the product codomain's factors.
    let s = SigMorphism::identity(&nat_sig());
    let t = SigMorphism::identity(&nat_sig());
    assert_eq!(
        restrict(&paired.cod, &s, &t).factors.len(),
        paired.cod.factors.len(),
        "restriction preserves the product's factor count"
    );
    // Replay spot-check: a pair replay has both factors, recoverable by
    // projection.
    let Maybe::Present(output) = replay(&paired, &[gen_x(nat(NumeralCount::from(2_usize)))])
    else {
        panic!("the pair fires");
    };
    assert_eq!(
        2,
        output.per_factor.len(),
        "the product has both factors at replay"
    );
    let first = LooseInstance {
        per_factor: vec![output.per_factor[0].clone()],
    };
    let proj0 = proj_cell(paired.cod, DescriptorFactorIndex::from(0_usize));
    let Maybe::Present(projected) = replay(&proj0, &[output])
    else {
        panic!("the projection fires");
    };
    assert!(
        bool::from(loose_instance_eq(&projected, &first)),
        "π₀ recovers the first factor"
    );
}

#[test]
fn the_cell_into_top_is_unique()
{
    let loose = loose_of(unary_relation("R".into()));
    let bang_one = Cell {
        dom: vec![loose],
        cod: LooseArrow::top(&nat_sig(), &nat_sig()),
        left_frame: SigMorphism::identity(&nat_sig()),
        right_frame: SigMorphism::identity(&nat_sig()),
        kind: CellKind::bang(),
    };
    let bang_two = Cell {
        kind: CellKind::bang(),
        ..bang_one.clone()
    };
    let corpus = single_input_corpus();
    assert!(
        bool::from(cells_equal(&bang_one, &bang_two, &corpus)),
        "any two cells into ⊤ agree"
    );
    let empty = LooseInstance {
        per_factor: Vec::new(),
    };
    assert_eq!(
        replay(&bang_one, &[gen_x(nat(NumeralCount::from(0_usize)))]),
        Maybe::Present(empty),
        "the cell into ⊤ produces the empty (terminal) instance"
    );
}
