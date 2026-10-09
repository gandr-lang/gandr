//! Law 2, multicategorical cell composition: up to replay-equivalence.
//!
//! On the stand-in cells, grafting is unital and associative up to replay,
//! and symbolic grafting agrees with replay-level composition wherever it is
//! defined. Where a shape is unsupported symbolically, `graft` declines and
//! replay-level composition still carries the composite.

use alloc::sync::Arc;

use quenchant_shape::shape::Maybe;

use crate::support::NumeralCount;
use crate::vdc_dictionary::fixtures::gen_x;
use crate::vdc_dictionary::fixtures::ident_cell;
use crate::vdc_dictionary::fixtures::loose_of;
use crate::vdc_dictionary::fixtures::nat;
use crate::vdc_dictionary::fixtures::relabel_cell;
use crate::vdc_dictionary::fixtures::single_input_corpus;
use crate::vdc_dictionary::fixtures::succ;
use crate::vdc_dictionary::fixtures::unary_relation;
use crate::vdc_dictionary::fixtures::var;
use crate::vdc_dictionary::harness::Cell;
use crate::vdc_dictionary::harness::CellKind;
use crate::vdc_dictionary::harness::cells_equal;
use crate::vdc_dictionary::harness::graft;
use crate::vdc_dictionary::harness::replay;
use crate::vdc_dictionary::harness::replay_compose;

/// The graft of `inners` into `outer`, which the caller knows is supported.
///
/// # Specification
/// - requires: the shapes are supported symbolically.
/// - panics: otherwise, a test-author error.
fn grafted(
    outer: &Cell,
    inners: &[Cell],
) -> Cell
{
    let Maybe::Present(cell) = graft(outer, inners)
    else {
        panic!("the graft shape is supported symbolically");
    };
    cell
}

/// The clause-cell chain `A : R⇒S`, `B : S⇒T`, `C : T⇒U`, where `A`
/// relabels identically and `B`, `C` each wrap the payload in a `Succ`.
///
/// # Specification
/// trivial.
fn chain() -> (Cell, Cell, Cell)
{
    let rel_r = unary_relation("R".into());
    let rel_s = unary_relation("S".into());
    let rel_t = unary_relation("T".into());
    let rel_u = unary_relation("U".into());
    let a = relabel_cell(rel_r, Arc::clone(&rel_s), var("p0.x".into()));
    let b = relabel_cell(rel_s, Arc::clone(&rel_t), succ(var("p0.x".into())));
    let c = relabel_cell(rel_t, rel_u, succ(var("p0.x".into())));
    (a, b, c)
}

#[test]
fn grafting_is_unital_up_to_replay()
{
    let (a, ..) = chain();
    let corpus = single_input_corpus();

    // graft(μ, [id]) ≡ μ
    let identity_inner = ident_cell(loose_of(unary_relation("R".into())));
    let right_unit = grafted(&a, &[identity_inner]);
    assert!(
        bool::from(cells_equal(&right_unit, &a, &corpus)),
        "graft(μ, [id]) ≡ μ up to replay"
    );

    // graft(id, [μ]) ≡ μ
    let identity_outer = ident_cell(loose_of(unary_relation("S".into())));
    let left_unit = grafted(&identity_outer, core::slice::from_ref(&a));
    assert!(
        bool::from(cells_equal(&left_unit, &a, &corpus)),
        "graft(id, [μ]) ≡ μ up to replay"
    );
}

#[test]
fn grafting_is_associative_up_to_replay()
{
    let (a, b, c) = chain();
    let corpus = single_input_corpus();

    // (C∘B)∘A
    let c_after_b = grafted(&c, core::slice::from_ref(&b));
    let left = grafted(&c_after_b, core::slice::from_ref(&a));
    // C∘(B∘A)
    let b_after_a = grafted(&b, core::slice::from_ref(&a));
    let right = grafted(&c, &[b_after_a]);

    assert!(
        bool::from(cells_equal(&left, &right, &corpus)),
        "(C∘B)∘A ≡ C∘(B∘A) up to replay"
    );
}

#[test]
fn symbolic_graft_agrees_with_replay_composition()
{
    let (_a, b, c) = chain();
    let composite = grafted(&c, core::slice::from_ref(&b));
    for k in 0 ..= 5_usize {
        let input = vec![gen_x(nat(NumeralCount::from(k)))];
        let symbolic = replay(&composite, &input);
        let staged = replay_compose(&c, &[&b], core::slice::from_ref(&input));
        assert_eq!(
            symbolic, staged,
            "replay(graft(C, [B])) = replay(C)(replay(B)) at input {k}"
        );
    }
    // A non-degenerate composite: the wrapping actually fires.
    let Maybe::Present(witness) = replay(&composite, &[gen_x(nat(NumeralCount::from(1_usize)))])
    else {
        panic!("the composite fires");
    };
    assert_eq!(
        1,
        witness.per_factor.len(),
        "the composite emits one factor"
    );
}

#[test]
fn unsupported_shapes_decline_symbolically_but_replay_composes()
{
    // A pairing outer is not a supported symbolic-graft shape: graft
    // declines, and replay-level composition still carries the composite.
    let (a, b, _c) = chain();
    let pair = Cell {
        dom: a.dom.clone(),
        cod: a.cod.clone(),
        left_frame: a.left_frame.clone(),
        right_frame: a.right_frame.clone(),
        kind: CellKind::pair(&a, &a),
    };
    assert!(
        matches!(graft(&pair, core::slice::from_ref(&b)), Maybe::Absent(_)),
        "grafting into a pairing outer is unsupported symbolically"
    );
    // Replay-level composition is always available.
    let staged = replay_compose(&pair, &[&b], &[vec![gen_x(nat(NumeralCount::from(
        0_usize,
    )))]]);
    assert!(
        matches!(staged, Maybe::Present(_)),
        "replay-level composition still carries it"
    );
}
