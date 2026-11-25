//! Law 5, units: path-relation cell induction. Partial, and the informative
//! law.
//!
//! Path formation is real — the bounded rewriter over the `plus` and
//! `double` rules — and path induction satisfies its β-rule on `refl`. On a
//! non-empty path the raw induction declines: the base cell's shared middle
//! variable needs the chain's endpoints to meet, and no generating instance
//! absorbs a path between them. The decline locates an obligation on a cell
//! store: for the unit's universal property to be bijective, instances must
//! be closed under path action, a saturation invariant (instances as modules
//! over the rewrite-path relation). The saturation probe shows that with
//! path absorption the induced value is defined and β-compatible, so the
//! invariant is sufficient, not merely necessary.

use anodized::spec;
use gandr_theory_levitation::FreeTerm;
use quenchant_shape::shape::Maybe;

use crate::support::GeneratorIndex;
use crate::support::NumeralCount;
use crate::support::RewriteDepth;
use crate::vdc_dictionary::fixtures::gen_x;
use crate::vdc_dictionary::fixtures::loose_of;
use crate::vdc_dictionary::fixtures::nat;
use crate::vdc_dictionary::fixtures::nat_desc;
use crate::vdc_dictionary::fixtures::nat_sig;
use crate::vdc_dictionary::fixtures::succ;
use crate::vdc_dictionary::fixtures::unary_relation;
use crate::vdc_dictionary::fixtures::var;
use crate::vdc_dictionary::fixtures::zero;
use crate::vdc_dictionary::harness::BaseInstance;
use crate::vdc_dictionary::harness::Cell;
use crate::vdc_dictionary::harness::CellClause;
use crate::vdc_dictionary::harness::CellKind;
use crate::vdc_dictionary::harness::LooseArrow;
use crate::vdc_dictionary::harness::LooseInstance;
use crate::vdc_dictionary::harness::SaturatedInstance;
use crate::vdc_dictionary::harness::SigMorphism;
use crate::vdc_dictionary::harness::cells_equal;
use crate::vdc_dictionary::harness::replay;
use crate::vdc_dictionary::harness::replay_outcome;
use crate::vdc_dictionary::harness::replay_path_ind_saturated;
use crate::vdc_dictionary::terms::Binding;
use crate::vdc_dictionary::terms::RewritePath;
use crate::vdc_dictionary::terms::apply_path;
use crate::vdc_dictionary::terms::enumerate_paths;

/// A two-input base cell `(a, b) ↦ S`: generator `0` matched at both
/// inputs, generator `0` emitted with `x` bound by the template (over
/// `p0.x`) and `y` bound to `p1.x`.
///
/// # Specification
/// trivial.
fn base_cell(template_for_x: FreeTerm) -> Cell
{
    let emit_templates: Binding = [
        ("x".into(), template_for_x),
        ("y".into(), var("p1.x".into())),
    ]
    .into_iter()
    .collect();
    Cell {
        dom: vec![
            loose_of(unary_relation("A".into())),
            loose_of(unary_relation("B".into())),
        ],
        cod: loose_of(unary_relation("S".into())),
        left_frame: SigMorphism::identity(&nat_sig()),
        right_frame: SigMorphism::identity(&nat_sig()),
        kind: CellKind::clauses(vec![CellClause {
            matches: vec![GeneratorIndex::from(0_usize), GeneratorIndex::from(0_usize)],
            emit: vec![(GeneratorIndex::from(0_usize), emit_templates)],
        }]),
    }
}

/// A path-induction cell over the given base, with domain `[A, path, B]`.
///
/// # Specification
/// trivial.
fn path_ind_cell(base: &Cell) -> Cell
{
    Cell {
        dom: vec![
            loose_of(unary_relation("A".into())),
            LooseArrow::path(&nat_sig()),
            loose_of(unary_relation("B".into())),
        ],
        cod: loose_of(unary_relation("S".into())),
        left_frame: SigMorphism::identity(&nat_sig()),
        right_frame: SigMorphism::identity(&nat_sig()),
        kind: CellKind::path_ind(base),
    }
}

/// A `refl` path instance at `start`.
///
/// # Specification
/// trivial.
fn refl(start: FreeTerm) -> LooseInstance
{
    LooseInstance {
        per_factor: vec![BaseInstance::Path {
            start,
            steps: Vec::new(),
        }],
    }
}

/// The first non-empty path among `paths`.
///
/// # Specification
/// - requires: some path is non-empty.
/// - ensures: the result is non-empty.
/// - panics: otherwise, a fixture error.
///
/// # Adequacy
/// - hypothesis: L3 — a reflexive prefix followed by paths of different lengths
///   exposes the first nonempty result; empty and all-reflexive corpora panic.
///   These observations reject choosing the last path, keeping a reflexive
///   prefix or silently manufacturing a path; rewrite validity belongs to the
///   enumerator.
/// - witness: `tests::vdc_dictionary::law5_units::first_nonempty_preserves_enumeration_order_and_refuses_empty_corpora`
#[spec(requires: paths.iter().any(|path| !path.0.is_empty()), ensures: |ref path| !path.0.is_empty())]
fn first_non_empty(paths: Vec<RewritePath>) -> RewritePath
{
    paths
        .into_iter()
        .find(|path| !path.0.is_empty())
        .expect("a non-empty path exists")
}

#[test]
fn saturation_makes_the_non_refl_value_defined_and_beta_compatible()
{
    let desc = nat_desc();
    let cells = &desc.rules;
    let base = base_cell(var("p0.x".into()));
    let a = gen_x(nat(NumeralCount::from(1_usize)));
    let b = gen_x(nat(NumeralCount::from(2_usize)));

    // A worked non-empty absorbed path: plus(Zero, Zero) reduces to Zero.
    let path_start = FreeTerm::op("plus", [zero(), zero()]);
    let (absorbed, _) = first_non_empty(enumerate_paths(
        &path_start,
        cells,
        RewriteDepth::from(1_usize),
    ));
    let saturated = SaturatedInstance {
        generator: BaseInstance::Gen {
            generator: GeneratorIndex::from(0_usize),
            subst: Binding::new(),
        },
        absorbed,
        path_start,
    };

    // Defined although the raw induction declines on a non-empty path.
    let value = replay_path_ind_saturated(&base, &a, &saturated, &b, cells);
    assert!(
        matches!(value, Maybe::Present(_)),
        "with path absorption the induced value IS defined"
    );

    // β-compatible: on an empty absorbed path it agrees with the refl value.
    let refl_saturated = SaturatedInstance {
        generator: BaseInstance::Gen {
            generator: GeneratorIndex::from(0_usize),
            subst: Binding::new(),
        },
        absorbed: Vec::new(),
        path_start: nat(NumeralCount::from(0_usize)),
    };
    let empty_value = replay_path_ind_saturated(&base, &a, &refl_saturated, &b, cells);
    let refl_value = replay(&base, &[a, b]);
    assert_eq!(
        empty_value, refl_value,
        "on refl the saturated value matches the β-value"
    );
}

#[test]
fn path_induction_satisfies_beta_on_refl()
{
    let base = base_cell(var("p0.x".into()));
    let induction = path_ind_cell(&base);
    let a = gen_x(nat(NumeralCount::from(1_usize)));
    let b = gen_x(nat(NumeralCount::from(2_usize)));
    let refl_at = refl(nat(NumeralCount::from(3_usize)));

    let via_induction = replay(&induction, &[a.clone(), refl_at, b.clone()]);
    let via_base = replay(&base, &[a, b]);
    assert_eq!(
        via_induction, via_base,
        "PathInd{{μ}}(a, refl, b) = μ(a, b)"
    );
    assert!(
        matches!(via_induction, Maybe::Present(_)),
        "the β-value is defined"
    );
}

#[test]
fn path_induction_declines_on_a_non_empty_path()
{
    let desc = nat_desc();
    let cells = &desc.rules;
    let start = FreeTerm::op("plus", [succ(zero()), zero()]);
    let (steps, _end) =
        first_non_empty(enumerate_paths(&start, cells, RewriteDepth::from(3_usize)));
    let nonrefl = LooseInstance {
        per_factor: vec![BaseInstance::Path { start, steps }],
    };

    let induction = path_ind_cell(&base_cell(var("p0.x".into())));
    let declined = replay(&induction, &[
        gen_x(nat(NumeralCount::from(1_usize))),
        nonrefl,
        gen_x(nat(NumeralCount::from(2_usize))),
    ]);
    assert_eq!(
        Maybe::Absent(replay_outcome::Absent::Declined),
        declined,
        "PathInd declines on a non-empty path — the located obligation: instances must be \
         closed under path action (a cell-store saturation invariant)"
    );
}

#[test]
fn distinct_bases_give_distinct_inductions_at_refl()
{
    let induction_one = path_ind_cell(&base_cell(var("p0.x".into())));
    let induction_two = path_ind_cell(&base_cell(succ(var("p0.x".into()))));
    let corpus: Vec<Vec<LooseInstance>> = (0 ..= 3_usize)
        .map(|k| {
            vec![
                gen_x(nat(NumeralCount::from(k))),
                refl(nat(NumeralCount::from(k))),
                gen_x(nat(NumeralCount::from(k.saturating_add(1)))),
            ]
        })
        .collect();
    assert!(
        !bool::from(cells_equal(&induction_one, &induction_two, &corpus)),
        "PathInd cells over replay-distinct bases are replay-distinct at refl"
    );
}

#[test]
fn path_formation_is_real_and_deterministic()
{
    let desc = nat_desc();
    let cells = &desc.rules;
    // plus(Succ(Zero), Zero) reduces to Succ(Zero) in two steps.
    let start = FreeTerm::op("plus", [succ(zero()), zero()]);
    let paths = enumerate_paths(&start, cells, RewriteDepth::from(3_usize));

    assert!(
        paths.iter().any(|path| path.0.is_empty()),
        "refl (the empty path) is enumerated"
    );
    assert!(
        paths.iter().any(|path| path.0.len() == 1),
        "a genuine one-step reduction is enumerated via the plus rules"
    );
    // A full reduction reaches the normal form Succ(Zero) = 1 + 0.
    let full = paths
        .iter()
        .find(|path| !path.0.is_empty() && path.1 == succ(zero()))
        .expect("a full reduction to Succ(Zero) exists");
    assert_eq!(
        apply_path(&start, &full.0, cells),
        Maybe::Present(succ(zero())),
        "replaying a real reduction path reaches Succ(Zero)"
    );
    // Determinism: the enumeration is reproducible.
    assert_eq!(
        paths,
        enumerate_paths(&start, cells, RewriteDepth::from(3_usize)),
        "path enumeration is deterministic"
    );
}

#[test]
fn first_nonempty_preserves_enumeration_order_and_refuses_empty_corpora()
{
    let desc = nat_desc();
    let start = FreeTerm::op("plus", [succ(zero()), zero()]);
    let paths = enumerate_paths(&start, &desc.rules, RewriteDepth::from(2_usize));
    let expected = paths.get(1).expect("the one-step reduction exists").clone();
    assert_eq!(expected.0.len(), 1);
    assert_eq!(first_non_empty(paths), expected);
    assert!(std::panic::catch_unwind(|| first_non_empty(Vec::new())).is_err());
    assert!(std::panic::catch_unwind(|| first_non_empty(vec![(Vec::new(), zero())])).is_err());
}
