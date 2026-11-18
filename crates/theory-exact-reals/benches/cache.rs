//! The measurement of the checked-result cache: a lookup that hits, one that
//! misses, a store, and a run of a quantified corpus uncached and cached.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `refine` | a fresh run of the enclosure of the square root of two to `2^-64`, the work that a hit replaces |
//! | `replay` | the checker's replay of that certificate alone |
//! | `hit` | a lookup of the enclosure of the square root of two to `2^-64`, its certificate moved and replayed |
//! | `miss` | a lookup of the same obligation in an empty cache |
//! | `store` | the store of that certificate, replayed and written as bytes |
//! | `uncached` | four quantified formulas, each run until it settles |
//! | `cached` | the same formulas, each consulted in a cache that a first run fills |
//!
//! `cargo bench` runs the full measurement and prints one table. Under any
//! other runner the binary runs one short pass of every row and prints
//! nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

mod support;

use core::hint::black_box;
use core::num::NonZeroU32;
use core::num::NonZeroUsize;

use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::Cache;
use gandr_theory_exact_reals::CacheBound;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::DeBruijn;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Domain;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceSlot;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::OpenId;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantifier;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::square_root_of_two;
use num_bigint::BigInt;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The plan that `build` makes, admitted with the laws, overt and compact
/// references registered.
///
/// # Specification
/// trivial.
fn admitted<Build>(build: Build) -> ValidatedPlan
where
    Build: FnOnce(&mut PlanBuilder) -> OpenId,
{
    let mut table = EvidenceTable::new();
    for (reference, judgement) in [
        (0_u32, Judgement::CutLaws),
        (1_u32, Judgement::Overt),
        (2_u32, Judgement::Compact),
    ] {
        table
            .register(Evidence::from(reference), judgement)
            .expect("a table");
    }
    let mut builder = PlanBuilder::new();
    let root = build(&mut builder);
    return admit(
        builder.finish(Root::Open(root)).expect("a plan"),
        &Quotas::default(),
        &table,
    )
    .expect("an admitted plan");
}

/// The quantifier of a formula.
#[derive(Clone, Copy)]
enum Form
{
    /// An existential.
    Exists,
    /// A universal.
    Forall,
}

/// The node of `Q x ∈ [0, 1]. first < second` in `builder`, its quantifier
/// `form`, the operands built by `operands` from the variable.
///
/// # Specification
/// trivial.
fn quantified<Operands>(
    builder: &mut PlanBuilder,
    form: Form,
    operands: Operands,
) -> OpenId
where
    Operands: FnOnce(&mut PlanBuilder, RealId) -> (RealId, RealId),
{
    let hull = NumericInterval::new(
        Bound::closed(Dyadic::ZERO),
        Bound::closed(Dyadic::ONE),
        Orientation::Proper,
    )
    .expect("a hull");
    let (overt, compact) = (Evidence::from(1_u32), Evidence::from(2_u32));
    let domain = builder
        .domain(Domain::Interval {
            hull,
            overt: EvidenceSlot::Given(overt),
            compact: EvidenceSlot::Given(compact),
        })
        .expect("a domain");
    let variable = builder
        .real(Real::Bound(DeBruijn::from(0_u32)))
        .expect("a variable");
    let (first, second) = operands(builder, variable);
    let body = builder.open(Open::Less(first, second)).expect("a body");
    let node = match form {
        Form::Exists => Open::Exists(Quantifier {
            domain,
            body,
            evidence: overt,
            dual: EvidenceSlot::Given(compact),
        }),
        Form::Forall => Open::Forall(Quantifier {
            domain,
            body,
            evidence: compact,
            dual: EvidenceSlot::Given(overt),
        }),
    };
    return builder.open(node).expect("a quantifier");
}

/// `1/2`.
///
/// # Specification
/// trivial.
fn half() -> Dyadic
{
    return Dyadic::new(BigInt::from(1_u8), Exponent::from(-1_i32)).expect("a half");
}

/// The plan of one quantified formula and the obligation that asks it
/// `demand`.
///
/// # Specification
/// trivial.
fn formula<Operands>(
    form: Form,
    demand: Demand,
    operands: Operands,
) -> (ValidatedPlan, Obligation)
where
    Operands: FnOnce(&mut PlanBuilder, RealId) -> (RealId, RealId),
{
    let plan = admitted(|builder| quantified(builder, form, operands));
    // The canonical walk numbers the nodes anew, so the quantifier is read
    // back from the admitted plan.
    let node = plan
        .plan()
        .nodes()
        .find(|&(_, node)| matches!(*node, Node::Open(Open::Exists(_) | Open::Forall(_))))
        .map(|(id, _)| id)
        .expect("the quantifier");
    let obligation = Obligation::new(&plan, node, demand).expect("an obligation");
    return (plan, obligation);
}

/// The quantified corpus: four formulas over `[0, 1]`, each asked the pole
/// that it settles.
///
/// # Specification
/// trivial.
fn corpus() -> [(ValidatedPlan, Obligation); 4]
{
    return [
        formula(Form::Forall, Demand::Holds, |builder, x| {
            let half = builder.real(Real::Constant(half())).expect("a half");
            let one = builder.real(Real::Constant(Dyadic::ONE)).expect("a one");
            let square = builder.real(Real::Mul(x, x)).expect("a square");
            let difference = builder.real(Real::Sub(square, x)).expect("a difference");
            let sum = builder.real(Real::Add(difference, one)).expect("a sum");
            (half, sum)
        }),
        formula(Form::Exists, Demand::Holds, |builder, x| {
            let half = builder.real(Real::Constant(half())).expect("a half");
            (half, x)
        }),
        formula(Form::Forall, Demand::Fails, |builder, x| {
            let half = builder.real(Real::Constant(half())).expect("a half");
            (x, half)
        }),
        formula(Form::Exists, Demand::Fails, |builder, x| {
            let two = builder
                .real(Real::Constant(Dyadic::from(2_i64)))
                .expect("a two");
            (two, x)
        }),
    ];
}

/// A run of each formula of `corpus`, after a consultation of `cache` when
/// there is one, and its record in `cache` afterwards.
///
/// # Specification
/// trivial.
fn run(
    corpus: &[(ValidatedPlan, Obligation)],
    mut cache: Option<&mut Cache>,
)
{
    let quantum = Quantum::from(NonZeroU32::new(64).expect("a quantum"));
    for &(ref plan, obligation) in corpus {
        let mut dovetail = Dovetail::new(plan, [obligation], quantum, CheckerQuotas::default());
        if let Some(ref mut cache) = cache {
            black_box(dovetail.consult(cache));
        }
        let report = dovetail.run(Budget::from(u64::MAX), Rounds::from(u64::MAX), || false);
        assert!(
            matches!(
                report.outcome(Position::from(0)),
                Some(Outcome::Certified(_))
            ),
            "each formula settles"
        );
        if let Some(ref mut cache) = cache {
            black_box(dovetail.record(cache));
        }
    }
}

/// A cache of 64 entries at most.
///
/// # Specification
/// trivial.
fn cache() -> Cache
{
    return Cache::new(CacheBound::from(NonZeroUsize::new(64).expect("a bound")));
}

/// Run the measurement, or the short pass outside `cargo bench`.
///
/// # Specification
/// trivial.
fn main()
{
    let output = Output::of_run();
    let (batch, samples) = match output {
        Output::Table => (Count(16), Count(400)),
        Output::Silent => (Count(1), Count(1)),
    };
    if matches!(output, Output::Table) {
        println!("| Row | What | p50 ns | p99 ns | Allocations |");
        println!("| --- | ---- | ------ | ------ | ----------- |");
    }
    let quotas = CheckerQuotas::default();
    // The enclosure of the square root of two to `2^-64`.
    let root = admitted(|builder| {
        let root = square_root_of_two(builder, Evidence::from(0_u32)).expect("a cut");
        let one = builder.real(Real::Constant(Dyadic::ONE)).expect("a one");
        builder.open(Open::Less(one, root)).expect("a comparison")
    });
    let cut = root
        .plan()
        .nodes()
        .find(|&(_, node)| matches!(*node, Node::Real(Real::Cut(_))))
        .map(|(id, _)| id)
        .expect("the cut");
    let enclose = Obligation::new(&root, cut, Demand::Encloses {
        width: Exponent::from(-64_i32),
    })
    .expect("an obligation");
    let refined = || {
        let mut dovetail = Dovetail::new(
            &root,
            [enclose],
            Quantum::from(NonZeroU32::new(64).expect("a quantum")),
            quotas,
        );
        return match dovetail
            .run(Budget::from(u64::MAX), Rounds::from(u64::MAX), || false)
            .outcome(Position::from(0))
        {
            Some(Outcome::Certified(certificate)) => Some(certificate.clone()),
            Some(
                Outcome::Pending | Outcome::Suspended(_) | Outcome::Exhausted | Outcome::Cancelled,
            )
            | None => None,
        };
    };
    let certificate: Certificate = refined().expect("the refinement settles");
    let refine = measure(batch, samples, || {
        black_box(refined());
    });
    let replay = measure(batch, samples, || {
        black_box(check(black_box(&root), &certificate, &quotas)).expect("a replay");
    });
    let mut filled = cache();
    filled
        .store(&root, enclose, &certificate, &quotas)
        .expect("a store");
    let hit = measure(batch, samples, || {
        black_box(filled.lookup(black_box(&root), enclose, &quotas));
    });
    let mut empty = cache();
    let miss = measure(batch, samples, || {
        black_box(empty.lookup(black_box(&root), enclose, &quotas));
    });
    let store = measure(batch, samples, || {
        let mut fresh = cache();
        black_box(fresh.store(black_box(&root), enclose, &certificate, &quotas)).expect("a store");
    });
    let corpus = corpus();
    let uncached = measure(batch, samples, || run(black_box(&corpus), None));
    let mut filled_by_run = cache();
    run(&corpus, Some(&mut filled_by_run));
    assert_eq!(filled_by_run.tally().held, 4, "each formula has its entry");
    let cached = measure(batch, samples, || {
        run(black_box(&corpus), Some(&mut filled_by_run));
    });
    if matches!(output, Output::Table) {
        let steps = usize::from(certificate.step_count());
        let hit_what = format!("a certificate of {steps} steps, moved and replayed");
        for (row, what, figures) in [
            (
                "refine",
                "the enclosure of the square root of two to 2^-64, run",
                &refine,
            ),
            ("replay", "the replay of its certificate alone", &replay),
            ("hit", hit_what.as_str(), &hit),
            ("miss", "the same obligation, an empty cache", &miss),
            (
                "store",
                "the same certificate, replayed and written",
                &store,
            ),
            (
                "uncached",
                "4 quantified formulas, each run until it settles",
                &uncached,
            ),
            (
                "cached",
                "the same 4 formulas, each consulted in a filled cache",
                &cached,
            ),
        ] {
            print_row(format_args!("{row} | {what}"), figures);
        }
    }
}
