//! The checked-result cache and the gate of stage B: the corpus of the epic
//! answers alike cached and uncached, a subterm that two plans share shares
//! its entry, an entry that does not replay leaves by name, the oldest entry
//! leaves past the bound, and no suspension, cancellation or exhausted budget
//! enters the cache.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::num::NonZeroU32;
use core::num::NonZeroUsize;

use gandr_theory_exact_reals::BitWidth;
use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::Cache;
use gandr_theory_exact_reals::CacheBound;
use gandr_theory_exact_reals::CacheRefusal;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CertificateCheck;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Conclusion;
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
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::OpenId;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::PlanError;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantifier;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::StepId;
use gandr_theory_exact_reals::StepSite;
use gandr_theory_exact_reals::Steps;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::square_root_of_two;
use num_bigint::BigInt;

/// The laws evidence of every registered cut here.
///
/// # Specification
/// trivial.
fn laws() -> Evidence
{
    return Evidence::from(0_u32);
}

/// The overt evidence of every domain here.
///
/// # Specification
/// trivial.
fn overt() -> Evidence
{
    return Evidence::from(1_u32);
}

/// The compact evidence of every domain here.
///
/// # Specification
/// trivial.
fn compact() -> Evidence
{
    return Evidence::from(2_u32);
}

/// The plan that `build` makes, admitted under the three references.
///
/// # Specification
/// trivial.
fn admitted<Build>(build: Build) -> ValidatedPlan
where
    Build: FnOnce(&mut PlanBuilder) -> OpenId,
{
    let mut table = EvidenceTable::new();
    table.register(laws(), Judgement::CutLaws).unwrap();
    table.register(overt(), Judgement::Overt).unwrap();
    table.register(compact(), Judgement::Compact).unwrap();
    let mut builder = PlanBuilder::new();
    let root = build(&mut builder);
    return admit(
        builder.finish(Root::Open(root)).unwrap(),
        &Quotas::default(),
        &table,
    )
    .unwrap();
}

/// The dyadic `mantissa · 2^exponent`.
///
/// # Specification
/// trivial.
fn dyadic(
    mantissa: BigInt,
    exponent: Exponent,
) -> Dyadic
{
    return Dyadic::new(mantissa, exponent).unwrap();
}

/// `1/2`.
///
/// # Specification
/// trivial.
fn half() -> Dyadic
{
    return dyadic(BigInt::from(1_u8), Exponent::from(-1_i32));
}

/// The quantifier of a formula.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Form
{
    /// An existential.
    Exists,
    /// A universal.
    Forall,
}

/// The node of `Q x ∈ [lower, upper]. first < second` in `builder`, the
/// operands built by `operands` from the variable, with evidence of both
/// modalities.
///
/// # Specification
/// trivial.
fn quantified<Operands>(
    builder: &mut PlanBuilder,
    form: Form,
    (lower, upper): (Dyadic, Dyadic),
    operands: Operands,
) -> OpenId
where
    Operands: FnOnce(&mut PlanBuilder, RealId) -> (RealId, RealId),
{
    let hull = NumericInterval::new(
        Bound::closed(lower),
        Bound::closed(upper),
        Orientation::Proper,
    )
    .unwrap();
    let domain = builder
        .domain(Domain::Interval {
            hull,
            overt: EvidenceSlot::Given(overt()),
            compact: EvidenceSlot::Given(compact()),
        })
        .unwrap();
    let variable = builder.real(Real::Bound(DeBruijn::from(0_u32))).unwrap();
    let (first, second) = operands(builder, variable);
    let body = builder.open(Open::Less(first, second)).unwrap();
    let (evidence, dual) = match form {
        Form::Exists => (overt(), compact()),
        Form::Forall => (compact(), overt()),
    };
    let quantifier = Quantifier {
        domain,
        body,
        evidence,
        dual: EvidenceSlot::Given(dual),
    };
    return builder
        .open(match form {
            Form::Exists => Open::Exists(quantifier),
            Form::Forall => Open::Forall(quantifier),
        })
        .unwrap();
}

/// `forall x ∈ [1, 2]. 0 < x · x` in `builder`.
///
/// # Specification
/// trivial.
fn square(builder: &mut PlanBuilder) -> OpenId
{
    return quantified(
        builder,
        Form::Forall,
        (Dyadic::ONE, Dyadic::from(2_i64)),
        |builder, x| {
            let zero = builder.real(Real::Constant(Dyadic::ZERO)).unwrap();
            let square = builder.real(Real::Mul(x, x)).unwrap();
            (zero, square)
        },
    );
}

/// The first node of `plan` that `wanted` accepts.
///
/// # Specification
/// trivial.
fn find<Wanted>(
    plan: &ValidatedPlan,
    wanted: Wanted,
) -> NodeId
where
    Wanted: Fn(&Node) -> bool,
{
    let count = usize::from(plan.plan().node_count());
    return (0 .. count)
        .map(|index| NodeId::try_from(index).unwrap())
        .find(|&id| wanted(plan.plan().node(id).unwrap()))
        .unwrap();
}

/// The open nodes of `plan` that `wanted` accepts, in order.
///
/// # Specification
/// trivial.
fn every<Wanted>(
    plan: &ValidatedPlan,
    wanted: Wanted,
) -> Vec<NodeId>
where
    Wanted: Fn(&Node) -> bool,
{
    return plan
        .plan()
        .nodes()
        .filter(|&(_, node)| wanted(node))
        .map(|(id, _)| id)
        .collect();
}

/// The corpus of the epic: the comparisons of #5345, the refinement of
/// #5346 and the quantified formulas of #5347, each plan with its
/// obligations.
///
/// # Specification
/// trivial.
fn corpus() -> Vec<(ValidatedPlan, Vec<Obligation>)>
{
    let comparisons = admitted(|builder| {
        let root = square_root_of_two(builder, laws()).unwrap();
        let point = builder
            .real(Real::Constant(dyadic(
                BigInt::from(45_u8),
                Exponent::from(-5_i32),
            )))
            .unwrap();
        let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
        let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
        let three_halves = builder
            .real(Real::Constant(dyadic(
                BigInt::from(3_u8),
                Exponent::from(-1_i32),
            )))
            .unwrap();
        let opens = [
            builder.open(Open::Less(point, root)).unwrap(),
            builder.open(Open::Less(root, root)).unwrap(),
            builder.open(Open::Less(one, two)).unwrap(),
            builder.open(Open::Less(two, one)).unwrap(),
            builder.open(Open::Less(root, three_halves)).unwrap(),
        ];
        let mut joined = opens[0];
        for open in &opens[1 ..] {
            joined = builder.open(Open::Join(joined, *open)).unwrap();
        }
        joined
    });
    let mut asks: Vec<Obligation> = every(&comparisons, |node| {
        matches!(*node, Node::Open(Open::Less(..)))
    })
    .into_iter()
    .flat_map(|less| [Demand::Holds, Demand::Fails].map(|demand| (less, demand)))
    .filter_map(|(less, demand)| Obligation::new(&comparisons, less, demand).ok())
    .collect();
    let cut = find(&comparisons, |node| {
        matches!(*node, Node::Real(Real::Cut(_)))
    });
    asks.push(
        Obligation::new(&comparisons, cut, Demand::Encloses {
            width: Exponent::from(-20_i32),
        })
        .unwrap(),
    );
    let formulas = admitted(|builder| {
        let unit = || (Dyadic::ZERO, Dyadic::ONE);
        let opens = [
            square(builder),
            quantified(builder, Form::Exists, unit(), |builder, x| {
                let half = builder.real(Real::Constant(half())).unwrap();
                (half, x)
            }),
            quantified(builder, Form::Forall, unit(), |builder, x| {
                let half = builder.real(Real::Constant(half())).unwrap();
                (x, half)
            }),
            quantified(builder, Form::Exists, unit(), |builder, x| {
                let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
                (two, x)
            }),
            quantified(builder, Form::Forall, unit(), |builder, x| {
                let zero = builder.real(Real::Constant(Dyadic::ZERO)).unwrap();
                let square = builder.real(Real::Mul(x, x)).unwrap();
                (zero, square)
            }),
        ];
        let mut joined = opens[0];
        for open in &opens[1 ..] {
            joined = builder.open(Open::Meet(joined, *open)).unwrap();
        }
        joined
    });
    let quantifiers: Vec<Obligation> = every(&formulas, |node| {
        matches!(*node, Node::Open(Open::Exists(_) | Open::Forall(_)))
    })
    .into_iter()
    .flat_map(|node| [Demand::Holds, Demand::Fails].map(|demand| (node, demand)))
    .filter_map(|(node, demand)| Obligation::new(&formulas, node, demand).ok())
    .collect();
    return vec![(comparisons, asks), (formulas, quantifiers)];
}

/// The quantum of `steps` steps.
///
/// # Specification
/// trivial.
fn quantum(steps: Steps) -> Quantum
{
    let steps = u32::try_from(u64::from(steps)).unwrap();
    return Quantum::from(NonZeroU32::new(steps).unwrap());
}

/// A count of cache entries.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Entries(usize);

/// A cache of `entries` entries at most.
///
/// # Specification
/// trivial.
fn bounded(entries: Entries) -> Cache
{
    return Cache::new(CacheBound::from(NonZeroUsize::new(entries.0).unwrap()));
}

/// The outcomes of one run of `obligations` over `plan` within `budget`,
/// after a consultation of `cache` when there is one, each certificate
/// cloned.
///
/// # Specification
/// trivial.
fn outcomes(
    plan: &ValidatedPlan,
    obligations: &[Obligation],
    budget: Budget,
    cache: Option<&mut Cache>,
) -> Vec<String>
{
    let mut dovetail = Dovetail::new(
        plan,
        obligations.iter().copied(),
        quantum(Steps::from(8_u64)),
        CheckerQuotas::default(),
    );
    let mut cache = cache;
    if let Some(cache) = cache.as_deref_mut() {
        assert_eq!(dovetail.consult(cache), Vec::new(), "no entry is refused");
    }
    let report = dovetail.run(budget, Rounds::from(u64::MAX), || false);
    let answers: Vec<String> = (0 .. obligations.len())
        .map(|index| format!("{:?}", report.outcome(Position::from(index))))
        .collect();
    // Complete replay: each certificate, a cached one included, replays from
    // its first step to the evidence that its obligation asks for.
    for (index, obligation) in obligations.iter().enumerate() {
        if let Some(Outcome::Certified(certificate)) = report.outcome(Position::from(index)) {
            let conclusion = check(plan, certificate, &CheckerQuotas::default())
                .unwrap()
                .conclusion()
                .clone();
            match (conclusion, obligation.demand()) {
                (Conclusion::Holds { open }, Demand::Holds)
                | (Conclusion::Fails { open }, Demand::Fails) => {
                    assert_eq!(open, obligation.node());
                },
                (Conclusion::Encloses { real, .. }, Demand::Encloses { .. }) => {
                    assert_eq!(real, obligation.node());
                },
                (other, demand) => panic!("{other:?} answers no {demand:?}"),
            }
        }
    }
    if let Some(cache) = cache {
        assert_eq!(
            dovetail.record(cache),
            Vec::new(),
            "every certificate enters"
        );
    }
    return answers;
}

#[test]
fn the_corpus_answers_alike_cached_and_uncached()
{
    // The gate of stage B: each plan of the corpus runs uncached, then twice
    // with one cache, and the three runs agree on every outcome and every
    // certificate.
    let budget = Budget::from(4096_u64);
    for (plan, obligations) in corpus() {
        let uncached = outcomes(&plan, &obligations, budget, None);
        // An obligation that stops never reads as false: no node certifies
        // both poles, and the cache below changes no outcome.
        let mut poles: BTreeMap<NodeId, (bool, bool)> = BTreeMap::new();
        for (obligation, outcome) in obligations.iter().zip(&uncached) {
            let certified = outcome.starts_with("Some(Certified");
            let pole = poles.entry(obligation.node()).or_default();
            match obligation.demand() {
                Demand::Holds => pole.0 |= certified,
                Demand::Fails => pole.1 |= certified,
                Demand::Encloses { .. } => {},
            }
        }
        assert!(
            poles.values().all(|&(holds, fails)| !(holds && fails)),
            "a node certifies both poles"
        );
        let mut cache = bounded(Entries(64));
        let first = outcomes(&plan, &obligations, budget, Some(&mut cache));
        let certified = uncached
            .iter()
            .filter(|outcome| outcome.starts_with("Some(Certified"))
            .count();
        assert!(certified > 0, "the plan certifies an obligation");
        // Suspension, cancellation and an exhausted budget never enter the
        // cache: it holds the certificates alone.
        assert_eq!(cache.tally().held, u64::try_from(certified).unwrap());
        assert_eq!(cache.tally().hits, 0);
        let second = outcomes(&plan, &obligations, budget, Some(&mut cache));
        assert_eq!(cache.tally().hits, u64::try_from(certified).unwrap());
        assert_eq!(first, uncached);
        assert_eq!(second, uncached);
        assert!(
            uncached
                .iter()
                .any(|outcome| outcome.starts_with("Some(Suspended")
                    || outcome.starts_with("Some(Exhausted")),
            "the corpus holds an obligation that never certifies"
        );
    }
    // A cancelled run certifies nothing, so it adds nothing.
    let (plan, obligations) = corpus().swap_remove(1);
    let mut cache = bounded(Entries(64));
    let mut dovetail = Dovetail::new(
        &plan,
        obligations.iter().copied(),
        quantum(Steps::from(8_u64)),
        CheckerQuotas::default(),
    );
    let report = dovetail.run(Budget::from(4096_u64), Rounds::from(u64::MAX), || true);
    assert!(
        (0 .. obligations.len())
            .all(|index| report.outcome(Position::from(index)) == Some(Outcome::Cancelled))
    );
    assert_eq!(dovetail.record(&mut cache), Vec::new());
    assert_eq!(cache.tally().held, 0);
}

#[test]
fn a_subterm_shared_by_two_plans_shares_its_entry()
{
    // `forall x ∈ [1, 2]. 0 < x · x` alone, and the same formula beside
    // another, where its nodes take other positions.
    let alone = admitted(square);
    let beside = admitted(|builder| {
        let other = quantified(
            builder,
            Form::Exists,
            (Dyadic::ZERO, Dyadic::ONE),
            |builder, x| {
                let half = builder.real(Real::Constant(half())).unwrap();
                (half, x)
            },
        );
        let formula = square(builder);
        builder.open(Open::Join(other, formula)).unwrap()
    });
    let forall =
        |plan: &ValidatedPlan| find(plan, |node| matches!(*node, Node::Open(Open::Forall(_))));
    assert_ne!(forall(&alone), forall(&beside), "the formula moves");
    let ask = |plan: &ValidatedPlan| Obligation::new(plan, forall(plan), Demand::Holds).unwrap();
    let mut cache = bounded(Entries(4));
    let stored = outcomes(
        &alone,
        &[ask(&alone)],
        Budget::from(4096_u64),
        Some(&mut cache),
    );
    let uncached = outcomes(&beside, &[ask(&beside)], Budget::from(4096_u64), None);
    let cached = outcomes(
        &beside,
        &[ask(&beside)],
        Budget::from(4096_u64),
        Some(&mut cache),
    );
    assert_eq!(cache.tally().hits, 1);
    assert_eq!(cached, uncached);
    assert_ne!(
        stored, cached,
        "the certificate names the positions of its plan"
    );
}

#[test]
fn a_certificate_moves_to_the_rooted_plan_and_back()
{
    // In the plan that stores it, a cached certificate reads back to itself.
    let quotas = CheckerQuotas::default();
    for (plan, obligations) in corpus() {
        let mut cache = bounded(Entries(64));
        let mut dovetail = Dovetail::new(
            &plan,
            obligations.iter().copied(),
            quantum(Steps::from(8_u64)),
            quotas,
        );
        let report = dovetail.run(Budget::from(4096_u64), Rounds::from(u64::MAX), || false);
        for (index, &obligation) in obligations.iter().enumerate() {
            if let Some(Outcome::Certified(certificate)) = report.outcome(Position::from(index)) {
                cache
                    .store(&plan, obligation, certificate, &quotas)
                    .unwrap();
                assert_eq!(
                    cache.lookup(&plan, obligation, &quotas),
                    gandr_theory_exact_reals::Lookup::Hit(certificate.clone())
                );
            }
        }
    }
}

#[test]
fn an_entry_that_does_not_replay_leaves_by_name()
{
    // A certificate stored under the default quotas does not replay under a
    // width quota of no bit, which refuses the constant one, so its entry
    // leaves the cache.
    let plan = admitted(square);
    let forall = find(&plan, |node| matches!(*node, Node::Open(Open::Forall(_))));
    let obligation = Obligation::new(&plan, forall, Demand::Holds).unwrap();
    let mut cache = bounded(Entries(4));
    let _stored = outcomes(
        &plan,
        &[obligation],
        Budget::from(4096_u64),
        Some(&mut cache),
    );
    assert_eq!(cache.tally().held, 1);
    let narrow = CheckerQuotas {
        width: BitWidth::from(0_u64),
        ..CheckerQuotas::default()
    };
    let mut dovetail = Dovetail::new(&plan, [obligation], quantum(Steps::from(8_u64)), narrow);
    let refusals = dovetail.consult(&mut cache);
    assert!(
        matches!(
            refusals.as_slice(),
            [(position, CacheRefusal::Replay(refusal))]
                if *position == Position::from(0) && refusal.check == CertificateCheck::WidthQuota
        ),
        "{refusals:?}"
    );
    assert_eq!(cache.tally().held, 0);
    assert_eq!(cache.tally().refusals, 1);
    // A certificate that holds is no evidence that the universal fails.
    let mut fresh = Dovetail::new(
        &plan,
        [obligation],
        quantum(Steps::from(8_u64)),
        CheckerQuotas::default(),
    );
    let report = fresh.run(Budget::from(4096_u64), Rounds::from(u64::MAX), || false);
    let Some(Outcome::Certified(holds)) = report.outcome(Position::from(0))
    else {
        panic!("the universal holds");
    };
    let fails = Obligation::new(&plan, forall, Demand::Fails).unwrap();
    assert_eq!(
        cache.store(&plan, fails, holds, &CheckerQuotas::default()),
        Err(CacheRefusal::Mismatch)
    );
    assert_eq!(cache.tally().held, 0);
}

#[test]
fn the_oldest_entry_leaves_past_the_bound()
{
    let (plan, obligations) = corpus().swap_remove(1);
    let quotas = CheckerQuotas::default();
    let mut dovetail = Dovetail::new(
        &plan,
        obligations.iter().copied(),
        quantum(Steps::from(8_u64)),
        quotas,
    );
    let report = dovetail.run(Budget::from(4096_u64), Rounds::from(u64::MAX), || false);
    let certified: Vec<(Obligation, Certificate)> = obligations
        .iter()
        .enumerate()
        .filter_map(
            |(index, &obligation)| match report.outcome(Position::from(index)) {
                Some(Outcome::Certified(certificate)) => Some((obligation, certificate.clone())),
                _ => None,
            },
        )
        .collect();
    assert!(certified.len() >= 3, "three certificates to store");
    let mut cache = bounded(Entries(2));
    for &(obligation, ref certificate) in &certified[.. 3] {
        cache
            .store(&plan, obligation, certificate, &quotas)
            .unwrap();
    }
    assert_eq!(cache.tally().held, 2);
    assert_eq!(cache.tally().evictions, 1);
    assert_eq!(
        cache.lookup(&plan, certified[0].0, &quotas),
        gandr_theory_exact_reals::Lookup::Miss
    );
    for &(obligation, ref certificate) in &certified[1 .. 3] {
        assert_eq!(
            cache.lookup(&plan, obligation, &quotas),
            gandr_theory_exact_reals::Lookup::Hit(certificate.clone())
        );
    }
}

#[test]
fn the_square_root_of_two_refines_alike_from_the_cache()
{
    // The try-first: the square root of two to `2^-64` twice, with the cache
    // between the runs. The two certificates agree byte by byte, and the
    // second run spends no step.
    let plan = admitted(|builder| {
        let root = square_root_of_two(builder, laws()).unwrap();
        let one = builder.real(Real::Constant(Dyadic::ONE)).unwrap();
        builder.open(Open::Less(one, root)).unwrap()
    });
    let cut = find(&plan, |node| matches!(*node, Node::Real(Real::Cut(_))));
    let obligation = Obligation::new(&plan, cut, Demand::Encloses {
        width: Exponent::from(-64_i32),
    })
    .unwrap();
    let mut cache = bounded(Entries(4));
    let run = |cache: &mut Cache| {
        let mut dovetail = Dovetail::new(
            &plan,
            [obligation],
            quantum(Steps::from(8_u64)),
            CheckerQuotas::default(),
        );
        assert_eq!(dovetail.consult(cache), Vec::new());
        let certificate = match dovetail
            .run(Budget::from(4096_u64), Rounds::from(u64::MAX), || false)
            .outcome(Position::from(0))
        {
            Some(Outcome::Certified(certificate)) => certificate.clone(),
            other => panic!("the refinement settles: {other:?}"),
        };
        assert_eq!(dovetail.record(cache), Vec::new());
        (certificate, dovetail.spent(Position::from(0)).unwrap())
    };
    let (first, first_spent) = run(&mut cache);
    let (second, second_spent) = run(&mut cache);
    assert_eq!(first.encode(), second.encode());
    assert_eq!(u64::from(first_spent), 65);
    assert_eq!(u64::from(second_spent), 0);
}

#[test]
fn refusals_render_distinct_phrases()
{
    let refusals = [
        CacheRefusal::Plan(PlanError::WrongSort),
        CacheRefusal::Foreign,
        CacheRefusal::Replay(gandr_theory_exact_reals::CertificateRefusal {
            site: StepSite::Step(StepId::from(0_u32)),
            check: CertificateCheck::WidthQuota,
        }),
        CacheRefusal::Mismatch,
    ];
    let lines: Vec<String> = refusals.iter().map(ToString::to_string).collect();
    assert!(
        lines
            .iter()
            .all(|line| !line.is_empty() && !line.contains('\n')),
        "a refusal renders no one line"
    );
    let distinct: BTreeSet<&String> = lines.iter().collect();
    assert_eq!(distinct.len(), lines.len(), "a refusal repeats a phrase");
}
