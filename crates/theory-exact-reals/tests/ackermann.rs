//! The hereditarily finite sets of rank at most 3: Tarau's operations against
//! Ackermann's code, and the real code of each set enclosed, told apart from
//! each other code, and read back. The checker replays each certificate.

use core::cmp::Ordering;
use core::num::NonZeroU32;

use gandr_theory_exact_reals::Ackermann;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Closure;
use gandr_theory_exact_reals::CodeError;
use gandr_theory_exact_reals::Conclusion;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exactness;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Rank;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounded;
use gandr_theory_exact_reals::Rounding;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::SetId;
use gandr_theory_exact_reals::Sets;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::code;
use num_bigint::BigInt;

/// The laws evidence of every registered cut here.
///
/// # Specification
/// trivial.
fn laws() -> Evidence
{
    return Evidence::from(0_u32);
}

/// The set of `sets` whose Ackermann code is `code`.
///
/// # Specification
/// trivial.
fn set(
    sets: &mut Sets,
    code: Ackermann,
) -> SetId
{
    return sets.unrank(code).unwrap();
}

/// The sixteen sets of rank at most 3, in the order of their codes.
///
/// # Specification
/// trivial.
fn slice(sets: &mut Sets) -> Vec<SetId>
{
    return (0_u64 .. 16)
        .map(|n| set(sets, Ackermann::from(n)))
        .collect();
}

/// A real `whole + root · √2` with dyadic parts: the exact form of the code of
/// each set of rank at most 3.
#[derive(Clone, Debug)]
struct Surd
{
    /// The rational part.
    whole: Dyadic,
    /// The coefficient of `√2`.
    root: Dyadic,
}

/// The exact real code of the set whose Ackermann code lies below 16. Its
/// four bits pick the members `∅`, `{∅}`, `{{∅}}` and `{∅, {∅}}`, whose terms
/// are `1`, `1/2`, `√2/2` and `√2/4`.
///
/// # Specification
/// trivial.
fn surd(code: Ackermann) -> Surd
{
    let bits = u64::from(code);
    assert!(bits < 16, "a set of rank at most 3");
    let bit = |place: u32| i64::try_from(bits.checked_shr(place).unwrap() & 1).unwrap();
    let halves = bit(0).checked_mul(2).unwrap() | bit(1);
    let quarters = bit(2).checked_mul(2).unwrap() | bit(3);
    return Surd {
        whole: Dyadic::new(BigInt::from(halves), Exponent::from(-1_i32)).unwrap(),
        root: Dyadic::new(BigInt::from(quarters), Exponent::from(-2_i32)).unwrap(),
    };
}

/// The value of an exact operation.
///
/// # Specification
/// trivial.
fn exact(rounded: Rounded) -> Dyadic
{
    assert_eq!(rounded.exactness(), Exactness::Exact);
    return rounded.into_value();
}

/// `point` against `surd`, exactly.
///
/// # Specification
/// trivial.
fn against(
    point: &Dyadic,
    surd: &Surd,
) -> Ordering
{
    let gap = exact(
        point
            .sub(&surd.whole, Precision::MAX, Rounding::Floor)
            .unwrap(),
    );
    let square = |value: &Dyadic| exact(value.mul(value, Precision::MAX, Rounding::Floor).unwrap());
    let (gap_squared, root_squared) = (square(&gap), square(&surd.root));
    let twice = exact(
        root_squared
            .add(&root_squared, Precision::MAX, Rounding::Floor)
            .unwrap(),
    );
    // `√2` is irrational, so a nonzero root term never equals a dyadic gap.
    return match (gap.cmp(&Dyadic::ZERO), surd.root.cmp(&Dyadic::ZERO)) {
        (order, Ordering::Equal) => order,
        (Ordering::Less | Ordering::Equal, Ordering::Greater) => Ordering::Less,
        (Ordering::Greater | Ordering::Equal, Ordering::Less) => Ordering::Greater,
        (Ordering::Greater, Ordering::Greater) => gap_squared.cmp(&twice),
        (Ordering::Less, Ordering::Less) => twice.cmp(&gap_squared),
    };
}

/// The order of two surds, exactly.
///
/// # Specification
/// trivial.
fn compare(
    first: &Surd,
    second: &Surd,
) -> Ordering
{
    let minus = |left: &Dyadic, right: &Dyadic| {
        exact(left.sub(right, Precision::MAX, Rounding::Floor).unwrap())
    };
    let difference = Surd {
        whole: Dyadic::ZERO,
        root: minus(&second.root, &first.root),
    };
    return against(&minus(&first.whole, &second.whole), &difference);
}

/// Assert that `interval` holds `surd`.
///
/// # Specification
/// trivial.
fn assert_holds(
    interval: &NumericInterval,
    surd: &Surd,
)
{
    let side = |end: &Endpoint, closure: Closure, inside: Ordering| match *end {
        Endpoint::Finite(ref value) => {
            let order = against(value, surd);
            order == inside || (order == Ordering::Equal && closure == Closure::Closed)
        },
        Endpoint::NegInf => inside == Ordering::Less,
        Endpoint::PosInf => inside == Ordering::Greater,
    };
    let (lower, upper) = (interval.lower(), interval.upper());
    assert!(
        side(&lower.endpoint, lower.closure, Ordering::Less)
            && side(&upper.endpoint, upper.closure, Ordering::Greater),
        "{interval:?} holds {surd:?}"
    );
}

/// The width of a finite interval.
///
/// # Specification
/// trivial.
fn width(interval: &NumericInterval) -> Dyadic
{
    let (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) =
        (&interval.lower().endpoint, &interval.upper().endpoint)
    else {
        panic!("a finite interval: {interval:?}");
    };
    return exact(upper.sub(lower, Precision::MAX, Rounding::Floor).unwrap());
}

/// The plan whose root `build` writes, admitted, and its root.
///
/// # Specification
/// trivial.
fn admitted<Build>(build: Build) -> (ValidatedPlan, NodeId)
where
    Build: FnOnce(&mut PlanBuilder) -> Root,
{
    let mut builder = PlanBuilder::new();
    let root = build(&mut builder);
    let mut table = EvidenceTable::new();
    table.register(laws(), Judgement::CutLaws).unwrap();
    let plan = admit(builder.finish(root).unwrap(), &Quotas::default(), &table).unwrap();
    let root = plan.plan().root().node();
    return (plan, root);
}

/// The steps that a run spends before it gives up on its obligations.
///
/// # Specification
/// trivial.
fn budget() -> Budget
{
    return Budget::from(4096_u64);
}

/// The conclusion of each obligation that a run within the budget certifies,
/// replayed by the checker, and `None` for each other obligation.
///
/// # Specification
/// trivial.
fn settle(
    plan: &ValidatedPlan,
    obligations: Vec<Obligation>,
) -> Vec<Option<Conclusion>>
{
    let count = obligations.len();
    let quantum = Quantum::from(NonZeroU32::new(1).unwrap());
    let mut dovetail = Dovetail::new(plan, obligations, quantum, CheckerQuotas::default());
    let report = dovetail.run(budget(), Rounds::from(u64::MAX), || false);
    return (0 .. count)
        .map(|index| {
            let Some(Outcome::Certified(certificate)) = report.outcome(Position::from(index))
            else {
                return None;
            };
            let checked = check(plan, certificate, &CheckerQuotas::default()).unwrap();
            Some(checked.conclusion().clone())
        })
        .collect();
}

/// The enclosure of the code of `set` to `2^-40`, replayed by the checker.
///
/// # Specification
/// trivial.
fn enclosure<Build>(build: Build) -> NumericInterval
where
    Build: FnOnce(&mut PlanBuilder) -> RealId,
{
    let (plan, root) = admitted(|builder| Root::Real(build(builder)));
    let demand = Demand::Encloses {
        width: Exponent::from(-40_i32),
    };
    let obligation = Obligation::new(&plan, root, demand).unwrap();
    let [Some(Conclusion::Encloses { ref interval, .. })] = settle(&plan, vec![obligation])[..]
    else {
        panic!("the enclosure is certified");
    };
    let bound = Dyadic::new(BigInt::from(1_u8), Exponent::from(-40_i32)).unwrap();
    assert!(width(interval) <= bound, "{interval:?} is too wide");
    return interval.clone();
}

/// What the machine certifies of a strict comparison.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Decision
{
    /// The first real lies below the second.
    Below,
    /// The first real lies at or above the second.
    NotBelow,
    /// The budget runs out, or a quota stops each pole: neither is certified.
    Stalls,
}

/// Decide `first < second` for the two reals that `build` writes: both poles
/// run side by side within the budget.
///
/// # Specification
/// trivial.
fn decide<Build>(build: Build) -> Decision
where
    Build: FnOnce(&mut PlanBuilder) -> (RealId, RealId),
{
    let (plan, less) = admitted(|builder| {
        let (first, second) = build(builder);
        Root::Open(builder.open(Open::Less(first, second)).unwrap())
    });
    let poles = [Demand::Holds, Demand::Fails]
        .map(|demand| Obligation::new(&plan, less, demand).unwrap())
        .to_vec();
    return match settle(&plan, poles)[..] {
        [Some(Conclusion::Holds { open }), None] if open == less => Decision::Below,
        [None, Some(Conclusion::Fails { open })] if open == less => Decision::NotBelow,
        [None, None] => Decision::Stalls,
        ref other => panic!("the poles conclude {other:?}"),
    };
}

/// The code of `set`, written to `builder`.
///
/// # Specification
/// trivial.
fn real(
    builder: &mut PlanBuilder,
    sets: &Sets,
    set: SetId,
) -> RealId
{
    return code(builder, sets, set, laws()).unwrap();
}

#[test]
fn tarau_operations_agree_with_the_codes()
{
    // Every set of rank at most 4, through Ackermann's code.
    let mut sets = Sets::new();
    let tower = [1_u64, 2, 4, 16, 0x0001_0000];
    for n in 0_u64 .. 0x0001_0000 {
        let here = set(&mut sets, Ackermann::from(n));
        assert_eq!(sets.ackermann(here), Ok(Ackermann::from(n)));
        let rank = tower.iter().position(|&top| n < top).unwrap();
        assert_eq!(
            sets.rank(here),
            Ok(Rank::from(u32::try_from(rank).unwrap()))
        );
        let members = sets.members(here).unwrap().to_vec();
        let codes: Vec<Ackermann> = members
            .iter()
            .map(|&member| sets.ackermann(member).unwrap())
            .collect();
        assert!(
            codes.is_sorted(),
            "the members of h_{n} in the order of their codes"
        );
        let shuffled: Vec<SetId> = members
            .iter()
            .rev()
            .chain(members.first())
            .copied()
            .collect();
        assert_eq!(sets.set(&shuffled), Ok(here));
        if n < 0xFFFF {
            let next = set(&mut sets, Ackermann::from(n + 1));
            assert_eq!(sets.successor(here), Ok(next), "the successor of h_{n}");
        }
    }
    let wide = set(&mut sets, Ackermann::from(64_u64));
    assert_eq!(sets.set(&[wide]), Err(CodeError::Wide));
    let beyond = Sets::new();
    assert_eq!(beyond.members(wide), Err(CodeError::Unknown));
}

#[test]
fn each_code_encloses_and_replays()
{
    let mut sets = Sets::new();
    for (n, here) in (0_u64 ..).zip(slice(&mut sets)) {
        let interval = enclosure(|builder| real(builder, &sets, here));
        assert_holds(&interval, &surd(Ackermann::from(n)));
    }
    // A set of rank 4 reads `2^-x` at an irrational `x`.
    let sixteen = set(&mut sets, Ackermann::from(16_u64));
    let mut builder = PlanBuilder::new();
    assert_eq!(
        code(&mut builder, &sets, sixteen, laws()),
        Err(CodeError::Rank)
    );
}

#[test]
fn each_pair_of_codes_is_apart()
{
    let mut sets = Sets::new();
    let slice = slice(&mut sets);
    let mut apart = 0_u32;
    for (left, &first) in (0_u64 ..).zip(&slice) {
        for (right, &second) in (0_u64 ..).zip(&slice).filter(|&(right, _)| right > left) {
            let decision =
                decide(|builder| (real(builder, &sets, first), real(builder, &sets, second)));
            let expected =
                match compare(&surd(Ackermann::from(left)), &surd(Ackermann::from(right))) {
                    Ordering::Less => Decision::Below,
                    Ordering::Greater => Decision::NotBelow,
                    Ordering::Equal => panic!("h_{left} and h_{right} share a code"),
                };
            assert_eq!(decision, expected, "h_{left} against h_{right}");
            apart += 1;
        }
    }
    assert_eq!(apart, 120);
}

#[test]
fn the_successor_carries_over_to_the_real_code()
{
    // `R(h_{n+1}) = R(h_n) - R(h_{2^k - 1}) + R({h_k})` for the `k` trailing
    // ones of `n`: the difference encloses zero at every width asked.
    let mut sets = Sets::new();
    for n in 0_u64 .. 15 {
        let here = set(&mut sets, Ackermann::from(n));
        let next = sets.successor(here).unwrap();
        let ones = n.trailing_ones();
        let low = set(&mut sets, Ackermann::from((1_u64 << ones) - 1));
        let single = set(&mut sets, Ackermann::from(1_u64 << ones));
        let interval = enclosure(|builder| {
            let (next, here, low, single) = (
                real(builder, &sets, next),
                real(builder, &sets, here),
                real(builder, &sets, low),
                real(builder, &sets, single),
            );
            let without = builder.real(Real::Sub(here, low)).unwrap();
            let with = builder.real(Real::Add(without, single)).unwrap();
            builder.real(Real::Sub(next, with)).unwrap()
        });
        let zero = Surd {
            whole: Dyadic::ZERO,
            root: Dyadic::ZERO,
        };
        assert_holds(&interval, &zero);
    }
}

/// Where the read-back of a real stops.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReadBack
{
    /// The code of the cumulus equals the real.
    Exact(SetId),
    /// No set of rank at most 3 extends the cumulus to a code at or below the
    /// real.
    Exhausted(SetId),
    /// The machine tells the real from the code of `candidate` in neither
    /// direction: the boundary of the closed test `R(candidate) ≤ α`.
    Stalled
    {
        /// The sets read before the stall.
        cumulus: SetId,
        /// The union whose code meets the real.
        candidate: SetId,
    },
}

/// A real that the read-back reads.
#[derive(Clone, Debug)]
enum Alpha
{
    /// The code of a set.
    Code(SetId),
    /// A dyadic constant.
    Constant(Dyadic),
}

/// The node of `alpha`, written to `builder`.
///
/// # Specification
/// trivial.
fn alpha_node(
    builder: &mut PlanBuilder,
    sets: &Sets,
    alpha: &Alpha,
) -> RealId
{
    return match *alpha {
        Alpha::Code(set) => real(builder, sets, set),
        Alpha::Constant(ref value) => builder.real(Real::Constant(value.clone())).unwrap(),
    };
}

/// The read-back of Cantone, Omodeo and Policriti, cut to the sets of rank at
/// most 3: the cumulus grows by the set of least Ackermann code whose union
/// with it has a code at or below the real, until its own code reaches it.
///
/// # Specification
/// trivial.
fn read_back(
    sets: &mut Sets,
    alpha: &Alpha,
) -> ReadBack
{
    let candidates = slice(sets);
    let mut cumulus = set(sets, Ackermann::from(0_u64));
    loop {
        // The first rule: the read-back ends when the cumulus reaches the real.
        match decide(|builder| {
            (
                real(builder, sets, cumulus),
                alpha_node(builder, sets, alpha),
            )
        }) {
            Decision::Below => {},
            Decision::NotBelow => return ReadBack::Exact(cumulus),
            Decision::Stalls => {
                return ReadBack::Stalled {
                    cumulus,
                    candidate: cumulus,
                };
            },
        }
        let mut next = None;
        for &candidate in candidates.iter().skip(1) {
            let held = sets.members(cumulus).unwrap().to_vec();
            let members = sets.members(candidate).unwrap().to_vec();
            // The union equals the cumulus when the cumulus holds the
            // candidate.
            let union = sets.set(&[held, members].concat()).unwrap();
            if union == cumulus {
                continue;
            }
            match decide(|builder| (alpha_node(builder, sets, alpha), real(builder, sets, union))) {
                Decision::Below => {},
                Decision::NotBelow => {
                    next = Some(union);
                    break;
                },
                Decision::Stalls => {
                    return ReadBack::Stalled {
                        cumulus,
                        candidate: union,
                    };
                },
            }
        }
        match next {
            Some(union) => cumulus = union,
            None => return ReadBack::Exhausted(cumulus),
        }
    }
}

#[test]
fn the_read_back_stalls_only_at_its_boundary()
{
    let mut sets = Sets::new();
    let h: Vec<SetId> = slice(&mut sets);
    let mut read = |alpha: Alpha| read_back(&mut sets, &alpha);
    // A dyadic code reads back to its set, past a test of equality.
    assert_eq!(read(Alpha::Code(h[2])), ReadBack::Exact(h[2]));
    assert_eq!(read(Alpha::Code(h[3])), ReadBack::Exact(h[3]));
    // The least code comes first, so the read-back of `R({{{∅}}})` and of
    // `R({∅, {{∅}}})` takes another set and then needs a set of rank 4.
    assert_eq!(read(Alpha::Code(h[4])), ReadBack::Exhausted(h[2]));
    assert_eq!(read(Alpha::Code(h[5])), ReadBack::Exhausted(h[3]));
    // At a code that reads a cut, the closed test `R(h) ≤ α` meets its
    // boundary: the machine certifies neither `α < R(h)` nor `R(h) ≤ α`.
    assert_eq!(read(Alpha::Code(h[8])), ReadBack::Stalled {
        cumulus: h[0],
        candidate: h[8],
    });
    assert_eq!(read(Alpha::Code(h[10])), ReadBack::Stalled {
        cumulus: h[2],
        candidate: h[10],
    });
    // Past the code of every set of rank at most 2, the slice has no more.
    assert_eq!(
        read(Alpha::Constant(Dyadic::from(3_i64))),
        ReadBack::Exhausted(h[15])
    );
}
