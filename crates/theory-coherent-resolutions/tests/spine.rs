//! One interface over two replay surfaces: the kernel's conversion replay and
//! this crate's tracelet replay.
//!
//! A [`Modality`] is a consumer that replays a recorded dialogue about an
//! object, in a context it holds, to a verdict. One law suite runs over every
//! instance: the unit law (an object's trivial dialogue certifies it) and the
//! property grade (the verdict is a function of the context, the object and
//! the dialogue, and a run leaves the context as it found it). Identity is
//! derived from evaluation and never read off a dialogue. Composition is not a
//! member: each instance composes in its own shape — a pair's component traces
//! concatenated for conversion, two tracelets grafted where the first's join
//! is the second's peak — and states its own law.

use core::fmt::Debug;

use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_core::EngineClaim;
use gandr_kernel_core::KernelVerdict;
use gandr_kernel_core::ParameterCount;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_core::ReplayDecline;
use gandr_kernel_core::ReplayNode;
use gandr_kernel_core::ReplaySides;
use gandr_kernel_core::Unfoldable;
use gandr_kernel_core::Unfoldings;
use gandr_kernel_core::replay;
use gandr_kernel_term::ArenaWatermark;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::replay_from_peak;
use quenchant_shape::shape::Maybe;

/// Whether a verdict lies in the laws' domain.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Certification
{
    /// The consumer re-derived the verdict.
    Certified,
    /// A decline or a refusal: outside the algebra.
    Outside,
}

/// Why an object has no trivial dialogue.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NoUnit
{
    /// The producer declined, so there is no claim to certify.
    Declined,
    /// The object's two ends differ, so some step must be taken.
    Apart,
}

/// Whether two dialogues of one object are one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Identification
{
    /// Both certify the object with one verdict.
    Identified,
    /// One does not certify it, or they certify different verdicts.
    Distinct,
}

/// A consumer that replays a recorded dialogue about an object.
trait Modality
{
    /// What the consumer holds while it replays.
    type Context: Clone;
    /// What a dialogue is about.
    type Object;
    /// The recorded queries and answers.
    type Dialogue;
    /// What a replay concludes.
    type Verdict: Debug + Eq;
    /// What a run must leave unchanged in the context.
    type Observed: Debug + Eq;

    /// The dialogue that asks nothing of `object`, where it has one.
    ///
    /// # Specification
    /// trivial.
    fn trivial(object: &Self::Object) -> Maybe<Self::Dialogue, NoUnit>;

    /// Replay `dialogue` about `object` in `context`.
    ///
    /// # Specification
    /// trivial.
    fn evaluate(
        context: &mut Self::Context,
        object: &Self::Object,
        dialogue: &Self::Dialogue,
    ) -> Self::Verdict;

    /// Whether `verdict` lies in the laws' domain.
    ///
    /// # Specification
    /// trivial.
    fn certifies(verdict: &Self::Verdict) -> Certification;

    /// What `context` shows of itself.
    ///
    /// # Specification
    /// trivial.
    fn observe(context: &Self::Context) -> Self::Observed;
}

/// Replay twice in place and once on a clone, and require one verdict and an
/// unchanged context: the property grade.
///
/// # Specification
/// trivial.
fn graded<M>(
    context: &mut M::Context,
    object: &M::Object,
    dialogue: &M::Dialogue,
) -> M::Verdict
where
    M: Modality,
{
    let before = M::observe(context);
    let mut copy = context.clone();
    let first = M::evaluate(context, object, dialogue);
    assert_eq!(
        before,
        M::observe(context),
        "a run adds nothing to the context"
    );
    let second = M::evaluate(context, object, dialogue);
    let independent = M::evaluate(&mut copy, object, dialogue);
    assert_eq!(first, second, "a repeated run gives the same verdict");
    assert_eq!(
        first, independent,
        "a run on a clone gives the same verdict"
    );
    assert_eq!(
        before,
        M::observe(context),
        "a second run adds nothing either"
    );
    first
}

/// The unit law: an object's trivial dialogue, replayed, certifies it.
///
/// # Specification
/// trivial.
fn unit<M>(
    context: &mut M::Context,
    object: &M::Object,
) -> Maybe<M::Verdict, NoUnit>
where
    M: Modality,
{
    match M::trivial(object) {
        Maybe::Present(dialogue) => Maybe::Present(graded::<M>(context, object, &dialogue)),
        Maybe::Absent(reason) => Maybe::Absent(reason),
    }
}

/// Two dialogues of one object are one exactly when both certify it with one
/// verdict, read off evaluation alone.
///
/// # Specification
/// trivial.
fn identified<M>(
    context: &mut M::Context,
    object: &M::Object,
    first: &M::Dialogue,
    second: &M::Dialogue,
) -> Identification
where
    M: Modality,
{
    let one = graded::<M>(context, object, first);
    let other = graded::<M>(context, object, second);
    match (M::certifies(&one), M::certifies(&other)) {
        (Certification::Certified, Certification::Certified) if one == other => {
            Identification::Identified
        },
        (Certification::Certified | Certification::Outside, _) => Identification::Distinct,
    }
}

/// The kernel's conversion replay as a modality.
struct Conversion;

/// What the kernel holds while it replays a conversion trace.
#[derive(Clone, Debug)]
struct Kernel
{
    /// The arena both sides and every unfolding body live in.
    arena: TermArena,
    /// The constants' unfoldings.
    unfoldings: Unfoldings,
    /// The replay's allowance.
    budget: ReplayBudget,
}

/// Two sides and the verdict the engine claims for them.
#[derive(Clone, Copy, Debug)]
struct Claim
{
    /// The sides compared.
    sides: ReplaySides,
    /// The engine's verdict.
    claim: EngineClaim,
}

/// The one-decision trace that closes a comparison on alpha-equality or rigid
/// separation.
const SHARED: ConversionDecision<ReplayNode> = ConversionDecision::ComparedShared {
    left: ReplayNode::Other,
    right: ReplayNode::Other,
};

impl Modality for Conversion
{
    type Context = Kernel;
    type Dialogue = Vec<ConversionDecision<ReplayNode>>;
    type Object = Claim;
    type Observed = ArenaWatermark;
    type Verdict = KernelVerdict;

    /// One shared-node decision for a claim the engine settled; none for a
    /// declined claim.
    ///
    /// # Specification
    /// trivial.
    fn trivial(object: &Claim) -> Maybe<Self::Dialogue, NoUnit>
    {
        match object.claim {
            EngineClaim::Convertible | EngineClaim::NotConvertible => Maybe::Present(vec![SHARED]),
            EngineClaim::Declined => Maybe::Absent(NoUnit::Declined),
        }
    }

    /// The kernel's replay of `dialogue` against `object`'s claim.
    ///
    /// # Specification
    /// trivial.
    fn evaluate(
        context: &mut Kernel,
        object: &Claim,
        dialogue: &Self::Dialogue,
    ) -> KernelVerdict
    {
        replay(
            &mut context.arena,
            &context.unfoldings,
            object.sides,
            object.claim,
            dialogue.iter().copied(),
            context.budget,
        )
    }

    /// A settled verdict certifies; a declined one is outside.
    ///
    /// # Specification
    /// trivial.
    fn certifies(verdict: &KernelVerdict) -> Certification
    {
        match *verdict {
            KernelVerdict::Convertible | KernelVerdict::NotConvertible => Certification::Certified,
            KernelVerdict::Declined(_) => Certification::Outside,
        }
    }

    /// The arena's watermark.
    ///
    /// # Specification
    /// trivial.
    fn observe(context: &Kernel) -> ArenaWatermark
    {
        context.arena.watermark()
    }
}

/// The tracelet replay as a modality, over the toy alphabet.
struct Tracelets;

/// A tracelet's boundary: the term both paths leave and the term they reach.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Boundary
{
    /// The peak.
    peak: Toy,
    /// The join.
    joins_at: Toy,
}

/// A tracelet's two paths.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Legs
{
    /// The first path.
    first: Vec<CellApp<ToyAlphabet>>,
    /// The second path.
    second: Vec<CellApp<ToyAlphabet>>,
}

impl Modality for Tracelets
{
    type Context = CellStore<ToyAlphabet>;
    type Dialogue = Legs;
    type Object = Boundary;
    type Observed = CellStore<ToyAlphabet>;
    type Verdict = Certification;

    /// Two empty paths when the boundary's ends coincide; none otherwise.
    ///
    /// # Specification
    /// trivial.
    fn trivial(object: &Boundary) -> Maybe<Legs, NoUnit>
    {
        if object.peak == object.joins_at {
            Maybe::Present(Legs {
                first: Vec::new(),
                second: Vec::new(),
            })
        }
        else {
            Maybe::Absent(NoUnit::Apart)
        }
    }

    /// Whether both legs replay from the peak to the join.
    ///
    /// # Specification
    /// trivial.
    fn evaluate(
        context: &mut CellStore<ToyAlphabet>,
        object: &Boundary,
        dialogue: &Legs,
    ) -> Certification
    {
        if bool::from(replay_from_peak(
            context,
            &object.peak,
            &object.joins_at,
            &dialogue.first,
            &dialogue.second,
        )) {
            Certification::Certified
        }
        else {
            Certification::Outside
        }
    }

    /// The verdict itself.
    ///
    /// # Specification
    /// trivial.
    fn certifies(verdict: &Certification) -> Certification
    {
        *verdict
    }

    /// The whole store.
    ///
    /// # Specification
    /// trivial.
    fn observe(context: &CellStore<ToyAlphabet>) -> CellStore<ToyAlphabet>
    {
        context.clone()
    }
}

/// Graft `second` onto `first` where `first` joins at `second`'s peak: the
/// boundary from `first`'s peak to `second`'s join, each path `first`'s
/// followed by `second`'s.
///
/// # Specification
/// trivial.
fn graft(
    first: (&Boundary, &Legs),
    second: (&Boundary, &Legs),
) -> Maybe<(Boundary, Legs), NoUnit>
{
    if first.0.joins_at != second.0.peak {
        return Maybe::Absent(NoUnit::Apart);
    }
    Maybe::Present((
        Boundary {
            peak: first.0.peak.clone(),
            joins_at: second.0.joins_at.clone(),
        },
        Legs {
            first: [first.1.first.as_slice(), second.1.first.as_slice()].concat(),
            second: [first.1.second.as_slice(), second.1.second.as_slice()].concat(),
        },
    ))
}

/// A toy store with two ways down a numeral: `succ(x) ~> x` and
/// `succ(succ(x)) ~> x`, and those two cells.
///
/// # Specification
/// trivial.
fn peeling() -> (CellStore<ToyAlphabet>, CellId, CellId)
{
    let mut store = CellStore::new();
    let once = store.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::var("x")));
    let twice = store.insert(toy_cell(Toy::succ(Toy::succ(Toy::var("x"))), Toy::var("x")));
    (store, once, twice)
}

/// `count` successors of zero.
///
/// # Specification
/// trivial.
fn numeral(count: Successors) -> Toy
{
    (0 .. count.0).fold(Toy::zero(), |term, _| Toy::succ(term))
}

/// A numeral's successor count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Successors(usize);

/// `cell` fired at the root, `count` times.
///
/// # Specification
/// trivial.
fn at_root(
    cell: CellId,
    count: Successors,
) -> Vec<CellApp<ToyAlphabet>>
{
    vec![
        CellApp {
            cell,
            at: ToyAlphabet::root_position(),
        };
        count.0
    ]
}

#[test]
fn both_replays_keep_the_unit_law()
{
    let mut kernel = Kernel {
        arena: TermArena::new(),
        unfoldings: Unfoldings::default(),
        budget: ReplayBudget::DEFAULT,
    };
    let unit_value = kernel.arena.value_unit();
    let bound = kernel.arena.value_variable(DeBruijnIndex::from(0_u32));
    let other = kernel.arena.value_variable(DeBruijnIndex::from(1_u32));
    let same = kernel.arena.value_tuple(&[bound, unit_value]);
    let again = kernel.arena.value_tuple(&[bound, unit_value]);
    for (claim, verdict) in [
        (
            Claim {
                sides: ReplaySides::Values(same, again),
                claim: EngineClaim::Convertible,
            },
            KernelVerdict::Convertible,
        ),
        (
            Claim {
                sides: ReplaySides::Values(bound, other),
                claim: EngineClaim::NotConvertible,
            },
            KernelVerdict::NotConvertible,
        ),
    ] {
        assert_eq!(
            Maybe::Present(verdict),
            unit::<Conversion>(&mut kernel, &claim),
            "the trivial trace certifies {claim:?}"
        );
    }
    assert_eq!(
        Maybe::Absent(NoUnit::Declined),
        unit::<Conversion>(&mut kernel, &Claim {
            sides: ReplaySides::Values(bound, other),
            claim: EngineClaim::Declined,
        })
    );
    let (mut store, _once, _twice) = peeling();
    let two = numeral(Successors(2));
    assert_eq!(
        Maybe::Present(Certification::Certified),
        unit::<Tracelets>(&mut store, &Boundary {
            peak: two.clone(),
            joins_at: two.clone(),
        }),
        "two empty paths certify a term against itself"
    );
    assert_eq!(
        Maybe::Absent(NoUnit::Apart),
        unit::<Tracelets>(&mut store, &Boundary {
            peak: two,
            joins_at: Toy::zero(),
        })
    );
}

#[test]
fn the_unit_law_binds_on_the_budgeted_fragment()
{
    // `(λx. x! x) (thunk (λx. x! x))` against `return ()`: the trivial trace
    // exists, and the replay spends its budget reducing the left side.
    let mut kernel = Kernel {
        arena: TermArena::new(),
        unfoldings: Unfoldings::default(),
        budget: ReplayBudget::from(64),
    };
    let bound = kernel.arena.value_variable(DeBruijnIndex::from(0_u32));
    let forced = kernel.arena.computation_force(bound);
    let self_applied = kernel.arena.computation_application(forced, bound);
    let lambda = kernel.arena.computation_lambda(self_applied);
    let suspended = kernel.arena.value_thunk(lambda);
    let omega = kernel.arena.computation_application(lambda, suspended);
    let unit_value = kernel.arena.value_unit();
    let target = kernel.arena.computation_return(unit_value);
    let divergent = Claim {
        sides: ReplaySides::Computations(omega, target),
        claim: EngineClaim::Convertible,
    };
    assert_eq!(
        Maybe::Present(KernelVerdict::Declined(ReplayDecline::Budget)),
        unit::<Conversion>(&mut kernel, &divergent),
        "outside the budgeted fragment the trivial trace declines, a verdict outside the algebra"
    );
}

#[test]
fn identity_is_read_off_evaluation_on_both_replays()
{
    // Conversion: two traces of one claim, each certifying it.
    let constant = ConstantIndex::from(0_usize);
    let mut arena = TermArena::new();
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let mut kernel = Kernel {
        arena,
        unfoldings: Unfoldings::new(vec![Unfoldable::Operator {
            parameters: ParameterCount::from(1),
            body: bound,
        }]),
        budget: ReplayBudget::DEFAULT,
    };
    let head = kernel.arena.value_constant(constant);
    let instance = kernel.arena.value_static_application(head, bound);
    let claim = Claim {
        sides: ReplaySides::Values(instance, bound),
        claim: EngineClaim::Convertible,
    };
    let unfolded = vec![
        ConversionDecision::Unfold {
            constant: ReplayNode::Constant(constant),
        },
        ConversionDecision::ReduceLeft {
            redex: ReplayNode::Constant(constant),
        },
        SHARED,
    ];
    assert_eq!(
        Identification::Identified,
        identified::<Conversion>(&mut kernel, &claim, &unfolded, &unfolded)
    );
    assert_eq!(
        Identification::Distinct,
        identified::<Conversion>(&mut kernel, &claim, &unfolded, &vec![SHARED]),
        "a trace that does not certify the claim is not identified with one that does"
    );
    // Tracelets: two different paths down one numeral, one boundary.
    let (mut store, once, twice) = peeling();
    let object = Boundary {
        peak: numeral(Successors(2)),
        joins_at: Toy::zero(),
    };
    let stepwise = Legs {
        first: at_root(once, Successors(2)),
        second: at_root(twice, Successors(1)),
    };
    let swapped = Legs {
        first: at_root(twice, Successors(1)),
        second: at_root(once, Successors(2)),
    };
    assert_eq!(
        Identification::Identified,
        identified::<Tracelets>(&mut store, &object, &stepwise, &swapped),
        "two certificates of one boundary are one, whatever their paths"
    );
    let short = Legs {
        first: at_root(once, Successors(1)),
        second: at_root(twice, Successors(1)),
    };
    assert_eq!(
        Identification::Distinct,
        identified::<Tracelets>(&mut store, &object, &stepwise, &short),
        "a path that stops short of the join certifies nothing"
    );
}

#[test]
fn tracelets_graft_where_one_joins_at_the_next_peak()
{
    let (mut store, once, twice) = peeling();
    let one = numeral(Successors(1));
    let upper = (
        Boundary {
            peak: numeral(Successors(3)),
            joins_at: one.clone(),
        },
        Legs {
            first: at_root(once, Successors(2)),
            second: at_root(twice, Successors(1)),
        },
    );
    let lower = (
        Boundary {
            peak: one,
            joins_at: Toy::zero(),
        },
        Legs {
            first: at_root(once, Successors(1)),
            second: at_root(once, Successors(1)),
        },
    );
    for &(ref object, ref legs) in [&upper, &lower] {
        assert_eq!(
            Certification::Certified,
            graded::<Tracelets>(&mut store, object, legs)
        );
    }
    let Maybe::Present(grafted) = graft((&upper.0, &upper.1), (&lower.0, &lower.1))
    else {
        panic!("the upper tracelet joins at the lower one's peak");
    };
    assert_eq!(
        Certification::Certified,
        graded::<Tracelets>(&mut store, &grafted.0, &grafted.1),
        "a graft of two certificates certifies the outer boundary"
    );
    assert_eq!(
        Maybe::Absent(NoUnit::Apart),
        graft((&lower.0, &lower.1), (&upper.0, &upper.1)),
        "a graft needs the first's join to be the second's peak"
    );
    // The trivial tracelet is a unit on either side, and grafting associates.
    for &(ref boundary, ref legs) in [&upper, &lower] {
        let Maybe::Present(before) = Tracelets::trivial(&Boundary {
            peak: boundary.peak.clone(),
            joins_at: boundary.peak.clone(),
        })
        else {
            panic!("a term has a trivial tracelet against itself");
        };
        let Maybe::Present(after) = Tracelets::trivial(&Boundary {
            peak: boundary.joins_at.clone(),
            joins_at: boundary.joins_at.clone(),
        })
        else {
            panic!("a term has a trivial tracelet against itself");
        };
        let left = Boundary {
            peak: boundary.peak.clone(),
            joins_at: boundary.peak.clone(),
        };
        let right = Boundary {
            peak: boundary.joins_at.clone(),
            joins_at: boundary.joins_at.clone(),
        };
        assert_eq!(
            Maybe::Present((boundary.clone(), legs.clone())),
            graft((&left, &before), (boundary, legs))
        );
        assert_eq!(
            Maybe::Present((boundary.clone(), legs.clone())),
            graft((boundary, legs), (&right, &after))
        );
    }
    // Three one-step tracelets down from three: grafting associates.
    let step = |from: Successors| {
        (
            Boundary {
                peak: numeral(Successors(from.0.saturating_add(1))),
                joins_at: numeral(from),
            },
            Legs {
                first: at_root(once, Successors(1)),
                second: at_root(once, Successors(1)),
            },
        )
    };
    let [top, middle, foot] = [
        step(Successors(2)),
        step(Successors(1)),
        step(Successors(0)),
    ];
    let Maybe::Present(top_middle) = graft((&top.0, &top.1), (&middle.0, &middle.1))
    else {
        panic!("three joins at two, the middle step's peak");
    };
    let Maybe::Present(middle_foot) = graft((&middle.0, &middle.1), (&foot.0, &foot.1))
    else {
        panic!("two joins at one, the foot step's peak");
    };
    let left_nested = graft((&top_middle.0, &top_middle.1), (&foot.0, &foot.1));
    assert_eq!(
        left_nested,
        graft((&top.0, &top.1), (&middle_foot.0, &middle_foot.1)),
        "grafting associates"
    );
    let Maybe::Present(whole) = left_nested
    else {
        panic!("the three steps graft");
    };
    assert_eq!(
        Certification::Certified,
        graded::<Tracelets>(&mut store, &whole.0, &whole.1)
    );
}

#[test]
fn a_pair_of_conversions_composes_by_its_components_traces()
{
    let mut kernel = Kernel {
        arena: TermArena::new(),
        unfoldings: Unfoldings::default(),
        budget: ReplayBudget::DEFAULT,
    };
    let unit_value = kernel.arena.value_unit();
    kernel.unfoldings = Unfoldings::new(vec![
        Unfoldable::Body(unit_value),
        Unfoldable::Body(unit_value),
    ]);
    let (first, second) = (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize));
    let left = kernel.arena.value_constant(first);
    let right = kernel.arena.value_constant(second);
    let unfold = |constant| {
        vec![
            ConversionDecision::Unfold {
                constant: ReplayNode::Constant(constant),
            },
            ConversionDecision::ReduceLeft {
                redex: ReplayNode::Constant(constant),
            },
        ]
    };
    let components = [
        (
            Claim {
                sides: ReplaySides::Values(left, unit_value),
                claim: EngineClaim::Convertible,
            },
            unfold(first),
        ),
        (
            Claim {
                sides: ReplaySides::Values(right, unit_value),
                claim: EngineClaim::Convertible,
            },
            unfold(second),
        ),
    ];
    for &(ref claim, ref trace) in &components {
        assert_eq!(
            KernelVerdict::Convertible,
            graded::<Conversion>(&mut kernel, claim, trace)
        );
    }
    let pair = Claim {
        sides: ReplaySides::Values(
            kernel.arena.value_tuple(&[left, right]),
            kernel.arena.value_tuple(&[unit_value, unit_value]),
        ),
        claim: EngineClaim::Convertible,
    };
    let composite = [unfold(first), unfold(second)].concat();
    assert_eq!(
        KernelVerdict::Convertible,
        graded::<Conversion>(&mut kernel, &pair, &composite),
        "the components' traces, first component first, certify the pair"
    );
}
