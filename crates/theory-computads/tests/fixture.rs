//! The descriptions, circuit rules, toy cells and supply points the suites
//! share.
//!
//! Every toy cell here is a first-order rule over `Zero`, `Succ` and `Add`.

use core::convert::Infallible;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::rewrite_at;
use gandr_theory_computads::ConvexitySupply;
use gandr_theory_levitation::CircuitBody;
use gandr_theory_levitation::CircuitFrame;
use gandr_theory_levitation::CircuitNode;
use gandr_theory_levitation::CircuitRedex;
use gandr_theory_levitation::CircuitRule;
use gandr_theory_levitation::FrameHead;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::RedexOccurrence;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SurfaceSpan;
use gandr_theory_levitation::derive_boundaries;
use quenchant_shape::shape::Maybe;

/// The grade a test description's fields would carry; no field here is
/// graded.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Ungraded {}

/// A face over two terms, with no derived metadata and an empty span.
///
/// # Specification
/// trivial.
pub fn face(
    lhs: FreeTerm,
    rhs: FreeTerm,
) -> RuleFace
{
    RuleFace::new(lhs, rhs, Vec::new(), SurfaceSpan::default())
}

/// A redex line applying `rewrite` from `source` to the port `out`.
///
/// # Specification
/// trivial.
pub fn redex<R, S, O>(
    rewrite: R,
    source: S,
    out: O,
) -> CircuitNode
where
    R: Into<Name>,
    S: Into<Name>,
    O: Into<Name>,
{
    let out = out.into();
    CircuitNode::Redex(CircuitRedex::new(
        rewrite,
        FreeTerm::var(source),
        FreeTerm::var(out.clone()),
        out,
    ))
}

/// A frame line applying the operation `op` to the ports `args`, binding
/// `out`.
///
/// # Specification
/// trivial.
pub fn op_frame<P, I, O>(
    op: P,
    args: I,
    out: O,
) -> CircuitNode
where
    P: Into<Name>,
    I: IntoIterator,
    I::Item: Into<Name>,
    O: Into<Name>,
{
    let args: Vec<FreeTerm> = args.into_iter().map(FreeTerm::var).collect();
    CircuitNode::Frame(CircuitFrame::new(FrameHead::Op(op.into()), args, out))
}

/// A circuit rule over `body`, declared at the sphere its wiring derives, as
/// the surface route supplies it; the instantiation site never reads the
/// sphere, because a peak is exercised rather than matched.
///
/// # Specification
/// - ensures: the sphere is the boundary pair derived from the retained body.
/// - panics: when the body derives no boundary pair, which is a fixture defect.
///
/// # Adequacy
/// - hypothesis: L3 observes disjoint, sequential and reconvergent circuits
///   through exact occurrence positions and shift outcomes. The predicate
///   checks the sphere/body relation; the consumer witnesses independently fix
///   the expected positions.
/// - witness: `tests::circuit_instantiation::the_instantiated_applications_carry_the_records_positions`
/// - witness: `tests::circuit_instantiation::a_sequential_two_redex_body_is_refused_comparable_positions`
/// - witness: `tests::circuit_instantiation::a_reconvergent_body_resolves_both_occurrences_through_one_binding`
#[spec(
    ensures: |ret| {
    derive_boundaries(&ret.body)
        .is_ok_and(|derived| {
            ret.sphere.lhs == derived.source && ret.sphere.rhs == derived.target
        })
},
)]
pub fn rule_over<N>(
    name: N,
    body: CircuitBody,
) -> CircuitRule
where
    N: Into<Name>,
{
    let derived = derive_boundaries(&body).expect("the fixture bodies derive their boundaries");
    CircuitRule::new(name, face(derived.source, derived.target), body)
}

/// The `cong2` rule `*p(-x, +x′); *q(-y, +y′); *add(-x′, -y′, +z);`, whose
/// two redexes sit at the frame's two argument positions.
///
/// # Specification
/// trivial.
pub fn cong2_rule() -> CircuitRule
{
    rule_over(
        "cong2",
        CircuitBody::new(
            [
                redex("p", "x", "x\u{2032}"),
                redex("q", "y", "y\u{2032}"),
                op_frame("add", ["x\u{2032}", "y\u{2032}"], "z"),
            ],
            "z",
        ),
    )
}

/// The sequential rule `*p(-x, +x′); *q(-x′, +y′); *add(-y′, -w, +z);`, whose
/// second redex consumes the first, so both unfold at one position.
///
/// # Specification
/// trivial.
pub fn sequential_rule() -> CircuitRule
{
    rule_over(
        "seq2",
        CircuitBody::new(
            [
                redex("p", "x", "x\u{2032}"),
                redex("q", "x\u{2032}", "y\u{2032}"),
                op_frame("add", ["y\u{2032}", "w"], "z"),
            ],
            "z",
        ),
    )
}

/// (f): `Succ(Zero) ~> Zero`, the rule the left redex is instantiated by.
///
/// # Specification
/// trivial.
pub fn f_faces() -> (Toy, Toy)
{
    (Toy::succ(Toy::zero()), Toy::zero())
}

/// (g): `Succ(Succ(Zero)) ~> Zero`, the rule the right redex is instantiated
/// by. Both faces of `f` and `g` are ground and neither right-hand side offers
/// a seam the other's left-hand side unifies with: they share no ports.
///
/// # Specification
/// trivial.
pub fn g_faces() -> (Toy, Toy)
{
    (Toy::succ(Toy::succ(Toy::zero())), Toy::zero())
}

/// (add-Z): `Add(Zero, x) ~> x`.
///
/// # Specification
/// trivial.
pub fn add_z_faces() -> (Toy, Toy)
{
    (Toy::add(Toy::zero(), Toy::var("x")), Toy::var("x"))
}

/// (add-S): `Add(Succ(m), n) ~> Succ(Add(m, n))`, which overlaps (add-Z).
///
/// # Specification
/// trivial.
pub fn add_s_faces() -> (Toy, Toy)
{
    (
        Toy::add(Toy::succ(Toy::var("m")), Toy::var("n")),
        Toy::succ(Toy::add(Toy::var("m"), Toy::var("n"))),
    )
}

/// A toy cell from its two faces.
///
/// # Specification
/// trivial.
pub fn toy((lhs, rhs): (Toy, Toy)) -> Cell<ToyAlphabet>
{
    toy_cell(lhs, rhs)
}

/// The peak the `cong2` rule is applied to: `Add(Succ(Zero),
/// Succ(Succ(Zero)))`, an `f` redex in the left argument and a `g` redex in
/// the right.
///
/// # Specification
/// trivial.
pub fn cong2_peak() -> Toy
{
    Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::succ(Toy::zero())))
}

/// The alphabet's position for an occurrence's argument path, read the way
/// the instantiation site reads it.
///
/// # Specification
/// trivial.
pub fn recorded_position<A>(occurrence: &RedexOccurrence) -> A::Pos
where
    A: CellAlphabet,
{
    let path: Vec<PositionStep> = occurrence
        .position
        .iter()
        .map(|&index| PositionStep::from(usize::from(index)))
        .collect();
    A::position_at_path(&path)
}

/// Run a recorded schedule from `start`.
///
/// # Specification
/// - ensures: the scheduled applications fire in order; an empty schedule
///   returns the original command.
/// - panics: at the first application whose cell is missing or whose rewrite
///   does not fire.
///
/// # Adequacy
/// - hypothesis: L3 over empty and concrete commuting schedules observes the
///   retained peak and exact composite. Missing cells and nonmatching steps
///   panic at the defective fixture; normal-return predicates check empty-path
///   identity and live applications without repeating alphabet callbacks.
/// - witness: `tests::fixture::recorded_schedules_preserve_empty_paths_and_refuse_invalid_steps`
/// - witness: `tests::convexity_supply::a_withheld_discharge_is_rechecked_by_the_supply_point`
#[spec(
    ensures: |ret| {
    schedule.iter().all(|step| matches!(store.get(step.cell), Maybe::Present(_)))
        && (!schedule.is_empty() || ret == *start)
},
)]
pub fn run<A>(
    store: &CellStore<A>,
    start: &A::Cmd,
    schedule: &[CellApp<A>],
) -> A::Cmd
where
    A: CellAlphabet,
{
    let mut current = start.clone();
    for step in schedule {
        let Maybe::Present(cell) = store.get(step.cell)
        else {
            panic!("the step names a stored cell");
        };
        let Maybe::Present(next) = rewrite_at(cell, &current, &step.at)
        else {
            panic!("the step fires where it was recorded");
        };
        current = next;
    }
    current
}

/// A supply point that refuses every pair, so a result other than its
/// refusal shows it was never asked.
pub struct RefusingSupply;

/// The refusal `RefusingSupply` answers with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Asked;

impl<A> ConvexitySupply<A> for RefusingSupply
where
    A: CellAlphabet,
{
    type Refusal = Asked;
    type Warrant = Infallible;

    /// Refuses.
    ///
    /// # Specification
    /// trivial.
    fn recheck(
        &self,
        _store: &CellStore<A>,
        _peak: &A::Cmd,
        _first: &CellApp<A>,
        _second: &CellApp<A>,
    ) -> Result<Infallible, Asked>
    {
        Err(Asked)
    }
}
#[test]
fn recorded_schedules_preserve_empty_paths_and_refuse_invalid_steps()
{
    let mut store = CellStore::new();
    let id = store.insert(toy(f_faces()));
    let start = cong2_peak();
    assert_eq!(start, run(&store, &start, &[]));
    let missing = CellApp {
        cell: gandr_theory_cell_complexes::CellId::from(usize::MAX),
        at: ToyAlphabet::root_position(),
    };
    assert!(std::panic::catch_unwind(|| run(&store, &start, &[missing])).is_err());
    let mismatch = CellApp {
        cell: id,
        at: ToyAlphabet::root_position(),
    };
    assert!(std::panic::catch_unwind(|| run(&store, &Toy::zero(), &[mismatch])).is_err());
}
