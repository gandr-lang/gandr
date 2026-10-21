//! Equations an implicit argument poses: solved, refuted, and postponed by
//! name in one store.

use gandr_core_term::Binders;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_unify::Equation;
use gandr_core_unify::MetaId;
use gandr_core_unify::Metas;
use gandr_core_unify::Postponed;
use gandr_core_unify::Reason;
use gandr_core_unify::Refutation;
use gandr_core_unify::Side;
use gandr_core_unify::Verdict;
use gandr_core_unify::declaration;
use gandr_core_unify::meta_lookup;
use gandr_core_unify::solve;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use quenchant_shape::shape::Maybe;

/// A numeral the witnesses write.
#[derive(Clone, Copy)]
enum Numeral
{
    /// `3`.
    Three,
    /// `4`.
    Four,
}

/// The integer literal `numeral` spells.
///
/// # Specification
/// trivial.
fn literal(numeral: Numeral) -> Literal
{
    let digits = match numeral {
        Numeral::Three => "3",
        Numeral::Four => "4",
    };
    let magnitude = Magnitude::from_decimal_text(digits.into()).expect("the digits are decimal");
    Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))
}

/// Declare `hole` a metavariable of a context of `scope` binders.
///
/// # Specification
/// trivial.
fn meta(
    metas: &mut Metas,
    hole: HoleId,
    scope: Binders,
) -> MetaId
{
    match metas.declare(hole, scope) {
        Maybe::Present(id) => id,
        Maybe::Absent(reason) => panic!("{hole:?} is declared once: {reason:?}"),
    }
}

/// The solution `meta` must have.
///
/// # Specification
/// trivial.
fn solution(
    metas: &Metas,
    meta: MetaId,
) -> ValueId
{
    match metas.solution(meta) {
        Maybe::Present(solution) => solution,
        Maybe::Absent(reason) => panic!("{meta:?} is solved: {reason:?}"),
    }
}

/// The decode of `hole` at level zero, as an implicit `a : Type` reads where
/// a parameter is typed `a`.
///
/// # Specification
/// trivial.
fn decoded(
    arena: &mut CoreArena,
    hole: HoleId,
) -> ValueTypeId
{
    let code = arena.value_hole(hole);
    arena.value_type_element(code, Level::zero())
}

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, index)
}

/// Why each equation in the store waits, in the order it was postponed.
///
/// # Specification
/// trivial.
fn reasons(metas: &Metas) -> Vec<Reason>
{
    metas.postponed().iter().map(Postponed::reason).collect()
}

/// A leaf spelled by its structure rather than its arena identity, so two runs
/// over two arenas compare: a hole by its name, a variable by its index, a
/// literal as itself.
///
/// # Specification
/// trivial.
fn leaf(
    arena: &CoreArena,
    value: ValueId,
) -> String
{
    match arena.value(value) {
        Some(&Value::Hole(hole)) => format!("?{}", u32::from(hole)),
        Some(&Value::Variable { index, .. }) => format!("#{}", u32::from(index)),
        Some(&Value::Literal(ref literal)) => format!("{literal:?}"),
        Some(other) => format!("{other:?}"),
        None => String::from("dangling"),
    }
}

/// A value spelled as [`leaf`] spells one, a tuple by its components'
/// spellings: the depth the witnesses build.
///
/// # Specification
/// trivial.
fn spelled(
    arena: &CoreArena,
    value: ValueId,
) -> String
{
    match arena.value(value) {
        Some(&Value::Tuple(ref items)) => {
            let items: Vec<String> = items.iter().map(|&item| leaf(arena, item)).collect();
            format!("({})", items.join(", "))
        },
        Some(_) | None => leaf(arena, value),
    }
}

/// The solution of each of `declared` and every waiting equation, spelled.
///
/// # Specification
/// trivial.
fn outcome(
    arena: &CoreArena,
    metas: &Metas,
    declared: &[MetaId],
) -> (Vec<String>, Vec<String>)
{
    let side = |side: Side| match side {
        Side::Value(value) => spelled(arena, value),
        Side::ValueType(_) | Side::CompType(_) => format!("{side:?}"),
    };
    let solutions = declared
        .iter()
        .map(|&meta| match metas.solution(meta) {
            Maybe::Present(solved) => spelled(arena, solved),
            Maybe::Absent(reason) => format!("{reason:?}"),
        })
        .collect();
    let waiting = metas
        .postponed()
        .iter()
        .map(|waiting| {
            let equation = waiting.equation();
            format!(
                "{} = {} under {}: {:?} on {:?}",
                side(equation.left()),
                side(equation.right()),
                u32::from(equation.scope()),
                waiting.reason(),
                waiting.blockers()
            )
        })
        .collect();
    (solutions, waiting)
}

#[test]
fn a_hole_is_declared_once()
{
    let mut metas = Metas::new();
    let hole = HoleId::from(4_u32);
    let first = meta(&mut metas, hole, Binders::NONE);
    assert_eq!(
        Maybe::Absent(declaration::Absent::Redeclared),
        metas.declare(hole, Binders::ONE)
    );
    assert_eq!(Maybe::Present(first), metas.meta(hole));
    assert_eq!(
        Maybe::Present(Binders::NONE),
        metas.scope(first),
        "a redeclaration keeps the first context"
    );
    assert_eq!(Maybe::Present(hole), metas.hole(first));
    assert_eq!(
        Maybe::Absent(meta_lookup::Absent::Undeclared),
        metas.meta(HoleId::from(5_u32))
    );
    assert_eq!(
        Maybe::Absent(meta_lookup::Absent::Unsolved),
        metas.solution(first)
    );
}

#[test]
fn a_decoded_metavariable_takes_the_quote()
{
    // `same @[a : Type] (x : a) : a` called at an integer: the parameter's
    // type `El(?a)` against the argument's.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let hole = HoleId::from(0_u32);
    let a = meta(&mut metas, hole, Binders::NONE);
    let parameter = decoded(&mut arena, hole);
    let integer = arena.value_type_base(BaseType::Integer);
    let equation = Equation::new(
        Binders::NONE,
        Side::ValueType(parameter),
        Side::ValueType(integer),
    );
    assert_eq!(Verdict::Solved, solve(&mut arena, &mut metas, &[equation]));
    let solved = solution(&metas, a);
    assert_eq!(Some(&Value::Quote(integer)), arena.value(solved));
    assert_eq!(
        integer,
        arena.value_type_element(solved, Level::zero()),
        "the parameter's type with the solution written is the argument's"
    );
}

#[test]
fn a_function_argument_solves_both_implicits()
{
    // `map @[a : Type, b : Type] (f : (x : a) -> b, …)` given a function
    // from integers to strings: `U (El ?a -> F El ?b)` against `U (Integer
    // -> F String)`.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second) = (HoleId::from(0_u32), HoleId::from(1_u32));
    let a = meta(&mut metas, first, Binders::NONE);
    let b = meta(&mut metas, second, Binders::NONE);
    let domain = decoded(&mut arena, first);
    let codomain = decoded(&mut arena, second);
    let returns = arena.comp_type_returner(codomain);
    let arrow = arena.comp_type_arrow(domain, returns);
    let parameter = arena.value_type_thunk(arrow);
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_type_base(BaseType::String);
    let returns = arena.comp_type_returner(text);
    let arrow = arena.comp_type_arrow(integer, returns);
    let argument = arena.value_type_thunk(arrow);
    let equation = Equation::new(
        Binders::NONE,
        Side::ValueType(parameter),
        Side::ValueType(argument),
    );
    assert_eq!(Verdict::Solved, solve(&mut arena, &mut metas, &[equation]));
    assert_eq!(
        Some(&Value::Quote(integer)),
        arena.value(solution(&metas, a))
    );
    assert_eq!(Some(&Value::Quote(text)), arena.value(solution(&metas, b)));
}

#[test]
fn a_data_argument_is_read_off_the_other_side()
{
    // A family indexed by an implicit `n`, `Vector(?n)`, against
    // `Vector(3)`; then against `Vector(4)`, which the solution refutes.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let hole = HoleId::from(0_u32);
    let n = meta(&mut metas, hole, Binders::NONE);
    let unknown = arena.value_hole(hole);
    let family = ConstantIndex::from(0_usize);
    let parameter = arena.value_type_data(family, vec![unknown]);
    let three = arena.value_literal(literal(Numeral::Three));
    let at_three = arena.value_type_data(family, vec![three]);
    let posed =
        |left, right| Equation::new(Binders::NONE, Side::ValueType(left), Side::ValueType(right));
    assert_eq!(
        Verdict::Solved,
        solve(&mut arena, &mut metas, &[posed(parameter, at_three)])
    );
    assert_eq!(
        Some(&Value::Literal(literal(Numeral::Three))),
        arena.value(solution(&metas, n))
    );
    let four = arena.value_literal(literal(Numeral::Four));
    let at_four = arena.value_type_data(family, vec![four]);
    assert!(
        matches!(
            solve(&mut arena, &mut metas, &[posed(parameter, at_four)]),
            Verdict::Refuted(Refutation::Clash { .. })
        ),
        "a solved metavariable reads as its solution"
    );
}

#[test]
fn a_solution_is_read_in_its_own_context()
{
    // A metavariable whose context holds one binder `x`, met under a second
    // binder `y`: against `x`, index 1 there, it is bound to index 0, `x` in
    // its own context; read again under both binders it is `x` again.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let hole = HoleId::from(0_u32);
    let m = meta(&mut metas, hole, Binders::ONE);
    let occurrence = arena.value_hole(hole);
    let x = variable(&mut arena, DeBruijnIndex::from(1_u32));
    let under_both = Binders::from(2_u32);
    let posed = |right| Equation::new(under_both, Side::Value(occurrence), Side::Value(right));
    assert_eq!(Verdict::Solved, solve(&mut arena, &mut metas, &[posed(x)]));
    assert_eq!(
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32)
        }),
        arena.value(solution(&metas, m))
    );
    assert_eq!(Verdict::Solved, solve(&mut arena, &mut metas, &[posed(x)]));
    // `y` against `x` is two distinct neutrals: a singleton type could relate
    // them, so it waits rather than clashing.
    let y = variable(&mut arena, DeBruijnIndex::from(0_u32));
    assert_eq!(
        Verdict::Postponed,
        solve(&mut arena, &mut metas, &[posed(y)])
    );
    assert_eq!(vec![Reason::Neutral], reasons(&metas));
}

#[test]
fn a_solution_naming_an_inner_binder_waits()
{
    // `U (Π (x : Integer). F El ?b)` against `U (Π (x : Integer). F El x)`:
    // the result type names the argument, which the carried support says no
    // implicit of the call's context can stand for. The support
    // over-approximates dependence, so the equation waits on `?b`.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let hole = HoleId::from(0_u32);
    let b = meta(&mut metas, hole, Binders::NONE);
    let integer = arena.value_type_base(BaseType::Integer);
    let flexible = decoded(&mut arena, hole);
    let returns = arena.comp_type_returner(flexible);
    let pi = arena.comp_type_pi(integer, returns);
    let parameter = arena.value_type_thunk(pi);
    let x = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let dependent = arena.value_type_element(x, Level::zero());
    let returns = arena.comp_type_returner(dependent);
    let pi = arena.comp_type_pi(integer, returns);
    let argument = arena.value_type_thunk(pi);
    let equation = Equation::new(
        Binders::NONE,
        Side::ValueType(parameter),
        Side::ValueType(argument),
    );
    assert_eq!(
        Verdict::Postponed,
        solve(&mut arena, &mut metas, &[equation])
    );
    assert_eq!(vec![Reason::Escape { meta: b }], reasons(&metas));
    assert_eq!(
        Some(&[b][..]),
        metas.postponed().first().map(Postponed::blockers)
    );
    assert_eq!(
        Maybe::Absent(meta_lookup::Absent::Unsolved),
        metas.solution(b)
    );
}

#[test]
fn a_metavariable_in_its_own_solution_is_refuted()
{
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second) = (HoleId::from(0_u32), HoleId::from(1_u32));
    let a = meta(&mut metas, first, Binders::NONE);
    let b = meta(&mut metas, second, Binders::NONE);
    let (hole_a, hole_b) = (arena.value_hole(first), arena.value_hole(second));
    let three = arena.value_literal(literal(Numeral::Three));
    let four = arena.value_literal(literal(Numeral::Four));
    // `?a = (?a, 3)` directly: the occurrence is under a tuple only, so no
    // instantiation removes it.
    let around_a = arena.value_tuple(&[hole_a, three]);
    let posed = |left, right| Equation::new(Binders::NONE, Side::Value(left), Side::Value(right));
    assert_eq!(
        Verdict::Refuted(Refutation::Occurs {
            meta: a,
            within: around_a
        }),
        solve(&mut arena, &mut metas, &[posed(hole_a, around_a)])
    );
    // `?a = (?b, 3)` then `?b = (?a, 4)`: the second reads through the
    // first's solution.
    let around_b = arena.value_tuple(&[hole_b, three]);
    let around_a = arena.value_tuple(&[hole_a, four]);
    assert_eq!(
        Verdict::Refuted(Refutation::Occurs {
            meta: b,
            within: around_a
        }),
        solve(&mut arena, &mut metas, &[
            posed(hole_a, around_b),
            posed(hole_b, around_a)
        ])
    );
}

#[test]
fn a_flexible_occurrence_waits()
{
    // `?m = (?f(?m),)`: the occurrence is under an applied metavariable,
    // whose solution may discard its argument, so the equation waits on both.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second) = (HoleId::from(0_u32), HoleId::from(1_u32));
    let m = meta(&mut metas, first, Binders::NONE);
    let f = meta(&mut metas, second, Binders::NONE);
    let (hole_m, hole_f) = (arena.value_hole(first), arena.value_hole(second));
    let applied = arena.value_static_application(hole_f, hole_m);
    let around = arena.value_tuple(&[applied]);
    let equation = Equation::new(Binders::NONE, Side::Value(hole_m), Side::Value(around));
    assert_eq!(
        Verdict::Postponed,
        solve(&mut arena, &mut metas, &[equation])
    );
    assert_eq!(vec![Reason::Occurs { meta: m }], reasons(&metas));
    assert_eq!(
        Some(&[m, f][..]),
        metas.postponed().first().map(Postponed::blockers)
    );
}

#[test]
fn a_postponed_equation_wakes_in_either_order()
{
    // Under one binder `x`, `?m = (x, ?k)` waits: `x` is outside `?m`'s
    // context. `?m = (?p, ?q)` solves `?m` and wakes it; it decomposes into
    // `?p = x`, which waits on `?p`, and `?q = ?k`, which binds `?k`. Posed in
    // the other order the run ends in the same solutions and the same store.
    let run = |escaping_first| {
        let mut arena = CoreArena::new();
        let mut metas = Metas::new();
        let holes = [0_u32, 1, 2, 3].map(HoleId::from);
        let declared = holes.map(|hole| meta(&mut metas, hole, Binders::NONE));
        let [hole_m, hole_p, hole_q, hole_k] = holes.map(|hole| arena.value_hole(hole));
        let bound = variable(&mut arena, DeBruijnIndex::from(0_u32));
        let escaping = arena.value_tuple(&[bound, hole_k]);
        let parts = arena.value_tuple(&[hole_p, hole_q]);
        let first = Equation::new(Binders::ONE, Side::Value(hole_m), Side::Value(escaping));
        let second = Equation::new(Binders::NONE, Side::Value(hole_m), Side::Value(parts));
        let equations = if escaping_first {
            [first, second]
        }
        else {
            [second, first]
        };
        let verdict = solve(&mut arena, &mut metas, &equations);
        (verdict, outcome(&arena, &metas, &declared))
    };
    let (verdict, (solutions, waiting)) = run(true);
    assert_eq!(Verdict::Postponed, verdict);
    assert_eq!(
        vec![
            String::from("(?1, ?2)"),
            String::from("Unsolved"),
            String::from("Unsolved"),
            String::from("?2"),
        ],
        solutions
    );
    assert_eq!(
        vec![String::from(
            "?1 = #0 under 1: Escape { meta: MetaId(1) } on [MetaId(1)]"
        )],
        waiting
    );
    assert_eq!(
        run(true),
        run(false),
        "the order of the equations is not seen"
    );
}
#[test]
fn two_metavariables_meet_in_the_wider_context()
{
    // `?b`, whose context holds one binder, against `?a`, whose context holds
    // none: `?b` is bound to `?a`, and a later `?b = 3` reads through it.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second) = (HoleId::from(0_u32), HoleId::from(1_u32));
    let a = meta(&mut metas, first, Binders::NONE);
    let b = meta(&mut metas, second, Binders::ONE);
    let (hole_a, hole_b) = (arena.value_hole(first), arena.value_hole(second));
    let three = arena.value_literal(literal(Numeral::Three));
    let posed = |left, right| Equation::new(Binders::ONE, Side::Value(left), Side::Value(right));
    assert_eq!(
        Verdict::Solved,
        solve(&mut arena, &mut metas, &[
            posed(hole_b, hole_a),
            posed(hole_b, three)
        ])
    );
    assert_eq!(hole_a, solution(&metas, b));
    assert_eq!(
        Some(&Value::Literal(literal(Numeral::Three))),
        arena.value(solution(&metas, a))
    );
}

#[test]
fn an_unconstrained_metavariable_stays_unsolved()
{
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second) = (HoleId::from(0_u32), HoleId::from(1_u32));
    let _a = meta(&mut metas, first, Binders::NONE);
    let b = meta(&mut metas, second, Binders::NONE);
    let parameter = decoded(&mut arena, first);
    let integer = arena.value_type_base(BaseType::Integer);
    let equation = Equation::new(
        Binders::NONE,
        Side::ValueType(parameter),
        Side::ValueType(integer),
    );
    assert_eq!(Verdict::Solved, solve(&mut arena, &mut metas, &[equation]));
    assert_eq!(
        Maybe::Absent(meta_lookup::Absent::Unsolved),
        metas.solution(b)
    );
}

#[test]
fn the_fragment_postpones_by_name()
{
    // Each equation the fragment cannot answer waits with its reason and its
    // blockers, and the run goes on: the last equation is still solved.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second, third, gradual) = (
        HoleId::from(0_u32),
        HoleId::from(1_u32),
        HoleId::from(2_u32),
        HoleId::from(9_u32),
    );
    let a = meta(&mut metas, first, Binders::NONE);
    let b = meta(&mut metas, second, Binders::ONE);
    let c = meta(&mut metas, third, Binders::NONE);
    let (hole_a, hole_b, hole_c) = (
        arena.value_hole(first),
        arena.value_hole(second),
        arena.value_hole(third),
    );
    let undeclared = arena.value_hole(gradual);
    let three = arena.value_literal(literal(Numeral::Three));
    let four = arena.value_literal(literal(Numeral::Four));
    let x = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let applied = arena.value_static_application(hole_a, x);
    let definition = arena.value_constant(ConstantIndex::from(0_usize));
    let around_b = arena.value_tuple(&[hole_b, three]);
    let family = arena.value_type_data(ConstantIndex::from(1_usize), vec![]);
    let built = arena.value_constructor(family, ConstructorTag::from(0_usize), vec![]);
    let unknown = arena.value_type_unknown();
    let integer = arena.value_type_base(BaseType::Integer);
    let values = |scope, left, right| Equation::new(scope, Side::Value(left), Side::Value(right));
    let equations = [
        values(Binders::ONE, applied, three),
        values(Binders::NONE, definition, three),
        values(Binders::NONE, undeclared, three),
        values(Binders::NONE, hole_a, undeclared),
        values(Binders::ONE, hole_a, around_b),
        values(Binders::ONE, x, built),
        Equation::new(
            Binders::NONE,
            Side::ValueType(unknown),
            Side::ValueType(integer),
        ),
        Equation::new(Binders::NONE, Side::Value(three), Side::ValueType(integer)),
        values(Binders::NONE, hole_c, four),
    ];
    assert_eq!(
        Verdict::Postponed,
        solve(&mut arena, &mut metas, &equations)
    );
    assert_eq!(
        vec![
            Reason::Spine,
            Reason::Unfolding,
            Reason::Gradual,
            Reason::Gradual,
            Reason::Pruning { meta: a, other: b },
            Reason::Neutral,
            Reason::Gradual,
            Reason::Families,
        ],
        reasons(&metas)
    );
    let blockers: Vec<&[MetaId]> = metas.postponed().iter().map(Postponed::blockers).collect();
    assert_eq!(
        vec![&[a][..], &[], &[], &[a], &[a, b], &[], &[], &[]],
        blockers
    );
    assert_eq!(
        Some(&Value::Literal(literal(Numeral::Four))),
        arena.value(solution(&metas, c)),
        "the equation after the waiting ones is solved"
    );
    assert_eq!(
        Maybe::Absent(meta_lookup::Absent::Unsolved),
        metas.solution(a),
        "nothing that waits binds"
    );
    // Two base types are two formers: a refutation no instantiation changes.
    let text = arena.value_type_base(BaseType::String);
    assert_eq!(
        Verdict::Refuted(Refutation::Clash {
            left: Side::ValueType(integer),
            right: Side::ValueType(text),
        }),
        solve(&mut arena, &mut metas, &[Equation::new(
            Binders::NONE,
            Side::ValueType(integer),
            Side::ValueType(text)
        )])
    );
}
