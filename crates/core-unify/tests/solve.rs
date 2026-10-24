//! Equations an implicit argument poses: solved, refuted, and postponed by
//! name in one store.

use alloc::collections::BTreeMap;

use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::FieldLabel;
use gandr_core_term::Sort;
use gandr_core_term::Summand;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::MarkIndex;
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
use gandr_kernel_term::GroundSort;
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
    // A prefix type and a run type: formers the fragment does not decompose.
    let open = arena.value_type_prefix(three);
    let complete = arena.value_type_run(three);
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
        Equation::new(
            Binders::NONE,
            Side::ValueType(open),
            Side::ValueType(complete),
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
            Reason::Outside,
            Reason::Families,
        ],
        reasons(&metas)
    );
    let blockers: Vec<&[MetaId]> = metas.postponed().iter().map(Postponed::blockers).collect();
    assert_eq!(
        vec![&[a][..], &[], &[], &[a], &[a, b], &[], &[], &[], &[]],
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

/// A former built around one value part.
type AroundValue = fn(&mut CoreArena, ValueId) -> ValueId;

/// A former built around one value-type part.
type AroundType = fn(&mut CoreArena, ValueTypeId) -> ValueTypeId;

/// Two values a refutation is read off.
type ValuePair = fn(&mut CoreArena) -> (ValueId, ValueId);

/// Two value types a refutation is read off.
type ValueTypePair = fn(&mut CoreArena) -> (ValueTypeId, ValueTypeId);

/// Two computation types a refutation is read off.
type CompTypePair = fn(&mut CoreArena) -> (CompTypeId, CompTypeId);

/// A field label the witnesses write.
#[derive(Clone, Copy)]
enum Label
{
    /// `size`.
    Size,
    /// `width`.
    Width,
}

/// The level one above zero.
///
/// # Specification
/// trivial.
fn one() -> Level
{
    Level::zero().succ().expect("level one is in range")
}

/// The record of one field labelled `label`.
///
/// # Specification
/// trivial.
fn field<T>(
    label: Label,
    part: T,
) -> BTreeMap<FieldLabel, T>
{
    let text = match label {
        Label::Size => "size",
        Label::Width => "width",
    };
    BTreeMap::from([(FieldLabel::from(String::from(text)), part)])
}

#[test]
fn every_value_former_decomposes_into_its_parts()
{
    // The same former around `?m` and around `3`: the run reads `?m = 3`
    // off the parts, whatever the former.
    let formers: [(&str, AroundValue); 8] = [
        ("an injection", |arena, part| {
            arena.value_injection(Summand::from(1_usize), part)
        }),
        ("a list cell", |arena, part| {
            let nil = arena.value_list_nil();
            arena.value_list_cons(part, nil)
        }),
        ("a quoted data type", |arena, part| {
            let quoted = arena.value_type_data(ConstantIndex::from(0_usize), vec![part]);
            arena.value_quote(quoted)
        }),
        ("a quoted returner", |arena, part| {
            let data = arena.value_type_data(ConstantIndex::from(0_usize), vec![part]);
            let returns = arena.comp_type_returner(data);
            arena.value_quote_computation(returns)
        }),
        ("a quoted codata type", |arena, part| {
            let codata = arena.comp_type_codata(ConstantIndex::from(2_usize), vec![part]);
            arena.value_quote_computation(codata)
        }),
        ("a static lambda", |arena, part| {
            arena.value_static_lambda(part)
        }),
        ("a constructor", |arena, part| {
            let family = arena.value_type_data(ConstantIndex::from(1_usize), vec![part]);
            arena.value_constructor(family, ConstructorTag::from(0_usize), vec![part])
        }),
        ("a record", |arena, part| {
            arena.value_record(field(Label::Size, part))
        }),
    ];
    for (former, around) in formers {
        let mut arena = CoreArena::new();
        let mut metas = Metas::new();
        let hole = HoleId::from(0_u32);
        let m = meta(&mut metas, hole, Binders::NONE);
        let unknown = arena.value_hole(hole);
        let three = arena.value_literal(literal(Numeral::Three));
        let (left, right) = (around(&mut arena, unknown), around(&mut arena, three));
        let equation = Equation::new(Binders::NONE, Side::Value(left), Side::Value(right));
        assert_eq!(
            Verdict::Solved,
            solve(&mut arena, &mut metas, &[equation]),
            "{former}"
        );
        assert_eq!(
            Some(&Value::Literal(literal(Numeral::Three))),
            arena.value(solution(&metas, m)),
            "{former} is read through its parts"
        );
    }
}

#[test]
fn differing_value_formers_clash()
{
    let pairs: [(&str, ValuePair); 6] = [
        ("two summands", |arena| {
            let three = arena.value_literal(literal(Numeral::Three));
            (
                arena.value_injection(Summand::from(0_usize), three),
                arena.value_injection(Summand::from(1_usize), three),
            )
        }),
        ("two tuple widths", |arena| {
            let three = arena.value_literal(literal(Numeral::Three));
            (
                arena.value_tuple(&[three]),
                arena.value_tuple(&[three, three]),
            )
        }),
        ("two constructor tags", |arena| {
            let family = arena.value_type_data(ConstantIndex::from(1_usize), vec![]);
            (
                arena.value_constructor(family, ConstructorTag::from(0_usize), vec![]),
                arena.value_constructor(family, ConstructorTag::from(1_usize), vec![]),
            )
        }),
        ("two constructor field counts", |arena| {
            let family = arena.value_type_data(ConstantIndex::from(1_usize), vec![]);
            let three = arena.value_literal(literal(Numeral::Three));
            (
                arena.value_constructor(family, ConstructorTag::from(0_usize), vec![three]),
                arena.value_constructor(family, ConstructorTag::from(0_usize), vec![three, three]),
            )
        }),
        ("two record labels", |arena| {
            let three = arena.value_literal(literal(Numeral::Three));
            (
                arena.value_record(field(Label::Size, three)),
                arena.value_record(field(Label::Width, three)),
            )
        }),
        ("a literal and a tuple", |arena| {
            let three = arena.value_literal(literal(Numeral::Three));
            (three, arena.value_tuple(&[three]))
        }),
    ];
    for (what, pair) in pairs {
        let mut arena = CoreArena::new();
        let mut metas = Metas::new();
        let (left, right) = pair(&mut arena);
        assert_eq!(
            Verdict::Refuted(Refutation::Clash {
                left: Side::Value(left),
                right: Side::Value(right),
            }),
            solve(&mut arena, &mut metas, &[Equation::new(
                Binders::NONE,
                Side::Value(left),
                Side::Value(right)
            )]),
            "{what}"
        );
    }
}

#[test]
fn every_type_former_decomposes_into_its_parts()
{
    // The same former around `El(?m)` and around `Integer`: the run binds
    // `?m` to the quote of `Integer`, a dependent pair's second factor under
    // one more binder than its first.
    let formers: [(&str, AroundType); 11] = [
        ("a record", |arena, part| {
            arena.value_type_record(field(Label::Size, part))
        }),
        ("a product", |arena, part| arena.value_type_product(&[part])),
        ("a sum", |arena, part| arena.value_type_sum(&[part])),
        ("a dependent pair's first factor", |arena, part| {
            let integer = arena.value_type_base(BaseType::Integer);
            arena.value_type_sigma(part, integer)
        }),
        ("a dependent pair's second factor", |arena, part| {
            let integer = arena.value_type_base(BaseType::Integer);
            arena.value_type_sigma(integer, part)
        }),
        ("a list", |arena, part| arena.value_type_list(part)),
        ("a lift", |arena, part| arena.value_type_lift(part, one())),
        ("a static pi's domain", |arena, part| {
            let integer = arena.value_type_base(BaseType::Integer);
            arena.value_type_static_pi(part, integer)
        }),
        ("a static pi's codomain", |arena, part| {
            let integer = arena.value_type_base(BaseType::Integer);
            arena.value_type_static_pi(integer, part)
        }),
        ("a lazy pair", |arena, part| {
            let returns = arena.comp_type_returner(part);
            let pair = arena.comp_type_with(&[returns]);
            arena.value_type_thunk(pair)
        }),
        ("a dependent function's domain", |arena, part| {
            let integer = arena.value_type_base(BaseType::Integer);
            let returns = arena.comp_type_returner(integer);
            let pi = arena.comp_type_pi(part, returns);
            arena.value_type_thunk(pi)
        }),
    ];
    for (former, around) in formers {
        let mut arena = CoreArena::new();
        let mut metas = Metas::new();
        let hole = HoleId::from(0_u32);
        let m = meta(&mut metas, hole, Binders::NONE);
        let unknown = decoded(&mut arena, hole);
        let integer = arena.value_type_base(BaseType::Integer);
        let (left, right) = (around(&mut arena, unknown), around(&mut arena, integer));
        let equation = Equation::new(Binders::NONE, Side::ValueType(left), Side::ValueType(right));
        assert_eq!(
            Verdict::Solved,
            solve(&mut arena, &mut metas, &[equation]),
            "{former}"
        );
        let Some(&Value::Quote(quoted)) = arena.value(solution(&metas, m))
        else {
            panic!("{former}: the metavariable is bound to a quote");
        };
        assert_eq!(
            Some(&ValueType::Base(BaseType::Integer)),
            arena.value_type(quoted),
            "{former} is read through its parts"
        );
    }
}

#[test]
fn differing_type_formers_clash()
{
    let value_types: [(&str, ValueTypePair); 7] = [
        ("two data declarations", |arena| {
            (
                arena.value_type_data(ConstantIndex::from(0_usize), vec![]),
                arena.value_type_data(ConstantIndex::from(1_usize), vec![]),
            )
        }),
        ("two record labels", |arena| {
            let integer = arena.value_type_base(BaseType::Integer);
            (
                arena.value_type_record(field(Label::Size, integer)),
                arena.value_type_record(field(Label::Width, integer)),
            )
        }),
        ("two product widths", |arena| {
            let integer = arena.value_type_base(BaseType::Integer);
            (
                arena.value_type_product(&[integer]),
                arena.value_type_product(&[integer, integer]),
            )
        }),
        ("two universe levels", |arena| {
            let sort = Sort::from(GroundSort::Value);
            (
                arena.value_type_universe(sort, Level::zero()),
                arena.value_type_universe(sort, one()),
            )
        }),
        ("two lift targets", |arena| {
            let integer = arena.value_type_base(BaseType::Integer);
            let two = one().succ().expect("level two is in range");
            (
                arena.value_type_lift(integer, one()),
                arena.value_type_lift(integer, two),
            )
        }),
        ("two abstract atoms", |arena| {
            (
                arena.value_type_abstract(ConstantIndex::from(0_usize)),
                arena.value_type_abstract(ConstantIndex::from(1_usize)),
            )
        }),
        ("a product and a list", |arena| {
            let integer = arena.value_type_base(BaseType::Integer);
            (
                arena.value_type_product(&[integer]),
                arena.value_type_list(integer),
            )
        }),
    ];
    for (what, pair) in value_types {
        let mut arena = CoreArena::new();
        let mut metas = Metas::new();
        let (left, right) = pair(&mut arena);
        let (left, right) = (Side::ValueType(left), Side::ValueType(right));
        assert_eq!(
            Verdict::Refuted(Refutation::Clash { left, right }),
            solve(&mut arena, &mut metas, &[Equation::new(
                Binders::NONE,
                left,
                right
            )]),
            "{what}"
        );
    }
    let comp_types: [(&str, CompTypePair); 4] = [
        ("two lazy pair widths", |arena| {
            let integer = arena.value_type_base(BaseType::Integer);
            let returns = arena.comp_type_returner(integer);
            (
                arena.comp_type_with(&[returns]),
                arena.comp_type_with(&[returns, returns]),
            )
        }),
        ("two codata declarations", |arena| {
            (
                arena.comp_type_codata(ConstantIndex::from(0_usize), vec![]),
                arena.comp_type_codata(ConstantIndex::from(1_usize), vec![]),
            )
        }),
        ("a returner and a lazy pair", |arena| {
            let integer = arena.value_type_base(BaseType::Integer);
            (arena.comp_type_returner(integer), arena.comp_type_with(&[]))
        }),
        ("two effect rows", |arena| {
            let integer = arena.value_type_base(BaseType::Integer);
            let console = EffectSig::new(EffectName::from("console"), Vec::<EffectOp>::new())
                .expect("an interface without operations has no duplicate");
            (
                arena.comp_type_returner(integer),
                arena.comp_type_returner_with_effects(integer, EffectRow::singleton(console)),
            )
        }),
    ];
    for (what, pair) in comp_types {
        let mut arena = CoreArena::new();
        let mut metas = Metas::new();
        let (left, right) = pair(&mut arena);
        let (left, right) = (Side::CompType(left), Side::CompType(right));
        assert_eq!(
            Verdict::Refuted(Refutation::Clash { left, right }),
            solve(&mut arena, &mut metas, &[Equation::new(
                Binders::NONE,
                left,
                right
            )]),
            "{what}"
        );
    }
}

#[test]
fn a_value_the_fragment_cannot_read_waits_by_name()
{
    // Under one binder `x`: two linear variables, a metavariable against a
    // linear one, a marked value, a metavariable applied twice, a
    // metavariable against an applied one, an undeclared hole applied, a
    // literal applied, a flow, and a solved metavariable applied.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second, third, gradual) = (
        HoleId::from(0_u32),
        HoleId::from(1_u32),
        HoleId::from(2_u32),
        HoleId::from(9_u32),
    );
    let m = meta(&mut metas, first, Binders::NONE);
    let f = meta(&mut metas, second, Binders::NONE);
    let s = meta(&mut metas, third, Binders::NONE);
    let (hole_m, hole_f, hole_s) = (
        arena.value_hole(first),
        arena.value_hole(second),
        arena.value_hole(third),
    );
    let undeclared = arena.value_hole(gradual);
    let three = arena.value_literal(literal(Numeral::Three));
    let four = arena.value_literal(literal(Numeral::Four));
    let x = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let linear = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let other_linear = arena.value_variable(Zone::Linear, DeBruijnIndex::from(1_u32));
    let marked = arena.value_mark(MarkIndex::from(0_u32), three);
    let once = arena.value_static_application(hole_f, x);
    let twice = arena.value_static_application(once, x);
    let undeclared_applied = arena.value_static_application(undeclared, x);
    let literal_applied = arena.value_static_application(three, x);
    let flow = arena.value_stay(three);
    let solved_applied = arena.value_static_application(hole_s, x);
    let posed = |left, right| Equation::new(Binders::ONE, Side::Value(left), Side::Value(right));
    let equations = [
        posed(linear, other_linear),
        posed(hole_m, linear),
        posed(three, marked),
        posed(twice, three),
        posed(hole_m, once),
        posed(undeclared_applied, three),
        posed(literal_applied, four),
        posed(flow, four),
        posed(hole_s, four),
        posed(solved_applied, three),
    ];
    assert_eq!(
        Verdict::Postponed,
        solve(&mut arena, &mut metas, &equations)
    );
    assert_eq!(
        vec![
            Reason::Linear,
            Reason::Linear,
            Reason::Gradual,
            Reason::Spine,
            Reason::Spine,
            Reason::Gradual,
            Reason::Outside,
            Reason::Outside,
            Reason::Outside,
        ],
        reasons(&metas)
    );
    let blockers: Vec<&[MetaId]> = metas.postponed().iter().map(Postponed::blockers).collect();
    assert_eq!(
        vec![&[][..], &[m], &[], &[f], &[m, f], &[], &[], &[], &[]],
        blockers
    );
    assert_eq!(
        Some(&Value::Literal(literal(Numeral::Four))),
        arena.value(solution(&metas, s)),
        "a solved metavariable applied is a redex the fragment does not reduce"
    );
}

#[test]
fn a_type_the_fragment_cannot_decompose_waits_by_name()
{
    // A buffer, two decodes at two levels, a decode of a literal, the
    // unknown computation type, two computation decodes at two levels, and a
    // function against a dependent function.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second) = (HoleId::from(0_u32), HoleId::from(1_u32));
    let a = meta(&mut metas, first, Binders::NONE);
    let c = meta(&mut metas, second, Binders::NONE);
    let (hole_a, hole_c) = (arena.value_hole(first), arena.value_hole(second));
    let three = arena.value_literal(literal(Numeral::Three));
    let integer = arena.value_type_base(BaseType::Integer);
    let buffer = arena.value_type_buffer();
    let low = arena.value_type_element(hole_a, Level::zero());
    let high = arena.value_type_element(three, one());
    let stuck = arena.value_type_element(three, Level::zero());
    let returns = arena.comp_type_returner(integer);
    let unknown = arena.comp_type_unknown();
    let comp_low = arena.comp_type_element(hole_c, Level::zero());
    let comp_high = arena.comp_type_element(three, one());
    let arrow = arena.comp_type_arrow(integer, returns);
    let pi = arena.comp_type_pi(integer, returns);
    let types =
        |left, right| Equation::new(Binders::NONE, Side::ValueType(left), Side::ValueType(right));
    let comps =
        |left, right| Equation::new(Binders::NONE, Side::CompType(left), Side::CompType(right));
    let equations = [
        types(buffer, integer),
        types(low, high),
        types(stuck, integer),
        comps(unknown, returns),
        comps(comp_low, comp_high),
        comps(arrow, pi),
    ];
    assert_eq!(
        Verdict::Postponed,
        solve(&mut arena, &mut metas, &equations)
    );
    assert_eq!(
        vec![
            Reason::Outside,
            Reason::Levels,
            Reason::Neutral,
            Reason::Gradual,
            Reason::Levels,
            Reason::Outside,
        ],
        reasons(&metas)
    );
    let blockers: Vec<&[MetaId]> = metas.postponed().iter().map(Postponed::blockers).collect();
    assert_eq!(vec![&[][..], &[a], &[], &[], &[c], &[]], blockers);
}

#[test]
fn a_decode_takes_the_quote_of_the_former_on_either_side()
{
    // `Integer = El(?b)`, a computation decode against a returner on either
    // side, and two computation decodes at one level, which meet.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let holes = [0_u32, 1, 2, 3, 4].map(HoleId::from);
    let [implicit, forward, backward, earlier, later] =
        holes.map(|hole| meta(&mut metas, hole, Binders::NONE));
    let [hole_b, hole_g, hole_h, hole_d, hole_e] = holes.map(|hole| arena.value_hole(hole));
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let decoded_b = arena.value_type_element(hole_b, Level::zero());
    let [decoded_g, decoded_h, decoded_d, decoded_e] =
        [hole_g, hole_h, hole_d, hole_e].map(|code| arena.comp_type_element(code, Level::zero()));
    let comps =
        |left, right| Equation::new(Binders::NONE, Side::CompType(left), Side::CompType(right));
    let equations = [
        Equation::new(
            Binders::NONE,
            Side::ValueType(integer),
            Side::ValueType(decoded_b),
        ),
        comps(decoded_g, returns),
        comps(returns, decoded_h),
        comps(decoded_d, decoded_e),
    ];
    assert_eq!(Verdict::Solved, solve(&mut arena, &mut metas, &equations));
    assert_eq!(
        Some(&Value::Quote(integer)),
        arena.value(solution(&metas, implicit))
    );
    for decoded in [forward, backward] {
        assert_eq!(
            Some(&Value::QuoteComputation(returns)),
            arena.value(solution(&metas, decoded))
        );
    }
    assert_eq!(
        hole_d,
        solution(&metas, later),
        "the later of two metavariables of one context is bound"
    );
    assert_eq!(
        Maybe::Absent(meta_lookup::Absent::Unsolved),
        metas.solution(earlier),
        "and the earlier one is left for its own equations"
    );
    // Read again once their codes are solved, the decodes are the types the
    // codes quote.
    assert_eq!(
        Verdict::Solved,
        solve(&mut arena, &mut metas, &[
            Equation::new(
                Binders::NONE,
                Side::ValueType(decoded_b),
                Side::ValueType(integer)
            ),
            comps(decoded_g, returns),
        ])
    );
    assert!(
        metas.postponed().is_empty(),
        "a solved decode decides its equation"
    );
}

#[test]
fn equal_leaves_hold()
{
    // Leaves minted twice, and one computation type against itself: nothing
    // to decompose, nothing to refute.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let [three, other_three] =
        [Numeral::Three; 2].map(|numeral| arena.value_literal(literal(numeral)));
    let sort = Sort::from(GroundSort::Value);
    let [universe, other_universe] =
        [(); 2].map(|()| arena.value_type_universe(sort, Level::zero()));
    let [atom, other_atom] =
        [(); 2].map(|()| arena.value_type_abstract(ConstantIndex::from(0_usize)));
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let types =
        |left, right| Equation::new(Binders::NONE, Side::ValueType(left), Side::ValueType(right));
    let equations = [
        Equation::new(Binders::NONE, Side::Value(three), Side::Value(other_three)),
        types(universe, other_universe),
        types(atom, other_atom),
        Equation::new(
            Binders::NONE,
            Side::CompType(returns),
            Side::CompType(returns),
        ),
    ];
    assert_eq!(Verdict::Solved, solve(&mut arena, &mut metas, &equations));
}

#[test]
fn a_node_another_arena_minted_waits_as_dangling()
{
    let mut minting = CoreArena::new();
    for _ in 0_u8 .. 8 {
        let _filler = minting.value_unit();
        let _filler = minting.value_type_unit();
        let _filler = minting.comp_type_unknown();
    }
    let three = minting.value_literal(literal(Numeral::Three));
    let four = minting.value_literal(literal(Numeral::Four));
    let integer = minting.value_type_base(BaseType::Integer);
    let text = minting.value_type_base(BaseType::String);
    let returns_integer = minting.comp_type_returner(integer);
    let returns_text = minting.comp_type_returner(text);
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    assert!(
        arena.value(three).is_none()
            && arena.value_type(integer).is_none()
            && arena.comp_type(returns_integer).is_none(),
        "the fresh arena holds none of the minted nodes"
    );
    let equations = [
        Equation::new(Binders::NONE, Side::Value(three), Side::Value(four)),
        Equation::new(
            Binders::NONE,
            Side::ValueType(integer),
            Side::ValueType(text),
        ),
        Equation::new(
            Binders::NONE,
            Side::CompType(returns_integer),
            Side::CompType(returns_text),
        ),
    ];
    assert_eq!(
        Verdict::Postponed,
        solve(&mut arena, &mut metas, &equations)
    );
    assert_eq!(vec![Reason::Dangling; 3], reasons(&metas));
}

#[test]
fn a_run_past_its_budget_postpones_what_is_left()
{
    // Two tuples of seventy thousand components pose more equations than one
    // run decides: those decided stand, the rest wait as spent.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let hole = HoleId::from(0_u32);
    let m = meta(&mut metas, hole, Binders::NONE);
    let unknown = arena.value_hole(hole);
    let three = arena.value_literal(literal(Numeral::Three));
    let width = 70_000_usize;
    let mut parts = vec![three; width];
    let right = arena.value_tuple(&parts);
    parts[0] = unknown;
    let left = arena.value_tuple(&parts);
    assert_eq!(
        Verdict::Postponed,
        solve(&mut arena, &mut metas, &[Equation::new(
            Binders::NONE,
            Side::Value(left),
            Side::Value(right)
        )])
    );
    let spent = reasons(&metas);
    assert!(
        !spent.is_empty() && spent.len() < width,
        "some components were decided and some were not"
    );
    assert!(spent.iter().all(|&reason| reason == Reason::Budget));
    assert!(
        metas
            .postponed()
            .iter()
            .all(|waiting| waiting.blockers().is_empty()),
        "no solution re-poses a spent equation"
    );
    assert_eq!(
        Some(&Value::Literal(literal(Numeral::Three))),
        arena.value(solution(&metas, m)),
        "the first component was decided before the steps ran out"
    );
}

#[test]
fn a_metavariable_under_any_introduction_form_is_refuted()
{
    let formers: [(&str, AroundValue); 6] = [
        ("an injection", |arena, part| {
            arena.value_injection(Summand::from(0_usize), part)
        }),
        ("a list cell", |arena, part| {
            let nil = arena.value_list_nil();
            arena.value_list_cons(part, nil)
        }),
        ("a constructor", |arena, part| {
            let family = arena.value_type_data(ConstantIndex::from(1_usize), vec![]);
            arena.value_constructor(family, ConstructorTag::from(0_usize), vec![part])
        }),
        ("a record", |arena, part| {
            arena.value_record(field(Label::Size, part))
        }),
        ("a static lambda", |arena, part| {
            arena.value_static_lambda(part)
        }),
        ("a tuple beside a shared part", |arena, part| {
            let three = arena.value_literal(literal(Numeral::Three));
            let shared = arena.value_tuple(&[three]);
            arena.value_tuple(&[part, shared, shared])
        }),
    ];
    for (former, around) in formers {
        let mut arena = CoreArena::new();
        let mut metas = Metas::new();
        let hole = HoleId::from(0_u32);
        let m = meta(&mut metas, hole, Binders::NONE);
        let unknown = arena.value_hole(hole);
        let within = around(&mut arena, unknown);
        assert_eq!(
            Verdict::Refuted(Refutation::Occurs { meta: m, within }),
            solve(&mut arena, &mut metas, &[Equation::new(
                Binders::NONE,
                Side::Value(unknown),
                Side::Value(within)
            )]),
            "{former}"
        );
    }
}

/// The row of the interfaces `names`, each with no operation.
///
/// # Specification
/// trivial.
fn interfaces<Name>(names: &[Name]) -> EffectRow
where
    Name: Copy + Into<EffectName>,
{
    names.iter().fold(EffectRow::EMPTY, |row, &name| {
        let signature = EffectSig::new(name.into(), Vec::<EffectOp>::new())
            .expect("an interface without operations has no duplicate");
        row.union(&EffectRow::singleton(signature), &CoreArena::new())
            .expect("the witnesses name each interface once")
    })
}

/// The returner of the unit at the interfaces `names`, open through the hole
/// `tail` when one is given.
///
/// # Specification
/// trivial.
fn returner<Name>(
    arena: &mut CoreArena,
    names: &[Name],
    tail: Option<HoleId>,
) -> CompTypeId
where
    Name: Copy + Into<EffectName>,
{
    let unit = arena.value_type_unit();
    let tail = tail.map(|hole| {
        let code = arena.value_hole(hole);
        arena.value_type_row_tail(code)
    });
    arena.comp_type_returner_with_effects(unit, interfaces(names).with_tail(tail))
}

/// The row a solution is, refused unless it is one.
///
/// # Specification
/// trivial.
fn row_of(
    arena: &CoreArena,
    value: ValueId,
) -> EffectRow
{
    let Some(&Value::Row(ref row)) = arena.value(value)
    else {
        panic!("a row's solution is a row: {:?}", arena.value(value));
    };
    row.clone()
}

/// The names of the interfaces `row` writes, in its order.
///
/// # Specification
/// trivial.
fn named(row: &EffectRow) -> Vec<String>
{
    row.signatures()
        .map(|signature| String::from(signature.name().as_ref()))
        .collect()
}

#[test]
fn an_open_row_takes_what_the_other_row_adds_2270()
{
    // `F^[Console | ?r] Unit` against `F^[Console, Div] Unit` solves `?r` as
    // `[Div]`; against `F^[Console] Unit` as the empty row; against
    // `F^[Div] Unit`, which lacks `Console`, the rows clash.
    for (written, solved) in [
        (&["Console", "Div"][..], &["Div"][..]),
        (&["Console"][..], &[][..]),
    ] {
        let mut arena = CoreArena::new();
        let mut metas = Metas::new();
        let hole = HoleId::from(0_u32);
        let r = meta(&mut metas, hole, Binders::NONE);
        let open = returner(&mut arena, &["Console"], Some(hole));
        let closed = returner(&mut arena, written, None);
        let equation = Equation::new(Binders::NONE, Side::CompType(open), Side::CompType(closed));
        assert_eq!(
            Verdict::Solved,
            solve(&mut arena, &mut metas, &[equation]),
            "{written:?}"
        );
        let row = row_of(&arena, solution(&metas, r));
        assert_eq!(
            named(&row),
            solved,
            "{written:?}: the tail is what the row adds"
        );
        assert_eq!(None, row.tail(), "{written:?}: closed");
    }
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let hole = HoleId::from(0_u32);
    let _r = meta(&mut metas, hole, Binders::NONE);
    let open = returner(&mut arena, &["Console"], Some(hole));
    let lacking = returner(&mut arena, &["Div"], None);
    assert!(
        matches!(
            solve(&mut arena, &mut metas, &[Equation::new(
                Binders::NONE,
                Side::CompType(open),
                Side::CompType(lacking)
            )]),
            Verdict::Refuted(Refutation::Clash { .. })
        ),
        "a closed row lacking an interface the open one writes"
    );
}

#[test]
fn an_open_row_takes_the_other_row_s_tail_2270()
{
    // `F^[Console | ?a] Unit` against `F^[Console, Div | ?b] Unit`: `?a` is
    // `[Div | ?b]`, the interface the other adds over the other's tail.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second) = (HoleId::from(0_u32), HoleId::from(1_u32));
    let a = meta(&mut metas, first, Binders::NONE);
    let _b = meta(&mut metas, second, Binders::NONE);
    let narrow = returner(&mut arena, &["Console"], Some(first));
    let wide = returner(&mut arena, &["Console", "Div"], Some(second));
    assert_eq!(
        Verdict::Solved,
        solve(&mut arena, &mut metas, &[Equation::new(
            Binders::NONE,
            Side::CompType(narrow),
            Side::CompType(wide)
        )])
    );
    let row = row_of(&arena, solution(&metas, a));
    assert_eq!(named(&row), ["Div"], "the interface the other adds");
    let tail = row.tail().expect("open");
    assert!(
        matches!(arena.value_type(tail), Some(&ValueType::RowTail(code)) if arena.value(code) == Some(&Value::Hole(second))),
        "the solution stays open through `?b`"
    );
}

#[test]
fn a_row_in_its_own_tail_is_refuted_2270()
{
    // `?a = [Div | ?a]`: no row is `Div` beside itself.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let hole = HoleId::from(0_u32);
    let a = meta(&mut metas, hole, Binders::NONE);
    let unknown = arena.value_hole(hole);
    let tail = arena.value_type_row_tail(unknown);
    let within = arena.value_row(interfaces(&["Div"]).with_tail(Some(tail)));
    assert_eq!(
        Verdict::Refuted(Refutation::Occurs { meta: a, within }),
        solve(&mut arena, &mut metas, &[Equation::new(
            Binders::NONE,
            Side::Value(unknown),
            Side::Value(within)
        )])
    );
}

#[test]
fn two_open_rows_each_lacking_an_interface_wait_2270()
{
    // `F^[Console | ?a] Unit` against `F^[Div | ?b] Unit`: each tail holds
    // what the other row writes, and the store mints no shared tail, so the
    // equation waits on both.
    let mut arena = CoreArena::new();
    let mut metas = Metas::new();
    let (first, second) = (HoleId::from(0_u32), HoleId::from(1_u32));
    let a = meta(&mut metas, first, Binders::NONE);
    let b = meta(&mut metas, second, Binders::NONE);
    let console = returner(&mut arena, &["Console"], Some(first));
    let div = returner(&mut arena, &["Div"], Some(second));
    assert_eq!(
        Verdict::Postponed,
        solve(&mut arena, &mut metas, &[Equation::new(
            Binders::NONE,
            Side::CompType(console),
            Side::CompType(div)
        )])
    );
    assert_eq!(vec![Reason::Rows], reasons(&metas));
    assert_eq!(
        Some(&[a, b][..]),
        metas.postponed().first().map(Postponed::blockers)
    );
}
