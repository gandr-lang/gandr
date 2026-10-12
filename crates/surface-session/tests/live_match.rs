//! Live answers and coverage over retained semantic scrutinees.

use core::fmt::Write as _;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Exhaustiveness;
use gandr_core_checker::Redundancy;
use gandr_core_checker::form_value_type;
use gandr_core_incremental::Typing;
use gandr_core_nbe::ArmIndex;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::Selection;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ValueId;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::TermId;
use gandr_core_term::pattern::BranchStatus;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_session::MatchCheckpoint;

use crate::common::Text;
use crate::common::resumed;
use crate::common::session;
use crate::common::submit;
use crate::written::COLOR;
use crate::written::NESTED;
use crate::written::Ran;
use crate::written::RowCount;
use crate::written::Written;
use crate::written::refusal;

/// `pick` over `Color`, its arms `arms` written in source.
///
/// # Specification
/// trivial.
fn color_pick<'arms>(arms: impl Into<Text<'arms>>) -> Written
{
    let Text(arms) = arms.into();
    Written::new(
        &alloc::format!("{COLOR}def pick(c : Color) -> -F Integer {{ case c {{ {arms} }} }}\n"),
        "pick",
    )
}

/// One step of spelling a pattern: a part still to spell, or text to emit.
#[derive(Clone, Copy, Debug)]
enum Spelling
{
    /// The pattern part at this id.
    Part(PatternId),
    /// Punctuation between or after parts.
    Text(&'static str),
}

/// The pattern `id` of `patterns`, spelled as a source author would.
///
/// # Specification
/// - requires: `id` and every part beneath it resolve in `patterns`, and every
///   literal beneath it is an integer.
/// - ensures: constructors as `#tag(fields)`, holes as `?`, binders as `x`,
///   wildcards as `_`, integers by their digits, injections as `inl`/`inr`.
/// - panics: if a part does not resolve or is a text or numeric literal.
///
/// # Adequacy
/// - hypothesis: L3 — two patterns of different shape never share a spelling.
/// - witness: `tests::live_match::translation_covers_the_landed_pattern_grammar`
#[spec(ensures: |ret| !ret.is_empty())]
fn spelled(
    patterns: &Patterns,
    id: PatternId,
) -> alloc::string::String
{
    let mut spelling = alloc::string::String::new();
    let mut pending = Vec::from([Spelling::Part(id)]);
    while let Some(step) = pending.pop() {
        let id = match step {
            | Spelling::Text(text) => {
                spelling.push_str(text);
                continue;
            },
            | Spelling::Part(id) => id,
        };
        let Some(pattern) = patterns.pattern(id)
        else {
            panic!("pattern {id:?} resolves");
        };
        match *pattern {
            | Pattern::Wildcard => spelling.push('_'),
            | Pattern::Binder => spelling.push('x'),
            | Pattern::Unit => spelling.push_str("()"),
            | Pattern::Hole(_) => spelling.push('?'),
            | Pattern::Literal(Literal::Integer(ref integer)) => {
                spelling.push_str(integer.magnitude().as_ref());
            },
            | Pattern::Literal(_) => panic!("the fixtures match integer literals only"),
            | Pattern::Pair(first, second) => {
                spelling.push('(');
                pending.extend([
                    Spelling::Text(")"),
                    Spelling::Part(second),
                    Spelling::Text(", "),
                    Spelling::Part(first),
                ]);
            },
            | Pattern::Injection(side, body) => {
                spelling.push_str(match side {
                    | Side::Left => "inl(",
                    | Side::Right => "inr(",
                });
                pending.extend([Spelling::Text(")"), Spelling::Part(body)]);
            },
            | Pattern::Constructor { tag, ref fields } => {
                write!(spelling, "#{}(", usize::from(tag)).expect("a string accepts text");
                pending.push(Spelling::Text(")"));
                for (position, &field) in fields.iter().enumerate().rev() {
                    pending.push(Spelling::Part(field));
                    if position > 0 {
                        pending.push(Spelling::Text(", "));
                    }
                }
            },
        }
    }
    spelling
}

/// Evaluate a closed fixture without global definitions.
///
/// # Specification
/// - requires: `value` is closed in `core`.
/// - ensures: the retained checkpoint holds its semantic result.
/// - panics: if the fixture cannot evaluate.
/// - executable: none — the checkpoint is opaque; callers observe what it holds
///   only through the analyses they run on it.
///
/// # Adequacy
/// - hypothesis: L3 — the callers distinguish constructor heads from holed
///   payloads.
/// - witness: `tests::live_match::a_constructor_scrutinee_refutes_the_head_and_suspends_the_payload`
pub fn checkpoint(
    core: &CoreArena,
    value: ValueId,
) -> MatchCheckpoint
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    MatchCheckpoint::evaluate(core, definitions, Fuel::from(10_000_u32), value)
        .expect("a closed fixture evaluates")
        .0
}

#[test]
fn a_hole_scrutinee_leaves_every_branch_possible()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let hole = core.value_hole(HoleId::from(0_u32));
    let checkpoint = checkpoint(&core, hole);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, any));
    let right = patterns.mint(Pattern::Injection(Side::Right, any));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).expect("sum forms");
    let analysis = checkpoint
        .analyze(&mut context, sum, &patterns, &[left, right])
        .unwrap();
    assert_eq!(analysis.branches(), &[
        BranchStatus::Possibly,
        BranchStatus::Possibly
    ]);
    assert_eq!(analysis.selection(), &Selection::Indeterminate {
        arm: ArmIndex::from(0_usize)
    });
    assert_eq!(
        analysis.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Exhaustive
    );
    let mut written = color_pick("Red => return 0, Green => return 1, Blue => return 2");
    let hole = HoleId::from(0_u32);
    let scrutinee = written.hole(hole);
    let written_analysis = written.analyze("Color", scrutinee);
    assert_eq!(
        written_analysis.branches(),
        &[BranchStatus::Possibly; 3],
        "a written match over a hole is stuck, every arm still in play"
    );
    assert_eq!(
        written.run(scrutinee),
        Ran::Hole(hole),
        "and its compiled tree stops at the scrutinee"
    );
}

#[test]
fn a_constructor_scrutinee_refutes_the_head_and_suspends_the_payload()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let hole = core.value_hole(HoleId::from(0_u32));
    let value = core.value_injection(Side::Left, hole);
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let unit_pattern = patterns.mint(Pattern::Unit);
    let right = patterns.mint(Pattern::Injection(Side::Right, any));
    let left_unit = patterns.mint(Pattern::Injection(Side::Left, unit_pattern));
    let left_any = patterns.mint(Pattern::Injection(Side::Left, any));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).unwrap();
    let analysis = checkpoint
        .analyze(&mut context, sum, &patterns, &[right, left_unit, left_any])
        .unwrap();
    assert_eq!(analysis.branches(), &[
        BranchStatus::Refuted,
        BranchStatus::Possibly,
        BranchStatus::Satisfied
    ]);
    assert_eq!(analysis.selection(), &Selection::Indeterminate {
        arm: ArmIndex::from(1_usize)
    });
}

#[test]
fn a_pattern_hole_downgrades_the_residue()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let value = core.value_unit();
    let value = core.value_injection(Side::Left, value);
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, any));
    let hole = patterns.mint(Pattern::Hole(HoleId::from(1_u32)));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).unwrap();
    let before = checkpoint
        .analyze(&mut context, sum, &patterns, &[left])
        .unwrap();
    let after = checkpoint
        .analyze(&mut context, sum, &patterns, &[left, hole])
        .unwrap();
    assert_eq!(
        before.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Inexhaustive
    );
    assert_eq!(
        after.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Possibly
    );
    assert_eq!(after.branches(), &[
        BranchStatus::Satisfied,
        BranchStatus::Possibly
    ]);
}

#[test]
fn completing_the_match_clears_the_obligation()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let value = core.value_hole(HoleId::from(0_u32));
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, any));
    let right = patterns.mint(Pattern::Injection(Side::Right, any));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).unwrap();
    let before = checkpoint
        .analyze(&mut context, sum, &patterns, &[left])
        .unwrap();
    let after = checkpoint
        .analyze(&mut context, sum, &patterns, &[left, right])
        .unwrap();
    assert_eq!(
        before.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Inexhaustive
    );
    assert_eq!(
        after.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Exhaustive
    );
}

#[test]
fn a_hole_in_the_prefix_leaves_redundancy_unproved()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let value = core.value_unit();
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let hole = patterns.mint(Pattern::Hole(HoleId::from(0_u32)));
    let any = patterns.mint(Pattern::Wildcard);
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let unit = form_value_type(&mut context, unit).unwrap();
    let analysis = checkpoint
        .analyze(&mut context, unit, &patterns, &[hole, any])
        .unwrap();
    assert_eq!(analysis.coverage().as_ref().unwrap().arms(), &[
        Redundancy::Possibly,
        Redundancy::Possibly
    ]);
    assert_eq!(analysis.branches(), &[
        BranchStatus::Possibly,
        BranchStatus::Satisfied
    ]);
    assert_eq!(analysis.selection(), &Selection::Indeterminate {
        arm: ArmIndex::from(0_usize)
    });
}

#[test]
fn a_live_branch_raises_no_redundancy_obligation()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let value = core.value_unit();
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let unit = form_value_type(&mut context, unit).unwrap();
    let analysis = checkpoint
        .analyze(&mut context, unit, &patterns, &[any])
        .unwrap();
    assert_eq!(analysis.coverage().as_ref().unwrap().arms(), &[
        Redundancy::Irredundant
    ]);
    assert_eq!(analysis.selection(), &Selection::Taken {
        arm: ArmIndex::from(0_usize),
        bindings: Vec::new()
    });
}

#[test]
fn filling_a_hole_refines_a_possible_verdict()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let hole = HoleId::from(0_u32);
    let value = core.value_hole(hole);
    let mut checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, any));
    let right = patterns.mint(Pattern::Injection(Side::Right, any));
    {
        let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
        let sum = form_value_type(&mut context, sum).unwrap();
        assert_eq!(
            checkpoint
                .analyze(&mut context, sum, &patterns, &[left, right])
                .unwrap()
                .branches(),
            &[BranchStatus::Possibly, BranchStatus::Possibly]
        );
    }
    let body = core.value_unit();
    let filled = core.value_injection(Side::Right, body);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    checkpoint
        .fill(
            &mut core,
            definitions,
            Fuel::from(10_000_u32),
            hole,
            TermId::Value(filled),
        )
        .unwrap();
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).unwrap();
    let after = checkpoint
        .analyze(&mut context, sum, &patterns, &[left, right])
        .unwrap();
    assert_eq!(after.branches(), &[
        BranchStatus::Refuted,
        BranchStatus::Satisfied
    ]);
    assert_eq!(after.selection(), &Selection::Taken {
        arm: ArmIndex::from(1_usize),
        bindings: Vec::new()
    });
}

#[test]
fn filling_preserves_the_captured_scrutinee_environment()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let hole = HoleId::from(7_u32);
    let body = core.value_hole(hole);
    let lambda = core.value_static_lambda(body);
    let argument = core.value_unit();
    let applied = core.value_static_application(lambda, argument);
    let mut checkpoint = checkpoint(&core, applied);
    let mut patterns = Patterns::new();
    let expected = patterns.mint(Pattern::Unit);
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let formed = form_value_type(&mut context, unit).unwrap();
    assert_eq!(
        checkpoint
            .analyze(&mut context, formed, &patterns, &[expected])
            .unwrap()
            .branches(),
        &[BranchStatus::Possibly]
    );
    let filling = core.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(0_u32),
    );
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    checkpoint
        .fill(
            &mut core,
            definitions,
            Fuel::from(1000_u32),
            hole,
            TermId::Value(filling),
        )
        .unwrap();
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    assert_eq!(
        checkpoint
            .analyze(&mut context, formed, &patterns, &[expected])
            .unwrap()
            .branches(),
        &[BranchStatus::Satisfied]
    );
}

#[test]
fn the_eliminator_still_fires_on_a_hole_payload()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let hole = core.value_hole(HoleId::from(0_u32));
    let left = core.value_injection(Side::Left, hole);
    let mut checkpoint = checkpoint(&core, left);
    let mut patterns = Patterns::new();
    let binder = patterns.mint(Pattern::Binder);
    let left = patterns.mint(Pattern::Injection(Side::Left, binder));
    let right = patterns.mint(Pattern::Injection(Side::Right, binder));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let formed = form_value_type(&mut context, sum).unwrap();
    let analysis = checkpoint
        .analyze(&mut context, formed, &patterns, &[left, right])
        .unwrap();
    let bound = core.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(0_u32),
    );
    let returned = core.computation_return(bound);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let (outcome, _) = checkpoint
        .run(&core, definitions, Fuel::from(1000_u32), &analysis, &[
            returned, returned,
        ])
        .unwrap();
    let gandr_surface_session::MatchRun::Evaluated { arm, result } = outcome
    else {
        panic!("the constructor head selects")
    };
    assert_eq!(arm, ArmIndex::from(0_usize));
    let Some(&gandr_core_nbe::DomainComp::Return { value, .. }) =
        checkpoint.domain().computation(result)
    else {
        panic!("returning the hole is not a stuck eliminator")
    };
    assert!(matches!(
        checkpoint.domain().value(value),
        Some(&gandr_core_nbe::DomainValue::Neutral { .. })
    ));
}

#[test]
fn a_missing_constructor_is_reported_by_name()
{
    let unfinished = alloc::format!(
        "{COLOR}def pick(c : Color) -> -F Integer {{ case c {{ Red => return 0, Green => return 1 }} }}\n"
    );
    assert!(
        matches!(
            refusal(&unfinished, "pick"),
            Some(LoweringRefusal::NonExhaustiveMatch { .. })
        ),
        "the lowering refuses the declaration a constructor has no arm in"
    );
    let mut written = color_pick("Red => return 0, Green => return 1, Blue => return 2");
    for tag in 0 .. 2_usize {
        let covered = written.construct("Color", tag, Vec::new());
        let analysis = written.analyze_prefix("Color", covered, RowCount(2));
        assert!(
            matches!(analysis.selection(), &Selection::Taken { arm, .. } if usize::from(arm) == tag),
            "the constructor at tag {tag} has its own row"
        );
    }
    let blue = written.construct("Color", 2, Vec::new());
    let analysis = written.analyze_prefix("Color", blue, RowCount(2));
    assert_eq!(
        analysis.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Inexhaustive,
        "the checker's report over the two written rows proves the residue"
    );
    assert_eq!(
        analysis.branches(),
        &[BranchStatus::Refuted; 2],
        "and the residue is `Blue`, the one constructor every row refutes"
    );
    assert_eq!(analysis.selection(), &Selection::Exhausted);
}

#[test]
fn an_inexhaustive_match_does_not_block_its_siblings()
{
    let mut session = session(SourceRoot::Strict);
    let source = alloc::format!(
        "{COLOR}def pick(c : Color) -> -F Integer {{ case c {{ Red => return 0 }} }}\ndef sibling = 41 ;\n"
    );
    let _submission = submit(&mut session, &source);
    assert!(
        matches!(
            refusal(&source, "pick"),
            Some(LoweringRefusal::NonExhaustiveMatch { .. })
        ),
        "the inexhaustive match is refused as its own declaration"
    );
    let typings = resumed(&session);
    assert!(
        matches!(typings.last(), Some(&Typing::Synthesised { .. })),
        "and the sibling definition still lands: {typings:?}"
    );
}

#[test]
fn an_or_pattern_entails_a_later_repeat_of_either_alternative()
{
    let mut written = color_pick("Red | Green => return 0, Green => return 1, Blue => return 2");
    let arms: Vec<usize> = written.rows().iter().map(|row| row.arm).collect();
    assert_eq!(
        arms,
        [0_usize, 0, 1, 2],
        "each alternative is a row of its arm"
    );
    let red = written.construct("Color", 0, Vec::new());
    let analysis = written.analyze("Color", red);
    assert_eq!(
        analysis.coverage().as_ref().unwrap().arms(),
        &[
            Redundancy::Irredundant,
            Redundancy::Irredundant,
            Redundancy::Redundant,
            Redundancy::Irredundant
        ],
        "the first arm alone entails the repeat of its `Green` alternative"
    );
}

#[test]
fn a_pattern_hole_carries_the_pattern_position_mark()
{
    let mut written = color_pick("Red => return 0, ? => return 1");
    let Some(&hole) = written.rows().get(1)
    else {
        panic!("two rows");
    };
    let Some(&Pattern::Hole(identity)) = written.patterns().pattern(hole.pattern)
    else {
        panic!("the second row is a pattern hole");
    };
    assert_eq!(
        identity,
        HoleId::from(u32::try_from(usize::from(hole.written)).unwrap()),
        "the hole is named by its pattern position"
    );
    let green = written.construct("Color", 1, Vec::new());
    let analysis = written.analyze("Color", green);
    assert_eq!(analysis.branches(), &[
        BranchStatus::Refuted,
        BranchStatus::Possibly
    ]);
    assert_eq!(
        written.run(green),
        Ran::Hole(identity),
        "the compiled tree stops at that same position, an unfinished test rather than an error"
    );
}

#[test]
fn translation_covers_the_landed_pattern_grammar()
{
    let source = alloc::format!(
        "{COLOR}{NESTED}def shapes(m : Outer) -> -F Integer {{ case m {{ None => return 0, Some(Yes(y)) => return 1, ? => return 2, ?named => return 3, x => return 4, _ => return 5 }} }}\ndef literal(n : Integer) -> -F Integer {{ case n {{ 7 => return 0, _ => return 1 }} }}\ndef flag(b : Bool) -> -F Integer {{ case b {{ true => return 0, false => return 1 }} }}\ndef either(c : Color) -> -F Integer {{ case c {{ Red | Green => return 0, Blue => return 1 }} }}\n"
    );
    for (function, expected) in [
        ("shapes", &["#0()", "#1(#1(x))", "?", "?", "x", "_"][..]),
        ("literal", &["7", "_"][..]),
        ("flag", &["inl(())", "inr(())"][..]),
        ("either", &["#0()", "#1()", "#2()"][..]),
    ] {
        let written = Written::new(&source, function);
        let rows: Vec<_> = written
            .rows()
            .iter()
            .map(|row| spelled(written.patterns(), row.pattern))
            .collect();
        assert_eq!(
            rows, expected,
            "every landed pattern form of `{function}` reaches the core matcher"
        );
    }
}
