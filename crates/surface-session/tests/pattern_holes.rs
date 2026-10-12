//! Ordered live pattern execution over native constructors.

use alloc::sync::Arc;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Exhaustiveness;
use gandr_core_checker::form_value_type;
use gandr_core_nbe::ArmIndex;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainComp;
use gandr_core_nbe::DomainValue;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::Selection;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::hole::HoleId;
use gandr_core_term::pattern::BranchStatus;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Side;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_session::MatchAnalysis;
use gandr_surface_session::MatchCheckpoint;
use gandr_surface_session::MatchRun;

use crate::common::Text;
use crate::written::COLOR;
use crate::written::NESTED;
use crate::written::Ran;
use crate::written::RowCount;
use crate::written::Written;
use crate::written::refusal;

/// A payload-bearing family without parameters: `Nothing` is tag 0 and
/// `Just(x)` tag 1.
const MAYBE: &str = "data Maybe : Type { Nothing : Maybe; Just : (x : Integer) --> Maybe; }\n";

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

/// `pick` over `Outer`, its arms `arms` written in source.
///
/// # Specification
/// trivial.
fn outer_pick<'arms>(arms: impl Into<Text<'arms>>) -> Written
{
    let Text(arms) = arms.into();
    Written::new(
        &alloc::format!("{NESTED}def pick(m : Outer) -> -F Integer {{ case m {{ {arms} }} }}\n"),
        "pick",
    )
}

/// `Some(Yes(n))`, the doubly nested inhabitant of `Outer`.
///
/// # Specification
/// trivial.
fn some_yes<'digits>(
    written: &mut Written,
    digits: impl Into<Text<'digits>>,
) -> ValueId
{
    let payload = written.integer(digits);
    let inner = written.construct("Inner", 1, Vec::from([payload]));
    written.construct("Outer", 1, Vec::from([inner]))
}

/// The nullary constructor `tag` of `family`.
///
/// # Specification
/// trivial.
fn nullary<'family>(
    written: &mut Written,
    family: impl Into<Text<'family>>,
    tag: impl Into<ConstructorTag>,
) -> ValueId
{
    written.construct(family, tag, Vec::new())
}

/// An integer result, as the fixture reads it back.
///
/// # Specification
/// trivial.
fn returned<'digits>(digits: impl Into<Text<'digits>>) -> Ran
{
    let Text(digits) = digits.into();
    Ran::Returned(alloc::string::String::from(digits))
}

/// The three inhabitants, also the three distinct arm results.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Color
{
    Red,
    Green,
    Blue,
}

impl Color
{
    /// The source declaration's ordinal.
    ///
    /// # Specification
    /// trivial.
    fn tag(self) -> ConstructorTag
    {
        ConstructorTag::from(match self {
            | Self::Red => 0_usize,
            | Self::Green => 1_usize,
            | Self::Blue => 2_usize,
        })
    }
}

/// One native datatype and its unfinished ordered match.
struct Fixture
{
    /// Terms and types for the checkpoint.
    core: CoreArena,
    /// The nominal scrutinee type.
    datatype: ValueTypeId,
    /// The datatype's admitted constructor shapes.
    signature: Arc<DataSignature>,
    /// Shared pattern vocabulary.
    patterns: Patterns,
    /// Red, unfinished, Blue in source order.
    arms: [PatternId; 3],
}

impl Fixture
{
    /// A three-constructor match whose middle arm is unfinished.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the arms test red, a hole, and blue, in that order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the written first arm is settled and the last is
    ///   held.
    /// - witness: `tests::pattern_holes::an_arm_before_the_hole_still_wins`
    #[spec(ensures: |ret| matches!(ret.patterns.pattern(ret.arms[1]), Some(Pattern::Hole(_))))]
    fn new() -> Self
    {
        let mut core = CoreArena::new();
        let kind = core.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let datatype = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let signature = Arc::new(DataSignature::new(
            Vec::new(),
            vec![Vec::new(), Vec::new(), Vec::new()],
            kind,
        ));
        let mut patterns = Patterns::new();
        let red = patterns.mint(Pattern::Constructor {
            tag: Color::Red.tag(),
            fields: Vec::new(),
        });
        let hole = patterns.mint(Pattern::Hole(HoleId::from(0_u32)));
        let blue = patterns.mint(Pattern::Constructor {
            tag: Color::Blue.tag(),
            fields: Vec::new(),
        });
        Self {
            core,
            datatype,
            signature,
            patterns,
            arms: [red, hole, blue],
        }
    }

    /// Mint a closed inhabitant of the fixture datatype.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        color: Color,
    ) -> ValueId
    {
        self.core
            .value_constructor(self.datatype, color.tag(), Vec::new())
    }

    /// Ask the checkpoint against the fixture's current arm table.
    ///
    /// # Specification
    /// - requires: the checkpoint uses this fixture's core arena.
    /// - ensures: all three source-order arms are reported.
    /// - panics: if the fixture's nominal type or patterns are invalid.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hole holds the two later constructors, not the
    ///   first.
    /// - witness: `tests::pattern_holes::an_arm_before_the_hole_still_wins`
    #[spec(ensures: |ret| ret.branches().len() == self.arms.len())]
    fn analyze(
        &mut self,
        checkpoint: &MatchCheckpoint,
    ) -> MatchAnalysis
    {
        let mut context = CheckingContext::new(&mut self.core, CheckBudget::DEFAULT);
        context
            .adopt_data(ConstantIndex::from(0_usize), Arc::clone(&self.signature))
            .unwrap();
        let formed = form_value_type(&mut context, self.datatype).unwrap();
        checkpoint
            .analyze(&mut context, formed, &self.patterns, &self.arms)
            .unwrap()
    }

    /// Evaluate the match, preserving a held arm as a distinct outcome.
    ///
    /// # Specification
    /// - requires: the fixture's source-order arms are well typed.
    /// - ensures: a taken arm returns its own color; a held arm runs nothing.
    /// - panics: if a fixture cannot evaluate or the selected arm returns
    ///   another color.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — constructor tests before a hole still select, while
    ///   the hole holds its own and later bodies.
    /// - witness: `tests::pattern_holes::an_arm_before_the_hole_still_wins`
    #[spec(ensures: |ret| !matches!(ret, MatchRun::Evaluated { arm, .. } if usize::from(arm) > 2))]
    fn run(
        &mut self,
        color: Color,
    ) -> MatchRun
    {
        let value = self.value(color);
        let mut checkpoint = super::live_match::checkpoint(&self.core, value);
        let analysis = self.analyze(&checkpoint);
        let bodies = [Color::Red, Color::Green, Color::Blue].map(|color| {
            let value = self.value(color);
            self.core.computation_return(value)
        });
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let (outcome, _) = checkpoint
            .run(
                &self.core,
                definitions,
                Fuel::from(1000_u32),
                &analysis,
                &bodies,
            )
            .unwrap();
        if let MatchRun::Evaluated { arm, result } = outcome {
            let Some(&DomainComp::Return {
                value: returned, ..
            }) = checkpoint.domain().computation(result)
            else {
                panic!("the selected body returns")
            };
            let Some(&DomainValue::Constructor { tag, .. }) = checkpoint.domain().value(returned)
            else {
                panic!("the selected body returns its color")
            };
            assert_eq!(usize::from(arm), usize::from(tag));
        }
        outcome
    }
}

#[test]
fn a_hole_shadows_the_arms_written_after_it()
{
    assert_eq!(
        Fixture::new().run(Color::Blue),
        MatchRun::Held(ArmIndex::from(1_usize))
    );
}

#[test]
fn a_hole_shadows_the_constructor_no_arm_names()
{
    assert_eq!(
        Fixture::new().run(Color::Green),
        MatchRun::Held(ArmIndex::from(1_usize))
    );
}

#[test]
fn an_arm_before_the_hole_still_wins()
{
    assert!(
        matches!(Fixture::new().run(Color::Red), MatchRun::Evaluated { arm, .. } if arm == ArmIndex::from(0_usize))
    );
}

#[test]
fn an_unfilled_hole_never_runs_its_own_arm()
{
    let mut fixture = Fixture::new();
    for color in [Color::Green, Color::Blue] {
        let value = fixture.value(color);
        let mut checkpoint = super::live_match::checkpoint(&fixture.core, value);
        let analysis = fixture.analyze(&checkpoint);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let budget = Fuel::from(0_u32);
        assert_eq!(
            checkpoint
                .run(&fixture.core, definitions, budget, &analysis, &[])
                .unwrap(),
            (MatchRun::Held(ArmIndex::from(1_usize)), budget)
        );
    }
}

#[test]
fn filling_the_hole_changes_exactly_the_branches_it_shadowed()
{
    let mut fixture = Fixture::new();
    let before = [Color::Red, Color::Green, Color::Blue].map(|color| fixture.run(color));
    fixture.arms[1] = fixture.patterns.mint(Pattern::Constructor {
        tag: Color::Green.tag(),
        fields: Vec::new(),
    });
    let after = [Color::Red, Color::Green, Color::Blue].map(|color| fixture.run(color));
    assert!(matches!(before[0], MatchRun::Evaluated { arm, .. } if arm == ArmIndex::from(0_usize)));
    assert_eq!(&before[1 ..], &[MatchRun::Held(ArmIndex::from(1_usize)); 2]);
    for (expected, outcome) in after.into_iter().enumerate() {
        assert!(matches!(outcome, MatchRun::Evaluated { arm, .. } if usize::from(arm) == expected));
    }
}

#[test]
fn filling_the_hole_moves_a_stuck_branch_to_uncovered_not_to_taken()
{
    let mut holed = color_pick("Red => return 0, ? => return 1");
    let blue = nullary(&mut holed, "Color", 2);
    assert_eq!(
        holed.analyze("Color", blue).selection(),
        &Selection::Indeterminate {
            arm: ArmIndex::from(1_usize)
        },
        "before the fill the hole holds `Blue`"
    );
    let mut filled = color_pick("Red => return 0, Green => return 1, Blue => return 2");
    let green = nullary(&mut filled, "Color", 1);
    assert_eq!(
        filled.run(green),
        returned("1"),
        "the filled pattern settles the constructor it names"
    );
    let blue = nullary(&mut filled, "Color", 2);
    assert_eq!(
        filled
            .analyze_prefix("Color", blue, RowCount(2))
            .selection(),
        &Selection::Exhausted,
        "while `Blue`, which the filled pattern does not name, is uncovered rather than taken"
    );
}

#[test]
fn a_fill_turns_a_held_constructor_into_an_uncovered_one()
{
    let mut holed = color_pick("Red => return 0, ? => return 1");
    let red = nullary(&mut holed, "Color", 0);
    assert_eq!(
        holed
            .analyze("Color", red)
            .coverage()
            .as_ref()
            .unwrap()
            .exhaustiveness(),
        Exhaustiveness::Possibly,
        "before the fill the match owes an unfinished test, not a missing arm"
    );
    let filled = alloc::format!(
        "{COLOR}def pick(c : Color) -> -F Integer {{ case c {{ Red => return 0, Green => return 1 }} }}\n"
    );
    assert!(
        matches!(
            refusal(&filled, "pick"),
            Some(LoweringRefusal::NonExhaustiveMatch { .. })
        ),
        "after it `Blue` is a missing arm, which the lowering refuses by name"
    );
}

#[test]
fn a_hole_in_a_payload_stops_only_its_own_constructor()
{
    let mut written = Written::new(
        &alloc::format!(
            "{MAYBE}def pick(m : Maybe) -> -F Integer {{ case m {{ Just(?) => return 0, Nothing => return 1 }} }}\n"
        ),
        "pick",
    );
    let nothing = nullary(&mut written, "Maybe", 0);
    assert_eq!(
        written.run(nothing),
        returned("1"),
        "`Nothing` is refuted by the written head, so its own arm runs"
    );
    let three = written.integer("3");
    let just = written.construct("Maybe", 1, Vec::from([three]));
    assert!(
        matches!(written.run(just), Ran::Hole(_)),
        "`Just` reaches the unfinished payload test and stops"
    );
}

#[test]
fn a_doubly_nested_hole_is_reached_only_through_its_written_tests()
{
    let mut written =
        outer_pick("Some(Yes(?inner)) => return 0, Some(No) => return 2, None => return 1");
    let none = nullary(&mut written, "Outer", 0);
    assert_eq!(
        written.run(none),
        returned("1"),
        "the outer head refutes, so the written arm runs"
    );
    let value = some_yes(&mut written, "3");
    assert!(
        matches!(written.run(value), Ran::Hole(_)),
        "both written tests pass, and the unfinished one stops the match"
    );
    let inner = nullary(&mut written, "Inner", 0);
    let some_no = written.construct("Outer", 1, Vec::from([inner]));
    assert_eq!(
        written.run(some_no),
        returned("2"),
        "the inner head refutes beside the hole, so no indeterminacy is reported"
    );
}

#[test]
fn a_nested_constructor_pattern_binds_and_runs()
{
    let mut written =
        outer_pick("Some(Yes(k)) => return k, Some(No) => return 0, None => return 1");
    let value = some_yes(&mut written, "41");
    assert_eq!(
        written.run(value),
        returned("41"),
        "the nested binder reaches the arm body bound to the payload it names"
    );
}

#[test]
fn an_or_pattern_of_holes_is_indeterminate()
{
    let mut written = color_pick("Red => return 7, ? | ?other => return 1");
    let blue = nullary(&mut written, "Color", 2);
    assert!(
        matches!(written.run(blue), Ran::Hole(_)),
        "neither alternative can be settled, so the arm settles nothing"
    );
}

#[test]
fn a_case_whose_first_arm_is_indeterminate_is_one_hole()
{
    for arms in ["? => return 0", "?arm => return 0"] {
        let mut written = color_pick(arms);
        let red = nullary(&mut written, "Color", 0);
        assert!(
            matches!(written.run(red), Ran::Hole(_)),
            "an all-hole arm set decides nothing, named or not: `{arms}`"
        );
    }
}

#[test]
fn the_sum_eliminator_stops_at_an_indeterminate_arm()
{
    let mut written = Written::new(
        "def pick(b : Bool) -> -F Integer { case b { true => return 1, ? => return 0 } }\n",
        "pick",
    );
    let yes = written.boolean(Side::Left);
    assert_eq!(
        written.run(yes),
        returned("1"),
        "the settled injection takes its own arm"
    );
    let no = written.boolean(Side::Right);
    assert!(
        matches!(written.run(no), Ran::Hole(_)),
        "the other injection reaches the unfinished arm and stops"
    );
}

#[test]
fn an_uncompiled_arm_is_declined_and_a_hole_is_not()
{
    let text =
        "def pick(s : String) -> -F Integer { case s { \"a\" => return 1, _ => return 2 } }\n";
    assert!(
        refusal(text, "pick").is_some(),
        "a text column has no test this lowering compiles, and is declined by name"
    );
    let holed = alloc::format!(
        "{COLOR}def pick(c : Color) -> -F Integer {{ case c {{ Red => return 0, ? => return 1 }} }}\n"
    );
    assert_eq!(
        refusal(&holed, "pick"),
        None,
        "a hole the author wrote is a pattern, not a lowering boundary"
    );
}

#[test]
fn a_hole_shadows_the_second_arm_at_one_head()
{
    let mut written = outer_pick(
        "? => return 0, Some(Yes(k)) => return k, Some(No) => return 8, None => return 1",
    );
    let none = nullary(&mut written, "Outer", 0);
    assert!(
        matches!(written.run(none), Ran::Hole(_)),
        "the unfinished test precedes both arms at `Some` and stops the match"
    );
}

#[test]
fn a_stuck_arm_and_a_missing_arm_carry_different_notes()
{
    let mut stuck = color_pick("Red => return 0, ? => return 1");
    let green = nullary(&mut stuck, "Color", 1);
    let held = stuck.analyze("Color", green);
    assert_eq!(
        held.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Possibly
    );
    assert_eq!(held.selection(), &Selection::Indeterminate {
        arm: ArmIndex::from(1_usize)
    });
    let missing = alloc::format!(
        "{COLOR}def pick(c : Color) -> -F Integer {{ case c {{ Red => return 0 }} }}\n"
    );
    assert!(
        matches!(
            refusal(&missing, "pick"),
            Some(LoweringRefusal::NonExhaustiveMatch { .. })
        ),
        "an arm the author never wrote is a refusal of its own, not an unfinished test"
    );
    let mut complete = color_pick("Red => return 0, Green => return 1, Blue => return 2");
    let green = nullary(&mut complete, "Color", 1);
    let uncovered = complete.analyze_prefix("Color", green, RowCount(1));
    assert_eq!(
        uncovered.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Inexhaustive,
        "and the checker reports the arms written so far as a proved gap"
    );
    assert_eq!(uncovered.selection(), &Selection::Exhausted);
    assert!(
        !uncovered.branches().contains(&BranchStatus::Possibly),
        "a match with no hole in it reports no unfinished test"
    );
}

#[test]
fn every_arm_of_a_declared_data_case_is_addressable()
{
    let mut written = color_pick("Red => return 0, Green => return 1, Blue => return 2");
    let rows = written.rows().to_vec();
    assert_eq!(rows.len(), 3, "one row per arm");
    for (tag, row) in rows.iter().enumerate() {
        assert_eq!(row.arm, tag, "row {tag} is its own arm");
        assert!(
            matches!(written.patterns().pattern(row.pattern), Some(&Pattern::Constructor { tag: written_tag, ref fields }) if usize::from(written_tag) == tag && fields.is_empty()),
            "row {tag} tests the constructor at tag {tag}"
        );
        assert!(
            rows.iter().filter(|other| other.body == row.body).count() == 1,
            "each arm's body has its own syntax node"
        );
        let value = nullary(&mut written, "Color", tag);
        assert_eq!(
            written.run(value),
            returned(&tag.to_string()),
            "the constructor at tag {tag} reaches its own arm"
        );
    }
    assert!(
        written.rows().get(3).is_none(),
        "no row past the last constructor"
    );
}
