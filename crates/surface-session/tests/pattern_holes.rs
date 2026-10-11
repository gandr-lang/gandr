//! Ordered live pattern execution over native constructors.

use alloc::sync::Arc;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::form_value_type;
use gandr_core_nbe::ArmIndex;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainComp;
use gandr_core_nbe::DomainValue;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::hole::HoleId;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::GroundSort;
use gandr_surface_session::MatchAnalysis;
use gandr_surface_session::MatchCheckpoint;
use gandr_surface_session::MatchRun;

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
    /// - hypothesis: the written first arm is settled and the last is held.
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
    /// - hypothesis: a hole holds the two later constructors, not the first.
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
    /// - hypothesis: constructor tests before a hole still select, while the
    ///   hole holds its own and later bodies.
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
