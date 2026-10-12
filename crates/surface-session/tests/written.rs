//! Matches written in source: the lowering's pattern table and compiled tree,
//! read back through the live evaluator and the checker.

use alloc::string::String;
use alloc::string::ToString as _;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::form_value_type;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::DomainComp;
use gandr_core_nbe::DomainValue;
use gandr_core_nbe::Environment;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::NeutralHead;
use gandr_core_nbe::eval_comp_within;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::hole::HoleId;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_lowering::ArmOrigin;
use gandr_surface_lowering::CaseOrigin;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_session::MatchAnalysis;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::GRAMMAR;
use crate::common::Text;

/// A three-constructor enumeration: Red, Green and Blue are tags 0, 1 and 2.
pub const COLOR: &str = "data Color : Type { Red : Color; Green : Color; Blue : Color; }\n";

/// A payload-bearing pair of families: `No` and `Yes(n)` are tags 0 and 1 of
/// `Inner`, `None` and `Some(i)` tags 0 and 1 of `Outer`.
pub const NESTED: &str = "data Inner : Type { No : Inner; Yes : (n : Integer) --> Inner; }\ndata Outer : Type { None : Outer; Some : (i : Inner) --> Outer; }\n";

/// The live evaluator's allowance for one fixture run.
const FUEL: u32 = 10_000;

/// How many of a match's rows, in source order, an analysis keeps.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RowCount(pub usize);

/// The lowering's refusal of the declaration `function` of `source`, if any.
///
/// # Specification
/// - requires: `source` lowers as a module and declares `function`.
/// - ensures: the refusal exactly when that declaration's outcome is one.
/// - panics: if the source does not lower or `function` is undeclared.
/// - executable: none — the outcome is read once from a module the call lowers
///   and drops; no state outside the call witnesses it.
///
/// # Adequacy
/// - hypothesis: L3 — a form the lowering cannot compile and a match missing an
///   arm are refused by name, and an author's hole is not.
/// - witness: `tests::pattern_holes::an_uncompiled_arm_is_declined_and_a_hole_is_not`
/// - witness: `tests::pattern_holes::a_stuck_arm_and_a_missing_arm_carry_different_notes`
pub fn refusal<'source, 'function>(
    source: impl Into<Text<'source>>,
    function: impl Into<Text<'function>>,
) -> Option<LoweringRefusal<'source>>
{
    let Text(source) = source.into();
    let Text(function) = function.into();
    let mut lowerings = LoweringCount::default();
    let lowering = lower_source(&GRAMMAR, SourceText::from(source), &mut lowerings)
        .expect("the source parses");
    let Lowered::Module { module, .. } = lowering.into_lowered()
    else {
        panic!("the source lowers as a module");
    };
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name().to_string() == function)
    else {
        panic!("`{function}` is declared");
    };
    match declaration.outcome() {
        | DeclarationOutcome::Refused(refusal) => Some(refusal),
        | _ => None,
    }
}

/// What running a written match came to.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ran
{
    /// The match returned this integer, as canonical decimal digits.
    Returned(String),
    /// The match stopped at this hole.
    Hole(HoleId),
}

/// One function whose body is a match, lowered from source.
pub struct Written
{
    /// The lowered module's arena, extended by the fixture's scrutinees.
    core: CoreArena,
    /// Every data declaration of the source: its name, constant and signature.
    families: Vec<(String, ConstantIndex, Arc<DataSignature>)>,
    /// The function's thunked body.
    function: ValueId,
    /// What the lowering kept of the match.
    case: CaseOrigin,
}

impl Written
{
    /// Lower `source` and keep the match `function`'s body is.
    ///
    /// # Specification
    /// - requires: `source` declares `function` with a body whose tail under
    ///   its parameters is a `case`.
    /// - ensures: the rows are the lowering's alternatives, in source order,
    ///   over its own pattern table.
    /// - panics: if the source does not lower, `function` lowers no body or its
    ///   body is no match.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the rows the checkpoint analyzes are the ones the
    ///   author wrote, holes and nested constructors included.
    /// - witness: `tests::live_match::translation_covers_the_landed_pattern_grammar`
    #[spec(ensures: |ret| ret.case.arms.iter().all(|row| ret.case.patterns.pattern(row.pattern).is_some()))]
    pub fn new<'source, 'function>(
        source: impl Into<Text<'source>>,
        function: impl Into<Text<'function>>,
    ) -> Self
    {
        let Text(source) = source.into();
        let Text(function) = function.into();
        let mut lowerings = LoweringCount::default();
        let lowering = lower_source(&GRAMMAR, SourceText::from(source), &mut lowerings)
            .expect("the source parses");
        let Lowered::Module {
            module,
            arena: core,
        } = lowering.into_lowered()
        else {
            panic!("the source lowers as a module");
        };
        let mut families = Vec::new();
        let mut body = None;
        for declaration in module.declarations() {
            let name = declaration.name().to_string();
            match declaration.outcome() {
                | DeclarationOutcome::Data(index) => {
                    let Maybe::Present(signature) = module.data(index)
                    else {
                        panic!("`{name}` keeps its signature");
                    };
                    families.push((name, declaration.constant(), Arc::clone(signature)));
                },
                | DeclarationOutcome::Completed { body: held, .. }
                | DeclarationOutcome::Bodied { body: held }
                    if name == function =>
                {
                    body = Some(held);
                },
                | other if name == function => panic!("`{function}` lowers a body: {other:?}"),
                | _ => {},
            }
        }
        let Some(function) = body
        else {
            panic!("`{function}` is declared");
        };
        let Some(&Value::Thunk(mut root)) = core.value(function)
        else {
            panic!("a function body is a thunk");
        };
        while let Some(&Computation::Lambda(under)) = core.computation(root) {
            root = under;
        }
        let Maybe::Present(case) = module.origins().case(root)
        else {
            panic!("the function's body is a match");
        };
        let case = case.clone();
        Self {
            core,
            families,
            function,
            case,
        }
    }

    /// The match's rows: one per alternative, in source order.
    ///
    /// # Specification
    /// trivial.
    pub fn rows(&self) -> &[ArmOrigin]
    {
        &self.case.arms
    }

    /// The table the rows' patterns live in.
    ///
    /// # Specification
    /// trivial.
    pub const fn patterns(&self) -> &Patterns
    {
        &self.case.patterns
    }

    /// The constant the family `name` was declared at.
    ///
    /// # Specification
    /// trivial.
    fn constant(
        &self,
        name: Text<'_>,
    ) -> ConstantIndex
    {
        let Text(name) = name;
        self.families
            .iter()
            .find(|family| family.0 == name)
            .map_or_else(
                || panic!("`{name}` is a declared family"),
                |&(_, constant, _)| constant,
            )
    }

    /// The nominal type of the family `name`.
    ///
    /// # Specification
    /// trivial.
    pub fn family<'name>(
        &mut self,
        name: impl Into<Text<'name>>,
    ) -> ValueTypeId
    {
        let constant = self.constant(name.into());
        self.core.value_type_data(constant, Vec::new())
    }

    /// The constructor `tag` of the family `family` over `fields`.
    ///
    /// # Specification
    /// trivial.
    pub fn construct<'family>(
        &mut self,
        family: impl Into<Text<'family>>,
        tag: impl Into<ConstructorTag>,
        fields: Vec<ValueId>,
    ) -> ValueId
    {
        let datatype = self.family(family);
        self.core.value_constructor(datatype, tag.into(), fields)
    }

    /// The nonnegative integer literal spelled `digits`.
    ///
    /// # Specification
    /// trivial.
    pub fn integer<'digits>(
        &mut self,
        digits: impl Into<Text<'digits>>,
    ) -> ValueId
    {
        let Text(digits) = digits.into();
        let magnitude =
            Magnitude::from_decimal_text(String::from(digits)).expect("canonical decimal digits");
        self.core
            .value_literal(Literal::Integer(IntegerLiteral::new(
                Sign::NonNegative,
                magnitude,
            )))
    }

    /// A value hole named `hole`.
    ///
    /// # Specification
    /// trivial.
    pub fn hole(
        &mut self,
        hole: HoleId,
    ) -> ValueId
    {
        self.core.value_hole(hole)
    }

    /// The boolean at `side`: the unit injected left for true, right for
    /// false.
    ///
    /// # Specification
    /// trivial.
    pub fn boolean(
        &mut self,
        side: Side,
    ) -> ValueId
    {
        let unit = self.core.value_unit();
        self.core.value_injection(side.into(), unit)
    }

    /// Every row's live answer against `scrutinee`, the selection, and the
    /// checker's coverage over the family `family`.
    ///
    /// # Specification
    /// trivial.
    pub fn analyze<'family>(
        &mut self,
        family: impl Into<Text<'family>>,
        scrutinee: ValueId,
    ) -> MatchAnalysis
    {
        let written = RowCount(self.case.arms.len());
        self.analyze_prefix(family, scrutinee, written)
    }

    /// The analysis of the match as written up to its row `written`: the
    /// arms after it as though the author had not written them yet.
    ///
    /// # Specification
    /// - requires: `scrutinee` is closed and inhabits `family`; `written` is at
    ///   most the number of rows.
    /// - ensures: one answer per kept row, in source order.
    /// - panics: if the checkpoint cannot evaluate or the rows cannot be read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the lowering's rows reach the core matcher and the
    ///   checker unchanged, and a constructor no kept row names is a proved
    ///   residue.
    /// - witness: `tests::live_match::a_missing_constructor_is_reported_by_name`
    #[spec(ensures: |ret| ret.branches().len() == written.0)]
    pub fn analyze_prefix<'family>(
        &mut self,
        family: impl Into<Text<'family>>,
        scrutinee: ValueId,
        written: RowCount,
    ) -> MatchAnalysis
    {
        let datatype = self.family(family);
        let checkpoint = crate::live_match::checkpoint(&self.core, scrutinee);
        let rows: Vec<PatternId> = self
            .case
            .arms
            .get(.. written.0)
            .expect("a prefix of the written rows")
            .iter()
            .map(|row| row.pattern)
            .collect();
        let mut context = CheckingContext::new(&mut self.core, CheckBudget::DEFAULT);
        for &(_, constant, ref signature) in &self.families {
            context
                .adopt_data(constant, Arc::clone(signature))
                .expect("a declared family is admitted");
        }
        let formed = form_value_type(&mut context, datatype).expect("the family forms");
        checkpoint
            .analyze(&mut context, formed, &self.case.patterns, &rows)
            .expect("the rows are readable")
    }

    /// Run the compiled match on `argument` through the live evaluator.
    ///
    /// # Specification
    /// - requires: `argument` is closed and inhabits the function's parameter.
    /// - ensures: the integer the selected arm returned, or the hole the tree
    ///   stopped at.
    /// - panics: if the run faults or ends in anything else.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the tree the lowering compiled stops at a pattern
    ///   hole for exactly the constructors the hole shadows.
    /// - witness: `tests::pattern_holes::a_hole_in_a_payload_stops_only_its_own_constructor`
    #[spec(ensures: |ret| !matches!(ret, Ran::Returned(ref digits) if digits.is_empty()))]
    pub fn run(
        &mut self,
        argument: ValueId,
    ) -> Ran
    {
        let forced = self.core.computation_force(self.function);
        let applied = self.core.computation_application(forced, argument);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let (result, _) = eval_comp_within(
            &self.core,
            &mut domain,
            definitions,
            Fuel::from(FUEL),
            applied,
            Environment::new(),
        )
        .expect("the match runs");
        match domain.computation(result) {
            | Some(&DomainComp::Return { value, .. }) => match domain.value(value) {
                | Some(&DomainValue::Literal { literal, .. }) => match self.core.value(literal) {
                    | Some(&Value::Literal(Literal::Integer(ref integer))) => {
                        Ran::Returned(String::from(integer.magnitude().as_ref()))
                    },
                    | other => panic!("the arm returns an integer: {other:?}"),
                },
                | other => panic!("the arm returns a literal: {other:?}"),
            },
            | Some(&DomainComp::Neutral { neutral, .. }) => {
                match domain.neutral(neutral).map(gandr_core_nbe::Neutral::head) {
                    | Some(NeutralHead::Hole { hole, .. }) => Ran::Hole(hole),
                    | other => panic!("the match stops only at a hole: {other:?}"),
                }
            },
            | other => panic!("the match returns or stops: {other:?}"),
        }
    }
}
