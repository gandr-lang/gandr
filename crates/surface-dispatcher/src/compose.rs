//! The one composition: parse, lower, adapt, check, settle.
//!
//! # One lowering, one verdict set
//!
//! A source is lowered exactly once per run, under one strictness, and every
//! declaration gets one verdict: the checker's, settled against what the
//! declaration states. The one call into the lowering sits in a private module
//! that counts it, and [`LoweringCount`] is the projection through which a run
//! shows it lowered each source once.
//!
//! # The kernel re-derives every acceptance
//!
//! After the checker judges a module, the kernel is offered every declaration
//! it accepted. A declaration the kernel does not re-derive is a disagreement
//! between the two checkers — an engine fault, never a verdict about the
//! author's source.

use core::fmt;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::SettleFault;
use gandr_surface_corpus::SettleReport;
use gandr_surface_corpus::settle;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::exercised::Exercised;

/// How many sources a run has lowered.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LoweringCount(usize);

impl From<usize> for LoweringCount
{
    /// The count of `lowerings` lowerings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(lowerings: usize) -> Self
    {
        Self(lowerings)
    }
}

impl From<LoweringCount> for usize
{
    /// The number of lowerings `count` records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: LoweringCount) -> Self
    {
        count.0
    }
}

impl fmt::Display for LoweringCount
{
    /// Writes the number of lowerings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// What one source became.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Composed<'source>
{
    /// The lowering read the source's declarations, and each was checked and
    /// settled against what it states.
    Settled
    {
        /// One report per declared name, and the module's ledger size.
        report: SettleReport<'source>,
        /// The rows of the fragment's exercised table the settled
        /// declarations carry.
        exercised: Exercised,
        /// The refusals no expectation can state, in admission order: each
        /// declaration the lowering refused at its own form files no half,
        /// so no attribute can be read off it.
        unstatable: Vec<LoweringRefusal<'source>>,
    },
    /// The lowering refused the source as a whole, before any declaration
    /// existed to carry a verdict: a root that is not a list of declarations.
    Refused(LoweringRefusal<'source>),
}

/// Why one source could not be carried through the pipeline: an engine
/// fault, never a verdict about the source.
#[derive(Clone, Debug)]
pub enum ComposeFault<'source>
{
    /// The parser could not commit its tree.
    Parse(MeldError),
    /// The lowering met an engine fault — an exhausted allowance, a tree of
    /// another grammar, a mold outside the grammar's table — so no declaration
    /// of the source can be trusted.
    Lowering(LoweringRefusal<'source>),
    /// The settle comparison was handed verdicts that are not the module's
    /// own.
    Settle(SettleFault),
    /// The kernel did not re-derive a declaration the checker accepted.
    Readmission(bridge::Readmitted),
}

impl fmt::Display for ComposeFault<'_>
{
    /// Writes the fault and what it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Parse(ref fault) => write!(f, "the parser could not commit its tree: {fault}"),
            | Self::Lowering(ref refusal) => write!(f, "the lowering faulted: {refusal}"),
            | Self::Settle(ref fault) => write!(f, "the settle comparison faulted: {fault}"),
            | Self::Readmission(ref readmitted) => {
                write!(
                    f,
                    "the kernel did not re-derive the declaration at position {} the checker accepted: ",
                    usize::from(readmitted.constant())
                )?;
                match *readmitted.outcome() {
                    | bridge::Outcome::Rejected(ref error) => {
                        write!(f, "the kernel rejected it: {error}")
                    },
                    | bridge::Outcome::Refused(refusal) => {
                        write!(f, "the bridge refused to offer it ({})", refusal.classify())
                    },
                    | bridge::Outcome::Defined { .. }
                    | bridge::Outcome::Assumed { .. }
                    | bridge::Outcome::Marked(_) => f.write_str("it crossed"),
                }
            },
        }
    }
}

impl core::error::Error for ComposeFault<'_>
{
}

/// The one call into the lowering, counted.
///
/// Nothing else in the crate names the lowering's entry, so the count this
/// module keeps is every lowering the crate performs.
mod lowering
{
    use gandr_core_term::CoreArena;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_lowering::LoweredModule;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_syntax::SyntaxTree;

    use super::LoweringCount;

    /// Lower `tree` into `arena`, counting the lowering in `lowerings`.
    ///
    /// # Specification
    /// - requires: `tree` was molded under `grammar`.
    /// - ensures: `lowerings` is one more, saturating, whatever the lowering
    ///   answered.
    /// - provides: the lowering's own answer, unchanged.
    /// - fails: the lowering's refusal of the whole module, unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`LoweringRefusal`] the lowering returns for the whole module.
    pub(super) fn lower<'source>(
        grammar: &Pbg,
        tree: &SyntaxTree<'source>,
        arena: &mut CoreArena,
        lowerings: &mut LoweringCount,
    ) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
    {
        *lowerings = LoweringCount(lowerings.0.saturating_add(1_usize));
        lower_module(grammar, tree, arena, LoweringBudget::DEFAULT)
    }
}

/// Carry one source through the pipeline: parse, lower, adapt, check, settle.
///
/// # Specification
/// - requires: `grammar` is the checked grammar the source is parsed under;
///   `root` is the corpus root the source sits under.
/// - ensures: the source is parsed once and lowered once, and `lowerings` is
///   exactly one more. A module the lowering reads is adapted to the checker's
///   input, judged, offered to the kernel and settled under `root`; the result
///   is [`Composed::Settled`] with one report per declared name, the exercised
///   rows its settled declarations carry, and the refusals of the declarations
///   refused at their own form, which no expectation can state. A source the
///   lowering refuses as a whole for a reason of the author's or of the
///   fragment's is [`Composed::Refused`] with that refusal.
/// - provides: the one verdict set a run gives the source, whichever verb runs
///   it.
/// - fails: [`ComposeFault::Parse`] when the parser cannot commit its tree;
///   [`ComposeFault::Lowering`] for a whole-module refusal of the engine-fault
///   class; [`ComposeFault::Readmission`] for a declaration the checker
///   accepted that the kernel does not re-derive; [`ComposeFault::Settle`] when
///   the settle comparison refuses the verdicts.
/// - panics: none.
/// - intension: one parse, one lowering, one judgement, one readmission and one
///   settle per source; [`LoweringCount`] is the declared projection of the
///   lowering half.
///
/// # Errors
/// - [`ComposeFault::Parse`]: the tree could not be committed.
/// - [`ComposeFault::Lowering`]: the lowering faulted before any declaration
///   could be trusted.
/// - [`ComposeFault::Readmission`]: the kernel disagreed with the checker.
/// - [`ComposeFault::Settle`]: the verdicts are not the module's own.
///
/// # Adequacy
/// - hypothesis: L2 for the settled shape — sources with every verdict kind are
///   composed and each declaration asserted at its exact stated and produced
///   verdicts, the kernel acting as the external oracle on every acceptance; L3
///   for the residue — a whole-module refusal under each class that reaches it,
///   and the lowering count asserted at one per composed source.
/// - witness: `compose::tests::a_module_settles_every_declaration_once`
/// - witness: `compose::tests::a_root_that_is_no_list_of_declarations_is_refused_whole`
/// - witness: `compose::tests::each_composition_lowers_once`
/// - witness: `compose::tests::the_root_decides_what_an_expectation_means`
/// - witness: `compose::tests::a_refusal_at_a_declaration_form_is_unstatable`
#[inline]
pub fn compose<'source>(
    grammar: &Pbg,
    root: CorpusRoot,
    source: SourceText<'source>,
    lowerings: &mut LoweringCount,
) -> Result<Composed<'source>, ComposeFault<'source>>
{
    let tree = parse(grammar, source)
        .map_err(ComposeFault::Parse)?
        .into_tree();
    let mut arena = CoreArena::new();
    let module = match lowering::lower(grammar, &tree, &mut arena, lowerings) {
        | Ok(module) => module,
        | Err(refusal) if refusal.classify() == FailureClass::EngineFault => {
            return Err(ComposeFault::Lowering(refusal));
        },
        | Err(refusal) => return Ok(Composed::Refused(refusal)),
    };
    let declarations = adapt(&module);
    let verdicts = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations,
    );
    readmitted(&arena, &verdicts)?;
    let report = settle(root, &arena, &module, &verdicts).map_err(ComposeFault::Settle)?;
    let exercised = Exercised::of(&arena, &module, &report);
    Ok(Composed::Settled {
        report,
        exercised,
        unstatable: unstatable(&module),
    })
}

/// The refusals of the declarations of `module` refused at their own form.
///
/// # Specification
/// trivial.
fn unstatable<'source>(module: &LoweredModule<'source>) -> Vec<LoweringRefusal<'source>>
{
    module
        .declarations()
        .iter()
        .filter_map(|lowered| {
            match (lowered.outcome(), lowered.signature(), lowered.definition()) {
                | (DeclarationOutcome::Refused(refusal), Maybe::Absent(_), Maybe::Absent(_)) => {
                    Some(refusal)
                },
                | (DeclarationOutcome::Refused(_), Maybe::Present(_), _)
                | (DeclarationOutcome::Refused(_), _, Maybe::Present(_))
                | (
                    DeclarationOutcome::Completed { .. }
                    | DeclarationOutcome::Uncompleted { .. }
                    | DeclarationOutcome::Bodied { .. },
                    ..,
                ) => None,
            }
        })
        .collect()
}

/// The checker's input for `module`: every declaration the lowering did not
/// refuse, in admission order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one [`Declaration`] per unrefused declaration, in admission
///   order, at the same position and with the lowering's origin as its token: a
///   completed declaration carries its declared type and its body, an
///   uncompleted one its declared type and a hole, a bodiless definition its
///   body and no signature. A refused declaration is not offered.
/// - provides: the one place that names both the lowering's module and the
///   checker's declaration input.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — one declaration of each of the four outcomes in one
///   module, asserted at its exact halves, position and origin.
/// - witness: `compose::tests::each_outcome_adapts_to_its_halves`
#[inline]
#[must_use]
pub fn adapt(module: &LoweredModule<'_>) -> Vec<Declaration>
{
    let mut declarations = Vec::with_capacity(module.declarations().len());
    for lowered in module.declarations() {
        let (declared, defined) = match lowered.outcome() {
            | DeclarationOutcome::Completed {
                declared_type,
                body,
            } => (Maybe::Present(declared_type), Maybe::Present(body)),
            | DeclarationOutcome::Uncompleted { declared_type } => (
                Maybe::Present(declared_type),
                Maybe::Absent(body::Absent::Hole),
            ),
            | DeclarationOutcome::Bodied { body } => (
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Present(body),
            ),
            | DeclarationOutcome::Refused(_) => continue,
        };
        declarations.push(Declaration::new(
            lowered.constant(),
            declared,
            defined,
            OriginToken::from(usize::from(lowered.origin())),
        ));
    }
    declarations
}

/// Have the kernel re-derive every declaration in `verdicts` the checker
/// accepted.
///
/// # Specification
/// - requires: `verdicts` was judged over `arena`.
/// - ensures: succeeds when every accepted declaration crossed as a definition
///   or an axiom; a refused declaration crosses as its mark, and a declaration
///   withheld because it names a refused one carries that one's reason, so
///   neither is a disagreement.
/// - provides: the kernel's repetition of every acceptance a run reports.
/// - fails: [`ComposeFault::Readmission`] with the first declaration the kernel
///   rejected or the bridge refused for any reason but a withheld constant.
/// - panics: none.
///
/// # Errors
/// [`ComposeFault::Readmission`]: the kernel did not re-derive an acceptance.
///
/// # Adequacy
/// - hypothesis: L3 — the routing of each outcome is separated by a module
///   readmitted over its own arena, which crosses whole beside a refused and a
///   withheld declaration, and over a foreign arena, where the first accepted
///   declaration's ids dangle.
/// - witness: `compose::tests::a_kernel_disagreement_is_an_engine_fault`
fn readmitted(
    arena: &CoreArena,
    verdicts: &ModuleReport,
) -> Result<(), ComposeFault<'static>>
{
    for readmitted in bridge::readmit(arena, verdicts).readmitted() {
        match *readmitted.outcome() {
            | bridge::Outcome::Defined { .. }
            | bridge::Outcome::Assumed { .. }
            | bridge::Outcome::Marked(_)
            | bridge::Outcome::Refused(bridge::Refusal::Withheld { .. }) => {},
            | bridge::Outcome::Refused(
                bridge::Refusal::OutOfFragment { .. }
                | bridge::Refusal::LinearVariable { .. }
                | bridge::Refusal::DanglingNode { .. }
                | bridge::Refusal::Cyclic { .. }
                | bridge::Refusal::MachineInvariant,
            )
            | bridge::Outcome::Rejected(_) => {
                return Err(ComposeFault::Readmission(readmitted.clone()));
            },
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests
{
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::Verdict;
    use gandr_core_checker::body;
    use gandr_core_checker::bridge;
    use gandr_core_checker::check_module;
    use gandr_core_checker::signature;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_corpus::Outcome;
    use gandr_surface_corpus::Produced;
    use gandr_surface_corpus::Settlement;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::FragmentBoundary;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::ComposeFault;
    use super::Composed;
    use super::LoweringCount;
    use super::adapt;
    use super::compose;
    use super::readmitted;

    /// The built-in grammar.
    ///
    /// # Specification
    ///
    /// trivial.
    fn grammar() -> Pbg
    {
        built_in().expect("the built-in grammar builds")
    }

    /// `source` composed under `root`, which must settle.
    ///
    /// # Specification
    ///
    /// trivial.
    fn settled<'source>(
        grammar: &Pbg,
        root: CorpusRoot,
        source: SourceText<'source>,
    ) -> gandr_surface_corpus::SettleReport<'source>
    {
        let mut lowerings = LoweringCount::default();
        match compose(grammar, root, source, &mut lowerings) {
            | Ok(Composed::Settled { report, .. }) => report,
            | Ok(Composed::Refused(refusal)) => panic!("refused as a whole: {refusal}"),
            | Err(fault) => panic!("faulted: {fault}"),
        }
    }

    #[test]
    fn a_module_settles_every_declaration_once()
    {
        let grammar = grammar();
        let report = settled(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(
                r#"def answer : Integer ;
def answer = 42 ;
def copy = answer ;
@[ owes(1) ] def later : Integer ;
@[ refuses("UnresolvedName") ] def broken = missing ;
def wrong : Integer ;
def wrong = "text" ;"#,
            ),
        );
        let rows: Vec<(String, Settlement, Outcome)> = report
            .declarations()
            .iter()
            .map(|declaration| {
                (
                    declaration.name().to_string(),
                    declaration.settlement(),
                    declaration.outcome(),
                )
            })
            .collect();
        let checks = |owed: usize| Outcome::Checks(gandr_core_checker::ObligationCount::from(owed));
        assert_eq!(
            rows,
            vec![
                ("answer".to_owned(), Settlement::Settled, checks(0)),
                ("copy".to_owned(), Settlement::Settled, checks(0)),
                ("later".to_owned(), Settlement::Settled, checks(1)),
                (
                    "broken".to_owned(),
                    Settlement::Settled,
                    Outcome::Refuses(gandr_surface_corpus::RefusalName::UnresolvedName)
                ),
                (
                    "wrong".to_owned(),
                    Settlement::Unsettled,
                    Outcome::Refuses(gandr_surface_corpus::RefusalName::TypeMismatch)
                ),
            ],
            "one report per declared name, in admission order"
        );
        assert!(
            matches!(
                report.declarations()[0].produced(),
                Produced::Judged(Verdict::Checked { .. })
            ),
            "a signed body checks"
        );
        assert!(
            matches!(
                report.declarations()[1].produced(),
                Produced::Judged(Verdict::Synthesised { .. })
            ),
            "an unsigned body synthesises"
        );
        assert_eq!(
            usize::from(report.ledger()),
            1_usize,
            "the owed signature is the module's one obligation"
        );
    }

    #[test]
    fn a_root_that_is_no_list_of_declarations_is_refused_whole()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let composed = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from("def greeting = \"hello\" ;\nret greeting"),
            &mut lowerings,
        );
        let Ok(Composed::Refused(refusal)) = composed
        else {
            panic!("a top-level expression refuses the module");
        };
        assert!(
            matches!(refusal, LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::WrongSort,
                ..
            }),
            "a root child that is no declaration is out of the fragment: {refusal}"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::Unrepresentable,
            "the fragment cannot represent it"
        );
    }

    #[test]
    fn each_composition_lowers_once()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let sources = [
            "def a = 3 ;",
            "ret 3",
            r#"@[ refuses("UnresolvedName") ] def a = b ;"#,
        ];
        for (composed, source) in sources.into_iter().enumerate() {
            let result = compose(
                &grammar,
                CorpusRoot::Fixture,
                SourceText::from(source),
                &mut lowerings,
            );
            assert!(result.is_ok(), "{source} composes");
            assert_eq!(
                usize::from(lowerings),
                composed.saturating_add(1_usize),
                "each composition lowers exactly once"
            );
        }
    }

    #[test]
    fn the_root_decides_what_an_expectation_means()
    {
        let grammar = grammar();
        let source = SourceText::from(r#"@[ owes(1) ] def later : Integer ;"#);
        let fixture = settled(&grammar, CorpusRoot::Fixture, source);
        let strict = settled(&grammar, CorpusRoot::Strict, source);
        assert_eq!(
            fixture.declarations()[0].settlement(),
            Settlement::Settled,
            "the fixture root reads the expectation"
        );
        assert_eq!(
            strict.declarations()[0].settlement(),
            Settlement::Unsettled,
            "the strict root refuses it"
        );
        assert_eq!(
            strict.declarations()[0].outcome(),
            Outcome::Refuses(gandr_surface_corpus::RefusalName::ExpectationOutsideFixtureRoot),
            "the guard stands in for what the declaration produced"
        );
    }

    #[test]
    fn a_refusal_at_a_declaration_form_is_unstatable()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let composed = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(
                r#"@[ refuses("OutOfFragment") ] def f(x: Integer) -> F Integer { ret x }
@[ refuses("UnresolvedName") ] def g = missing ;
def h = 1 ;"#,
            ),
            &mut lowerings,
        );
        let Ok(Composed::Settled {
            report, unstatable, ..
        }) = composed
        else {
            panic!("the module lowers");
        };
        assert!(
            matches!(unstatable.as_slice(), [LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unadmitted,
                ..
            }]),
            "the function form is refused at its own form, and only it"
        );
        let settlements: Vec<Settlement> = report
            .declarations()
            .iter()
            .map(gandr_surface_corpus::DeclarationReport::settlement)
            .collect();
        assert_eq!(
            settlements,
            vec![
                Settlement::Unsettled,
                Settlement::Settled,
                Settlement::Settled
            ],
            "the refused form's expectation cannot be read; a refused body's can"
        );
    }

    #[test]
    fn each_outcome_adapts_to_its_halves()
    {
        let grammar = grammar();
        let source = SourceText::from(
            "def done : Integer ; def done = 1 ; def owed : Integer ; def bare = 2 ; def bad = missing ; def last = 3 ;",
        );
        let tree = parse(&grammar, source).expect("parses").into_tree();
        let mut arena = CoreArena::new();
        let module = lower_module(&grammar, &tree, &mut arena, LoweringBudget::DEFAULT)
            .expect("the module lowers");
        let declarations = adapt(&module);
        let [ref done, ref owed, ref bare, _, ref last] = *module.declarations()
        else {
            panic!("five declarations are lowered");
        };
        let kept = [done, owed, bare, last];
        let positions: Vec<usize> = declarations
            .iter()
            .map(|d| usize::from(d.constant()))
            .collect();
        let expected: Vec<usize> = kept.iter().map(|l| usize::from(l.constant())).collect();
        assert_eq!(
            positions, expected,
            "every declaration but the refused one, in admission order"
        );
        for (declaration, lowered) in declarations.iter().zip(kept) {
            assert_eq!(
                usize::from(declaration.origin()),
                usize::from(lowered.origin()),
                "the origin token is the lowering's"
            );
        }
        assert!(
            matches!(
                (declarations[0].signature(), declarations[0].body()),
                (Maybe::Present(_), Maybe::Present(_))
            ),
            "a completed declaration carries both halves"
        );
        assert!(
            matches!(
                (declarations[1].signature(), declarations[1].body()),
                (Maybe::Present(_), Maybe::Absent(body::Absent::Hole))
            ),
            "an uncompleted one carries its signature and a hole"
        );
        assert!(
            matches!(
                (declarations[2].signature(), declarations[2].body()),
                (
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(_)
                )
            ),
            "a bodiless definition carries its body alone"
        );
    }

    #[test]
    fn a_kernel_disagreement_is_an_engine_fault()
    {
        let grammar = grammar();
        let source = SourceText::from(
            r#"def a : Integer ; def a = 1 ; def w : Integer ; def w = "text" ; def r = w ;"#,
        );
        let tree = parse(&grammar, source).expect("parses").into_tree();
        let mut arena = CoreArena::new();
        let module = lower_module(&grammar, &tree, &mut arena, LoweringBudget::DEFAULT)
            .expect("the module lowers");
        let verdicts = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &adapt(&module),
        );
        let outcomes: Vec<bridge::Outcome> = bridge::readmit(&arena, &verdicts)
            .readmitted()
            .iter()
            .map(|crossed| crossed.outcome().clone())
            .collect();
        assert!(
            matches!(outcomes.as_slice(), [
                bridge::Outcome::Defined { .. },
                bridge::Outcome::Marked(_),
                bridge::Outcome::Refused(bridge::Refusal::Withheld { .. }),
            ]),
            "a definition, a mark and a withheld reference: {outcomes:?}"
        );
        assert!(
            readmitted(&arena, &verdicts).is_ok(),
            "over its own arena every acceptance crosses, and a mark or a withheld reference is no \
             disagreement"
        );

        let foreign = CoreArena::new();
        let Err(ComposeFault::Readmission(fault)) = readmitted(&foreign, &verdicts)
        else {
            panic!("over a foreign arena the accepted ids dangle");
        };
        assert_eq!(
            fault.constant(),
            module.declarations()[0].constant(),
            "the first accepted declaration is the one reported"
        );
        assert!(
            matches!(
                fault.outcome(),
                bridge::Outcome::Refused(bridge::Refusal::DanglingNode { .. })
            ),
            "the bridge refused its dangling ids"
        );
    }
}
