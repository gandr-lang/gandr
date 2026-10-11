//! Test fixtures: synthetic modules, parsed, lowered and checked from source
//! text.
//!
//! A fixture runs the composition a driver runs — parse, lower, adapt the
//! lowering's declarations to the checker's input, check — so a witness
//! settles exactly what a real run hands this crate.

use alloc::format;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::AttributeRegistry;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::RegisteredAttribute;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::report::SettleReport;
use crate::root::CorpusRoot;
use crate::run::RunSpelling;
use crate::settle::settle;

/// A module lowered and checked, beside the arena both wrote into.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the fixture producer supplies the arena used to lower the module
///   and the verdicts for its accepted declarations in admission order.
/// - panics: none.
/// - executable: none — the record has no call boundary or arena-provenance
///   identity. `checked` checks the observable declaration/verdict pairing; its
///   consumer witnesses use the same arena.
///
/// # Adequacy
/// - hypothesis: L3 — clean fixture sources, including refused and owed
///   declarations; settlement and exact refusal positions observe the composed
///   inputs. Dropped, reordered or foreign verdicts are distinguished; arena
///   provenance is a construction precondition, not an identity carried by the
///   record.
/// - witness: `settle::tests::verdicts_that_are_not_the_modules_own_are_refused`
/// - witness: `settle::tests::a_lowering_refused_declaration_consumes_no_verdict`
pub struct Checked<'source>
{
    /// The arena the lowering minted into and the checker read.
    pub arena: CoreArena,
    /// The lowered module.
    pub module: LoweredModule<'source>,
    /// The checker's report for the module.
    pub verdicts: ModuleReport,
}

/// Parse, lower and check `source`, which the parser must accept cleanly and
/// the lowering must not refuse as a whole.
///
/// # Specification
/// - requires: `source` parses without repair and lowers as a module within the
///   fixture budgets.
/// - ensures: every non-refused declaration has exactly one checker verdict in
///   admission order, and every declaration span resolves in `source`.
/// - panics: when parsing needs repair, lowering refuses the module, or a
///   fixture budget is exhausted.
///
/// # Adequacy
/// - hypothesis: L3 — clean sources with checked, owed and lowering-refused
///   names; exact settlement reports and mismatch refusals observe positions,
///   order and spans. Omitting a surviving declaration, consuming a verdict for
///   a refusal or shifting a source span changes those observations.
/// - witness: `settle::tests::a_lowering_refused_declaration_consumes_no_verdict`
/// - witness: `settle::tests::verdicts_that_are_not_the_modules_own_are_refused`
#[spec(
    ensures: |ret| {
    ret.verdicts.judged().len()
        == ret
            .module
            .declarations()
            .iter()
            .filter(|lowered| {
                !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
            })
            .count()
        && ret
            .verdicts
            .judged()
            .iter()
            .zip(
                ret
                    .module
                    .declarations()
                    .iter()
                    .filter(|lowered| {
                        !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                    }),
            )
            .all(|(judged, lowered)| judged.constant() == lowered.constant())
        && ret
            .module
            .declarations()
            .iter()
            .all(|lowered| source.fragment(lowered.span()).is_ok())
},
)]
pub fn checked(source: SourceText<'_>) -> Checked<'_>
{
    let pbg = built_in().expect("the built-in grammar builds");
    let parsed = parse(&pbg, source).expect("the parser reads the source");
    assert!(
        bool::from(parsed.is_clean()),
        "the fixture source is one the parser accepts without repair"
    );
    let tree = parsed.into_tree();
    let mut arena = CoreArena::new();
    let module = lower_module(
        &pbg,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .expect("the lowering reads the module");
    let declarations = declarations(&module);
    let verdicts = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations,
    );

    Checked {
        arena,
        module,
        verdicts,
    }
}

/// The checker's input for `module`: every declaration the lowering did not
/// refuse, in admission order, its origin carried through.
///
/// # Specification
/// - requires: `module` is a lowered fixture module.
/// - ensures: only non-refused declarations are returned, in admission order,
///   preserving each constant, origin, declared type and body or its absence
///   reason.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — parsed declarations with both halves, either half and a
///   lowering refusal; the checker and settlement witnesses distinguish missing
///   signatures, missing bodies and refused entries. Reordering admitted
///   constants, losing a half or inserting a refused declaration changes the
///   observable judgement or its pairing.
/// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
/// - witness: `settle::tests::a_lowering_refused_declaration_consumes_no_verdict`
/// - witness: `settle::tests::verdicts_that_are_not_the_modules_own_are_refused`
#[spec(
    ensures: |ret| {
    ret.len()
        == module
            .declarations()
            .iter()
            .filter(|lowered| {
                !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
            })
            .count()
        && ret
            .iter()
            .zip(
                module
                    .declarations()
                    .iter()
                    .filter(|lowered| {
                        !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                    }),
            )
            .all(|(declared, lowered)| {
                let gandr_core_checker::DeclarationContent::Value { ref signature, body: ref held_body } = *declared.content() else { return false; };
                declared.constant() == lowered.constant()
                    && usize::from(declared.origin()) == usize::from(lowered.origin())
                    && match lowered.outcome() {
                        DeclarationOutcome::Completed { declared_type, body: value } => {
                            *signature == Maybe::Present(declared_type)
                                && *held_body == Maybe::Present(value)
                        }
                        DeclarationOutcome::Uncompleted { declared_type } => {
                            *signature == Maybe::Present(declared_type)
                                && *held_body == Maybe::Absent(body::Absent::Hole)
                        }
                        DeclarationOutcome::Bodied { body: value } => {
                            *signature == Maybe::Absent(signature::Absent::Unsigned)
                                && *held_body == Maybe::Present(value)
                        }
                        DeclarationOutcome::Refused(_) => false,
                    }
            })
},
)]
pub fn declarations(module: &LoweredModule<'_>) -> Vec<Declaration>
{
    module
        .declarations()
        .iter()
        .filter_map(|lowered| {
            let (declared, defined) = match lowered.outcome() {
                | DeclarationOutcome::Completed {
                    declared_type,
                    body: value,
                } => (Maybe::Present(declared_type), Maybe::Present(value)),
                | DeclarationOutcome::Uncompleted { declared_type } => (
                    Maybe::Present(declared_type),
                    Maybe::Absent(body::Absent::Hole),
                ),
                | DeclarationOutcome::Bodied { body: value } => (
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(value),
                ),
                | DeclarationOutcome::Refused(_) => return None,
            };
            let origin = OriginToken::from(usize::from(lowered.origin()));
            Some(Declaration::new(
                lowered.constant(),
                declared,
                defined,
                origin,
            ))
        })
        .collect()
}

/// The settle report for `source` under `root`, over its own verdicts, each
/// run outcome asked for spelled by [`ran_at`].
///
/// # Specification
/// - requires: `source` parses cleanly and lowers as a module within the
///   fixture budgets.
/// - ensures: the report retains `root`, and all reported declaration spans
///   resolve in `source`; its expectations are compared with its own checker
///   verdicts.
/// - panics: when the fixture cannot be parsed, lowered or paired with its
///   verdicts.
///
/// # Adequacy
/// - hypothesis: L3 — the same clean declarations under both roots, with
///   matching and mismatching expectations; exact stated/produced outcomes,
///   refusal spans and settlement distinguish a root swap, shifted span or
///   mismatched verdict sequence.
/// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
/// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
#[spec(
    ensures: |ret| {
    ret.root() == root
        && ret
            .declarations()
            .iter()
            .all(|declaration| source.fragment(declaration.span()).is_ok())
},
)]
pub fn settled(
    root: CorpusRoot,
    source: SourceText<'_>,
) -> SettleReport<'_>
{
    let checked = checked(source);
    settle(
        root,
        &checked.arena,
        &checked.module,
        &checked.verdicts,
        &mut ran_at,
    )
    .expect("the verdicts are the module's own")
}

/// The outcome the test runner spells for the declaration at `constant`:
/// `ran at n`, so a comparison shows which declaration was run.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the fixture spelling identifies exactly `constant` as `ran at n`
///   in decimal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — accepted, owed and refused declarations at distinct
///   admission positions, with and without a run expectation; settled run
///   outcomes and the callback argument sequence distinguish an off-by-one
///   constant or an unrequested execution.
/// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
#[spec(
    ensures: |ret| {
    ret
        .as_ref()
        .strip_prefix("ran at ")
        .is_some_and(|digits| digits.parse::<usize>() == Ok(usize::from(constant)))
},
)]
pub fn ran_at(constant: ConstantIndex) -> RunSpelling
{
    RunSpelling::from(format!("ran at {}", usize::from(constant)))
}

/// The span from `start` to `end`.
///
/// # Specification
/// - requires: `start` is at or before `end`.
/// - ensures: both supplied endpoints are preserved, including an empty range.
/// - panics: when the endpoints are reversed.
///
/// # Adequacy
/// - hypothesis: L3 — ordered empty and nonempty byte ranges in refusal
///   fixtures; exact reported spans observe both endpoints. Changing an
///   endpoint or rejecting the empty range breaks the payload and
///   conflicting-expectation witnesses.
/// - witness: `expectation::tests::a_payload_the_arena_does_not_hold_is_unreadable`
/// - witness: `settle::tests::a_name_carrying_two_expectations_states_none`
#[spec(
    requires: usize::from(start) <= usize::from(end),
    ensures: |ret| ret.start() == start && ret.end() == end,
)]
pub fn span(
    start: ByteOffset,
    end: ByteOffset,
) -> ByteSpan
{
    ByteSpan::new(start, end).expect("the fixture span is ordered")
}

/// The empty span at the start of a source.
///
/// # Specification
/// trivial.
pub fn empty_span() -> ByteSpan
{
    span(ByteOffset::from(0_usize), ByteOffset::from(0_usize))
}

/// The registry entry `name` spells, which must be registered.
///
/// # Specification
/// - requires: `name` is present in the attribute registry.
/// - ensures: the returned registered name has exactly the requested spelling.
/// - panics: when `name` is not registered.
///
/// # Adequacy
/// - hypothesis: L3 — registered owes and refuses schemas, with numeric and
///   text payloads; exact stated outcomes and unreadable-payload refusals
///   distinguish selecting another schema or changing its spelling.
/// - witness: `expectation::tests::an_owes_payload_outside_the_counts_states_no_verdict`
/// - witness: `expectation::tests::a_payload_the_arena_does_not_hold_is_unreadable`
#[spec(
    ensures: |ret| ret.as_ref() == name.as_ref(),
)]
pub fn registered(name: SurfaceName<'_>) -> RegisteredAttribute
{
    let Maybe::Present((entry, _schema)) = AttributeRegistry::lookup(name)
    else {
        panic!("the fixture names a registered attribute");
    };

    entry
}

/// A stateless sink used to exercise formatting failure propagation.
///
/// # Specification
/// trivial.
pub struct RefusingWriter;

impl fmt::Write for RefusingWriter
{
    /// Refuse every supplied string without writing it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every call returns the formatting refusal.
    /// - fails: always with `fmt::Error`.
    /// - panics: none.
    ///
    /// # Errors
    /// Always returns `fmt::Error`; this sink accepts no output.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a corpus report writing to an already-failed sink;
    ///   the returned refusal distinguishes swallowing the write failure.
    /// - witness: `fixture::tests::report_propagates_sink_refusal`
    #[spec(
        ensures: |ret| ret.is_err(),
    )]
    fn write_str(
        &mut self,
        _text: &str,
    ) -> fmt::Result
    {
        Err(fmt::Error)
    }
}

#[cfg(test)]
mod tests
{
    use core::fmt;

    use gandr_surface_syntax::SourceText;

    use super::RefusingWriter;
    use super::settled;
    use crate::root::CorpusRoot;

    #[test]
    fn report_propagates_sink_refusal()
    {
        let report = settled(
            CorpusRoot::Fixture,
            SourceText::from("@[ owes(1) ] def owed : Integer ;"),
        );
        assert_eq!(
            fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{report}")),
            Err(fmt::Error),
            "report rendering must propagate a sink failure"
        );
    }
}
