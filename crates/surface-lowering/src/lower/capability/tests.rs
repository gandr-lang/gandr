use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::OriginToken;
use gandr_core_checker::Verdict;
use gandr_core_checker::body;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::error::CrossedExit;
use crate::error::LoweringRefusal;
use crate::fixture::grammar;
use crate::fixture::parsed;
use crate::lower::LoweringBudget;
use crate::lower::lower_module;
use crate::module::DeclarationOutcome;
use crate::module::LoweredModule;
use crate::namespace::Recognition;
use crate::origin::Labelled;
use crate::resolve::HeadArity;
use crate::resolve::SurfaceName;

/// The module the parser and the lowering make of `source`.
///
/// # Specification
/// - requires: the source parses cleanly within the default allowance.
/// - ensures: one declaration per declared name.
/// - fails: never on accepted fixtures.
/// - panics: if the lowering refuses the module.
///
/// # Adequacy
/// - hypothesis: L3 — every witness below reads its module through here.
/// - witness: `lower::capability::tests::a_capability_type_lowers_to_its_authority`
#[spec(ensures: |ret| !ret.declarations().is_empty())]
fn lowered<'source>(
    source: SourceText<'source>,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
{
    let pbg = grammar();
    let tree = parsed(&pbg, source);

    lower_module(
        &pbg,
        &tree,
        arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap()
}

/// The checker's verdicts over every declaration of `module` the lowering did
/// not refuse, in admission order.
///
/// # Specification
/// - requires: `module` was lowered over `arena` and declares no data and no
///   abstract type.
/// - ensures: one verdict per unrefused declaration.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the capability rules judge what the lowering made.
/// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
#[spec(ensures: |ret| ret.judged().len() <= module.declarations().len())]
fn judged(
    module: &LoweredModule<'_>,
    arena: &mut CoreArena,
) -> ModuleReport
{
    let declarations: Vec<Declaration> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let origin = OriginToken::from(usize::from(declaration.origin()));
            let (declared, defined) = match declaration.outcome() {
                DeclarationOutcome::Completed {
                    declared_type,
                    body,
                } => (Maybe::Present(declared_type), Maybe::Present(body)),
                DeclarationOutcome::Uncompleted { declared_type } => (
                    Maybe::Present(declared_type),
                    Maybe::Absent(body::Absent::Hole),
                ),
                DeclarationOutcome::Bodied { body } => (
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(body),
                ),
                DeclarationOutcome::Data(_)
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World
                | DeclarationOutcome::Refused(_) => return None,
            };
            Some(Declaration::new(
                declaration.constant(),
                declared,
                defined,
                origin,
            ))
        })
        .collect();

    check_module(
        &mut CheckingContext::new(arena, CheckBudget::DEFAULT),
        &declarations,
    )
}

/// The outcome of the declaration `name` in `module`.
///
/// # Specification
/// - requires: `module` declares `name`.
/// - ensures: that declaration's outcome.
/// - fails: never.
/// - panics: if the declaration is missing.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses read each outcome here.
/// - witness: `lower::capability::tests::a_capability_type_lowers_to_its_authority`
#[spec(ensures: |ret| module.declarations().iter().any(|declaration| declaration.outcome() == ret))]
fn outcome_of<'source>(
    module: &LoweredModule<'source>,
    name: SurfaceName<'_>,
) -> DeclarationOutcome<'source>
{
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
    else {
        panic!("`{name:?}` is declared");
    };

    declaration.outcome()
}

/// The verdict the checker gave the declaration `name` of `module`.
///
/// # Specification
/// - requires: `report` judged `module`, and `name` was not refused by the
///   lowering.
/// - ensures: that declaration's verdict.
/// - fails: never.
/// - panics: if the declaration was not judged.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses read each verdict here.
/// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
#[spec(ensures: |ret| report.judged().iter().any(|judged| judged.verdict() == ret))]
fn verdict_of(
    module: &LoweredModule<'_>,
    report: &ModuleReport,
    name: SurfaceName<'_>,
) -> Verdict
{
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
    else {
        panic!("`{name:?}` is declared");
    };
    let Some(judged) = report
        .judged()
        .iter()
        .find(|judged| judged.constant() == declaration.constant())
    else {
        panic!("`{name:?}` is judged");
    };

    judged.verdict()
}

/// The computation a function body runs under its parameters.
///
/// # Specification
/// - requires: `name` lowers to a function's thunked lambda chain.
/// - ensures: the computation under the thunk and every lambda.
/// - fails: never.
/// - panics: if `name` lowers no body or its body is no thunk.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses read each exercise and scope here.
/// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
#[spec(ensures: |ret| !matches!(arena.computation(ret), Some(&Computation::Lambda(_))))]
fn tail_of(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    name: SurfaceName<'_>,
) -> ComputationId
{
    let body = match outcome_of(module, name) {
        DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => body,
        other @ (DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_)) => panic!("`{name:?}` lowers a body: {other:?}"),
    };
    let Some(&Value::Thunk(mut computation)) = arena.value(body)
    else {
        panic!("a function body is a thunk");
    };
    while let Some(&Computation::Lambda(under)) = arena.computation(computation) {
        computation = under;
    }

    computation
}

/// The capability type declared at `declared`.
///
/// # Specification
/// trivial.
fn capability(
    arena: &CoreArena,
    declared: ValueTypeId,
) -> (&EffectRow, CapabilityGrade, Region)
{
    let Some(&ValueType::Capability {
        ref authority,
        grade,
        region,
    }) = arena.value_type(declared)
    else {
        panic!("a capability type");
    };
    (authority, grade, region)
}

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
const fn variable(index: DeBruijnIndex) -> Value
{
    Value::Variable {
        zone: Zone::Intuitionistic,
        index,
    }
}

#[test]
fn a_capability_type_lowers_to_its_authority()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def fs : Cap {write, read, exit} ;\ndef once : Cap[1] {write} ;\ndef every : Cap[ω] {read} ;\ndef none : Cap[0] {read} ;\ndef named : Cap[n] {read} ;\n",
        ),
        &mut arena,
    );
    let DeclarationOutcome::Uncompleted { declared_type } = outcome_of(&module, "fs".into())
    else {
        panic!("a held capability lowers its type");
    };
    let (authority, grade, region) = capability(&arena, declared_type);
    let granted: Vec<(&str, Vec<&str>)> = authority
        .signatures()
        .map(|signature| {
            (
                signature.name().as_ref(),
                signature
                    .operations()
                    .map(|operation| operation.name.as_ref())
                    .collect(),
            )
        })
        .collect();
    assert_eq!(
        granted,
        [
            ("Fs", alloc::vec!["read", "write"]),
            ("Proc", alloc::vec!["exit"])
        ],
        "each operation is granted under the interface offering it, and only it"
    );
    assert_eq!((grade, region), (CapabilityGrade::Durable, Region::Held));
    for (name, expected) in [
        ("once", CapabilityGrade::Consumable),
        ("every", CapabilityGrade::Durable),
    ] {
        let DeclarationOutcome::Uncompleted { declared_type } = outcome_of(&module, name.into())
        else {
            panic!("`{name}` lowers its type");
        };
        assert_eq!(capability(&arena, declared_type).1, expected, "{name}");
    }
    assert!(
        matches!(
            outcome_of(&module, "none".into()),
            DeclarationOutcome::Refused(LoweringRefusal::GradedBridge { grade, .. })
                if grade == SurfaceName::from("0")
        ),
        "a type-only grade is refused by name"
    );
    assert!(
        matches!(
            outcome_of(&module, "named".into()),
            DeclarationOutcome::Refused(LoweringRefusal::GradedBridge { grade, .. })
                if grade == SurfaceName::from("n")
        ),
        "a grade written as a name is refused by that name: {:?}",
        outcome_of(&module, "named".into())
    );
}

#[test]
fn a_returner_row_names_whole_interfaces()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def peek(c : Cap {read}) -> -F [Proc, Fs] String { c.read(\"notes\") }\n",
        ),
        &mut arena,
    );
    let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, "peek".into())
    else {
        panic!("the function lowers");
    };
    let Some(&ValueType::Thunk(arrow)) = arena.value_type(declared_type)
    else {
        panic!("a function's type is a thunk");
    };
    let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(arrow)
    else {
        panic!("one parameter's arrow");
    };
    let Some(&CompType::Returner {
        ref effects,
        result,
    }) = arena.comp_type(codomain)
    else {
        panic!("the result is a returner");
    };
    assert_eq!(
        arena.value_type(result),
        Some(&ValueType::Base(gandr_kernel_term::BaseType::String)),
        "the row qualifies the returner, not its result"
    );
    let names: Vec<(&str, usize)> = effects
        .signatures()
        .map(|signature| (signature.name().as_ref(), signature.operations().len()))
        .collect();
    assert_eq!(
        names,
        [("Fs", 8_usize), ("Proc", 1_usize)],
        "each interface the row names is held whole"
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "peek".into()),
            Verdict::Checked { .. }
        ),
        "a row wider than the body's requests checks"
    );
}

#[test]
fn an_unknown_operation_or_interface_is_refused_by_name()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def held : Cap {delete} ;\n",
            "def row(c : Cap {read}) -> -F [Net] String { c.read(\"x\") }\n",
            "def sent(c : Cap {read}) -> -F [Fs] String { c.delete(\"x\") }\n",
            "def scoped() -> -F Unit { handle c : Net { pure unit } with { pure(x) => pure x } }\n",
            "def twice() -> -F Unit { handle c : Proc { pure unit } with { pure(x) => pure x, pure(y) => pure y, oper exit(code, k) => k(unit) } }\n",
        )),
        &mut arena,
    );
    for name in ["held", "sent"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name: refused, .. })
                    if refused == SurfaceName::from("delete")
            ),
            "{name}: an operation no host interface offers"
        );
    }
    for name in ["row", "scoped"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedTypeHead {
                    name: refused,
                    arity: HeadArity::Nullary,
                    ..
                }) if refused == SurfaceName::from("Net")
            ),
            "{name}: an interface the host does not declare"
        );
    }
    assert!(
        matches!(
            outcome_of(&module, "twice".into()),
            DeclarationOutcome::Refused(LoweringRefusal::DuplicateDefinition { name, .. })
                if name == SurfaceName::from("pure")
        ),
        "a scope answers its return once"
    );
}

#[test]
fn an_exercise_is_checked_against_the_authority_it_was_attenuated_to()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def fs : Cap {read, write} ;\n",
            "def peek(c : Cap {read}) -> -F [Fs] String { c.read(\"notes\") }\n",
            "def main() -> -F [Fs] String { peek(fs) }\n",
            "def save(c : Cap {read, write}) -> -F [Fs] Unit { c.write(\"notes\", \"x\") }\n",
            "def denied(c : Cap {read}) -> -F [Fs] Unit { c.write(\"notes\", \"x\") }\n",
            "def direct() -> -F [Fs] String { fs.read(\"notes\") }\n",
        )),
        &mut arena,
    );
    let peek = tail_of(&module, &arena, "peek".into());
    let Some(&Computation::Exercise {
        capability,
        ref signature,
        ref operation,
        payload,
    }) = arena.computation(peek)
    else {
        panic!("`c.read(…)` is an exercise");
    };
    assert_eq!(
        arena.value(capability),
        Some(&variable(DeBruijnIndex::from(0_u32))),
        "through the parameter"
    );
    assert_eq!(
        (signature.name().as_ref(), operation.as_ref()),
        ("Fs", "read")
    );
    assert!(
        matches!(arena.value(payload), Some(&Value::Literal(_))),
        "one argument is the payload itself"
    );
    let save = tail_of(&module, &arena, "save".into());
    let Some(&Computation::Exercise { payload, .. }) = arena.computation(save)
    else {
        panic!("`c.write(…)` is an exercise");
    };
    assert!(
        arena
            .value(payload)
            .is_some_and(|value| matches!(*value, Value::Tuple(ref members) if members.len() == 2)),
        "two arguments are their pair"
    );

    let report = judged(&module, &mut arena);
    for name in ["peek", "main", "save", "direct"] {
        assert!(
            matches!(
                verdict_of(&module, &report, name.into()),
                Verdict::Checked { .. } | Verdict::Synthesised { .. }
            ),
            "{name}: {:?}",
            verdict_of(&module, &report, name.into())
        );
    }
    assert!(
        matches!(verdict_of(&module, &report, "fs".into()), Verdict::Owed(_)),
        "a held capability is a hypothesis the ledger owes"
    );
    assert!(
        matches!(
            verdict_of(&module, &report, "denied".into()),
            Verdict::Refused(CheckRefusal::CapabilityOutsideAuthority { .. })
        ),
        "the write a read capability withholds is refused at check time"
    );
}

#[test]
fn an_exercise_s_head_answers_at_its_operation()
{
    let text = concat!(
        "def peek(c : Cap {read}) -> -F [Fs] String { c.read(\"notes\") }\n",
        "def save(c : Cap {read, write}) -> -F [Fs] Unit { c.write(\"notes\", \"x\") }\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(text), &mut arena);
    let read = |ty| arena.value_type(ty).cloned();
    let mut heads: Vec<(&str, Option<ValueType>, Option<ValueType>)> = module
        .origins()
        .labels()
        .iter()
        .filter_map(|label| match label.labelled {
            Labelled::CompType { ty, ref context } if context.is_empty() => {
                let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(ty)
                else {
                    return None;
                };
                let Some(&CompType::Returner { result: reply, .. }) = arena.comp_type(codomain)
                else {
                    return None;
                };
                Some((
                    text.get(usize::from(label.span.start()) .. usize::from(label.span.end()))?,
                    read(domain),
                    read(reply),
                ))
            },
            Labelled::ValueType { .. }
            | Labelled::CompType { .. }
            | Labelled::Value(_)
            | Labelled::Endpoint(_)
            | Labelled::Branch { .. }
            | Labelled::Bound(_) => None,
        })
        .collect();
    heads.sort_by_key(|&(written, ..)| written);
    let string = Some(ValueType::Base(BaseType::String));
    let [
        (read_head, ref read_payload, ref read_reply),
        (write_head, ref write_payload, ref write_reply),
    ] = heads[..]
    else {
        panic!("one label per exercise's head: {heads:?}");
    };
    assert_eq!(
        (read_head, read_payload, read_reply),
        ("c.read", &string, &string),
        "a read's head answers at its operation, a string to the returner of a string"
    );
    assert!(
        write_head == "c.write"
            && matches!(*write_payload, Some(ValueType::Product(ref factors)) if factors.len() == 2)
            && *write_reply == Some(ValueType::unit()),
        "a write's head answers at a pair of strings to the returner of the unit: {heads:?}"
    );
}

#[test]
fn a_scope_handles_its_capability_and_resumes()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def quit() -> -F Unit { handle c : Proc { c.exit(1) } with { pure(x) => pure x, oper exit(code, k) => k(unit) } }\n",
        ),
        &mut arena,
    );
    let quit = tail_of(&module, &arena, "quit".into());
    let Some(&Computation::Scope {
        ref signature,
        subject,
        on_return,
        ref clauses,
    }) = arena.computation(quit)
    else {
        panic!("`handle` is a capability scope");
    };
    assert_eq!(signature.name().as_ref(), "Proc");
    let Some(&Computation::Exercise { capability, .. }) = arena.computation(subject)
    else {
        panic!("the subject exercises its capability");
    };
    let bound = variable(DeBruijnIndex::from(0_u32));
    assert_eq!(
        arena.value(capability),
        Some(&bound),
        "the scope's own binder"
    );
    let Some(&Computation::Return(result)) = arena.computation(on_return)
    else {
        panic!("the return clause returns");
    };
    assert_eq!(arena.value(result), Some(&bound), "its result's binder");
    let (1, Some(clause)) = (clauses.len(), clauses.first())
    else {
        panic!("one operation clause");
    };
    assert_eq!(clause.operation.as_ref(), "exit");
    let Some(&Computation::Resume(continuation, reply)) = arena.computation(clause.body)
    else {
        panic!("`k(unit)` resumes");
    };
    assert_eq!(
        arena.value(continuation),
        Some(&bound),
        "the continuation, bound after the payload"
    );
    assert!(
        matches!(arena.computation(reply), Some(&Computation::Return(unit)) if arena.value(unit).is_some_and(|value| matches!(*value, Value::Tuple(ref members) if members.is_empty()))),
        "with the reply returned"
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "quit".into()),
            Verdict::Checked { .. }
        ),
        "{:?}",
        verdict_of(&module, &report, "quit".into())
    );
}

#[test]
fn a_scoped_capability_cannot_escape()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def leak() -> -F Cap {exit} { handle c : Proc { pure c } with { pure(x) => pure x, oper exit(code, k) => k(unit) } }\n",
        ),
        &mut arena,
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "leak".into()),
            Verdict::Refused(CheckRefusal::CapabilityEscaped { .. })
        ),
        "{:?}",
        verdict_of(&module, &report, "leak".into())
    );
}

#[test]
fn a_return_in_a_subject_leaves_past_the_handler()
{
    let mut arena = CoreArena::new();
    let source = concat!(
        "def leave(n : Integer) -> -F Integer { handle c : Proc { c.exit(1); return n } with { pure(x) => pure x + 1, oper exit(code, k) => k(unit) } }\n",
        "def kept() -> -F Integer { handle c : Proc { 1 } with { pure(x) => pure x, oper exit(code, k) => k(unit) } }\n",
    );
    let module = lowered(SourceText::from(source), &mut arena);
    let leave = tail_of(&module, &arena, "leave".into());
    let Some(&Computation::Reset(delimited)) = arena.computation(leave)
    else {
        panic!("a body a subject returns from is delimited");
    };
    let Some(&Computation::Scope { subject, .. }) = arena.computation(delimited)
    else {
        panic!("the delimiter holds the scope");
    };
    let Some(&Computation::Bind(_, discarded)) = arena.computation(subject)
    else {
        panic!("the subject binds its statement");
    };
    let Some(&Computation::Split { body: rest, .. }) = arena.computation(discarded)
    else {
        panic!("and discards its unit");
    };
    let Some(&Computation::Shift(unwound)) = arena.computation(rest)
    else {
        panic!("the `return` is a capture: {:?}", arena.computation(rest));
    };
    let Some(&Computation::Return(returned)) = arena.computation(unwound)
    else {
        panic!("whose body returns");
    };
    assert_eq!(
        arena.value(returned),
        Some(&variable(DeBruijnIndex::from(3_u32))),
        "the parameter, past the capture's stack, the statement and the capability"
    );
    let kept = tail_of(&module, &arena, "kept".into());
    let Some(&Computation::Scope { subject, .. }) = arena.computation(kept)
    else {
        panic!("a body nothing unwinds from is not delimited");
    };
    assert!(
        matches!(arena.computation(subject), Some(&Computation::Return(_))),
        "a subject's value tail is its result"
    );
    let subjects: Vec<core::ops::Range<usize>> = ["{ c.exit(1); return n }", "{ 1 }"]
        .into_iter()
        .filter_map(|subject| {
            source
                .find(subject)
                .map(|start| start .. start.saturating_add(subject.len()))
        })
        .collect();
    assert_eq!(subjects.len(), 2, "both subjects are written");
    assert!(
        module.inferred_exits().iter().all(|exit| {
            !subjects
                .iter()
                .any(|subject| subject.contains(&usize::from(exit.span.start())))
        }),
        "no tail of a subject is an inferred exit: {:?}",
        module.inferred_exits()
    );
    let report = judged(&module, &mut arena);
    for name in ["leave", "kept"] {
        assert!(
            matches!(
                verdict_of(&module, &report, name.into()),
                Verdict::Checked { .. }
            ),
            "{name}: {:?}",
            verdict_of(&module, &report, name.into())
        );
    }
}

#[test]
fn an_exit_that_would_run_in_a_live_frame_is_refused()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def one() -> -F Integer { 1 }\n",
            "def became() -> -F Integer { handle c : Proc { become one() } with { pure(x) => pure x, oper exit(code, k) => k(unit) } }\n",
            "def broke() -> -F Integer { loop { handle c : Proc { break(1) } with { pure(x) => pure x, oper exit(code, k) => k(unit) } } }\n",
            "def again() -> -F Integer { loop { handle c : Proc { continue } with { pure(x) => pure x, oper exit(code, k) => k(unit) } } }\n",
            "def inner() -> -F Integer { handle c : Proc { run v <- loop { break(5) } ; pure v } with { pure(x) => pure x, oper exit(code, k) => k(unit) } }\n",
        )),
        &mut arena,
    );
    for (name, crossed) in [
        ("became", CrossedExit::Become),
        ("broke", CrossedExit::Break),
        ("again", CrossedExit::Continue),
    ] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(LoweringRefusal::AcrossHandler { exit, .. })
                    if exit == crossed
            ),
            "{name}: {:?}",
            outcome_of(&module, name.into())
        );
    }
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "inner".into()),
            Verdict::Checked { .. }
        ),
        "a loop inside the subject leaves only itself: {:?}",
        verdict_of(&module, &report, "inner".into())
    );
}

#[test]
fn a_capability_at_a_scope_lives_in_its_region()
{
    let mut arena = CoreArena::new();
    let clauses = "with { pure(x) => pure x, oper exit(code, k) => k(unit) }";
    let source = alloc::format!(
        "def regions() -> -F Unit {{ handle c : Proc {{ handle e : Proc {{ run d : Cap {{exit}} at c <- pure c ; run f : Cap {{exit}} at e <- pure e ; pure unit }} {clauses} }} {clauses} }}\n\
         def unbound(c : Integer) -> -F Unit {{ handle e : Proc {{ run d : Cap {{exit}} at c <- pure e ; pure unit }} {clauses} }}\n\
         def plain() -> -F Unit {{ handle c : Proc {{ run d : Integer at c <- pure 1 ; pure unit }} {clauses} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let outer = tail_of(&module, &arena, "regions".into());
    let Some(&Computation::Scope { subject: inner, .. }) = arena.computation(outer)
    else {
        panic!("the outer scope");
    };
    let Some(&Computation::Scope { subject, .. }) = arena.computation(inner)
    else {
        panic!("the inner scope");
    };
    // The region each typed bind of the inner subject ascribes, in order.
    let mut regions = Vec::new();
    let mut at = subject;
    while let Some(&Computation::Bind(bound, rest)) = arena.computation(at) {
        let Some(&Computation::Ascribe { ty, .. }) = arena.computation(bound)
        else {
            panic!("a typed bind ascribes its computation");
        };
        let Some(&CompType::Returner { result, .. }) = arena.comp_type(ty)
        else {
            panic!("at a returner");
        };
        regions.push(capability(&arena, result).2);
        at = rest;
    }
    assert_eq!(
        regions,
        [
            Region::Scoped(RegionDepth::from(1_u32)),
            Region::Scoped(RegionDepth::from(2_u32))
        ],
        "`at c` names the outer scope's region and `at e` the inner one's"
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "regions".into()),
            Verdict::Checked { .. }
        ),
        "{:?}",
        verdict_of(&module, &report, "regions".into())
    );
    assert!(
        matches!(
            outcome_of(&module, "unbound".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name, .. })
                if name == SurfaceName::from("c")
        ),
        "a parameter names no region: {:?}",
        outcome_of(&module, "unbound".into())
    );
    assert!(
        matches!(
            outcome_of(&module, "plain".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment { .. })
        ),
        "only a capability lives in a region: {:?}",
        outcome_of(&module, "plain".into())
    );
}
