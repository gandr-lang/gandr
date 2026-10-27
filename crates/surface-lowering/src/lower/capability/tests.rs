use alloc::string::String;
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
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::IntegerWidth;
use gandr_kernel_term::RuleIndex;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::error::CrossedExit;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::fixture::grammar;
use crate::fixture::parsed;
use crate::lower::LoweringBudget;
use crate::lower::lower_module;
use crate::model::InterfaceFault;
use crate::module::DeclarationOutcome;
use crate::module::LoweredDeclaration;
use crate::module::LoweredModule;
use crate::namespace::Recognition;
use crate::origin::ClauseBinder;
use crate::origin::ClausePlace;
use crate::origin::Labelled;
use crate::origin::Omitted;
use crate::origin::ScopeAnswer;
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
                | DeclarationOutcome::Codata(_)
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World
                | DeclarationOutcome::Refused(_) => return None,
            };
            Some(
                Declaration::new(declaration.constant(), declared, defined, origin)
                    .resolving(module.models(declaration).to_vec())
                    .obliged(module.handler_laws(declaration).to_vec()),
            )
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
        | DeclarationOutcome::Codata(_)
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
fn a_row_stays_open_through_its_tail_2270()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def log @[r : Row] (s : String) -> -F [Console | r] Unit { Console.print(s) }\n",
            "def alone @[r : Row] () -> -F [r] Unit { pure unit }\n",
        )),
        &mut arena,
    );
    for (name, written) in [("log", ["Console"].as_slice()), ("alone", [].as_slice())] {
        let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, name.into())
        else {
            panic!("{name}: the function lowers");
        };
        let Some(&ValueType::Thunk(mut at)) = arena.value_type(declared_type)
        else {
            panic!("{name}: a function's type is a thunk");
        };
        let mut domains = Vec::new();
        let (result, effects) = loop {
            match arena.comp_type(at) {
                Some(
                    &(CompType::Pi { domain, codomain } | CompType::Arrow { domain, codomain }),
                ) => {
                    domains.push(domain);
                    at = codomain;
                },
                Some(&CompType::Returner {
                    result,
                    ref effects,
                }) => break (result, effects.clone()),
                other => panic!("{name}: a returner ends the type, not {other:?}"),
            }
        };
        assert_eq!(
            domains.first().and_then(|&kind| arena.value_type(kind)),
            Some(&ValueType::Row),
            "{name}: the implicit ranges over rows"
        );
        assert_eq!(
            arena.value_type(result),
            Some(&ValueType::unit()),
            "{name}: the result"
        );
        let names: Vec<&str> = effects
            .signatures()
            .map(|signature| signature.name().as_ref())
            .collect();
        assert_eq!(names, written, "{name}: the interfaces the row writes");
        let tail = effects.tail().expect("the row stays open");
        let Some(&ValueType::RowTail(code)) = arena.value_type(tail)
        else {
            panic!("{name}: the tail stands for a row");
        };
        assert!(
            matches!(arena.value(code), Some(&Value::Variable { .. })),
            "{name}: the tail is the implicit, not a row written out"
        );
    }
    let report = judged(&module, &mut arena);
    for name in ["log", "alone"] {
        assert!(
            matches!(
                verdict_of(&module, &report, name.into()),
                Verdict::Checked { .. }
            ),
            "{name}: the open row checks"
        );
    }
}

#[test]
fn an_unknown_operation_or_interface_is_refused_by_name()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def held : Cap {delete} ;\n",
            "def row(c : Cap {read}) -> -F [Radio] String { c.read(\"x\") }\n",
            "def sent(c : Cap {read}) -> -F [Fs] String { c.delete(\"x\") }\n",
            "def scoped() -> -F Unit { handle c : Radio { pure unit } with { pure(x) => pure x } }\n",
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
                }) if refused == SurfaceName::from("Radio")
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
fn a_row_names_each_interface_once()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def twice() -> -F [Fs, Fs] Integer { pure 1 }\n",
            "def apart() -> -F [Fs, Div] Integer { pure 1 }\n",
        )),
        &mut arena,
    );
    let DeclarationOutcome::Refused(LoweringRefusal::DuplicateDefinition { span, name, first }) =
        outcome_of(&module, "twice".into())
    else {
        panic!("a row naming `Fs` twice is refused");
    };
    assert_eq!(
        (
            name,
            (usize::from(first.start()), usize::from(first.end())),
            (usize::from(span.start()), usize::from(span.end()))
        ),
        (
            SurfaceName::from("Fs"),
            (19_usize, 21_usize),
            (23_usize, 25_usize)
        ),
        "the second `Fs` is refused, pointing back at the first"
    );
    assert!(
        matches!(
            outcome_of(&module, "apart".into()),
            DeclarationOutcome::Completed { .. }
        ),
        "two interfaces, each named once, make a row"
    );
}

#[test]
fn a_row_names_two_instances_of_one_interface_apart_2271()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def both() -> -F [x : Console, y : Console] Unit { x.print(\"x\") }\n",
            "def twice() -> -F [o : Console, o : Console] Unit { pure unit }\n",
            "def lost(k : +U (-F [z : Console] Unit)) -> -F Unit { pure unit }\n",
        )),
        &mut arena,
    );
    let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, "both".into())
    else {
        panic!("both: the function lowers");
    };
    let Some(&ValueType::Thunk(mut at)) = arena.value_type(declared_type)
    else {
        panic!("both: a function's type is a thunk");
    };
    let mut domains = Vec::new();
    let effects = loop {
        match arena.comp_type(at) {
            Some(&(CompType::Pi { domain, codomain } | CompType::Arrow { domain, codomain })) => {
                domains.push(domain);
                at = codomain;
            },
            Some(&CompType::Returner { ref effects, .. }) => break effects.clone(),
            other => panic!("both: a returner ends the type, not {other:?}"),
        }
    };
    let [first, second] = [0_u32, 1].map(|ordinal| {
        Region::Bound(gandr_core_term::effect::capability::RegionBinder::from(
            ordinal,
        ))
    });
    let placed: Vec<(Region, &str)> = effects
        .instances()
        .map(|(label, signature)| (label.region(), signature.name().as_ref()))
        .collect();
    assert_eq!(
        placed,
        [(first, "Console"), (second, "Console")],
        "each label is an instance of `Console` at its own region binder"
    );
    let regions: Vec<Region> = domains
        .iter()
        .map(|&domain| match arena.value_type(domain) {
            Some(&ValueType::Capability { region, .. }) => region,
            other => panic!("both: each label binds a capability, not {other:?}"),
        })
        .collect();
    assert_eq!(
        regions,
        [first, second],
        "each label's capability lives where its instance does"
    );
    assert!(
        matches!(
            outcome_of(&module, "twice".into()),
            DeclarationOutcome::Refused(LoweringRefusal::DuplicateDefinition { name, .. })
                if name == SurfaceName::from("o")
        ),
        "a row holds each label once"
    );
    assert!(
        matches!(
            outcome_of(&module, "lost".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name, .. })
                if name == SurfaceName::from("z")
        ),
        "a label naming no instance in scope"
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "both".into()),
            Verdict::Checked { .. }
        ),
        "both: the instance it exercises is in its row"
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
            "def granted() -> -F [Fs] String { peek(fs) }\n",
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
    for name in ["peek", "granted", "save", "direct"] {
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

/// An operation selected off a host interface's name, no value in scope
/// bearing that name, is performed by the interface: `Console.print(s)`
/// lowers to a perform of `Console`'s `print` the checker admits under the
/// row naming `Console`; an operation the named interface does not offer is
/// refused by name (#2279).
#[test]
fn an_operation_is_performed_by_its_interface_s_name_2279()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def hello() -> -F [Console] Unit { Console.print(\"hello, world!\") }\n",
            "def elsewhere() -> -F [Proc] Unit { Proc.print(\"x\") }\n",
        )),
        &mut arena,
    );
    let hello = tail_of(&module, &arena, "hello".into());
    let Some(&Computation::Perform {
        ref signature,
        ref operation,
        payload,
    }) = arena.computation(hello)
    else {
        panic!(
            "`Console.print(…)` is a perform: {:?}",
            arena.computation(hello)
        );
    };
    assert_eq!(
        (signature.name().as_ref(), operation.as_ref()),
        ("Console", "print")
    );
    assert!(
        matches!(arena.value(payload), Some(&Value::Literal(_))),
        "the one argument is the payload"
    );
    assert!(
        matches!(
            outcome_of(&module, "elsewhere".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name, .. })
                if name == SurfaceName::from("print")
        ),
        "`Proc` offers no `print`"
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "hello".into()),
            Verdict::Checked { .. } | Verdict::Synthesised { .. }
        ),
        "{:?}",
        verdict_of(&module, &report, "hello".into())
    );
}

/// An `extern "rust"` block declares an interface its source's rows name and
/// its calls perform, one operation per member, and declares no name of its
/// own (#2901).
#[test]
fn an_extern_block_declares_an_interface_its_callers_perform_2901()
{
    let text = concat!(
        "extern \"rust\" from \"boundary\" as Boundary {\n",
        "  def add(x : u32, n : u32) -> u32;\n",
        "  def negate(x : i64) -> i64;\n",
        "}\n",
        "extern \"rust\" from \"idle\" as Idle { def peek(x : u64) -> u64; }\n",
        "def twice(x : u32) -> -F [Boundary] u32 { run y <- Boundary.add(x, x) ; Boundary.add(y, y) }\n",
        "def flipped(x : i64) -> -F [Boundary] i64 { Boundary.negate(x) }\n",
        "def missing(x : u32) -> -F [Boundary] u32 { Boundary.sub(x, x) }\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(text), &mut arena);
    let names: Vec<String> = module
        .declarations()
        .iter()
        .map(|declaration| String::from(declaration.name().as_ref()))
        .collect();
    assert_eq!(
        names,
        ["twice", "flipped", "missing"],
        "the block declares no name"
    );
    let flipped = tail_of(&module, &arena, "flipped".into());
    let Some(&Computation::Perform {
        ref signature,
        ref operation,
        payload,
    }) = arena.computation(flipped)
    else {
        panic!(
            "`Boundary.negate(…)` is a perform: {:?}",
            arena.computation(flipped)
        );
    };
    assert_eq!(
        (signature.name().as_ref(), operation.as_ref()),
        ("Boundary", "negate")
    );
    assert!(
        matches!(arena.value(payload), Some(&Value::Variable { .. })),
        "the one argument is the payload: {:?}",
        arena.value(payload)
    );
    let fixed = |arena: &CoreArena, ty, width| matches!(arena.value_type(ty), Some(&ValueType::Base(BaseType::Fixed(found))) if found == width);
    let added = signature.operation(&"add".into());
    let Maybe::Present(added) = added
    else {
        panic!("the block's first member is an operation: {signature:?}");
    };
    let Some(&ValueType::Product(ref parameters)) = arena.value_type(added.payload)
    else {
        panic!(
            "two parameters are passed as their product: {:?}",
            arena.value_type(added.payload)
        );
    };
    assert!(
        parameters.len() == 2
            && parameters
                .iter()
                .all(|&parameter| fixed(&arena, parameter, IntegerWidth::U32))
            && fixed(&arena, added.reply, IntegerWidth::U32),
        "`add` takes two `u32` and answers one"
    );
    assert!(
        matches!(
            outcome_of(&module, "missing".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name, .. })
                if name == SurfaceName::from("sub")
        ),
        "the block declares no `sub`"
    );
    let report = judged(&module, &mut arena);
    for name in ["twice", "flipped"] {
        assert!(
            matches!(
                verdict_of(&module, &report, name.into()),
                Verdict::Checked { .. } | Verdict::Synthesised { .. }
            ),
            "{name}: {:?}",
            verdict_of(&module, &report, name.into())
        );
    }
    // Each member type answers at its own bytes, at the universe it is read
    // at, the block no declaration performs included.
    let mut kinded: Vec<(usize, &str)> = module
        .origins()
        .labels()
        .iter()
        .filter_map(|label| {
            let Labelled::Kind(kind) = label.labelled
            else {
                return None;
            };
            matches!(arena.value_type(kind), Some(&ValueType::Universe { .. })).then_some(())?;
            let start = usize::from(label.span.start());
            Some((start, text.get(start .. usize::from(label.span.end()))?))
        })
        .collect();
    kinded.sort_unstable();
    let spelled: Vec<&str> = kinded.iter().map(|&(_, written)| written).collect();
    assert_eq!(
        spelled,
        ["u32", "u32", "u32", "i64", "i64", "u64", "u64"],
        "every member type, and only those, answers at its kind"
    );
    assert!(
        kinded
            .iter()
            .all(|&(start, _)| start < text.find("def twice").unwrap_or(0)),
        "each at the bytes its block writes it"
    );
}

/// A `rust` block's piece beyond the form is refused where it stands, a
/// member or an interface written twice at the second, and a block of
/// another language as before (#2901).
#[test]
fn an_extern_block_beyond_the_form_is_refused_at_the_piece_2901()
{
    let beyond = |boundary: FragmentBoundary| {
        boundary == FragmentBoundary::Unadmitted(crate::unbuilt::Unbuilt::ExternBlock)
    };
    for (source, at, expected) in [
        (
            "extern \"rust\" from \"m\" { def f(x : Integer) -> u32; }\n",
            "Integer",
            "a type no fixed width spells",
        ),
        (
            "extern \"rust\" from \"m\" { type Handle; }\n",
            "type",
            "a type member",
        ),
        (
            "extern \"rust\" from \"m\" { def f(x : u32); }\n",
            "f",
            "a member with no result",
        ),
        (
            "extern \"rust\" from \"m\" { def f(x : shared u32) -> u32; }\n",
            "shared",
            "a mode",
        ),
    ] {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        let refused = module.declarations().iter().find_map(|declaration| {
            if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                Some(refusal)
            }
            else {
                None
            }
        });
        let Some(LoweringRefusal::OutOfFragment {
            span,
            form,
            boundary,
            ..
        }) = refused
        else {
            panic!("{expected}: {refused:?}");
        };
        assert!(
            form == crate::form::FormName::EXTERN_BLOCK
                && beyond(boundary)
                && source.get(usize::from(span.start()) .. usize::from(span.end())) == Some(at),
            "{expected} is refused at `{at}`: {refused:?}"
        );
    }
    for (source, second) in [
        (
            "extern \"rust\" from \"m\" { def f(x : u32) -> u32; def f(y : u32) -> u32; }\n",
            "f(y",
        ),
        (
            "extern \"rust\" from \"m\" as M { def f(x : u32) -> u32; }\nextern \"rust\" from \"n\" as M { def g(x : u32) -> u32; }\n",
            "M {",
        ),
    ] {
        let at = source.rfind(second);
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        assert!(
            module.declarations().iter().any(|declaration| matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::DuplicateDefinition { span, .. })
                    if Some(usize::from(span.start())) == at
            )),
            "the second is refused at `{second}`: {:?}",
            module
                .declarations()
                .iter()
                .map(LoweredDeclaration::outcome)
                .collect::<Vec<_>>()
        );
    }
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from("extern \"c\" from \"m\" { def f(x : u32) -> u32; }\n"),
        &mut arena,
    );
    assert!(
        module.declarations().iter().any(|declaration| matches!(
            declaration.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::WrongSort,
                ..
            })
        )),
        "a C block is refused whole, as before"
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
            | Labelled::Bound(_)
            | Labelled::Kind(_) => None,
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

/// The theory `State`, its value sort `S` and its carrier `C`, as a handled
/// scope reads it.
const STATE: &str = concat!(
    "theory State {\n",
    "  sort S : Type+;\n",
    "  sort C : Type;\n",
    "  oper get : (k : pi+ (s : S) . C) --> C;\n",
    "  oper put : (s : S, k : C) --> C;\n",
    "}\n",
);

/// A scope handling `State` with `S` fixed at `Integer` lowers to one scope
/// whose signature has a `get` sending nothing and replying an integer and a
/// `put` sending an integer and replying nothing, and it checks. The
/// exercises in its subject stand after the manifest's `Integer` in the tree,
/// so the type is minted before them.
#[test]
fn a_scope_handles_a_theory_s_operations_2272()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{STATE}def constant() -> -F Integer {{ handle st : State with sort S = Integer {{ run a <- st.get(); st.put(a); run b <- st.get(); pure a + b + 1 }} with {{ pure(x) => pure x, oper get(k) => k(4), oper put(s, k) => k(unit) }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let constant = tail_of(&module, &arena, "constant".into());
    let Some(&Computation::Scope {
        ref signature,
        ref clauses,
        ..
    }) = arena.computation(constant)
    else {
        panic!("`handle` over a theory is a capability scope");
    };
    assert_eq!(signature.name().as_ref(), "State");
    let integer = ValueType::Base(BaseType::Integer);
    let operations: Vec<(&str, Option<&ValueType>, Option<&ValueType>)> = signature
        .operations()
        .map(|operation| {
            (
                operation.name.as_ref(),
                arena.value_type(operation.payload),
                arena.value_type(operation.reply),
            )
        })
        .collect();
    assert_eq!(
        operations,
        [
            ("get", Some(&ValueType::unit()), Some(&integer)),
            ("put", Some(&integer), Some(&ValueType::unit())),
        ],
        "`get` replies the fixed sort and `put` sends it"
    );
    let handled: Vec<&str> = clauses
        .iter()
        .map(|clause| clause.operation.as_ref())
        .collect();
    assert_eq!(handled, ["get", "put"], "one clause per operation");
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "constant".into()),
            Verdict::Checked { .. }
        ),
        "{:?}",
        verdict_of(&module, &report, "constant".into())
    );
}

/// A scope over a theory records, at the scope, the theory and each sort its
/// manifest fixes beside the type it fixes it to, which the scope's signature
/// holds only substituted; a scope over a host interface records none
/// (#2382).
#[test]
fn a_scope_records_the_theory_and_sorts_it_handles_2382()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        concat!(
            "{state}",
            "def fixed() -> -F Integer {{ handle st : State with sort S = Integer {{ run a <- st.get(); pure a }} with {{ pure(x) => pure x, oper get(k) => k(4), oper put(s, k) => k(unit) }} }}\n",
            "def hosted() -> -F Unit {{ handle c : Proc {{ pure unit }} with {{ pure(x) => pure x, oper exit(code, k) => k(unit) }} }}\n",
        ),
        state = STATE,
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let fixed = tail_of(&module, &arena, "fixed".into());
    let hosted = tail_of(&module, &arena, "hosted".into());
    let &[(scope, ref model)] = module.origins().scope_theories()
    else {
        panic!(
            "the theory scope alone is recorded, not the scope over `Proc` at {hosted:?}: {:?}",
            module.origins().scope_theories()
        );
    };
    assert_eq!(scope, fixed, "recorded at the scope over `State`");
    assert_eq!(model.theory.as_ref(), "State");
    let sorts: Vec<(&str, Option<&ValueType>)> = model
        .sorts
        .iter()
        .map(|&(ref sort, carrier)| (sort.as_ref(), arena.value_type(carrier)))
        .collect();
    assert_eq!(
        sorts,
        [("S", Some(&ValueType::Base(BaseType::Integer)))],
        "`S` at `Integer`"
    );
}

/// A scope's manifest fixes only the value sorts of the theory it handles,
/// each once: a sort the theory does not declare, a sort fixed twice and a
/// manifest on a host interface are refused by name, and a value sort left
/// unfixed or a carrier fixed is refused as the member the scope cannot
/// read as an operation.
#[test]
fn a_scope_s_manifest_names_only_its_theory_s_sorts_2272()
{
    let mut arena = CoreArena::new();
    let handlers = "with { pure(x) => pure x, oper get(k) => k(4), oper put(s, k) => k(unit) }";
    let source = alloc::format!(
        concat!(
            "{state}",
            "def undeclared() -> -F Integer {{ handle st : State with sort T = Integer {{ pure 1 }} {handlers} }}\n",
            "def twice() -> -F Integer {{ handle st : State with sort S = Integer with sort S = Integer {{ pure 1 }} {handlers} }}\n",
            "def hosted() -> -F Unit {{ handle c : Proc with sort S = Integer {{ pure unit }} with {{ pure(x) => pure x, oper exit(code, k) => k(unit) }} }}\n",
            "def unfixed() -> -F Integer {{ handle st : State {{ pure 1 }} {handlers} }}\n",
            "def carried() -> -F Integer {{ handle st : State with sort S = Integer with sort C = Integer {{ pure 1 }} {handlers} }}\n",
        ),
        state = STATE,
        handlers = handlers,
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for (name, sort) in [("undeclared", "T"), ("hosted", "S")] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name: refused, .. })
                    if refused == SurfaceName::from(sort)
            ),
            "{name}: `{sort}` is no value sort of the interface: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert!(
        matches!(
            outcome_of(&module, "twice".into()),
            DeclarationOutcome::Refused(LoweringRefusal::DuplicateDefinition { name, .. })
                if name == SurfaceName::from("S")
        ),
        "a manifest fixes a sort once: {:?}",
        outcome_of(&module, "twice".into())
    );
    for (name, fault) in [
        ("unfixed", InterfaceFault::Unfixed),
        ("carried", InterfaceFault::Fixed),
    ] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(LoweringRefusal::UninterfacedMember { name: member, fault: refused, .. })
                    if member == SurfaceName::from(if name == "unfixed" { "S" } else { "C" }) && refused == fault
            ),
            "{name}: {:?}",
            outcome_of(&module, name.into())
        );
    }
}

/// A returner's row names `State` with `S` fixed at `Integer`. Labelled, the
/// label's capability and the row's instance carry one signature, `get`
/// replying an integer and `put` sending one, a label after the entry's
/// manifest is an instance too, and a scope over `State` at `Integer`
/// discharges the call; whole, beside a host interface, it is a default
/// instance. Each refusal a scope's manifest meets, the row's meets at the
/// entry, and a name neither the host nor a theory answers is an unresolved
/// head.
#[test]
fn a_row_names_a_theory_at_the_sorts_it_fixes_2844()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        concat!(
            "{state}",
            "def labelled() -> -F [st : State with sort S = Integer] Integer {{ st.get() }}\n",
            "def after() -> -F [st : State with sort S = Integer, out : Console] Integer {{ out.print(\"x\"); st.get() }}\n",
            "def whole() -> -F [State with sort S = Integer, Console] Unit {{ Console.print(\"x\") }}\n",
            "def discharged() -> -F Integer {{ handle s : State with sort S = Integer {{ labelled() }} with {{ pure(x) => pure x, oper get(k) => k(7), oper put(v, k) => k(unit) }} }}\n",
            "def undeclared() -> -F [st : State with sort T = Integer] Integer {{ st.get() }}\n",
            "def hosted() -> -F [Console with sort S = Integer] Unit {{ pure unit }}\n",
            "def twice() -> -F [st : State with sort S = Integer with sort S = Integer] Integer {{ st.get() }}\n",
            "def again() -> -F [State with sort S = Integer, State with sort S = Integer] Unit {{ pure unit }}\n",
            "def unfixed() -> -F [st : State] Integer {{ st.get() }}\n",
            "def unknown() -> -F [Nothing with sort S = Integer] Unit {{ pure unit }}\n",
        ),
        state = STATE,
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Completed { declared_type, .. } =
        outcome_of(&module, "labelled".into())
    else {
        panic!(
            "labelled: the function lowers: {:?}",
            outcome_of(&module, "labelled".into())
        );
    };
    let Some(&ValueType::Thunk(at)) = arena.value_type(declared_type)
    else {
        panic!("labelled: a function's type is a thunk");
    };
    let Some(&(CompType::Pi { domain, codomain } | CompType::Arrow { domain, codomain })) =
        arena.comp_type(at)
    else {
        panic!("labelled: the label is a parameter");
    };
    let Some(&CompType::Returner { ref effects, .. }) = arena.comp_type(codomain)
    else {
        panic!("labelled: a returner ends the type");
    };
    let (authority, grade, region) = capability(&arena, domain);
    let instances: Vec<(Region, &EffectSig)> = effects
        .instances()
        .map(|(label, signature)| (label.region(), signature))
        .collect();
    let &[(placed, signature)] = instances.as_slice()
    else {
        panic!("labelled: the row holds the label's instance alone: {instances:?}");
    };
    assert_eq!(
        placed, region,
        "the capability lives where the instance does"
    );
    assert_eq!(grade, CapabilityGrade::Durable);
    assert_eq!(
        authority.signatures().collect::<Vec<_>>(),
        [signature],
        "the capability holds the instance's signature"
    );
    assert_eq!(signature.name().as_ref(), "State");
    let integer = ValueType::Base(BaseType::Integer);
    let operations: Vec<(&str, Option<&ValueType>, Option<&ValueType>)> = signature
        .operations()
        .map(|operation| {
            (
                operation.name.as_ref(),
                arena.value_type(operation.payload),
                arena.value_type(operation.reply),
            )
        })
        .collect();
    assert_eq!(
        operations,
        [
            ("get", Some(&ValueType::unit()), Some(&integer)),
            ("put", Some(&integer), Some(&ValueType::unit())),
        ],
        "`get` replies the fixed sort and `put` sends it"
    );
    let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, "after".into())
    else {
        panic!(
            "after: the function lowers: {:?}",
            outcome_of(&module, "after".into())
        );
    };
    let Some(&ValueType::Thunk(mut at)) = arena.value_type(declared_type)
    else {
        panic!("after: a function's type is a thunk");
    };
    let mut held = Vec::new();
    while let Some(&(CompType::Pi { domain, codomain } | CompType::Arrow { domain, codomain })) =
        arena.comp_type(at)
    {
        let (authority, ..) = capability(&arena, domain);
        held.extend(
            authority
                .signatures()
                .map(|signature| signature.name().as_ref()),
        );
        at = codomain;
    }
    assert_eq!(
        held,
        ["State", "Console"],
        "the label after the manifest is an instance too"
    );
    let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, "whole".into())
    else {
        panic!(
            "whole: the function lowers: {:?}",
            outcome_of(&module, "whole".into())
        );
    };
    let Some(&ValueType::Thunk(at)) = arena.value_type(declared_type)
    else {
        panic!("whole: a function's type is a thunk");
    };
    let Some(&CompType::Returner { ref effects, .. }) = arena.comp_type(at)
    else {
        panic!("whole: a returner is the type");
    };
    let mut names: Vec<&str> = effects
        .signatures()
        .map(|signature| signature.name().as_ref())
        .collect();
    names.sort_unstable();
    assert_eq!(names, ["Console", "State"], "each named whole");
    for (name, sort) in [("undeclared", "T"), ("hosted", "S")] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name: refused, .. })
                    if refused == SurfaceName::from(sort)
            ),
            "{name}: `{sort}` is no value sort of the interface: {:?}",
            outcome_of(&module, name.into())
        );
    }
    for (name, again) in [("twice", "S"), ("again", "State")] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(LoweringRefusal::DuplicateDefinition { name: refused, .. })
                    if refused == SurfaceName::from(again)
            ),
            "{name}: `{again}` is written once: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert!(
        matches!(
            outcome_of(&module, "unfixed".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UninterfacedMember { name, fault, .. })
                if name == SurfaceName::from("S") && fault == InterfaceFault::Unfixed
        ),
        "a value sort the row leaves unfixed: {:?}",
        outcome_of(&module, "unfixed".into())
    );
    assert!(
        matches!(
            outcome_of(&module, "unknown".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedTypeHead { name, .. })
                if name == SurfaceName::from("Nothing")
        ),
        "neither the host nor a theory answers: {:?}",
        outcome_of(&module, "unknown".into())
    );
    let report = judged(&module, &mut arena);
    for name in ["labelled", "after", "whole", "discharged"] {
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

/// A row's theory entry as recorded: its returner, whether its region is
/// held, its theory, and each sort it fixes beside the fixed type.
type Recorded<'arena> = (
    CompTypeId,
    bool,
    &'arena str,
    Vec<(&'arena str, Option<&'arena ValueType>)>,
);

/// A returner's row records each entry over a theory as written, at the
/// returner: the theory, each sort the entry fixes beside its type, and the
/// instance's region, held for an entry naming the theory whole and a region
/// binder for a labelled one. A host interface's entry records nothing, so a
/// printer writes `State with sort S = Integer` and the interface's name
/// alone (#3230).
#[test]
fn a_row_records_the_theory_and_sorts_each_entry_fixes_3230()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        concat!(
            "{state}",
            "def labelled() -> -F [st : State with sort S = Integer] Integer {{ st.get() }}\n",
            "def whole() -> -F [State with sort S = Integer, Console] Unit {{ Console.print(\"x\") }}\n",
            "def hosted() -> -F [Console] Unit {{ Console.print(\"x\") }}\n",
        ),
        state = STATE,
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let returner = |name: &str| {
        let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, name.into())
        else {
            panic!("{name}: the function lowers");
        };
        let mut at = match arena.value_type(declared_type) {
            Some(&ValueType::Thunk(at)) => at,
            other => panic!("{name}: a function's type is a thunk: {other:?}"),
        };
        while let Some(&(CompType::Pi { codomain, .. } | CompType::Arrow { codomain, .. })) =
            arena.comp_type(at)
        {
            at = codomain;
        }
        at
    };
    let recorded: Vec<Recorded<'_>> = module
        .origins()
        .row_theories()
        .iter()
        .map(|&(at, ref entry)| {
            (
                at,
                entry.region == Region::Held,
                entry.model.theory.as_ref(),
                entry
                    .model
                    .sorts
                    .iter()
                    .map(|&(ref sort, ty)| (sort.as_ref(), arena.value_type(ty)))
                    .collect(),
            )
        })
        .collect();
    let integer = Some(&ValueType::Base(BaseType::Integer));
    assert_eq!(
        recorded,
        [
            (
                returner("labelled"),
                false,
                "State",
                Vec::from([("S", integer)])
            ),
            (
                returner("whole"),
                true,
                "State",
                Vec::from([("S", integer)])
            ),
        ],
        "the labelled entry at its binder and the whole one held, `Console` none at {:?}",
        returner("hosted")
    );
}

/// A scope whose manifest fixes `S` to a parameter reads the parameter where
/// the scope stands, past the parameters after it, and an exercise in its
/// subject reads it past the capability too. A row fixing `S` to a parameter
/// checks, and a scope at `Integer` discharges it (#2881).
#[test]
fn a_scope_fixing_a_sort_to_a_parameter_reads_it_where_it_is_used_2881()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        concat!(
            "{state}",
            "def scoped(a : Type, x : a, y : Integer) -> -F a {{ handle s : State with sort S = a {{ s.get() }} with {{ pure(w) => pure w, oper get(k) => k(x), oper put(v, k) => k(unit) }} }}\n",
            "def labelled(a : Type, x : a) -> -F [st : State with sort S = a] a {{ st.get() }}\n",
            "def discharged() -> -F Integer {{ handle s : State with sort S = Integer {{ labelled(Integer, 0) }} with {{ pure(w) => pure w, oper get(k) => k(7), oper put(v, k) => k(unit) }} }}\n",
        ),
        state = STATE,
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let scoped = tail_of(&module, &arena, "scoped".into());
    let Some(&Computation::Scope {
        ref signature,
        subject,
        ..
    }) = arena.computation(scoped)
    else {
        panic!("`handle` over a theory is a capability scope");
    };
    let Some(&Computation::Exercise {
        signature: ref exercised,
        ..
    }) = arena.computation(subject)
    else {
        panic!(
            "the subject exercises `get`: {:?}",
            arena.computation(subject)
        );
    };
    let replied = |signature: &EffectSig| {
        signature
            .operations()
            .find(|operation| operation.name.as_ref() == "get")
            .and_then(|operation| match arena.value_type(operation.reply) {
                Some(&ValueType::Element { code, .. }) => arena.value(code),
                Some(_) | None => None,
            })
    };
    assert_eq!(
        replied(signature),
        Some(&variable(DeBruijnIndex::from(2_u32))),
        "`a` at the scope, past `x` and `y`"
    );
    assert_eq!(
        replied(exercised),
        Some(&variable(DeBruijnIndex::from(3_u32))),
        "`a` at the exercise, past the capability too"
    );
    let report = judged(&module, &mut arena);
    for name in ["scoped", "labelled", "discharged"] {
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

/// The theory `StatePutLaws`: `State` with put-get and put-put stated.
const PUT_LAWS: &str = concat!(
    "theory StatePutLaws {\n",
    "  sort S : Type+;\n",
    "  sort C : Type;\n",
    "  oper get : (k : pi+ (s : S) . C) --> C;\n",
    "  oper put : (s : S, k : C) --> C;\n",
    "  rule putGet : put(s, get(bind t . k(t))) <=> put(s, k(s));\n",
    "  rule putPut : put(s, put(u, k)) <=> put(u, k);\n",
    "}\n",
);

/// A scope over a theory with laws owes each of them at the declaration
/// holding it, in the theory's order, and a scope over a theory with none
/// owes nothing. A handler answering every read with four and forgetting
/// every store satisfies put-put but not put-get, and is refused at its scope
/// naming put-get's place.
#[test]
fn a_scope_owes_its_theory_s_laws_2272()
{
    let mut arena = CoreArena::new();
    let clauses = "with { pure(x) => pure x, oper get(k) => k(4), oper put(s, k) => k(unit) }";
    let source = alloc::format!(
        "{STATE}{PUT_LAWS}def lawless() -> -F Integer {{ handle st : State with sort S = Integer {{ st.put(1); st.get() }} {clauses} }}\ndef forgetful() -> -F Integer {{ handle st : StatePutLaws with sort S = Integer {{ st.put(1); st.get() }} {clauses} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let owed = |name: &str| -> Vec<(ComputationId, RuleIndex)> {
        let Some(declaration) = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
        else {
            panic!("`{name}` is declared");
        };
        module
            .handler_laws(declaration)
            .iter()
            .map(|law| (law.scope, law.rule))
            .collect()
    };
    let scope = tail_of(&module, &arena, "forgetful".into());
    assert_eq!(
        owed("forgetful"),
        [
            (scope, RuleIndex::from(0_usize)),
            (scope, RuleIndex::from(1_usize))
        ],
        "put-get, then put-put, both at the scope"
    );
    assert_eq!(owed("lawless"), [], "a theory with no laws owes none");
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "lawless".into()),
            Verdict::Checked { .. }
        ),
        "{:?}",
        verdict_of(&module, &report, "lawless".into())
    );
    assert!(
        matches!(
            verdict_of(&module, &report, "forgetful".into()),
            Verdict::Refused(CheckRefusal::HandlerUnlawful { at, rule, .. })
                if at == scope && rule == RuleIndex::from(0_usize)
        ),
        "{:?}",
        verdict_of(&module, &report, "forgetful".into())
    );
}

/// The theory `StateGetGet`: `State`'s read with get-get stated.
const GET_GET: &str = concat!(
    "theory StateGetGet {\n",
    "  sort S : Type+;\n",
    "  sort C : Type;\n",
    "  oper get : (k : pi+ (s : S) . C) --> C;\n",
    "  rule getGet : get(bind s . get(bind t . k(s, t))) <=> get(bind s . k(s, s));\n",
    "}\n",
);

/// A scope's subject normalises by its theory's laws before it runs: over
/// get-get, two reads lower to one, the second statement binding the first's
/// reply where its request stood, the return at the request's origin and the
/// bind still naming `b`, and the scope checks; over `State`, which states no
/// law, the same subject keeps both reads (#2272).
#[test]
fn a_scope_s_subject_normalises_by_its_theory_s_laws_2272()
{
    let mut arena = CoreArena::new();
    let subject = "{ run a <- st.get(); run b <- st.get(); pure a * 10 + b }";
    let source = alloc::format!(
        "{STATE}{GET_GET}def once() -> -F Integer {{ handle st : StateGetGet with sort S = Integer {subject} with {{ pure(x) => pure x, oper get(k) => k(4) }} }}\ndef twice() -> -F Integer {{ handle st : State with sort S = Integer {subject} with {{ pure(x) => pure x, oper get(k) => k(4), oper put(s, k) => k(unit) }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    // Each step the scope's subject binds, outermost first.
    let steps = |name: &str| -> Vec<(ComputationId, ComputationId)> {
        let Some(&Computation::Scope { subject, .. }) =
            arena.computation(tail_of(&module, &arena, name.into()))
        else {
            panic!("`{name}` is a scope");
        };
        let mut steps = Vec::new();
        let mut at = subject;
        while let Some(&Computation::Bind(bound, rest)) = arena.computation(at) {
            steps.push((at, bound));
            at = rest;
        }
        steps
    };
    let exercised = |name: &str| {
        steps(name)
            .iter()
            .filter(|&&(_, bound)| {
                matches!(arena.computation(bound), Some(Computation::Exercise { .. }))
            })
            .count()
    };
    assert_eq!(exercised("once"), 1, "get-get leaves one read");
    assert_eq!(exercised("twice"), 2, "no law, no rewrite");
    let Some(&(second, answered)) = steps("once").get(1)
    else {
        panic!("the second statement stays a bind");
    };
    let Some(&Computation::Ascribe { body: returned, .. }) = arena.computation(answered)
    else {
        panic!(
            "the answer is ascribed the reply's type: {:?}",
            arena.computation(answered)
        );
    };
    assert!(
        matches!(arena.computation(returned), Some(&Computation::Return(first)) if arena.value(first) == Some(&Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) })),
        "binding the first read's reply: {:?}",
        arena.computation(returned)
    );
    let text = |origin: Maybe<crate::origin::Origin, _>| match origin {
        Maybe::Present(origin) => source
            .get(usize::from(origin.span().start()) .. usize::from(origin.span().end()))
            .map(String::from),
        Maybe::Absent(_) => None,
    };
    assert_eq!(
        text(module.origins().computation(answered)).as_deref(),
        Some("st.get()"),
        "the return answers at the request it stands for"
    );
    assert_eq!(
        text(module.origins().binder(second)).as_deref(),
        Some("b"),
        "the rebuilt statement still binds `b`"
    );
    let report = judged(&module, &mut arena);
    for name in ["once", "twice"] {
        assert!(
            matches!(
                verdict_of(&module, &report, name.into()),
                Verdict::Checked { .. }
            ),
            "`{name}` checks: {:?}",
            verdict_of(&module, &report, name.into())
        );
    }
}

/// The theory `StatePutPut`: `State` with put-put stated.
const PUT_PUT: &str = concat!(
    "theory StatePutPut {\n",
    "  sort S : Type+;\n",
    "  sort C : Type;\n",
    "  oper get : (k : pi+ (s : S) . C) --> C;\n",
    "  oper put : (s : S, k : C) --> C;\n",
    "  rule putPut : put(s, put(u, k)) <=> put(u, k);\n",
    "}\n",
);

/// A state-passing model of `StatePutPut`, which proves put-put by
/// conversion.
const PASSING: &str = concat!(
    "module Passing : Model(StatePutPut) with sort S = Integer {\n",
    "  type C = Integer => Integer;\n",
    "  def get(k : Integer => Integer => Integer) -> Integer => Integer {\n",
    "    thunk { fn (s) { run after <- k(s); after(s) } }\n",
    "  }\n",
    "  def put(s : Integer, k : Integer => Integer) -> Integer => Integer {\n",
    "    thunk { fn (_old) { k(s) } }\n",
    "  }\n",
    "  def putPut(s : Integer, u : Integer, k : Integer => Integer) -> Path(\n",
    "    Integer => Integer,\n",
    "    put(s, put(u, k)),\n",
    "    put(u, k)\n",
    "  ) {\n",
    "    here(put(u, k))\n",
    "  }\n",
    "}\n",
);

/// A scope naming a model of the theory it handles takes each operation's
/// clause from the module's component of its name, ascribed its type: `get`
/// applies it to the thunk of the function resuming the continuation with the
/// state it is handed, and `put` resumes the continuation at unit and applies
/// it to the stored value and that answer. The return clause returns the
/// result at the module's carrier. The scope owes none of the theory's laws,
/// which the module's ascription states, where the same operations' clauses
/// written out owe put-put; and it checks. A module no declaration names is
/// refused by its name, and a module named for a host interface is refused
/// at the name as a former of the wrong sort.
#[test]
fn a_scope_names_a_model_of_its_theory_2272()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        concat!(
            "{state}{put_put}{passing}",
            "def answered() -> Integer => Integer {{ handle st : StatePutPut with sort S = Integer {{ st.put(4); run a <- st.get(); pure fn (_s) {{ pure a }} }} with Passing }}\n",
            "def unnamed() -> Integer => Integer {{ handle st : StatePutPut with sort S = Integer {{ pure fn (s) {{ pure s }} }} with Stateless }}\n",
            "def hosted() -> -F Unit {{ handle c : Proc {{ pure unit }} with Passing }}\n",
        ),
        state = STATE,
        put_put = PUT_PUT,
        passing = PASSING,
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let answered = tail_of(&module, &arena, "answered".into());
    let Some(&Computation::Scope {
        on_return,
        ref clauses,
        ..
    }) = arena.computation(answered)
    else {
        panic!("`handle … with Passing` is a capability scope");
    };
    let at = |index: u32| Some(variable(DeBruijnIndex::from(index)));
    let returned = match arena.computation(on_return) {
        Some(&Computation::Ascribe { body, .. }) => arena.computation(body),
        other => panic!("the return clause is ascribed the carrier: {other:?}"),
    };
    assert!(
        matches!(returned, Some(&Computation::Return(result)) if arena.value(result) == at(0).as_ref()),
        "the return clause returns its result: {returned:?}"
    );
    // A component forced, ascribed its type.
    let forced = |head: ComputationId| {
        matches!(
            arena.computation(head),
            Some(&Computation::Force(ascribed))
                if matches!(arena.value(ascribed), Some(&Value::Ascribe { .. }))
        )
    };
    // The continuation at `index` resumed with `pure` of the value `replied`
    // reads.
    let resumed = |id: ComputationId, index: u32, replied: &dyn Fn(Option<&Value>) -> bool| {
        matches!(
            arena.computation(id),
            Some(&Computation::Resume(continuation, reply))
                if arena.value(continuation) == at(index).as_ref()
                    && matches!(arena.computation(reply), Some(&Computation::Return(value)) if replied(arena.value(value)))
        )
    };
    let bodies: Vec<(&str, ComputationId)> = clauses
        .iter()
        .map(|clause| (clause.operation.as_ref(), clause.body))
        .collect();
    let &[("get", get), ("put", put)] = bodies.as_slice()
    else {
        panic!("one clause per operation, in the theory's order: {bodies:?}");
    };
    // `get`: the component applied to `thunk (λx. resume(k, pure x))`.
    let get_holds = match arena.computation(get) {
        Some(&Computation::Application(head, argument)) => {
            forced(head)
                && match arena.value(argument) {
                    Some(&Value::Thunk(function)) => match arena.computation(function) {
                        Some(&Computation::Lambda(body)) => {
                            resumed(body, 1, &|value| value == at(0).as_ref())
                        },
                        _ => false,
                    },
                    _ => false,
                }
        },
        _ => false,
    };
    assert!(
        get_holds,
        "`get` hands the component the resumption as a function of the state"
    );
    // `put`: `r ← resume(k, pure unit); component(s, r)`.
    let put_holds = match arena.computation(put) {
        Some(&Computation::Bind(bound, body)) => {
            resumed(bound, 0, &|value| value == Some(&Value::unit()))
                && match arena.computation(body) {
                    Some(&Computation::Application(applied, answer)) => {
                        arena.value(answer) == at(0).as_ref()
                            && matches!(
                                arena.computation(applied),
                                Some(&Computation::Application(head, stored))
                                    if forced(head) && arena.value(stored) == at(2).as_ref()
                            )
                    },
                    _ => false,
                }
        },
        _ => false,
    };
    assert!(
        put_holds,
        "`put` hands the component the stored value and what runs after"
    );
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("answered"))
    else {
        panic!("`answered` is declared");
    };
    assert!(
        module.handler_laws(declaration).is_empty(),
        "the module's ascription states put-put, so the scope owes none"
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "answered".into()),
            Verdict::Checked { .. }
        ),
        "{:?}",
        verdict_of(&module, &report, "answered".into())
    );
    assert!(
        matches!(
            outcome_of(&module, "unnamed".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name, .. })
                if name == SurfaceName::from("Stateless")
        ),
        "{:?}",
        outcome_of(&module, "unnamed".into())
    );
    assert!(
        matches!(
            outcome_of(&module, "hosted".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                span,
                boundary: FragmentBoundary::WrongSort,
                ..
            }) if source.get(usize::from(span.start()) .. usize::from(span.end())) == Some("Passing")
        ),
        "{:?}",
        outcome_of(&module, "hosted".into())
    );
}

/// A scope a model answers records, at the scope, the answer as written: the
/// module it names, `with Passing`, or the one model in scope, for a scope
/// writing no `with`. A scope writing its clauses records none, so a printer
/// spells it by its clauses and the others as written, not by the clauses the
/// lowering derives from the model (#3196).
#[test]
fn a_scope_records_the_model_answering_it_3196()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        concat!(
            "{state}{put_put}{passing}",
            "def named() -> Integer => Integer {{ handle st : StatePutPut with sort S = Integer {{ pure fn (s) {{ pure s }} }} with Passing }}\n",
            "def inScope() -> Integer => Integer {{ handle st : StatePutPut with sort S = Integer {{ pure fn (s) {{ pure s }} }} }}\n",
            "def written() -> -F Integer {{ handle st : State with sort S = Integer {{ run a <- st.get(); pure a }} with {{ pure(x) => pure x, oper get(k) => k(4), oper put(s, k) => k(unit) }} }}\n",
        ),
        state = STATE,
        put_put = PUT_PUT,
        passing = PASSING,
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let named = tail_of(&module, &arena, "named".into());
    let in_scope = tail_of(&module, &arena, "inScope".into());
    let written = tail_of(&module, &arena, "written".into());
    let mut answers: Vec<(ComputationId, ScopeAnswer)> = module.origins().scope_answers().to_vec();
    answers.sort_by_key(|&(scope, _)| scope);
    let mut expected = [
        (named, ScopeAnswer::Named("Passing".into())),
        (in_scope, ScopeAnswer::InScope),
    ];
    expected.sort_by_key(|&(scope, _)| scope);
    assert_eq!(
        answers, expected,
        "the named and the in-scope answers, none for the written scope at {written:?}"
    );
}

/// Two models of `State` at an integer state: reading answers zero or one,
/// and storing is forgotten.
const ZERO_AND_ONE: &str = concat!(
    "module Zero : Model(State) with sort S = Integer {\n",
    "  type C = Integer => Integer;\n",
    "  def get(k : Integer => Integer => Integer) -> Integer => Integer { k(0) }\n",
    "  def put(s : Integer, k : Integer => Integer) -> Integer => Integer { pure k }\n",
    "}\n",
    "module One : Model(State) with sort S = Integer {\n",
    "  type C = Integer => Integer;\n",
    "  def get(k : Integer => Integer => Integer) -> Integer => Integer { k(1) }\n",
    "  def put(s : Integer, k : Integer => Integer) -> Integer => Integer { pure k }\n",
    "}\n",
);

/// A scope over a theory writing no `with` is answered by the one model of
/// the theory in scope: each clause applies a hole in place of a module's
/// component, every hole recorded as the scope's beside the modules that may
/// answer it, and the slot planned under the scope's declaration with those
/// modules as its candidates. `Passing`, the one model of `StatePutPut`,
/// answers such a scope, which checks owing no law. Two models of `State`
/// answering one are refused as ambiguous; none at its stored sort, as
/// unanswered. A host interface's scope writing no `with` is refused at its
/// interface as a former of the wrong sort.
#[test]
fn a_scope_is_answered_by_the_model_in_scope_2272()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        concat!(
            "{state}{put_put}{passing}{zero_and_one}",
            "def answered() -> Integer => Integer {{ handle st : StatePutPut with sort S = Integer {{ st.put(4); run a <- st.get(); pure fn (_s) {{ pure a }} }} }}\n",
            "def ambiguous() -> Integer => Integer {{ handle st : State with sort S = Integer {{ pure fn (s) {{ pure s }} }} }}\n",
            "def unanswered() -> Integer => Integer {{ handle st : State with sort S = Unit {{ pure fn (s) {{ pure 1 }} }} }}\n",
            "def hosted() -> -F Unit {{ handle c : Proc {{ pure unit }} }}\n",
        ),
        state = STATE,
        put_put = PUT_PUT,
        passing = PASSING,
        zero_and_one = ZERO_AND_ONE,
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let answered = tail_of(&module, &arena, "answered".into());
    let Some(&Computation::Scope { ref clauses, .. }) = arena.computation(answered)
    else {
        panic!("`handle …` writing no `with` is a capability scope");
    };
    let Some(get) = clauses
        .iter()
        .find(|clause| clause.operation.as_ref() == "get")
    else {
        panic!("the scope answers `get`: {clauses:?}");
    };
    // `get`'s clause applies the forced component, ascribed its type.
    let hole = match arena.computation(get.body) {
        Some(&Computation::Application(head, _)) => match arena.computation(head) {
            Some(&Computation::Force(ascribed)) => match arena.value(ascribed) {
                Some(&Value::Ascribe { value, .. }) => value,
                other => panic!("the component is ascribed its type: {other:?}"),
            },
            other => panic!("the component is forced: {other:?}"),
        },
        other => panic!("`get`'s clause applies the component: {other:?}"),
    };
    assert!(
        matches!(arena.value(hole), Some(&Value::Hole(_))),
        "a hole stands for the component: {:?}",
        arena.value(hole)
    );
    assert_eq!(
        module.origins().omitted(hole),
        Maybe::Present(&Omitted::Scope {
            theory: String::from("StatePutPut"),
            candidates: Vec::from([String::from("Passing")]),
        }),
        "the hole is the scope's, `Passing` the one module that may answer it"
    );
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("answered"))
    else {
        panic!("`answered` is declared");
    };
    let slots = module.models(declaration);
    assert!(
        matches!(slots, [slot] if slot.candidates.len() == 1
            && slot.candidates.iter().all(|candidate| candidate.components.len() == slot.holes.len())),
        "one slot planned under `answered`, `Passing` its candidate: {slots:?}"
    );
    assert!(
        module.handler_laws(declaration).is_empty(),
        "the model's ascription states put-put, so the scope owes none"
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, "answered".into()),
            Verdict::Checked { .. }
        ),
        "{:?}",
        verdict_of(&module, &report, "answered".into())
    );
    assert!(
        matches!(
            verdict_of(&module, &report, "ambiguous".into()),
            Verdict::Refused(CheckRefusal::ModelAmbiguous { survivors, .. })
                if survivors.places().map(usize::from).eq([0, 1])
        ),
        "`Zero` and `One` both answer: {:?}",
        verdict_of(&module, &report, "ambiguous".into())
    );
    assert!(
        matches!(
            verdict_of(&module, &report, "unanswered".into()),
            Verdict::Refused(CheckRefusal::ModelUnanswered { .. })
        ),
        "neither stores the unit: {:?}",
        verdict_of(&module, &report, "unanswered".into())
    );
    assert!(
        matches!(
            outcome_of(&module, "hosted".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                span,
                boundary: FragmentBoundary::WrongSort,
                ..
            }) if source.get(usize::from(span.start()) .. usize::from(span.end())) == Some("Proc")
        ),
        "{:?}",
        outcome_of(&module, "hosted".into())
    );
}

/// A function stating a continuation's type resumes the continuation it is
/// handed as the clause that bound it would, and checks; a thunk a parameter
/// holds is still forced (#1387). A type member abbreviating the stack, read
/// bare inside its module or qualified outside it, states it too (#1651).
#[test]
fn a_stated_stack_is_resumed_as_a_clause_resumes_1387()
{
    let mut arena = CoreArena::new();
    let source = concat!(
        "def later(j : Stack(-F Unit, -F Integer)) -> -F Integer { j(unit) }\n",
        "def apply(f : +U (Unit -> -F Integer)) -> -F Integer { f(unit) }\n",
        "module Conts {\n",
        "  type K = Stack(-F Unit, -F Integer) ;\n",
        "  def aliased(j : K) -> -F Integer { j(unit) }\n",
        "}\n",
        "def qualified(j : Conts.K) -> -F Integer { j(unit) }\n",
    );
    let module = lowered(SourceText::from(source), &mut arena);
    let resumes = |arena: &CoreArena, name: &str| {
        let mut at = tail_of(&module, arena, name.into());
        while let Some(&Computation::Lambda(body)) = arena.computation(at) {
            at = body;
        }
        match arena.computation(at) {
            Some(&Computation::Resume(continuation, _)) => {
                Some(arena.value(continuation) == Some(&variable(DeBruijnIndex::from(0_u32))))
            },
            Some(_) | None => None,
        }
    };
    assert_eq!(
        resumes(&arena, "later"),
        Some(true),
        "`j(unit)` resumes the stack its parameter holds"
    );
    assert_eq!(
        resumes(&arena, "apply"),
        None,
        "`f(unit)` is not a resumption"
    );
    for name in ["aliased", "qualified"] {
        assert_eq!(
            resumes(&arena, name),
            Some(true),
            "{name}: a member abbreviating the stack states it"
        );
    }
    let report = judged(&module, &mut arena);
    for name in ["later", "apply", "aliased", "qualified"] {
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

/// A member abbreviating anything but a stack states no stack: a plain type
/// and another family's application are read as the types they are, and a
/// parameter of either resumes nothing.
#[test]
fn a_member_abbreviating_no_stack_states_none()
{
    let mut arena = CoreArena::new();
    let source = concat!(
        "module Others {\n",
        "  type P = Integer ;\n",
        "  type A = List(Integer) ;\n",
        "}\n",
        "def plain(j : Others.P) -> -F Integer { return j }\n",
        "def boxed(j : Others.A) -> -F Integer { return 0 }\n",
    );
    let module = lowered(SourceText::from(source), &mut arena);
    for name in ["plain", "boxed"] {
        let mut at = tail_of(&module, &arena, name.into());
        while let Some(&Computation::Lambda(body)) = arena.computation(at) {
            at = body;
        }
        assert!(
            !matches!(arena.computation(at), Some(&Computation::Resume(..))),
            "{name}: no stack is stated, so nothing resumes"
        );
    }
    let report = judged(&module, &mut arena);
    for name in ["plain", "boxed"] {
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

/// `abandon(k)` in an operation clause ends the clause's continuation without
/// running it, and the clause checks; a program that binds its own `abandon`
/// calls it (#1334).
#[test]
fn a_clause_abandons_its_continuation_1334()
{
    let mut arena = CoreArena::new();
    let source = concat!(
        "def quit() -> -F Unit { handle c : Proc { c.exit(1) } with { pure(x) => pure x, oper exit(code, k) => abandon(k) } }\n",
        "def abandon(n : Integer) -> -F Unit { pure unit }\n",
        "def halt() -> -F Unit { abandon(1) }\n",
    );
    let module = lowered(SourceText::from(source), &mut arena);
    let quit = tail_of(&module, &arena, "quit".into());
    let Some(&Computation::Scope { ref clauses, .. }) = arena.computation(quit)
    else {
        panic!("`handle` is a capability scope");
    };
    let Some(clause) = clauses.first()
    else {
        panic!("one operation clause");
    };
    let Some(&Computation::Abandon(continuation)) = arena.computation(clause.body)
    else {
        panic!(
            "`abandon(k)` abandons: {:?}",
            arena.computation(clause.body)
        );
    };
    assert_eq!(
        arena.value(continuation),
        Some(&variable(DeBruijnIndex::from(0_u32))),
        "the continuation, bound after the payload"
    );
    let halt = tail_of(&module, &arena, "halt".into());
    assert!(
        !matches!(arena.computation(halt), Some(&Computation::Abandon(_))),
        "a program's own `abandon` is called: {:?}",
        arena.computation(halt)
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
         def plain() -> -F Unit {{ handle c : Proc {{ run d : Integer at c <- pure 1 ; pure unit }} {clauses} }}\n\
         def held() -> -F Unit {{ hold s = 1 ; handle c : Proc {{ run d : Integer at s <- pure 1 ; run e : Integer at c <- pure 2 ; pure unit }} {clauses} }}\n"
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
    // The value type a typed bind keeps, and the region it keeps it in.
    let kept = |bind: ComputationId| {
        let Some(&Computation::Bind(bound, _)) = arena.computation(bind)
        else {
            panic!("the typed bind");
        };
        let Some(&Computation::Ascribe { ty, .. }) = arena.computation(bound)
        else {
            panic!("a typed bind ascribes its computation");
        };
        let Some(&CompType::Returner { result, .. }) = arena.comp_type(ty)
        else {
            panic!("at a returner");
        };
        let Some(&ValueType::Kept { value, region }) = arena.value_type(result)
        else {
            panic!(
                "an integer at a region is kept in it: {:?}",
                arena.value_type(result)
            );
        };
        (arena.value_type(value).cloned(), region)
    };
    let plain = tail_of(&module, &arena, "plain".into());
    let Some(&Computation::Scope { subject, .. }) = arena.computation(plain)
    else {
        panic!("the scope");
    };
    assert_eq!(
        kept(subject),
        (
            Some(ValueType::Base(BaseType::Integer)),
            Region::Scoped(RegionDepth::from(1_u32))
        ),
        "the integer kept in the scope's region"
    );
    let held = tail_of(&module, &arena, "held".into());
    let Some(&Computation::Memory(MemoryForm::Hold { body, .. })) = arena.computation(held)
    else {
        panic!("the hold: {:?}", arena.computation(held));
    };
    let Some(&Computation::Scope { subject, .. }) = arena.computation(body)
    else {
        panic!("the scope: {:?}", arena.computation(body));
    };
    let Some(&Computation::Bind(_, rest)) = arena.computation(subject)
    else {
        panic!("the first typed bind");
    };
    let integer = Some(ValueType::Base(BaseType::Integer));
    assert_eq!(
        (kept(subject), kept(rest)),
        (
            (integer.clone(), Region::Scoped(RegionDepth::from(1_u32))),
            (integer, Region::Scoped(RegionDepth::from(2_u32)))
        ),
        "`at s` names the hold's region and `at c` the scope's inside it"
    );
    for name in ["plain", "held"] {
        assert!(
            matches!(
                verdict_of(&module, &report, name.into()),
                Verdict::Checked { .. }
            ),
            "an integer enters the region at `{name}`: {:?}",
            verdict_of(&module, &report, name.into())
        );
    }
}

/// A kept type naming a region binder of its definition, `A at r` under
/// `@[q : Region, r : Region]`, keeps its value at that binder's ordinal among
/// the telescope's region binders, and the binder named as a value is refused
/// as one (#1221).
#[test]
fn a_kept_type_at_a_region_binder_is_bound_to_it_1221()
{
    use gandr_core_term::effect::capability::RegionBinder;

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def read @[q : Region, r : Region] (k : (() => Integer) at r) -> -F Integer { force \
             k }\n",
            "def named @[r : Region] (k : (() => Integer) at r) -> -F Integer { pure r }\n",
        )),
        &mut arena,
    );
    let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, "read".into())
    else {
        panic!(
            "a definition over regions lowers: {:?}",
            outcome_of(&module, "read".into())
        );
    };
    let Some(&ValueType::Thunk(body)) = arena.value_type(declared_type)
    else {
        panic!("a function type");
    };
    let Some(&CompType::Arrow { domain, .. }) = arena.comp_type(body)
    else {
        panic!("an arrow");
    };
    assert!(
        matches!(
            arena.value_type(domain),
            Some(&ValueType::Kept { region, .. }) if region == Region::Bound(RegionBinder::from(1_u32))
        ),
        "`at r` keeps the parameter at r, the second region binder: {:?}",
        arena.value_type(domain)
    );
    assert!(
        matches!(
            outcome_of(&module, "named".into()),
            DeclarationOutcome::Refused(LoweringRefusal::RegionAsValue { name, .. })
                if name == SurfaceName::from("r")
        ),
        "a region binder is no value: {:?}",
        outcome_of(&module, "named".into())
    );
}

#[test]
fn an_allocated_buffer_is_placed_live_and_freed()
{
    use gandr_core_term::session::SessionAction;

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def ring() -> -F Unit { handle r : Ring { run b <- r.alloc(4096) ; r.free(b) } with { pure(x) => pure x, oper alloc(n, b, k) => k(b), oper free(b, k) => k(unit) } }\n\
             def named() -> -F Unit { handle c : Proc { run code <- c.exit(1) ; pure code } with { pure(x) => pure x, oper exit(code, k) => k(unit) } }\n",
        ),
        &mut arena,
    );
    let ring = tail_of(&module, &arena, "ring".into());
    let Some(&Computation::Scope {
        subject,
        ref clauses,
        ..
    }) = arena.computation(ring)
    else {
        panic!("`handle` is a capability scope");
    };
    let linear = Value::Variable {
        zone: Zone::Linear,
        index: DeBruijnIndex::from(0_u32),
    };
    let Some(&Computation::Bind(alloc, placed)) = arena.computation(subject)
    else {
        panic!("the allocation binds its reply");
    };
    assert!(
        matches!(arena.computation(alloc), Some(Computation::Exercise { operation, .. }) if operation.as_ref() == "alloc")
    );
    let Some(&Computation::Session(SessionAction::Place { payload, body })) =
        arena.computation(placed)
    else {
        panic!("the reply is placed live: {:?}", arena.computation(placed));
    };
    assert_eq!(
        arena.value(payload),
        Some(&variable(DeBruijnIndex::from(0_u32))),
        "the placement holds the reply's binder"
    );
    let Some(&Computation::Exercise {
        payload: freed,
        ref operation,
        ..
    }) = arena.computation(body)
    else {
        panic!("the rest of the block frees the buffer");
    };
    assert_eq!(operation.as_ref(), "free");
    assert_eq!(
        arena.value(freed),
        Some(&linear),
        "`b` names the placement's linear binder"
    );
    let Some(clause) = clauses
        .iter()
        .find(|clause| clause.operation.as_ref() == "alloc")
    else {
        panic!("an `alloc` clause");
    };
    let Some(&Computation::Split {
        scrutinee: tuple,
        arity,
        body: split,
        ..
    }) = arena.computation(clause.body)
    else {
        panic!(
            "the clause splits its payload: {:?}",
            arena.computation(clause.body)
        );
    };
    assert_eq!(
        (arena.value(tuple), usize::from(arity)),
        (Some(&variable(DeBruijnIndex::from(1_u32))), 2_usize),
        "the pair under the continuation splits into the payload and the mint"
    );
    let Some(&Computation::Session(SessionAction::Place {
        payload: mint,
        body: resumed,
    })) = arena.computation(split)
    else {
        panic!("the mint is placed live");
    };
    assert_eq!(
        arena.value(mint),
        Some(&variable(DeBruijnIndex::from(0_u32)))
    );
    let Some(&Computation::Resume(continuation, reply)) = arena.computation(resumed)
    else {
        panic!("`k(b)` resumes");
    };
    assert_eq!(
        arena.value(continuation),
        Some(&variable(DeBruijnIndex::from(2_u32))),
        "`k` past the payload and the mint"
    );
    let Some(&Computation::Return(returned)) = arena.computation(reply)
    else {
        panic!("the resumption returns its reply");
    };
    assert_eq!(
        arena.value(returned),
        Some(&linear),
        "`b` names the mint's linear binder"
    );
    let named = tail_of(&module, &arena, "named".into());
    let Some(&Computation::Scope { subject, .. }) = arena.computation(named)
    else {
        panic!("`handle` is a capability scope");
    };
    assert!(
        matches!(arena.computation(subject), Some(&Computation::Bind(_, rest)) if matches!(arena.computation(rest), Some(Computation::Return(_)))),
        "a run of an operation replying no buffer names its reply"
    );
    let report = judged(&module, &mut arena);
    for name in ["ring", "named"] {
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

/// #1439: a scope records where each binder its clauses write is written: the
/// return clause's result, and each operation clause's payload and
/// continuation by the clause's place, a minting clause's among them.
#[test]
fn a_scope_records_where_its_clauses_bind_1439()
{
    let written = "def ring() -> -F Unit { handle r : Ring { run b <- r.alloc(4096) ; r.free(b) } \
                   with { pure(x) => pure x, oper alloc(n, b, k) => k(b), oper free(m, j) => \
                   j(unit) } }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(written), &mut arena);
    let ring = tail_of(&module, &arena, "ring".into());
    let spelled: Vec<(ClauseBinder, &str)> = module
        .origins()
        .clause_binders()
        .iter()
        .filter(|entry| entry.0.0 == ring)
        .map(|entry| {
            let span = entry.1.span();
            (
                entry.0.1,
                written
                    .get(usize::from(span.start()) .. usize::from(span.end()))
                    .unwrap_or_default(),
            )
        })
        .collect();
    let place = ClausePlace::from;
    assert_eq!(spelled, [
        (ClauseBinder::Result, "x"),
        (ClauseBinder::Payload(place(0_usize)), "n"),
        (ClauseBinder::Payload(place(1_usize)), "m"),
        (ClauseBinder::Continuation(place(0_usize)), "k"),
        (ClauseBinder::Continuation(place(1_usize)), "j"),
    ]);
}
