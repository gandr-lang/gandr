use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_checker::Verdict;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_term::Literal;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::error::LoweringRefusal;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::module::DeclarationOutcome;
use crate::module::LoweredModule;
use crate::resolve::SurfaceName;

/// The data a boundary check builds, declared as `std.boundary` and
/// `std.layout` declare them, with one row.
const DATA: &str = concat!(
    "data Scalar : Type { U32 : Scalar; U64 : Scalar; I32 : Scalar; I64 : Scalar; }\n",
    "data Code : Type { Plain : (s : Scalar) --> Code; }\n",
    "data Coded : Type { NoCoded : Coded; Coded : (name : String, c : Code, rest : Coded) --> Coded; }\n",
    "data Signature : Type { Signature : (params : Coded, result : Code) --> Signature; }\n",
    "data Signatures : Type { NoSignature : Signatures; Member : (s : Signature, rest : Signatures) --> Signatures; }\n",
    "data Row : Type { Row : (result : Code) --> Row; }\n",
    "data Rows : Type { NoRow : Rows; Named : (r : Row, rest : Rows) --> Rows; }\n",
    "data Admission : Type { Admitted : Admission; }\n",
    "def addRow : Row = Row(Plain(U32));\n",
);

/// The call a boundary check makes.
const ADMIT: &str = "def admitBlock(ss : Signatures, rs : Rows) -> Admission { Admitted }\n";

/// A step of [`spelled`]'s walk: a value to read, or a constructor whose
/// fields are spelled and wait to be closed over.
///
/// # Specification
/// trivial.
enum Step
{
    /// Read the value.
    Visit(ValueId),
    /// Close the constructor over its fields' spellings.
    Close(ValueId),
}

/// The value `value` spelled: a constructor as its tag and its fields, a text
/// quoted, a constant by the name `module` declares it under.
///
/// # Specification
/// trivial.
fn spelled(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    value: ValueId,
) -> String
{
    let names: BTreeMap<_, _> = module
        .declarations()
        .iter()
        .map(|declaration| (declaration.constant(), declaration.name()))
        .collect();
    let mut steps = vec![Step::Visit(value)];
    let mut done: Vec<String> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(id) => match arena.value(id) {
                Some(&Value::Constructor { ref fields, .. }) => {
                    steps.push(Step::Close(id));
                    steps.extend(fields.iter().rev().map(|&field| Step::Visit(field)));
                },
                Some(&Value::Literal(Literal::Text(ref text))) => {
                    done.push(format!("{:?}", text.as_ref()));
                },
                Some(&Value::Constant(constant)) => done.push(names.get(&constant).map_or_else(
                    || format!("{constant:?}"),
                    |name| String::from(name.as_ref()),
                )),
                other => done.push(format!("{other:?}")),
            },
            Step::Close(id) => {
                let Some(&Value::Constructor {
                    tag, ref fields, ..
                }) = arena.value(id)
                else {
                    continue;
                };
                let fields = done.split_off(done.len().saturating_sub(fields.len()));
                done.push(if fields.is_empty() {
                    format!("#{}", usize::from(tag))
                }
                else {
                    format!("#{}({})", usize::from(tag), fields.join(", "))
                });
            },
        }
    }
    done.pop().unwrap_or_default()
}

/// A block carrying `boundary` takes one slot under its interface's name: a
/// call of `admitBlock` on its members' codes and the rows its payload names,
/// which the checker accepts. A block carrying another attribute takes none,
/// and that attribute decorates nothing (#2901).
#[test]
fn a_boundary_block_takes_the_slot_its_check_runs_in_2901()
{
    let text = format!(
        "{DATA}{ADMIT}{}",
        concat!(
            "@[ boundary(addRow) ]\n",
            "extern \"rust\" from \"boundary\" as Boundary { def add(x : u32, n : u64) -> u32; }\n",
            "@[ checks ]\n",
            "extern \"rust\" from \"idle\" as Idle { def peek(x : u64) -> u64; }\n",
        )
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(text.as_str()), &mut arena);
    let names: Vec<String> = module
        .declarations()
        .iter()
        .map(|declaration| String::from(declaration.name().as_ref()))
        .collect();
    assert_eq!(
        names.iter().filter(|name| *name == "Boundary").count(),
        1,
        "the checked block takes one slot: {names:?}"
    );
    assert!(
        names.iter().all(|name| name != "Idle"),
        "a block carrying no `boundary` takes none: {names:?}"
    );
    assert_eq!(
        module
            .declarations()
            .iter()
            .filter(|declaration| matches!(declaration.outcome(), DeclarationOutcome::Refused(_)))
            .count(),
        1,
        "the other block's attribute decorates nothing, and is refused alone"
    );
    let body = body_named(&module, SurfaceName::from("Boundary"));
    let call = tail_of(&arena, body);
    let Some(&Computation::Application(applied, rows)) = arena.computation(call)
    else {
        panic!(
            "the check applies its call to the rows: {:?}",
            arena.computation(call)
        );
    };
    let Some(&Computation::Application(forced, members)) = arena.computation(applied)
    else {
        panic!(
            "and before them to the members: {:?}",
            arena.computation(applied)
        );
    };
    let Some(&Computation::Force(callee)) = arena.computation(forced)
    else {
        panic!("the callee is forced: {:?}", arena.computation(forced));
    };
    assert_eq!(spelled(&module, &arena, callee), "admitBlock");
    assert_eq!(
        spelled(&module, &arena, members),
        r##"#1(#0(#1("x", #0(#0), #1("n", #0(#1), #0)), #0(#0)), #0)"##,
        "one member, `x : u32, n : u64 -> u32`, each type coded as its scalar"
    );
    assert_eq!(
        spelled(&module, &arena, rows),
        "#1(addRow, #0)",
        "one row, the payload's"
    );
    let report = judged(&module, &mut arena);
    let Some(check) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("Boundary"))
    else {
        panic!("the check is declared");
    };
    assert!(
        module.laws(check).is_empty(),
        "the row the payload names is no law"
    );
    let verdict = report
        .judged()
        .iter()
        .find(|judged| judged.constant() == check.constant())
        .map(gandr_core_checker::Judged::verdict);
    assert!(
        matches!(
            verdict,
            Some(Verdict::Checked { .. } | Verdict::Synthesised { .. })
        ),
        "the call is typed: {verdict:?}"
    );
}

/// A check whose call names nothing the source declares is refused at the
/// payload by that name; a row that names nothing, and a row written as a
/// text, are refused there as any payload is (#2901).
#[test]
fn a_check_naming_no_admission_is_refused_at_its_payload_2901()
{
    let block =
        "extern \"rust\" from \"boundary\" as Boundary { def add(x : u32, n : u32) -> u32; }\n";
    let cases: [(String, &str, Option<&str>); 3] = [
        (
            format!("{DATA}@[ boundary(addRow) ]\n{block}"),
            "addRow",
            Some("admitBlock"),
        ),
        (
            format!("{DATA}{ADMIT}@[ boundary(nowhere) ]\n{block}"),
            "nowhere",
            Some("nowhere"),
        ),
        (
            format!("{DATA}{ADMIT}@[ boundary(\"addRow\") ]\n{block}"),
            "\"addRow\"",
            None,
        ),
    ];
    for (text, payload, unresolved) in cases {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(text.as_str()), &mut arena);
        let refusal = refusal_of(&module, SurfaceName::from("Boundary"));
        let named = match (refusal, unresolved) {
            (LoweringRefusal::UnresolvedName { name, .. }, Some(unresolved)) => {
                name == SurfaceName::from(unresolved)
            },
            (LoweringRefusal::IllTypedPayload { .. }, None) => true,
            _ => false,
        };
        assert!(named, "{payload}: {refusal:?}");
        let at = text
            .find(&format!("boundary({payload})"))
            .map(|at| at + "boundary(".len());
        let Maybe::Present(span) = refusal.span()
        else {
            panic!("{payload}: the refusal is placed: {refusal:?}");
        };
        assert_eq!(
            Some(usize::from(span.start())),
            at,
            "{payload}: refused at the payload"
        );
    }
}
