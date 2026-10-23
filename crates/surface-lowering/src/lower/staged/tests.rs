use alloc::format;

use gandr_core_checker::CheckRefusal;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::Verdict;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::staged::Part;
use gandr_core_term::staged::unstaged;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageBinder;
use gandr_kernel_term::StageBound;
use gandr_kernel_term::StageId;
use gandr_surface_syntax::SourceText;

use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::module::LoweredModule;
use crate::resolve::SurfaceName;

/// The naturals the staged functions take.
const NAT: &str = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n";

/// A function applied at a stage, and a recursion handing its claim to it.
const APPLIED: &str = "def applyAt @[i : Size] (f : Nat[<i] => Nat, x : Nat[<i]) -> -F Nat {\n  f(x)\n}\ndef rec helped(n : Nat) -> -F Nat {\n  case n {\n    Zero => Zero,\n    Succ(p) => Succ(applyAt(helped[<], p))\n  }\n}\n";

/// The bounds `name`'s telescope files.
///
/// # Specification
/// trivial.
fn stages_of<'module>(
    module: &'module LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> &'module [StageBound]
{
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
    else {
        panic!("{name:?} is declared");
    };
    module.stages(declaration)
}

/// The verdict the checker gave `name`.
///
/// # Specification
/// trivial.
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
        panic!("{name:?} is declared");
    };
    let Some(judged) = report
        .judged()
        .iter()
        .find(|judged| judged.constant() == declaration.constant())
    else {
        panic!("{name:?} is judged: {report:?}");
    };
    judged.verdict()
}

#[test]
fn a_telescope_files_its_bounds_and_marks_its_stages()
{
    let source = format!(
        "{NAT}{APPLIED}def bounded @[n : Size, i : Size, i < n] (x : Nat[i], y : Nat[<n]) -> -F Nat {{\n  return x\n}}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert_eq!(
        stages_of(&module, SurfaceName::from("applyAt")),
        [StageBound::Unbounded],
        "one binder, unbounded"
    );
    assert_eq!(
        stages_of(&module, SurfaceName::from("bounded")),
        [
            StageBound::Unbounded,
            StageBound::Below(StageBinder::from(0_usize))
        ],
        "the bound names the binder written before it"
    );
    assert!(
        stages_of(&module, SurfaceName::from("helped")).is_empty(),
        "a function with no telescope is quantified over nothing"
    );
    let report = judged(&module, &mut arena);
    for name in ["applyAt", "bounded", "helped"] {
        assert!(
            matches!(
                verdict_of(&module, &report, SurfaceName::from(name)),
                Verdict::Checked { .. }
            ),
            "`{name}` checks: {report:?}"
        );
    }
}

/// #2138: a definition over regions files each binder's name at its ordinal,
/// so a diagnostic spells a type kept at one by the name the telescope
/// writes; a definition over none files nothing.
#[test]
fn a_definition_s_region_binders_are_named_by_ordinal_2138()
{
    let source = "def crossed @[s : Region, i : Size, r : Region] (k : (() => Integer) at r, j : (() => Integer) at s) -> -F Integer {\n  force k\n}\ndef plain(x : Integer) -> -F Integer {\n  return x\n}\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let named = |name: &str| {
        let Some(declaration) = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
        else {
            panic!("{name} is declared");
        };
        module.region_names(declaration.constant())
    };
    assert_eq!(
        named("crossed"),
        [Some(SurfaceName::from("s")), Some(SurfaceName::from("r"))],
        "the region binders in written order, the stage binder between them not counted"
    );
    assert!(
        named("plain").is_empty(),
        "a definition over no region names none"
    );
}

#[test]
fn a_call_handing_the_scrutinee_is_refused()
{
    let source = format!(
        "{NAT}{APPLIED}def rec again(n : Nat) -> -F Nat {{\n  case n {{\n    Zero => Zero,\n    Succ(p) => Succ(applyAt(again[<], n))\n  }}\n}}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, SurfaceName::from("again")),
            Verdict::Refused(CheckRefusal::StageNotBelow { .. })
        ),
        "the scrutinee stands at the recursion's own stage, so the binder is \
         instantiated there and `again[<]` takes nothing at it: {report:?}"
    );
}

#[test]
fn a_bound_or_stage_naming_no_binder_is_refused_by_name()
{
    let source = format!(
        "{NAT}def later @[i : Size, i < n, n : Size] (x : Nat[i]) -> -F Nat {{\n  return x\n}}\ndef stray @[i : Size] (x : Nat[j]) -> -F Nat {{\n  return x\n}}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("later")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("n")
        ),
        "a bound names a binder written before the one it bounds"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("stray")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("j")
        ),
        "a staged type names a binder of its function's telescope"
    );
}

#[test]
fn a_supplied_stage_crosses_at_the_call_s_head_1227()
{
    let source = format!(
        "{NAT}{APPLIED}def appliedAt @[j : Size, k : Size] (f : Nat[<k] => Nat, x : Nat[<k]) -> -F Nat {{\n  applyAt[i = k](f, x)\n}}\ndef stray @[j : Size] (f : Nat[<j] => Nat, x : Nat[<j]) -> -F Nat {{\n  applyAt[i = m](f, x)\n}}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let named = |name: &str| {
        let Some(declaration) = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
        else {
            panic!("{name} is declared");
        };
        declaration
    };
    let [supply] = *module.supplies(named("appliedAt"))
    else {
        panic!(
            "the call files one supply: {:?}",
            module.supplies(named("appliedAt"))
        );
    };
    assert_eq!(
        (supply.binder, supply.stage),
        (
            StageBinder::from(0_usize),
            Stage::At(StageId::from(1_usize))
        ),
        "`applyAt`'s first binder at the caller's second"
    );
    assert_eq!(
        arena.value(supply.head),
        Some(&Value::Constant(named("applyAt").constant())),
        "at the value the call forces, `applyAt`'s name"
    );
    assert!(
        module.supplies(named("helped")).is_empty(),
        "a call supplying nothing files nothing"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("stray")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("m")
        ),
        "a supply names a stage binder of the function making the call"
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, SurfaceName::from("appliedAt")),
            Verdict::Checked { .. }
        ),
        "the arguments show `i` at `k`, the stage supplied: {report:?}"
    );
}

#[test]
fn a_stage_outside_a_signature_leaves_the_fragment()
{
    let source = format!(
        "{NAT}def inside @[i : Size] (x : Nat[i]) -> -F Nat {{\n  return (x : Nat[i])\n}}\ndef carried @[i : Size] (a : Nat, q : Path(Nat[i], a, a)) -> -F Nat {{\n  return a\n}}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for (name, why) in [
        ("inside", "a stage is its signature's, never a body's"),
        ("carried", "a path's carrier places no stage"),
    ] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::OutOfFragment {
                    boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::StagedType),
                    ..
                }
            ),
            "{why}"
        );
    }
}

#[test]
fn a_case_under_a_staged_result_answers_plainly()
{
    let source = format!(
        "{NAT}def predAt @[i : Size] (n : Nat[i]) -> -F Nat[i] {{\n  case n {{\n    Zero => Zero,\n    Succ(p) => p\n  }}\n}}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let body = body_named(&module, SurfaceName::from("predAt"));
    let Some(&Computation::DataCase { motive, .. }) = arena.computation(tail_of(&arena, body))
    else {
        panic!("the body is a case on the parameter");
    };
    assert_eq!(
        unstaged(&mut arena, Part::Computation(motive)),
        Some(Part::Computation(motive)),
        "the case answers the result plainly"
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            verdict_of(&module, &report, SurfaceName::from("predAt")),
            Verdict::Checked { .. }
        ),
        "the branches are read at the result's stage: {report:?}"
    );
}
