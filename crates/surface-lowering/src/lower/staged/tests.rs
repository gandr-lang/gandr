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
const NAT: &str = "data Nat : Type where { | Zero : Nat | Succ : (n : Nat) --> Nat }\n";

/// A function applied at a stage, and a recursion handing its claim to it.
const APPLIED: &str = include_str!("tests/unformatted/applied.gandr");

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
        include_str!("tests/unformatted/a-telescope-files-its-bounds-and-marks-its-stages.gandr"),
        APPLIED = APPLIED,
        NAT = NAT
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
    let source = include_str!(
        "tests/fixtures/a-definition-s-region-binders-are-named-by-ordinal-2138.gandr"
    );
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
        include_str!("tests/unformatted/a-call-handing-the-scrutinee-is-refused.gandr"),
        APPLIED = APPLIED,
        NAT = NAT
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
        include_str!(
            "tests/unformatted/a-bound-or-stage-naming-no-binder-is-refused-by-name.gandr"
        ),
        NAT = NAT
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
        include_str!("tests/unformatted/a-supplied-stage-crosses-at-the-call-s-head-1227.gandr"),
        APPLIED = APPLIED,
        NAT = NAT
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
        include_str!("tests/unformatted/a-stage-outside-a-signature-leaves-the-fragment.gandr"),
        NAT = NAT
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
        include_str!("tests/unformatted/a-case-under-a-staged-result-answers-plainly.gandr"),
        NAT = NAT
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
