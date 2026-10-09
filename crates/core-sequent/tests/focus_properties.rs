//! Focusing and unfocusing over generated and hand-built core terms.
//!
//! The generated suites run over closed, well-typed computations and values
//! from [`crate::generate`]: focusing is total on them, its image passes the
//! typed-IL check closed, every covariable it mints is the innermost one, and
//! unfocusing reads each image back as the term it came from. The hand-built
//! suite pins one case per core former to its exact rendering and provenance.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::ConsumerId;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::CovariableIndex;
use gandr_core_sequent::FocusOrigin;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::check_command;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::focus_top_value;
use gandr_core_sequent::focus_value;
use gandr_core_sequent::render_command;
use gandr_core_sequent::unfocus_command;
use gandr_core_sequent::unfocus_value;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use proptest::prelude::*;

use crate::compare::Agreement;
use crate::compare::same_computation;
use crate::compare::same_value;
use crate::generate::GeneratedRoot;
use crate::generate::computations;
use crate::generate::values;

/// An integer's spelling in a hand-built case.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Integer(i32);

/// The integer literal value `n` in `core`.
///
/// # Specification
/// trivial.
fn integer(
    core: &mut CoreArena,
    value: Integer,
) -> gandr_core_term::ValueId
{
    let sign = if value.0 < 0_i32 {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    let digits = Magnitude::from_decimal_text(alloc::format!("{}", value.0.unsigned_abs()))
        .expect("decimal digits");
    core.value_literal(Literal::Integer(IntegerLiteral::new(sign, digits)))
}

/// Every covariable node of an arena is the innermost one.
///
/// # Specification
/// trivial.
fn every_covariable_is_innermost(arena: &CommandArena) -> Agreement
{
    let count = usize::from(arena.consumer_count());
    for offset in 0 .. count {
        let id = ConsumerId::from(u32::try_from(offset).expect("a small arena"));
        if let Some(&ConsumerNode::Covariable(index)) = arena.consumer(id)
            && index != CovariableIndex::from(0_u32)
        {
            return Agreement::Differ;
        }
    }
    Agreement::Same
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    /// Focusing a closed, well-typed computation succeeds, its image is well
    /// formed and closed, and its every covariable is the innermost one.
    #[test]
    fn focusing_is_total_on_generated_computations(generated in computations())
    {
        let GeneratedRoot::Computation(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields computations"));
        };
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let focused = focus_computation(&generated.core, root, &mut arena, &mut provenance);
        prop_assert!(focused.is_ok(), "focusing refused a closed term: {:?}", focused);
        let command = focused.expect("checked above");
        prop_assert_eq!(Ok(FreeSet::default()), check_command(&arena, command), "the image is well formed and closed");
        prop_assert_eq!(Agreement::Same, every_covariable_is_innermost(&arena), "a covariable other than α0 was minted");
    }

    /// Unfocusing reads a focused computation back as the computation it came
    /// from.
    #[test]
    fn unfocusing_inverts_focusing_on_generated_computations(generated in computations())
    {
        let GeneratedRoot::Computation(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields computations"));
        };
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(&generated.core, root, &mut arena, &mut provenance).expect("focusing is total");
        let mut decoded = CoreArena::new();
        let back = unfocus_command(&arena, command, &mut decoded);
        prop_assert!(back.is_ok(), "the image did not decode: {:?}", back);
        prop_assert_eq!(
            Agreement::Same,
            same_computation(&generated.core, root, &decoded, back.expect("checked above")),
            "unfocusing changed the term"
        );
    }

    /// Unfocusing reads a focused value back as the value it came from.
    #[test]
    fn unfocusing_inverts_focusing_on_generated_values(generated in values())
    {
        let GeneratedRoot::Value(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields values"));
        };
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let producer = focus_value(&generated.core, root, &mut arena, &mut provenance).expect("focusing is total");
        let mut decoded = CoreArena::new();
        let back = unfocus_value(&arena, producer, &mut decoded);
        prop_assert!(back.is_ok(), "the image did not decode: {:?}", back);
        prop_assert_eq!(
            Agreement::Same,
            same_value(&generated.core, root, &decoded, back.expect("checked above")),
            "unfocusing changed the value"
        );
    }
}

/// One hand-built case: its label, its term, the origin of its root command
/// and its exact rendering.
struct Case
{
    /// What the case exercises.
    label: &'static str,
    /// The arena the term lives in.
    core: CoreArena,
    /// The term.
    root: ComputationId,
    /// The origin focusing records for the root command.
    origin: FocusOrigin,
    /// The rendered image.
    rendering: &'static str,
}

/// The hand-built cases, one per former and one per naming rule.
///
/// # Specification
/// trivial.
fn cases() -> Vec<Case>
{
    let mut cases = Vec::new();

    let mut core = CoreArena::new();
    let seven = integer(&mut core, Integer(7));
    let root = core.computation_return(seven);
    cases.push(Case {
        label: "return",
        core,
        root,
        origin: FocusOrigin::Return,
        rendering: "⟨7 |+ ★⟩",
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let body = core.computation_return(unit);
    let thunk = core.value_thunk(body);
    let root = core.computation_force(thunk);
    cases.push(Case {
        label: "force a thunk",
        core,
        root,
        origin: FocusOrigin::Force,
        rendering: "⟨{force(α) ⇒ ⟨() |+ α0⟩} |+ force(★)⟩",
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let variable = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let body = core.computation_return(variable);
    let lambda = core.computation_lambda(body);
    let root = core.computation_application(lambda, unit);
    cases.push(Case {
        label: "apply a lambda",
        core,
        root,
        origin: FocusOrigin::Lambda,
        rendering: "⟨cocase {apply(x; α) ⇒ ⟨x0 |+ α0⟩} |− apply((); ★)⟩",
    });

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let head = core.computation_return(one);
    let variable = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let body = core.computation_return(variable);
    let root = core.computation_bind(head, body);
    cases.push(Case {
        label: "bind under a tail",
        core,
        root,
        origin: FocusOrigin::Return,
        rendering: "⟨1 |+ μ̃x. ⟨x0 |+ ★⟩⟩",
    });

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let unit = core.value_unit();
    let head = core.computation_return(one);
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let inner = core.computation_return(outer);
    let function = core.computation_lambda(inner);
    let bound = core.computation_bind(head, function);
    let root = core.computation_application(bound, unit);
    cases.push(Case {
        label: "bind under a frame",
        core,
        root,
        origin: FocusOrigin::Bind,
        rendering: "⟨μα. ⟨1 |+ μ̃x. ⟨cocase {apply(x; α) ⇒ ⟨x1 |+ α0⟩} |− α0⟩⟩ |− apply((); ★)⟩",
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let scrutinee = core.value_injection(Side::Left, unit);
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let on_left = core.computation_return(one);
    let on_right = core.computation_return(two);
    let root = core.computation_case(scrutinee, on_left, on_right);
    cases.push(Case {
        label: "case under a tail",
        core,
        root,
        origin: FocusOrigin::Case,
        rendering: "⟨inl(()) |+ case {inl(x) ⇒ ⟨1 |+ ★⟩ | inr(x) ⇒ ⟨2 |+ ★⟩}⟩",
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let scrutinee = core.value_injection(Side::Left, unit);
    let own = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let left_body = core.computation_return(own);
    let on_left = core.computation_lambda(left_body);
    let five = integer(&mut core, Integer(5));
    let right_body = core.computation_return(five);
    let on_right = core.computation_lambda(right_body);
    let cased = core.computation_case(scrutinee, on_left, on_right);
    let three = integer(&mut core, Integer(3));
    let root = core.computation_application(cased, three);
    cases.push(Case {
        label: "case under a frame",
        core,
        root,
        origin: FocusOrigin::Case,
        rendering: "⟨μα. ⟨inl(()) |+ case {inl(x) ⇒ ⟨cocase {apply(x; α) ⇒ ⟨x0 |+ α0⟩} |− α0⟩ | inr(x) ⇒ ⟨cocase {apply(x; α) ⇒ ⟨5 |+ α0⟩} |− α0⟩}⟩ |− apply(3; ★)⟩",
    });

    let mut core = CoreArena::new();
    let constant = core.value_constant(ConstantIndex::from(0_usize));
    let minus_three = integer(&mut core, Integer(-3));
    let lifted = core.value_lift(Level::zero(), minus_three);
    let pair = core.value_pair(constant, lifted);
    let root = core.computation_return(pair);
    cases.push(Case {
        label: "structured values",
        core,
        root,
        origin: FocusOrigin::Return,
        rendering: "⟨pair(c0, lift(-3)) |+ ★⟩",
    });

    cases
}

/// Each former focuses to its exact rendering, records its origin, passes the
/// check closed, and reads back as itself; together the cases record every
/// origin a computation can contribute.
#[test]
fn hand_built_cases_cover_every_former()
{
    let mut seen = BTreeSet::new();
    for case in cases() {
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(&case.core, case.root, &mut arena, &mut provenance)
            .unwrap_or_else(|refusal| panic!("{}: focusing refused: {refusal}", case.label));
        assert_eq!(
            String::from(case.rendering),
            render_command(&arena, command),
            "{}: the rendering",
            case.label
        );
        assert_eq!(
            Some(case.origin),
            provenance.origin(command),
            "{}: the root's origin",
            case.label
        );
        assert_eq!(
            Ok(FreeSet::default()),
            check_command(&arena, command),
            "{}: the image is well formed and closed",
            case.label
        );
        let mut decoded = CoreArena::new();
        let back = unfocus_command(&arena, command, &mut decoded)
            .unwrap_or_else(|refusal| panic!("{}: unfocusing refused: {refusal}", case.label));
        assert_eq!(
            Agreement::Same,
            same_computation(&case.core, case.root, &decoded, back),
            "{}: the round trip",
            case.label
        );
        seen.extend(provenance.entries().map(|(_, origin)| origin));
    }
    assert_eq!(
        BTreeSet::from([
            FocusOrigin::Return,
            FocusOrigin::Force,
            FocusOrigin::Lambda,
            FocusOrigin::Case,
            FocusOrigin::Bind,
        ]),
        seen,
        "every computation origin is exercised"
    );
}

/// A declaration's value focuses to one positive cut against `★`, recorded
/// as a top value.
#[test]
fn top_level_value_focuses_against_top()
{
    let mut core = CoreArena::new();
    let seven = integer(&mut core, Integer(7));
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let command =
        focus_top_value(&core, seven, &mut arena, &mut provenance).expect("a literal focuses");
    assert_eq!(
        "⟨7 |+ ★⟩",
        render_command(&arena, command),
        "the cut against ★"
    );
    assert_eq!(
        Some(FocusOrigin::TopValue),
        provenance.origin(command),
        "recorded as a top value"
    );
    assert_eq!(
        Ok(FreeSet::default()),
        check_command(&arena, command),
        "well formed and closed"
    );
}
