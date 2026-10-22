use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::TrackingIssue;
use quenchant_shape::shape::Maybe;

use super::CheckRefusal;
use super::CheckingForm;
use super::Compared;
use super::CoreNode;
use super::ExpectedShape;
use super::Mismatch;
use super::TermNode;
use super::TypeNode;
use super::UnadmittedFormer;
use super::compared;

#[test]
fn a_refusal_compares_the_types_it_names()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let list = arena.value_type_list(unit);
    let returns_unit = arena.comp_type_returner(unit);
    let returns_list = arena.comp_type_returner(list);
    let term = arena.value_unit();
    let body = arena.computation_return(term);
    let unnamed = Maybe::Absent(compared::Absent::Unnamed);
    assert_eq!(
        CheckRefusal::TypeMismatch(Mismatch::Value {
            at: term,
            synthesised: list,
            expected: unit,
        })
        .compared(),
        Compared {
            expected: Maybe::Present(TypeNode::Value(unit)),
            found: Maybe::Present(TypeNode::Value(list)),
        },
        "a value mismatch expects the checked type and found the synthesised one"
    );
    assert_eq!(
        CheckRefusal::TypeMismatch(Mismatch::Computation {
            at: body,
            synthesised: returns_list,
            expected: returns_unit,
        })
        .compared(),
        Compared {
            expected: Maybe::Present(TypeNode::Computation(returns_unit)),
            found: Maybe::Present(TypeNode::Computation(returns_list)),
        },
        "a computation mismatch compares computation types"
    );
    assert_eq!(
        CheckRefusal::ShapeMismatch {
            at: TermNode::Value(term),
            wanted: ExpectedShape::Thunk,
            found: TypeNode::Value(unit),
        }
        .compared(),
        Compared {
            expected: unnamed,
            found: Maybe::Present(TypeNode::Value(unit)),
        },
        "a shape mismatch expects a former, not a type"
    );
    assert_eq!(
        CheckRefusal::NotSynthesisable {
            form: CheckingForm::Thunk(term),
        }
        .compared(),
        Compared {
            expected: unnamed,
            found: unnamed,
        },
        "a checking-only form compares nothing"
    );
    assert_eq!(
        CheckRefusal::EndpointMismatch {
            at: term,
            left: term,
            right: term,
        }
        .compared(),
        Compared {
            expected: unnamed,
            found: unnamed,
        },
        "an endpoint mismatch names terms, not types"
    );
}

#[test]
fn each_unadmitted_former_carries_its_pinned_class()
{
    let mut arena = CoreArena::new();
    let at = CoreNode::Term(TermNode::Value(arena.value_unit()));
    let unfiled = FailureClass::Unimplemented(TrackingIssue::UNFILED);
    let rows = [
        (UnadmittedFormer::Stage, FailureClass::MalformedSource),
        (UnadmittedFormer::TypeLift, FailureClass::MalformedSource),
        (UnadmittedFormer::NumericLiteral, unfiled),
        (UnadmittedFormer::NumericAtom, unfiled),
        (UnadmittedFormer::ValueLift, unfiled),
        (UnadmittedFormer::SortParameter, unfiled),
        (UnadmittedFormer::TopUniverse, FailureClass::EngineFault),
        (UnadmittedFormer::Abstract, FailureClass::EngineFault),
        (UnadmittedFormer::StaticLambda, FailureClass::EngineFault),
        (UnadmittedFormer::EffectRow, FailureClass::EngineFault),
        (UnadmittedFormer::Reify, FailureClass::EngineFault),
        (UnadmittedFormer::Stack, FailureClass::EngineFault),
        (UnadmittedFormer::Perform, FailureClass::EngineFault),
        (UnadmittedFormer::Handle, FailureClass::EngineFault),
        (UnadmittedFormer::Resume, FailureClass::EngineFault),
        (UnadmittedFormer::Reset, FailureClass::EngineFault),
        (UnadmittedFormer::Shift, FailureClass::EngineFault),
        (UnadmittedFormer::Capability, FailureClass::EngineFault),
        (UnadmittedFormer::Exercise, FailureClass::EngineFault),
        (UnadmittedFormer::Scope, FailureClass::EngineFault),
        (UnadmittedFormer::Run, FailureClass::EngineFault),
        (UnadmittedFormer::HigherFlow, FailureClass::EngineFault),
        (UnadmittedFormer::Memory, FailureClass::EngineFault),
        (UnadmittedFormer::Buffer, FailureClass::EngineFault),
        (UnadmittedFormer::Abandon, FailureClass::EngineFault),
    ];
    for (former, class) in rows {
        assert_eq!(
            CheckRefusal::OutOfFragment { at, former }.classify(),
            class,
            "the judgement's refusal of {former:?}"
        );
    }
}
