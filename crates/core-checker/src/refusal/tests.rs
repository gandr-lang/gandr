use gandr_core_term::CoreArena;
use quenchant_shape::shape::Maybe;

use super::CheckRefusal;
use super::CheckingForm;
use super::Compared;
use super::ExpectedShape;
use super::Mismatch;
use super::TermNode;
use super::TypeNode;
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
