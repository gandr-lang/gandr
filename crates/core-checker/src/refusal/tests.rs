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
            miss: crate::EndpointMiss::Unshown,
        }
        .compared(),
        Compared {
            expected: unnamed,
            found: unnamed,
        },
        "an endpoint mismatch names terms, not types"
    );
}

/// Every refusal that names types reports them on its own sides: a sort,
/// level, family-argument or `over` mismatch and an amplified capability
/// expect the checked type and found the synthesised one; a forged
/// capability expects the type it stood at; a dependent bind or stack and a
/// compound endpoint found the computation type their body synthesised; each
/// refusal naming one classifier, capability or code found that; and a
/// refused crossing found the former that does not cross, whichever
/// predicate it fails, while a refused mark compares nothing.
#[test]
fn each_refusal_naming_types_reports_them_on_its_own_sides()
{
    use gandr_kernel_term::ConstantIndex;

    use super::ArgumentPosition;

    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let list = arena.value_type_list(unit);
    let returns_unit = arena.comp_type_returner(unit);
    let returns_list = arena.comp_type_returner(list);
    let term = arena.value_unit();
    let body = arena.computation_return(term);
    let unnamed = Maybe::Absent(compared::Absent::Unnamed);
    let both = Compared {
        expected: Maybe::Present(TypeNode::Value(unit)),
        found: Maybe::Present(TypeNode::Value(list)),
    };
    let found_list = Compared {
        expected: unnamed,
        found: Maybe::Present(TypeNode::Value(list)),
    };
    let found_body = Compared {
        expected: unnamed,
        found: Maybe::Present(TypeNode::Computation(returns_list)),
    };
    let rows = [
        (
            CheckRefusal::SortMismatch {
                at: term,
                synthesised: list,
                expected: unit,
            },
            both,
        ),
        (
            CheckRefusal::LevelMismatch {
                at: term,
                synthesised: list,
                expected: unit,
            },
            both,
        ),
        (
            CheckRefusal::FamilyArgumentClassifier {
                at: term,
                position: ArgumentPosition::from(1_u32),
                synthesised: list,
                expected: unit,
            },
            both,
        ),
        (
            CheckRefusal::NotOver {
                at: term,
                synthesised: list,
                expected: unit,
            },
            both,
        ),
        (
            CheckRefusal::CapabilityAmplified(Mismatch::Value {
                at: term,
                synthesised: list,
                expected: unit,
            }),
            both,
        ),
        (
            CheckRefusal::CapabilityAmplified(Mismatch::Computation {
                at: body,
                synthesised: returns_list,
                expected: returns_unit,
            }),
            Compared {
                expected: Maybe::Present(TypeNode::Computation(returns_unit)),
                found: Maybe::Present(TypeNode::Computation(returns_list)),
            },
        ),
        (
            CheckRefusal::CapabilityForged {
                at: term,
                expected: unit,
            },
            Compared {
                expected: Maybe::Present(TypeNode::Value(unit)),
                found: unnamed,
            },
        ),
        (
            CheckRefusal::CapabilityEscaped {
                at: TermNode::Value(term),
                found: TypeNode::Value(list),
            },
            found_list,
        ),
        (
            CheckRefusal::DependentBind {
                at: body,
                synthesised: returns_list,
            },
            found_body,
        ),
        (
            CheckRefusal::DependentStack {
                at: term,
                synthesised: returns_list,
            },
            found_body,
        ),
        (
            CheckRefusal::CompoundEndpoint {
                at: term,
                synthesised: returns_list,
            },
            found_body,
        ),
        (
            CheckRefusal::StaticClassifierExpected {
                at: unit,
                found: list,
            },
            found_list,
        ),
        (
            CheckRefusal::CapabilityOutsideAuthority {
                at: body,
                capability: list,
            },
            found_list,
        ),
        (CheckRefusal::CapabilityConsumable(list), found_list),
        (
            CheckRefusal::CapabilityUngranted {
                constant: ConstantIndex::from(0_usize),
                declared: list,
            },
            found_list,
        ),
        (
            CheckRefusal::FunextUnsupported {
                at: term,
                classifier: list,
            },
            found_list,
        ),
        (
            CheckRefusal::EquivUnsupported {
                at: term,
                classifier: list,
            },
            found_list,
        ),
        (
            CheckRefusal::UncertifiedStratum {
                at: term,
                code: list,
            },
            found_list,
        ),
        (
            CheckRefusal::Located {
                at: CoreNode::Term(TermNode::Value(term)),
                defect: crate::worlds::LocatedDefect::Immobile {
                    crossed: crate::worlds::Crossed::Result,
                    ty: unit,
                    former: list,
                    predicate: crate::worlds::Predicate::Mobile,
                },
            },
            found_list,
        ),
        (
            CheckRefusal::Located {
                at: CoreNode::Term(TermNode::Value(term)),
                defect: crate::worlds::LocatedDefect::Immobile {
                    crossed: crate::worlds::Crossed::Constant,
                    ty: unit,
                    former: list,
                    predicate: crate::worlds::Predicate::Open,
                },
            },
            found_list,
        ),
        (
            CheckRefusal::Located {
                at: CoreNode::Term(TermNode::Value(term)),
                defect: crate::worlds::LocatedDefect::MarkUnfounded {
                    atom: ConstantIndex::from(0_usize),
                    former: list,
                    predicate: crate::worlds::Predicate::Open,
                },
            },
            Compared {
                expected: unnamed,
                found: unnamed,
            },
        ),
    ];
    for (refusal, compared) in rows {
        assert_eq!(refusal.compared(), compared, "{refusal:?}");
    }
}

#[test]
fn each_unadmitted_former_carries_its_pinned_class()
{
    let mut arena = CoreArena::new();
    let at = CoreNode::Term(TermNode::Value(arena.value_unit()));
    let unruled = FailureClass::Unimplemented(TrackingIssue::JUDGEMENT_FORMER);
    let rows = [
        (UnadmittedFormer::Stage, FailureClass::MalformedSource),
        (UnadmittedFormer::TypeLift, FailureClass::MalformedSource),
        (UnadmittedFormer::NumericLiteral, unruled),
        (UnadmittedFormer::NumericAtom, unruled),
        (UnadmittedFormer::ValueLift, unruled),
        (UnadmittedFormer::SortParameter, unruled),
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
