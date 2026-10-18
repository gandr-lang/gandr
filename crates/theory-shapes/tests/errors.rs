//! The rendering of refusals: each names the index or the leg it refuses,
//! and no two render alike.

use gandr_theory_shapes::Leg;
use gandr_theory_shapes::NodeId;
use gandr_theory_shapes::Point;
use gandr_theory_shapes::ShapeError;
use gandr_theory_shapes::Variable;

#[test]
fn every_refusal_names_its_index()
{
    let index = 37_usize;
    let needle = format!("{index}");
    let point = Point::from(index);
    let variable = Variable::from(index);
    let node = NodeId::from(index);
    let indexed = [
        ShapeError::PointOutside(point),
        ShapeError::NotIncluded(point),
        ShapeError::Disagreement(point),
        ShapeError::VariableOutside(variable),
        ShapeError::WrongCarrier(variable),
        ShapeError::Disjunction(node),
        ShapeError::AssignedOutside(variable),
        ShapeError::CarrierInhabited(variable),
        ShapeError::NotPremiseBottom(node),
        ShapeError::NotPremiseMember(node),
        ShapeError::CitedVariable(node),
        ShapeError::NotDisjoint(variable),
        ShapeError::Unsupported(node),
    ];
    for error in indexed {
        assert!(
            format!("{error}").contains(&needle),
            "{error:?} renders as `{error}`"
        );
    }
    let left = format!("{}", Leg::Left);
    let right = format!("{}", Leg::Right);
    assert_ne!(left, right);
    assert!(format!("{}", ShapeError::MapLength(Leg::Left)).contains(&left));
    assert!(format!("{}", ShapeError::MapLength(Leg::Right)).contains(&right));
    let bare = [
        ShapeError::DifferentAmbient,
        ShapeError::MapLength(Leg::Left),
        ShapeError::MapLength(Leg::Right),
        ShapeError::MalformedFormula,
        ShapeError::AssignmentLength,
        ShapeError::NotCountermodel,
        ShapeError::CitationCount,
    ];
    let mut rendered: Vec<String> = indexed
        .iter()
        .chain(&bare)
        .map(|error| format!("{error}"))
        .collect();
    let count = rendered.len();
    rendered.sort();
    rendered.dedup();
    assert_eq!(rendered.len(), count, "every refusal renders distinctly");
}
