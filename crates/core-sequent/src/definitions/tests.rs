use gandr_kernel_term::ConstantIndex;

use super::Definition;
use super::Definitions;
use crate::il::ProducerId;

/// Admissions take consecutive positions from zero, each reading back the
/// definition admitted there, and a position never admitted reads nothing:
/// the dispatcher's constant indices are these positions.
#[test]
fn each_admission_takes_the_next_position()
{
    let mut definitions = Definitions::new();
    let opaque = definitions.push(Definition::Opaque);
    let transparent = definitions.push(Definition::Transparent(ProducerId::from(7_u32)));
    assert_eq!(ConstantIndex::from(0_usize), opaque, "the first position");
    assert_eq!(
        ConstantIndex::from(1_usize),
        transparent,
        "the next position"
    );
    assert_eq!(Some(Definition::Opaque), definitions.get(opaque));
    assert_eq!(
        Some(Definition::Transparent(ProducerId::from(7_u32))),
        definitions.get(transparent)
    );
    assert_eq!(
        None,
        definitions.get(ConstantIndex::from(2_usize)),
        "past the last admission"
    );
}
