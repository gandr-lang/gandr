use super::FamilyAddress as _;
use crate::il::ProducerId;

/// The excluded address ceiling is reached without allocating node bytes.
#[test]
fn addresses_refuse_exactly_at_the_u32_ceiling()
{
    assert_eq!(
        Some(ProducerId::from(0_u32)),
        ProducerId::next_in::<()>(&[])
    );
    assert_eq!(
        Some(ProducerId::from(2_u32)),
        ProducerId::next_in(&[(), ()])
    );
    let ceiling = usize::try_from(u32::MAX).expect("the address ceiling fits usize");
    let mut family = alloc::vec![(); ceiling];
    assert_eq!(None, ProducerId::next_in(&family));
    family.pop().expect("the ceiling is positive");
    assert_eq!(
        Some(ProducerId::from(u32::MAX.saturating_sub(1))),
        ProducerId::next_in(&family),
    );
}

/// Reads distinguish the last live slot from the exact end and a dropped
/// slot.
#[test]
fn address_reads_distinguish_end_and_truncation()
{
    let mut family = alloc::vec![11_u32, 29_u32];
    let first = ProducerId::from(0_u32);
    let last = ProducerId::from(1_u32);
    assert_eq!(Some(&11_u32), first.read_in(&family));
    assert_eq!(Some(&29_u32), last.read_in(&family));
    assert_eq!(None, ProducerId::from(2_u32).read_in(&family));
    family.truncate(1);
    assert_eq!(Some(&11_u32), first.read_in(&family));
    assert_eq!(None, last.read_in(&family));
    family.clear();
    assert_eq!(None, first.read_in(&family));
}
