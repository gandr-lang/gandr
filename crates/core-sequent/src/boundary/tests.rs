use gandr_kernel_term::ArenaLength;
use gandr_kernel_term::Family;

use super::FamilyAddress as _;
use crate::il::ProducerId;

/// The excluded address ceiling is reached without allocating node bytes.
#[test]
fn addresses_refuse_exactly_at_the_u32_ceiling()
{
    assert_eq!(
        Some(ProducerId::from(0_u32)),
        ProducerId::next_in(&Family::<()>::default())
    );
    assert_eq!(
        Some(ProducerId::from(2_u32)),
        ProducerId::next_in(&Family::from(alloc::vec![(), ()]))
    );
    let ceiling = usize::try_from(u32::MAX).expect("the address ceiling fits usize");
    let mut family = Family::from(alloc::vec![(); ceiling]);
    assert_eq!(None, ProducerId::next_in(&family));
    family.truncate(ArenaLength::from(ceiling.saturating_sub(1)));
    assert_eq!(
        Some(ProducerId::from(u32::MAX.saturating_sub(1))),
        ProducerId::next_in(&family),
    );
}

/// Reads distinguish the last live slot from the exact end and a dropped
/// slot, in a family with nothing frozen and in one frozen part way.
#[test]
fn address_reads_distinguish_end_and_truncation()
{
    let mut family = Family::from(alloc::vec![11_u32, 29_u32]);
    let first = ProducerId::from(0_u32);
    let last = ProducerId::from(1_u32);
    assert_eq!(Some(&11_u32), first.read_in(&family));
    assert_eq!(Some(&29_u32), last.read_in(&family));
    assert_eq!(None, ProducerId::from(2_u32).read_in(&family));
    family.truncate(ArenaLength::from(1_usize));
    assert_eq!(Some(&11_u32), first.read_in(&family));
    assert_eq!(None, last.read_in(&family));
    family.truncate(ArenaLength::from(0_usize));
    assert_eq!(None, first.read_in(&family));

    // The first node frozen, the second the family's own: a read on either
    // side of the boundary, and past it, answers as the unfrozen family's did.
    let mut frozen = Family::default();
    frozen.push(11_u32);
    frozen.freeze();
    frozen.push(29_u32);
    assert_eq!(Some(&11_u32), first.read_in(&frozen));
    assert_eq!(Some(&29_u32), last.read_in(&frozen));
    assert_eq!(None, ProducerId::from(2_u32).read_in(&frozen));
    assert_eq!(Some(ProducerId::from(2_u32)), ProducerId::next_in(&frozen));
    frozen.truncate(ArenaLength::from(1_usize));
    assert_eq!(Some(&11_u32), first.read_in(&frozen));
    assert_eq!(None, last.read_in(&frozen));
    frozen.truncate(ArenaLength::from(0_usize));
    assert_eq!(None, first.read_in(&frozen));
}
