//! The thin shared pointer: its one word, its block's layout, its header and
//! its items, the order of its drops, and a build whose iterator falls short.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the fixtures count blocks, and an iterator states its length"
    )
)]

use alloc::alloc::Global;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::cell::Cell;
use core::cell::RefCell;
use core::iter;
use core::mem::size_of;
use core::panic::AssertUnwindSafe;
use std::panic::catch_unwind;

use gandr_kernel_data::Identity;
use gandr_kernel_data::Refused;
use gandr_kernel_data::ThinShared;

use crate::shared::Ledger;
use crate::shared::Refusing;
use crate::shared::built;

/// A value that logs its name when it drops, and panics in its drop when it
/// explodes.
struct Logged<'log>
{
    /// The names of the drops so far, in order.
    log: &'log RefCell<Vec<&'static str>>,
    /// The name that the drop logs.
    name: &'static str,
    /// Whether the drop panics.
    explodes: bool,
}

impl Drop for Logged<'_>
{
    /// Logs the name, and panics when the value explodes.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        self.log.borrow_mut().push(self.name);
        assert!(!self.explodes, "the value's drop panics");
    }
}

/// An iterator that states `len` as its exact length, whatever `items`
/// yields.
struct Stated<I>
{
    /// The items that the iterator yields.
    items: I,
    /// The length that the iterator states.
    len: usize,
}

impl<I> Iterator for Stated<I>
where
    I: Iterator,
{
    type Item = I::Item;

    /// # Specification
    /// trivial.
    fn next(&mut self) -> Option<I::Item>
    {
        self.items.next()
    }

    /// # Specification
    /// trivial.
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        (self.len, Some(self.len))
    }
}

impl<I> ExactSizeIterator for Stated<I> where I: Iterator
{
}

/// The logged values of `names`, none of which explodes.
///
/// # Specification
/// trivial.
fn logged<'log, const N: usize>(
    log: &'log RefCell<Vec<&'static str>>,
    names: [&'static str; N],
) -> [Logged<'log>; N]
{
    names.map(|name| Logged {
        log,
        name,
        explodes: false,
    })
}

#[test]
fn a_thin_block_holds_the_count_the_length_the_header_and_the_items()
{
    let drawn = Cell::new(0);
    let returned = Cell::new(0);
    let last = Cell::new(Layout::new::<()>());
    let ledger = Ledger {
        drawn: &drawn,
        returned: &returned,
        last: &last,
    };
    let thin = built(ThinShared::from_header_and_iter_in(
        0xabcd_u32,
        [1_u16, 2, 3],
        ledger,
    ));
    assert_eq!(*thin.header(), 0xabcd);
    assert_eq!(thin.slice(), [1, 2, 3]);
    assert_eq!(
        (last.get().size(), last.get().align()),
        (32, 8),
        "the count and the length take 16 bytes, the header 4, and three items 6, padded to 8"
    );
    let empty = built(ThinShared::from_header_and_iter_in(
        1_u32,
        iter::empty::<u16>(),
        ledger,
    ));
    assert_eq!(empty.slice(), [0_u16; 0]);
    assert_eq!((last.get().size(), last.get().align()), (24, 8));
    drop((thin, empty));
    assert_eq!((drawn.get(), returned.get()), (2, 2));
    assert_eq!(
        size_of::<ThinShared<u32, u16, Global>>(),
        size_of::<usize>()
    );

    let refused = ThinShared::from_header_and_iter_in(
        0_u32,
        Stated {
            items: iter::empty::<u16>(),
            len: usize::MAX,
        },
        ledger,
    );
    assert!(
        matches!(refused, Err(Refused::Overflow)),
        "a layout past isize::MAX is refused"
    );
    assert_eq!(drawn.get(), 2, "a layout past isize::MAX draws no block");
}

#[test]
fn an_iterator_short_of_its_length_panics_and_leaves_nothing()
{
    let drawn = Cell::new(0);
    let returned = Cell::new(0);
    let last = Cell::new(Layout::new::<()>());
    let ledger = Ledger {
        drawn: &drawn,
        returned: &returned,
        last: &last,
    };
    let log = RefCell::new(Vec::new());
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        ThinShared::from_header_and_iter_in(
            Logged {
                log: &log,
                name: "header",
                explodes: false,
            },
            Stated {
                items: logged(&log, ["item 0", "item 1"]).into_iter(),
                len: 3,
            },
            ledger,
        )
    }));
    assert!(outcome.is_err());
    assert_eq!(*log.borrow(), ["header", "item 0", "item 1"]);
    assert_eq!((drawn.get(), returned.get()), (1, 1));
}

#[test]
fn a_refused_block_gives_the_refusal_and_drops_the_header()
{
    let log = RefCell::new(Vec::new());
    let refused = ThinShared::from_header_and_iter_in(
        Logged {
            log: &log,
            name: "header",
            explodes: false,
        },
        logged(&log, ["item 0", "item 1"]),
        Refusing,
    );
    let Err(Refused::Allocator(layout)) = refused
    else {
        panic!("a refusing allocator gives its refusal");
    };
    assert_eq!(
        layout.size(),
        size_of::<usize>()
            .saturating_mul(2)
            .saturating_add(size_of::<Logged<'_>>().saturating_mul(3)),
        "the refusal names the block of the count, the length, the header and two items"
    );
    let mut dropped = log.borrow().clone();
    dropped.sort_unstable();
    assert_eq!(
        dropped,
        ["header", "item 0", "item 1"],
        "the header and the items drop once"
    );
}

#[test]
fn a_mutable_borrow_writes_a_sole_block_in_place_and_copies_a_shared_one()
{
    let mut sole = ThinShared::from_header_and_iter(7_u8, [1_u16, 2, 3]);
    if let Some(first) = ThinShared::make_mut(&mut sole).first_mut() {
        *first = 9;
    }
    assert_eq!(
        sole.slice(),
        [9, 2, 3],
        "a sole block takes the write in place"
    );
    let kept = sole.clone();
    assert_eq!(
        ThinShared::ptr_eq(&sole, &kept),
        Identity::Same,
        "a clone shares the block"
    );
    if let Some(last) = ThinShared::make_mut(&mut sole).last_mut() {
        *last = 4;
    }
    assert_eq!(
        ThinShared::ptr_eq(&sole, &kept),
        Identity::Distinct,
        "the write moves the holder to a block of its own"
    );
    assert_eq!(
        (sole.slice(), kept.slice()),
        (&[9, 2, 4][..], &[9, 2, 3][..]),
        "the other holder reads the old items"
    );
    assert_eq!(
        (*sole.header(), *kept.header()),
        (7, 7),
        "the copy keeps the header"
    );
}

#[test]
fn an_empty_default_shares_the_static_block()
{
    let first = ThinShared::<(), u64, Global>::default();
    let second = ThinShared::<(), u64, Global>::default();
    assert_eq!(first.slice(), [0_u64; 0]);
    assert_eq!(
        ThinShared::ptr_eq(&first, &second),
        Identity::Same,
        "two empty defaults share the static block"
    );
    let narrow = ThinShared::<(), u8, Global>::default();
    assert_eq!(narrow.slice(), [0_u8; 0]);
    let mut written = second.clone();
    assert_eq!(ThinShared::make_mut(&mut written), [0_u64; 0]);
    assert_eq!(
        ThinShared::ptr_eq(&written, &first),
        Identity::Distinct,
        "a mutable borrow moves the holder to a block of its own"
    );
    drop((first, second, narrow, written));
    let again = ThinShared::<(), u64, Global>::default();
    assert_eq!(
        ThinShared::ptr_eq(&again, &ThinShared::default()),
        Identity::Same,
        "the drops leave the static block whole"
    );
}

#[test]
fn a_collect_holds_the_items_with_or_without_an_exact_hint()
{
    let hinted: ThinShared<(), u32, Global> = (1_u32 ..= 5_u32).collect();
    let filtered: ThinShared<(), u32, Global> =
        (1_u32 ..= 10_u32).filter(|item| item % 2 == 1).collect();
    assert_eq!(hinted.slice(), [1, 2, 3, 4, 5]);
    assert_eq!(filtered.slice(), [1, 3, 5, 7, 9]);
    let empty: ThinShared<(), u32, Global> = iter::empty().collect();
    let none_kept: ThinShared<(), u32, Global> = (1_u32 ..= 3_u32).filter(|_| false).collect();
    assert_eq!(
        ThinShared::ptr_eq(&empty, &ThinShared::default()),
        Identity::Same,
        "an empty collect shares the static block"
    );
    assert_eq!(
        ThinShared::ptr_eq(&none_kept, &ThinShared::default()),
        Identity::Same,
        "a collect that keeps nothing shares the static block"
    );
}

#[test]
fn an_iterator_off_its_exact_hint_panics()
{
    let short = catch_unwind(|| {
        Stated {
            items: [1_u32, 2].into_iter(),
            len: 3,
        }
        .collect::<ThinShared<(), u32, Global>>()
    });
    assert!(short.is_err(), "an iterator short of its hint panics");
    let long = catch_unwind(|| {
        Stated {
            items: [1_u32, 2, 3, 4].into_iter(),
            len: 3,
        }
        .collect::<ThinShared<(), u32, Global>>()
    });
    assert!(long.is_err(), "an iterator past its hint panics");
}

#[test]
fn the_last_holder_drops_the_header_before_the_items()
{
    let log = RefCell::new(Vec::new());
    let thin = ThinShared::from_header_and_iter(
        Logged {
            log: &log,
            name: "header",
            explodes: false,
        },
        logged(&log, ["item 0", "item 1"]),
    );
    let clone = thin.clone();
    assert_eq!(clone.slice().len(), 2);
    drop(clone);
    assert_eq!(
        *log.borrow(),
        [""; 0],
        "a holder that stays keeps the block"
    );
    drop(thin);
    assert_eq!(*log.borrow(), ["header", "item 0", "item 1"]);

    log.borrow_mut().clear();
    let drawn = Cell::new(0);
    let returned = Cell::new(0);
    let last = Cell::new(Layout::new::<()>());
    let ledger = Ledger {
        drawn: &drawn,
        returned: &returned,
        last: &last,
    };
    let bomb = built(ThinShared::from_header_and_iter_in(
        Logged {
            log: &log,
            name: "header",
            explodes: true,
        },
        logged(&log, ["item 0", "item 1"]),
        ledger,
    ));
    assert!(catch_unwind(AssertUnwindSafe(|| drop(bomb))).is_err());
    assert_eq!(
        *log.borrow(),
        ["header", "item 0", "item 1"],
        "a header whose drop panics leaves the items to drop"
    );
    assert_eq!(
        (drawn.get(), returned.get()),
        (1, 1),
        "and the block returns"
    );
}
