//! The shared pointer: its block, its count, its mutable borrows, each
//! value's one drop and each block's one free, and the `loom` model of its
//! orderings.

use alloc::alloc::Global;
use alloc::vec;
use alloc::vec::Vec;
use core::alloc::AllocError;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::cell::Cell;
use core::iter;
use core::mem::size_of;
use core::panic::AssertUnwindSafe;
use core::ptr::NonNull;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::panic::catch_unwind;
use std::thread;

use gandr_kernel_data::Held;
use gandr_kernel_data::Identity;
use gandr_kernel_data::Refused;
use gandr_kernel_data::Shared;
use gandr_kernel_data::Unique;
use quenchant_shape::shape::Maybe;

/// The global allocator, which counts the blocks it draws and returns, and
/// keeps the layout of the last draw.
#[derive(Clone, Copy)]
pub struct Ledger<'count>
{
    /// The blocks drawn so far.
    pub drawn: &'count Cell<usize>,
    /// The blocks returned so far.
    pub returned: &'count Cell<usize>,
    /// The layout of the last draw.
    pub last: &'count Cell<Layout>,
}

/// # Safety
/// - unsafe invariants: each block comes from `Global` and returns to it, so
///   the allocator keeps `Global`'s own.
// SAFETY: each block comes from `Global` and returns to it.
unsafe impl Allocator for Ledger<'_>
{
    /// A block of `layout` from `Global`, counted.
    ///
    /// # Specification
    /// trivial.
    fn allocate(
        &self,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    {
        self.drawn.set(self.drawn.get().saturating_add(1));
        self.last.set(layout);
        Global.allocate(layout)
    }

    /// # Safety
    /// - unsafe invariants: the caller's, as `Allocator::deallocate` states.
    ///
    /// # Specification
    /// trivial.
    unsafe fn deallocate(
        &self,
        ptr: NonNull<u8>,
        layout: Layout,
    )
    {
        self.returned.set(self.returned.get().saturating_add(1));
        // SAFETY: the caller's block came from `allocate`, which drew it from
        // `Global` with `layout`.
        unsafe {
            Global.deallocate(ptr, layout);
        }
    }
}

/// A value that counts its drops, and panics in its drop when it explodes.
struct Bomb<'count>
{
    /// The drops so far.
    drops: &'count Cell<usize>,
    /// Whether the drop panics.
    explodes: bool,
}

impl Drop for Bomb<'_>
{
    /// Counts the drop, and panics when the value explodes.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        self.drops.set(self.drops.get().saturating_add(1));
        assert!(!self.explodes, "the value's drop panics");
    }
}

/// A value that counts its drops on any thread.
#[repr(transparent)]
struct Tally<'count>(&'count AtomicUsize);

impl Drop for Tally<'_>
{
    /// Counts the drop.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        self.0.fetch_add(1, Ordering::Relaxed);
    }
}

/// The value of a build that the allocator accepts.
///
/// # Specification
/// trivial.
pub fn built<T>(result: Result<T, Refused>) -> T
{
    match result {
        Ok(value) => value,
        Err(refused) => panic!("the allocator refuses the block: {refused:?}"),
    }
}

/// An allocator that refuses each block.
#[derive(Clone, Copy)]
pub struct Refusing;

/// # Safety
/// - unsafe invariants: the allocator gives no block, so no block returns to
///   it.
// SAFETY: the allocator gives no block.
unsafe impl Allocator for Refusing
{
    /// A refusal of each layout.
    ///
    /// # Specification
    /// trivial.
    fn allocate(
        &self,
        _layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    {
        Err(AllocError)
    }

    /// # Safety
    /// - unsafe invariants: the caller's, as `Allocator::deallocate` states.
    ///
    /// # Specification
    /// trivial.
    unsafe fn deallocate(
        &self,
        _ptr: NonNull<u8>,
        _layout: Layout,
    )
    {
        // The allocator gives no block, so no block returns here.
    }
}

#[test]
fn a_block_holds_one_count_and_the_value()
{
    let drawn = Cell::new(0);
    let returned = Cell::new(0);
    let last = Cell::new(Layout::new::<()>());
    let ledger = Ledger {
        drawn: &drawn,
        returned: &returned,
        last: &last,
    };
    let shared = built(Unique::new_in(7_u64, ledger)).into_shared();
    assert_eq!(*shared, 7);
    assert_eq!(drawn.get(), 1);
    assert_eq!(
        last.get().size(),
        size_of::<usize>().saturating_add(size_of::<u64>())
    );
    assert_eq!(last.get().align(), 8);
    drop(shared);
    assert_eq!(returned.get(), 1);
    assert_eq!(size_of::<Shared<u64, Global>>(), size_of::<usize>());
    assert_eq!(size_of::<Unique<u64, Global>>(), size_of::<usize>());
}

#[test]
fn a_unique_value_builds_in_place_and_shares_with_one_holder()
{
    let mut unique = Unique::new(vec![1_u8, 2]);
    unique.push(3);
    let shared = unique.into_shared();
    assert_eq!(*shared, [1, 2, 3]);
    assert_eq!(usize::from(Shared::strong_count(&shared)), 1);
}

#[test]
fn the_count_follows_each_clone_and_each_drop()
{
    let first = Shared::new(5_u32);
    assert_eq!(usize::from(Shared::strong_count(&first)), 1);
    let second = first.clone();
    assert_eq!(usize::from(Shared::strong_count(&first)), 2);
    assert_eq!(Shared::ptr_eq(&first, &second), Identity::Same);
    drop(second);
    assert_eq!(usize::from(Shared::strong_count(&first)), 1);
    let other = Shared::new(5_u32);
    assert_eq!(Shared::ptr_eq(&first, &other), Identity::Distinct);
}

#[test]
fn a_mutable_borrow_writes_a_sole_value_in_place_and_copies_a_shared_one()
{
    let drawn = Cell::new(0);
    let returned = Cell::new(0);
    let last = Cell::new(Layout::new::<()>());
    let ledger = Ledger {
        drawn: &drawn,
        returned: &returned,
        last: &last,
    };
    let mut sole = built(Unique::new_in(1_u64, ledger)).into_shared();
    *Shared::make_mut(&mut sole) = 2;
    assert_eq!(*sole, 2);
    assert_eq!(drawn.get(), 1, "a sole value is written in place");

    let other = sole.clone();
    *Shared::make_mut(&mut sole) = 3;
    assert_eq!(
        (*sole, *other),
        (3, 2),
        "the other holder keeps the old value"
    );
    assert_eq!(
        drawn.get(),
        2,
        "a shared value is copied to a block of its own"
    );
    assert_eq!(Shared::ptr_eq(&sole, &other), Identity::Distinct);
    assert_eq!(usize::from(Shared::strong_count(&other)), 1);

    let mut first = other.clone();
    assert!(matches!(
        Shared::get_mut(&mut first),
        Maybe::Absent(Held::ByOthers)
    ));
    drop(other);
    let Maybe::Present(value) = Shared::get_mut(&mut first)
    else {
        panic!("a sole holder borrows its value mutably");
    };
    *value = 4;
    assert_eq!(*first, 4);
    drop((sole, first));
    assert_eq!(returned.get(), drawn.get());
}

#[test]
fn a_sole_holder_takes_its_value_out()
{
    let drawn = Cell::new(0);
    let returned = Cell::new(0);
    let last = Cell::new(Layout::new::<()>());
    let ledger = Ledger {
        drawn: &drawn,
        returned: &returned,
        last: &last,
    };
    let first = built(Unique::new_in(vec![9_u8], ledger)).into_shared();
    let second = first.clone();
    let Err(first) = Shared::try_unwrap(first)
    else {
        panic!("a shared value stays in its block");
    };
    assert_eq!(usize::from(Shared::strong_count(&first)), 2);
    drop(second);
    let Ok(value) = Shared::try_unwrap(first)
    else {
        panic!("a sole holder takes its value out");
    };
    assert_eq!(value, [9]);
    assert_eq!((drawn.get(), returned.get()), (1, 1));
}

#[test]
fn each_value_drops_once_and_each_block_frees_once()
{
    let drawn = Cell::new(0);
    let returned = Cell::new(0);
    let last = Cell::new(Layout::new::<()>());
    let ledger = Ledger {
        drawn: &drawn,
        returned: &returned,
        last: &last,
    };
    let drops = Cell::new(0);
    let holders: Vec<_> = {
        let first = built(Unique::new_in(
            Bomb {
                drops: &drops,
                explodes: false,
            },
            ledger,
        ))
        .into_shared();
        iter::repeat_with(|| first.clone()).take(4).collect()
    };
    assert_eq!(drops.get(), 0);
    drop(holders);
    assert_eq!((drops.get(), drawn.get(), returned.get()), (1, 1, 1));

    let bomb = built(Unique::new_in(
        Bomb {
            drops: &drops,
            explodes: true,
        },
        ledger,
    ))
    .into_shared();
    let clone = bomb.clone();
    drop(bomb);
    assert!(catch_unwind(AssertUnwindSafe(|| drop(clone))).is_err());
    assert_eq!(
        (drops.get(), drawn.get(), returned.get()),
        (2, 2, 2),
        "a panicking drop still frees its block"
    );

    let unique = built(Unique::new_in(
        Bomb {
            drops: &drops,
            explodes: true,
        },
        ledger,
    ));
    assert!(catch_unwind(AssertUnwindSafe(|| drop(unique))).is_err());
    assert_eq!((drops.get(), drawn.get(), returned.get()), (3, 3, 3));
}

#[test]
fn a_refused_block_gives_the_refusal_and_drops_the_value()
{
    let drops = Cell::new(0);
    let refused = Unique::new_in(
        Bomb {
            drops: &drops,
            explodes: false,
        },
        Refusing,
    );
    let Err(Refused::Allocator(layout)) = refused
    else {
        panic!("a refusing allocator gives its refusal");
    };
    assert_eq!(
        layout.size(),
        size_of::<usize>().saturating_add(size_of::<Bomb<'_>>()),
        "the refusal names the block's layout"
    );
    assert_eq!(drops.get(), 1, "the value of a refused block drops once");
}

#[test]
fn holders_on_many_threads_drop_the_value_once()
{
    let drops = AtomicUsize::new(0);
    let first = Shared::new(Tally(&drops));
    thread::scope(|scope| {
        for _ in 0_u8 .. 8 {
            let holder = first.clone();
            scope.spawn(move || {
                let copies: Vec<_> = iter::repeat_with(|| holder.clone()).take(64).collect();
                drop(copies);
            });
        }
    });
    assert_eq!(usize::from(Shared::strong_count(&first)), 1);
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    drop(first);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

/// The `loom` model of the count's orderings. Run it with
/// `RUSTFLAGS="--cfg loom"` and a target directory of its own.
#[cfg(loom)]
mod model
{
    use loom::cell::UnsafeCell;
    use loom::thread;

    use super::Shared;

    /// A value whose reads and writes `loom` checks for a race.
    #[repr(transparent)]
    struct Tracked(UnsafeCell<usize>);

    /// # Safety
    /// - unsafe invariants: `loom` checks each access to the cell, and reports
    ///   each pair of accesses that no ordering separates.
    // SAFETY: `loom` checks each access, so a race fails the model.
    unsafe impl Sync for Tracked
    {
    }

    impl Tracked
    {
        /// The value, read under `loom`'s check.
        ///
        /// # Specification
        /// trivial.
        fn get(&self) -> usize
        {
            // SAFETY: `loom` checks the read against each write.
            self.0.with(|value| unsafe { *value })
        }

        /// Writes `value` under `loom`'s check.
        ///
        /// # Specification
        /// trivial.
        fn set(
            &self,
            value: usize,
        )
        {
            // SAFETY: `loom` checks the write against each access.
            self.0.with_mut(|place| unsafe { *place = value });
        }
    }

    impl Clone for Tracked
    {
        /// # Specification
        /// trivial.
        fn clone(&self) -> Self
        {
            Self(UnsafeCell::new(self.get()))
        }
    }

    impl Drop for Tracked
    {
        /// Writes the value, so a read that no ordering puts before the drop
        /// races with it.
        ///
        /// # Specification
        /// trivial.
        fn drop(&mut self)
        {
            self.set(0);
        }
    }

    #[test]
    fn two_holders_drop_on_two_threads()
    {
        loom::model(|| {
            let first = Shared::new(Tracked(UnsafeCell::new(1)));
            let second = first.clone();
            let other = thread::spawn(move || {
                assert_eq!(second.get(), 1);
                drop(second);
            });
            assert_eq!(first.get(), 1);
            drop(first);
            other.join().expect("the other thread ends");
        });
    }

    #[test]
    fn a_mutable_borrow_races_a_drop()
    {
        loom::model(|| {
            let mut first = Shared::new(Tracked(UnsafeCell::new(1)));
            let second = first.clone();
            let other = thread::spawn(move || {
                assert_eq!(second.get(), 1);
                drop(second);
            });
            Shared::make_mut(&mut first).set(2);
            assert_eq!(first.get(), 2);
            other.join().expect("the other thread ends");
        });
    }

    #[test]
    fn three_holders_clone_drop_and_borrow_on_three_threads()
    {
        loom::model(|| {
            let mut first = Shared::new(Tracked(UnsafeCell::new(1)));
            let second = first.clone();
            let third = first.clone();
            let cloner = thread::spawn(move || {
                let copy = second.clone();
                assert_eq!(copy.get(), 1);
                drop((second, copy));
            });
            let dropper = thread::spawn(move || {
                assert_eq!(third.get(), 1);
                drop(third);
            });
            Shared::make_mut(&mut first).set(3);
            assert_eq!(first.get(), 3);
            cloner.join().expect("the cloning thread ends");
            dropper.join().expect("the dropping thread ends");
        });
    }
}
