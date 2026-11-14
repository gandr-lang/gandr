//! The region: its values under a budget, and each of its three crossings.

use alloc::alloc::Global;
use core::convert::Infallible;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;

use gandr_kernel_data::Budget;
use gandr_kernel_data::Child;
use gandr_kernel_data::Id;
use gandr_kernel_data::Key;
use gandr_kernel_data::Rebase;
use gandr_kernel_data::Region;
use gandr_kernel_data::Shift;
use gandr_kernel_data::Width;
use gandr_kernel_data::scoped;
use gandr_kernel_data::scoped_in;

/// The bytes of one first bucket of `u64` values with their cells, and a
/// little more: room for one bucket and not for the second.
const ONE_BUCKET: usize = 1_536;

/// A budget that holds every value a test mints: one mebibyte.
const LARGE: usize = 0x10_0000;

/// A value of a forked region: a word, or the key of another value of the
/// region.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Value
{
    /// A word.
    Word(u64),
    /// The key of another value.
    Names(Key),
}

impl Rebase for Value
{
    /// The value with the key it names read through `shift`.
    ///
    /// # Specification
    /// trivial.
    fn rebase(
        self,
        shift: Shift,
    ) -> Self
    {
        match self {
            Self::Word(_) => self,
            Self::Names(key) => Self::Names(shift.key(key)),
        }
    }
}

/// Values minted across two buckets read back at their ids, and the value
/// past a budget that holds one bucket is refused.
#[test]
fn a_region_reads_each_value_at_its_id_and_refuses_past_its_budget()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let ids: Vec<Id<'_>> = (0_u64 .. 100_u64)
            .map(|value| region.mint(&mut mint, value))
            .collect::<Result<_, _>>()
            .expect("the budget holds two buckets");
        ids.iter()
            .map(|&id| region.get(id).copied())
            .collect::<Option<Vec<u64>>>()
    });
    assert_eq!(
        read,
        Some((0_u64 .. 100_u64).collect()),
        "each id reads the value minted at it"
    );
    let refused = scoped(Budget::from(ONE_BUCKET), |region, mut mint| {
        (0_u64 .. 64_u64).try_for_each(|value| region.mint::<()>(&mut mint, value).map(drop))?;
        region.mint::<()>(&mut mint, 64_u64).map(drop)
    });
    assert!(
        refused.is_err(),
        "the 65th value needs a second bucket past the budget"
    );
}

/// A child reads a value of its parent through `adopt`, and its own first id
/// stands apart from it.
#[test]
fn a_child_reads_a_value_of_its_parent_through_adopt()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let parent: Id<'_> = region
            .mint(&mut mint, Value::Word(7))
            .expect("the budget holds it");
        region
            .forks::<(), (), _, _>(
                &mut mint,
                Width::ONE,
                &|_sibling, child, mut own, adopt| {
                    let adopted = adopt.adopt(parent);
                    let first = child.mint(&mut own, Value::Word(9)).ok().ok_or(())?;
                    (adopted != first
                        && child.get(adopted) == Some(&Value::Word(7))
                        && child.get(first) == Some(&Value::Word(9)))
                    .then_some(())
                    .ok_or(())
                },
                |children| children.iter_mut().for_each(Child::enter),
            )
            .expect("the join holds no suffix past the budget")
            .into_first()
    });
    assert_eq!(
        read,
        Ok(()),
        "the child reads the parent's value and its own"
    );
}

/// A child that keeps its answer folds its values into the parent at the
/// offsets it minted them at; the parent reads them at the ids the join
/// gives, and its next id follows them.
#[test]
fn a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let before: Id<'_> = region
            .mint(&mut mint, Value::Word(1))
            .expect("the budget holds it");
        let joined = region
            .forks::<Id<'static>, (), _, _>(
                &mut mint,
                Width::ONE,
                &|_sibling, child, mut own, _adopt| {
                    let _second = child.mint::<()>(&mut own, Value::Word(2)).ok().ok_or(())?;
                    child.mint(&mut own, Value::Word(3)).ok().ok_or(())
                },
                |children| children.iter_mut().for_each(Child::enter),
            )
            .expect("the budget holds the suffix")
            .into_first()
            .expect("the child keeps its answer");
        let after: Id<'_> = region
            .mint(&mut mint, Value::Word(4))
            .expect("the budget holds it");
        (
            u32::from(before.key()),
            u32::from(joined.key()),
            region.get(joined).copied(),
            u32::from(after.key()),
        )
    });
    assert_eq!(
        read,
        (0_u32, 2_u32, Some(Value::Word(3)), 3_u32),
        "the suffix lands at offsets 1 and 2, and the parent goes on at 3"
    );
}

/// A child that drops its suffix drops it whole: the parent's next id stands
/// at the mark, and no value of the child reads in the parent.
#[test]
fn a_fork_that_disagrees_drops_its_suffix_whole()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let _before = region
            .mint::<()>(&mut mint, Value::Word(1))
            .expect("the budget holds it");
        let joined = region
            .forks::<(), (), _, _>(
                &mut mint,
                Width::ONE,
                &|_sibling, child, mut own, _adopt| {
                    let _dropped = child.mint::<()>(&mut own, Value::Word(2)).ok().ok_or(())?;
                    Err(())
                },
                |children| children.iter_mut().for_each(Child::enter),
            )
            .expect("a dropped suffix draws nothing")
            .into_first();
        let after: Id<'_> = region
            .mint(&mut mint, Value::Word(5))
            .expect("the budget holds it");
        (joined, u32::from(after.key()), region.get(after).copied())
    });
    assert_eq!(
        read,
        (Err(()), 1_u32, Some(Value::Word(5))),
        "the parent's next value takes the mark, offset 1"
    );
}

/// A speculation keeps nothing: its child mints, reads its own values and a
/// value of the parent, and hands back the verdict that it reads as the
/// reason of its drop. The parent's next id stands at the mark.
#[test]
fn a_speculation_hands_back_its_verdict_and_drops_its_suffix()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let parent: Id<'_> = region
            .mint(&mut mint, Value::Word(5))
            .expect("the budget holds it");
        let Err(verdict) = region
            .forks::<Infallible, Option<u64>, _, _>(
                &mut mint,
                Width::ONE,
                &|_sibling, child, mut own, adopt| {
                    let Some(Value::Word(base)) = child.get(adopt.adopt(parent)).copied()
                    else {
                        return Err(None);
                    };
                    let ids = [1_u64, 2_u64, 3_u64]
                        .map(|word| child.mint::<()>(&mut own, Value::Word(word)).ok());
                    let sum = ids.iter().try_fold(base, |sum, id| {
                        let Some(Value::Word(word)) = id.and_then(|id| child.get(id)).copied()
                        else {
                            return None;
                        };
                        sum.checked_add(word)
                    });
                    Err(sum)
                },
                |children| children.iter_mut().for_each(Child::enter),
            )
            .expect("a dropped suffix draws nothing")
            .into_first();
        let after: Id<'_> = region
            .mint(&mut mint, Value::Word(9))
            .expect("the budget holds it");
        (verdict, u32::from(after.key()))
    });
    assert_eq!(
        read,
        (Some(11_u64), 1_u32),
        "the verdict sums the parent's word and the child's three, and the parent goes on at \
         the mark"
    );
}

/// A run that enters one child of three leaves two, and the glue runs each of
/// them once on the calling thread.
#[test]
fn a_child_that_the_run_leaves_runs_once_on_the_calling_thread()
{
    let width = Width::from(NonZeroUsize::new(3).expect("three is not zero"));
    let runs = AtomicUsize::new(0);
    let caller = std::thread::current().id();
    let read = scoped(
        Budget::from(LARGE),
        |region: &Region<'_, Value, Global>, mut mint| {
            region
                .forks::<Infallible, (usize, bool), _, _>(
                    &mut mint,
                    width,
                    &|sibling, _child, _own, _adopt| {
                        let _before = runs.fetch_add(1, Ordering::Relaxed);
                        Err((usize::from(sibling), std::thread::current().id() == caller))
                    },
                    |children| {
                        std::thread::scope(|threads| {
                            if let Some(child) = children.iter_mut().nth(1) {
                                let _running = threads.spawn(|| child.enter());
                            }
                        });
                    },
                )
                .expect("a dropped suffix draws nothing")
                .into_iter()
                .map(|answer| match answer {
                    Err(dropped) => dropped,
                })
                .collect::<Vec<_>>()
        },
    );
    assert_eq!(
        (read, runs.load(Ordering::Relaxed)),
        (
            vec![(0_usize, true), (1_usize, false), (2_usize, true)],
            3_usize
        ),
        "the run's child runs on its thread, and each child it leaves runs once on the caller"
    );
}

/// Four children on four threads read one frozen value at one address, and
/// the two that keep their answers glue in the order of the siblings. The
/// second keeping child's values move past the first one's suffix, the key
/// that one of them names moves with them, and the id that the child answers
/// reads its value there. Each child that drops hands back its place.
#[test]
fn siblings_over_one_frozen_prefix_glue_their_suffixes_in_order()
{
    let width = Width::from(NonZeroUsize::new(4).expect("four is not zero"));
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let frozen: Id<'_> = region
            .mint(&mut mint, Value::Word(7))
            .expect("the budget holds it");
        let address = region
            .get(frozen)
            .map(|value| core::ptr::from_ref(value).addr());
        let answers = region
            .forks::<Id<'static>, Option<u64>, _, _>(
                &mut mint,
                width,
                &|sibling, child, mut own, adopt| {
                    let index = u64::try_from(usize::from(sibling)).ok().ok_or(None)?;
                    // Each child reads the frozen value where the parent
                    // holds it, with no copy.
                    let seen = child
                        .get(adopt.adopt(frozen))
                        .map(|value| core::ptr::from_ref(value).addr());
                    (seen == address).then_some(()).ok_or(None)?;
                    let word: Id<'_> = child.mint(&mut own, Value::Word(index)).ok().ok_or(None)?;
                    let names: Id<'_> = child
                        .mint(&mut own, Value::Names(word.key()))
                        .ok()
                        .ok_or(None)?;
                    // The children at 1 and 3 keep, and those at 0 and 2
                    // drop with their places.
                    if index & 1_u64 == 1_u64 {
                        Ok(names)
                    }
                    else {
                        Err(Some(index))
                    }
                },
                |children| {
                    std::thread::scope(|threads| {
                        for child in children.iter_mut() {
                            let _running = threads.spawn(|| child.enter());
                        }
                    });
                },
            )
            .expect("the budget holds both suffixes");
        let after: Id<'_> = region
            .mint(&mut mint, Value::Word(9))
            .expect("the budget holds it");
        let glued = answers
            .into_iter()
            .map(|answer| answer.map(|names| (u32::from(names.key()), region.get(names).copied())))
            .collect::<Vec<_>>();
        let moved = region
            .seat::<()>(Key::from(3_u32))
            .and_then(|id| region.get(id))
            .copied();
        (glued, moved, u32::from(after.key()))
    });
    assert_eq!(
        read,
        (
            vec![
                Err(Some(0_u64)),
                Ok((2_u32, Some(Value::Names(Key::from(1_u32))))),
                Err(Some(2_u64)),
                Ok((4_u32, Some(Value::Names(Key::from(3_u32))))),
            ],
            Some(Value::Word(3)),
            5_u32,
        ),
        "the first kept suffix stays at 1 and 2, the second moves to 3 and 4 with its key, and \
         the parent goes on at 5"
    );
}

/// A key of each of two values seats back as its own id, and a key past the
/// region is refused.
#[test]
fn a_key_seats_back_in_its_region_and_a_key_past_it_is_refused()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let first: Id<'_> = region.mint(&mut mint, 10_u64).expect("the budget holds it");
        let second: Id<'_> = region.mint(&mut mint, 20_u64).expect("the budget holds it");
        (
            region.seat(first.key()) == Some(first),
            region.seat(second.key()) == Some(second),
            region.seat::<()>(Key::from(2_u32)).is_none(),
        )
    });
    assert_eq!(
        read,
        (true, true, true),
        "each key seats back, and the key past the region is refused"
    );
}

/// A vector in a region grows across its chunks and keeps each element, and
/// a reserve past the region's budget is refused.
#[test]
fn a_vector_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget()
{
    let (sum, refused) = scoped::<u64, _, _>(Budget::from(LARGE), |region, _mint| {
        let mut values = Vec::new_in(region);
        values.extend(0_u64 .. 2_000_u64);
        let sum: u64 = values.iter().sum();
        let mut past = Vec::<u64, _>::new_in(region);
        (sum, past.try_reserve(LARGE).is_err())
    });
    assert_eq!(
        sum, 1_999_000_u64,
        "a vector across chunks keeps each element"
    );
    assert!(refused, "a reserve past the budget is refused");
}

/// A region over a region draws its buckets from the region below: it reads
/// its value when the budget below holds the bucket, and is refused when it
/// does not.
#[test]
fn a_region_over_a_region_draws_its_buckets_from_the_region_below()
{
    let read = scoped::<u64, _, _>(Budget::from(LARGE), |outer, _outer_mint| {
        scoped_in::<u64, _, _, _>(Budget::from(LARGE), outer, |inner, mut mint| {
            let id: Id<'_> = inner.mint(&mut mint, 7_u64).ok()?;
            inner.get(id).copied()
        })
    });
    assert_eq!(read, Some(7_u64), "the region below holds the bucket");
    let refused = scoped::<u64, _, _>(Budget::from(ONE_BUCKET), |outer, _outer_mint| {
        scoped_in::<u64, _, _, _>(Budget::from(LARGE), outer, |inner, mut mint| {
            inner.mint::<()>(&mut mint, 7_u64).is_err()
        })
    });
    assert!(refused, "the budget below refuses the bucket's chunk");
}
