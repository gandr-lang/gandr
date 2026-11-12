use alloc::vec::Vec;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;

use super::*;

/// An item: its slice position and the order of each visit it received.
#[derive(Debug)]
struct Visited
{
    /// The item's position in the slice.
    position: usize,
    /// The running count at each visit.
    visits: Vec<usize>,
}

#[test]
fn serial_runs_each_item_in_order_from_one_state()
{
    for count in [0_usize, 1, 5] {
        let made = AtomicUsize::new(0);
        let mut items: Vec<Visited> = (0 .. count)
            .map(|position| Visited {
                position,
                visits: Vec::new(),
            })
            .collect();
        Serial.each(
            &mut items,
            || {
                made.fetch_add(1, Ordering::Relaxed);
                0_usize
            },
            |seen, item| {
                item.visits.push(*seen);
                *seen = seen.checked_add(1).unwrap();
            },
        );
        assert_eq!(
            made.load(Ordering::Relaxed),
            usize::from(count > 0),
            "states made for {count} items"
        );
        for item in &items {
            assert_eq!(item.visits, [item.position], "one visit, in slice order");
        }
    }
}

#[test]
fn serial_runs_the_left_half_before_the_right()
{
    let order = AtomicUsize::new(0);
    let (left, right) = Serial.join(
        || ('l', order.fetch_add(1, Ordering::Relaxed)),
        || ('r', order.fetch_add(1, Ordering::Relaxed)),
    );
    assert_eq!(
        (left, right),
        (('l', 0), ('r', 1)),
        "the left half runs first, and the pair is in argument order"
    );
}

/// How many runs a counted job found before its own.
#[derive(Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Runs(usize);

/// A job that counts its runs, and answers the count it found.
#[repr(transparent)]
struct Counted<'count>(&'count AtomicUsize);

impl<'scope, 'count: 'scope> Scoped<'scope> for Counted<'count>
{
    type Output = Runs;

    /// Count this run.
    ///
    /// # Specification
    /// trivial.
    fn run<Spawner>(
        self,
        _spawner: &Spawner,
    ) -> Runs
    where
        Spawner: Spawn<'scope>,
    {
        Runs(self.0.fetch_add(1, Ordering::Relaxed))
    }
}

/// The sum of a spawn tree's leaves.
#[derive(Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Sum(u64);

/// A leaf of a spawn tree: its own value.
#[repr(transparent)]
struct Leaf(u64);

impl<'scope> Scoped<'scope> for Leaf
{
    type Output = Sum;

    /// The leaf's value.
    ///
    /// # Specification
    /// trivial.
    fn run<Spawner>(
        self,
        _spawner: &Spawner,
    ) -> Sum
    where
        Spawner: Spawn<'scope>,
    {
        Sum(self.0)
    }
}

/// A node of a spawn tree: two subtrees, each spawned before either is waited
/// for.
struct Pair<Tree>(Tree, Tree);

impl<'scope, Tree> Scoped<'scope> for Pair<Tree>
where
    Tree: Scoped<'scope, Output = Sum> + Send + 'scope,
{
    type Output = Sum;

    /// Spawn both subtrees, wait for the right one and then the left one, and
    /// add their sums.
    ///
    /// # Specification
    /// trivial.
    fn run<Spawner>(
        self,
        spawner: &Spawner,
    ) -> Sum
    where
        Spawner: Spawn<'scope>,
    {
        let Self(left, right) = self;
        let left = spawner.spawn(left);
        let Sum(right) = spawner.wait(spawner.spawn(right)).unwrap();
        let Sum(left) = spawner.wait(left).unwrap();
        Sum(left.checked_add(right).unwrap())
    }
}

#[test]
fn serial_runs_a_spawned_job_at_its_wait()
{
    let count = AtomicUsize::new(0);
    let spawned = Serial.spawn(Counted(&count));
    assert_eq!(count.load(Ordering::Relaxed), 0, "a spawn starts nothing");
    assert_eq!(Serial.wait(spawned), Ok(Runs(0)), "the wait runs the job");
    assert_eq!(count.load(Ordering::Relaxed), 1, "the job ran once");
    {
        let _unwaited = Serial.spawn(Counted(&count));
    }
    assert_eq!(
        count.load(Ordering::Relaxed),
        1,
        "a job whose handle was dropped never runs"
    );
}

#[test]
fn a_nested_serial_spawn_sums_the_leaves()
{
    let tree = Pair(
        Pair(Pair(Leaf(1), Leaf(2)), Pair(Leaf(3), Leaf(4))),
        Pair(Pair(Leaf(5), Leaf(6)), Pair(Leaf(7), Leaf(8))),
    );
    assert_eq!(
        Serial.scope(tree),
        Sum(36),
        "the serial scope sums the leaves"
    );
}

/// An item of a schedule: the running count when its job ran and when it was
/// folded.
#[derive(Debug, Default)]
struct Stamped
{
    /// The count at each run of the item's job.
    jobs: Vec<usize>,
    /// The count at each fold of the item.
    folds: Vec<usize>,
}

#[test]
fn serial_runs_each_job_then_its_fold_in_order()
{
    for count in [0_usize, 1, 5] {
        let made = AtomicUsize::new(0);
        let clock = AtomicUsize::new(0);
        let tick = || clock.fetch_add(1, Ordering::Relaxed);
        let mut items: Vec<Stamped> = core::iter::repeat_with(Stamped::default)
            .take(count)
            .collect();
        let chain = Dependences::new((1 .. count).map(|after| Dependence {
            before: after.checked_sub(1).unwrap(),
            after,
        }))
        .unwrap();
        Serial.schedule(
            &mut items,
            &chain,
            || {
                made.fetch_add(1, Ordering::Relaxed);
            },
            |_state, item| item.jobs.push(tick()),
            |item| item.folds.push(tick()),
        );
        assert_eq!(
            made.load(Ordering::Relaxed),
            usize::from(count > 0),
            "states made for {count} items"
        );
        for (position, item) in items.iter().enumerate() {
            let job = position.checked_mul(2).unwrap();
            assert_eq!(item.jobs, [job], "item {position}'s job, once, in order");
            assert_eq!(
                item.folds,
                [job.checked_add(1).unwrap()],
                "item {position}'s fold, once, right after its job"
            );
        }
    }
}

#[test]
fn dependences_keep_forward_edges_once_in_order()
{
    let edges = |pairs: &[(usize, usize)]| -> Vec<Dependence> {
        pairs
            .iter()
            .map(|&(before, after)| Dependence { before, after })
            .collect()
    };
    let kept = Dependences::new(edges(&[(2, 5), (0, 1), (2, 5), (0, 3)])).unwrap();
    assert_eq!(kept.edges(), edges(&[(0, 1), (0, 3), (2, 5)]));
    assert_eq!(Dependences::new([]).unwrap(), Dependences::default());
    assert_eq!(
        Dependences::new(edges(&[(0, 1), (3, 3)])),
        Err(Backward {
            edge: Dependence {
                before: 3,
                after: 3
            }
        }),
        "an item cannot wait on itself"
    );
    assert_eq!(
        Dependences::new(edges(&[(4, 2)])),
        Err(Backward {
            edge: Dependence {
                before: 4,
                after: 2
            }
        }),
        "an item cannot wait on a later one"
    );
}

/// The dependences of `pairs`, each `(before, after)`.
fn dependences(pairs: &[(usize, usize)]) -> Dependences
{
    Dependences::new(
        pairs
            .iter()
            .map(|&(before, after)| Dependence { before, after }),
    )
    .unwrap()
}

/// Each cost in microseconds.
fn costs(micros: &[u64]) -> Vec<Duration>
{
    micros.iter().copied().map(Duration::from_micros).collect()
}

/// The slice positions of the chain of `bound`.
fn chain_of(bound: &Bound) -> Vec<usize>
{
    bound.chain().iter().copied().map(usize::from).collect()
}

#[test]
fn the_bound_of_jobs_with_no_edge_is_the_costliest_job()
{
    let bound = Dependences::default().bound(&costs(&[3, 1, 4, 1]));
    assert_eq!(
        bound.serial(),
        Duration::from_micros(9),
        "the serial cost sums every job"
    );
    assert_eq!(
        bound.critical(),
        Duration::from_micros(4),
        "no job waits, so the costliest one is the critical path"
    );
    assert_eq!(
        bound.folded(),
        Duration::from_micros(4),
        "every job starts at once, and the last fold waits for the costliest"
    );
    assert_eq!(
        chain_of(&bound),
        [2],
        "the chain is the costliest job alone"
    );
    assert_eq!(
        Dependences::default().bound(&[]),
        Bound::default(),
        "no job has no cost and no chain"
    );
}

#[test]
fn the_bound_of_a_chain_is_its_whole_cost()
{
    let chain = dependences(&[(0, 1), (1, 2), (2, 3)]);
    let bound = chain.bound(&costs(&[1, 2, 3, 4]));
    assert_eq!(bound.serial(), Duration::from_micros(10));
    assert_eq!(
        bound.critical(),
        Duration::from_micros(10),
        "each job waits on the one before, so the chain costs the whole"
    );
    assert_eq!(bound.folded(), Duration::from_micros(10));
    assert_eq!(chain_of(&bound), [0, 1, 2, 3], "the chain in slice order");
    let past = dependences(&[(0, 1), (1, 7), (5, 6)]).bound(&costs(&[2, 2]));
    assert_eq!(
        (past.critical(), chain_of(&past)),
        (Duration::from_micros(4), alloc::vec![0_usize, 1]),
        "an edge past the costs is ignored"
    );
}

#[test]
fn a_fold_in_slice_order_waits_behind_a_costly_item()
{
    // The costly item 0 waits on nothing. Item 2 waits on the cheap item 1,
    // whose fold comes after the fold of item 0.
    let bound = dependences(&[(1, 2)]).bound(&costs(&[5, 1, 1]));
    assert_eq!(bound.serial(), Duration::from_micros(7));
    assert_eq!(
        bound.critical(),
        Duration::from_micros(5),
        "item 2 can start once item 1 returns, at 1"
    );
    assert_eq!(chain_of(&bound), [0]);
    assert_eq!(
        bound.folded(),
        Duration::from_micros(6),
        "item 2 starts at the fold of item 1, which waits for the fold of item 0 at 5"
    );
}
