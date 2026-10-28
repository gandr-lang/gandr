//! A staged program checked serially and on forks that schedule every job
//! differently, against one-arena normalization.

use alloc::format;
use alloc::string::String;
use alloc::vec;

use gandr_core_fork::Dependences;
use gandr_core_fork::Serial;
use gandr_kernel_term::stage::Extent;
use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::Type;

use super::*;
use crate::template::harvest;

/// A clock that never advances, so every report is free of time.
#[derive(Clone, Copy)]
struct Stopped;

impl Clock for Stopped
{
    /// Always the origin.
    ///
    /// # Specification
    /// trivial.
    fn now(&mut self) -> Duration
    {
        Duration::ZERO
    }
}

/// One job a test fork runs: the item's slice position and the item.
struct Ready<'items, Item>
{
    /// The item's position in the slice.
    position: usize,
    /// The item.
    item: &'items mut Item,
}

/// The jobs a test fork runs a schedule's items in: at each step the latest
/// item whose jobs it waits on have all run, so the order keeps every edge
/// and, with no edge, runs last to first.
///
/// # Specification
/// trivial.
fn latest_ready_first<'items, Item>(
    items: &'items mut [Item],
    after: &Dependences,
) -> Vec<Ready<'items, Item>>
{
    let count = items.len();
    let edges: Vec<(usize, usize)> = after
        .edges()
        .iter()
        .map(|edge| (edge.before, edge.after))
        .filter(|&(_, later)| later < count)
        .collect();
    let mut waiting = vec![0_usize; count];
    for &(_, later) in &edges {
        let count = waiting
            .get_mut(later)
            .expect("an edge ends inside the slice");
        *count = count.checked_add(1).unwrap();
    }
    let mut ready: Vec<usize> = (0 .. count)
        .filter(|&item| waiting.get(item) == Some(&0))
        .collect();
    let mut slots: Vec<Option<&mut Item>> = items.iter_mut().map(Some).collect();
    let mut order = Vec::with_capacity(count);
    while let Some(next) = ready.pop() {
        order.push(Ready {
            position: next,
            item: slots
                .get_mut(next)
                .and_then(Option::take)
                .expect("each position is ready once"),
        });
        for &(_, later) in edges.iter().filter(|&&(earlier, _)| earlier == next) {
            let count = waiting
                .get_mut(later)
                .expect("an edge ends inside the slice");
            *count = count.checked_sub(1).unwrap();
            if *count == 0 {
                ready.push(later);
                ready.sort_unstable();
            }
        }
    }
    order
}

/// A fork that runs items last to first, each from a fresh state, and the
/// right half before the left: every worker a stranger to the others.
struct Scrambled;

impl Fork for Scrambled
{
    /// Every item from a fresh state, last first.
    ///
    /// # Specification
    /// trivial.
    fn each<Item, State, Start, Job>(
        &self,
        items: &mut [Item],
        start: Start,
        job: Job,
    ) where
        Item: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
    {
        for item in items.iter_mut().rev() {
            job(&mut start(), item);
        }
    }

    /// The right half, then the left.
    ///
    /// # Specification
    /// trivial.
    fn join<Left, Right, LeftOutput, RightOutput>(
        &self,
        left: Left,
        right: Right,
    ) -> (LeftOutput, RightOutput)
    where
        Left: FnOnce() -> LeftOutput + Send,
        Right: FnOnce() -> RightOutput + Send,
        LeftOutput: Send,
        RightOutput: Send,
    {
        let right = right();
        (left(), right)
    }

    /// Every job from a fresh state, latest ready first, then every fold.
    ///
    /// # Specification
    /// trivial.
    fn schedule<Item, State, Start, Job, Fold>(
        &self,
        items: &mut [Item],
        after: &Dependences,
        start: Start,
        job: Job,
        mut fold: Fold,
    ) where
        Item: Send,
        State: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
        Fold: FnMut(&mut Item),
    {
        for Ready { item, .. } in latest_ready_first(items, after) {
            job(&mut start(), item);
        }
        items.iter_mut().for_each(&mut fold);
    }
}

/// A fork of two workers: the second half of the items on one state, then
/// the first half on another, so a worker's state carries over between the
/// items it runs.
struct Halves;

impl Fork for Halves
{
    /// The second half from one state, then the first half from another.
    ///
    /// # Specification
    /// trivial.
    fn each<Item, State, Start, Job>(
        &self,
        items: &mut [Item],
        start: Start,
        job: Job,
    ) where
        Item: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
    {
        let middle = items.len().checked_div(2).unwrap();
        let (first, second) = items.split_at_mut(middle);
        for half in [second, first] {
            let mut state = start();
            for item in half {
                job(&mut state, item);
            }
        }
    }

    /// The left half, then the right.
    ///
    /// # Specification
    /// trivial.
    fn join<Left, Right, LeftOutput, RightOutput>(
        &self,
        left: Left,
        right: Right,
    ) -> (LeftOutput, RightOutput)
    where
        Left: FnOnce() -> LeftOutput + Send,
        Right: FnOnce() -> RightOutput + Send,
        LeftOutput: Send,
        RightOutput: Send,
    {
        (left(), right())
    }

    /// Every job latest ready first, the second half's from one state and the
    /// first half's from another, then every fold.
    ///
    /// # Specification
    /// trivial.
    fn schedule<Item, State, Start, Job, Fold>(
        &self,
        items: &mut [Item],
        after: &Dependences,
        start: Start,
        job: Job,
        mut fold: Fold,
    ) where
        Item: Send,
        State: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
        Fold: FnMut(&mut Item),
    {
        let middle = items.len().checked_div(2).unwrap();
        let (mut first, mut second) = (None, None);
        for Ready { position, item } in latest_ready_first(items, after) {
            let state = if position < middle {
                &mut first
            }
            else {
                &mut second
            };
            job(state.get_or_insert_with(&start), item);
        }
        items.iter_mut().for_each(&mut fold);
    }
}

/// A fork of one worker that meets the items last to first, so every item
/// comes below the one before it on the same state.
struct Backwards;

impl Fork for Backwards
{
    /// Every item from one state, last first.
    ///
    /// # Specification
    /// trivial.
    fn each<Item, State, Start, Job>(
        &self,
        items: &mut [Item],
        start: Start,
        job: Job,
    ) where
        Item: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
    {
        let mut state = start();
        for item in items.iter_mut().rev() {
            job(&mut state, item);
        }
    }

    /// The left half, then the right.
    ///
    /// # Specification
    /// trivial.
    fn join<Left, Right, LeftOutput, RightOutput>(
        &self,
        left: Left,
        right: Right,
    ) -> (LeftOutput, RightOutput)
    where
        Left: FnOnce() -> LeftOutput + Send,
        Right: FnOnce() -> RightOutput + Send,
        LeftOutput: Send,
        RightOutput: Send,
    {
        (left(), right())
    }

    /// Every job from one state, latest ready first, then every fold.
    ///
    /// # Specification
    /// trivial.
    fn schedule<Item, State, Start, Job, Fold>(
        &self,
        items: &mut [Item],
        after: &Dependences,
        start: Start,
        job: Job,
        mut fold: Fold,
    ) where
        Item: Send,
        State: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
        Fold: FnMut(&mut Item),
    {
        let mut state = None;
        for Ready { item, .. } in latest_ready_first(items, after) {
            job(state.get_or_insert_with(&start), item);
        }
        items.iter_mut().for_each(&mut fold);
    }
}

/// A staging observer program.
#[derive(Clone, Copy)]
enum Body
{
    /// `pow`, its input left free under a quoted lambda.
    Power,
    /// `double`, over the inner inputs two and three.
    Double,
}

/// The program of `body` at the exponents `low ..= high`.
///
/// # Specification
/// - ensures: one source per exponent for the power, two per exponent for the
///   double, exponents outermost, all in the program's arena.
/// - panics: fixture allocation failure.
/// - executable: none — a fixture builder; the witness checks every source it
///   builds through the program check.
///
/// # Adequacy
/// - hypothesis: L2 — every source normalizes and readmits, independently of
///   how the program was built.
/// - witness: `staging::tests::every_width_checks_the_serial_program`
fn program(
    body: Body,
    low: Natural,
    high: Natural,
) -> Program
{
    let mut arena = Arena::default();
    let model = Model(0);
    let context = Vec::from([arena.alloc_type(Type::In(model)).unwrap()]);
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(model))).unwrap();
    let function = match body {
        Body::Power => gandr_core_nbe::stage::power(&mut arena, model).unwrap(),
        Body::Double => gandr_core_nbe::stage::double(&mut arena, model).unwrap(),
    };
    let mut sources = Vec::new();
    for exponent in low.0 ..= high.0 {
        let numeral = arena
            .alloc(Term::Natural(Stage::Outer, Natural(exponent)))
            .unwrap();
        let applied = arena.alloc(Term::Apply(function, numeral)).unwrap();
        match body {
            Body::Power => {
                let input = arena.alloc(Term::Variable(Index(0))).unwrap();
                let input = arena.alloc(Term::Quote(input)).unwrap();
                let source = arena.alloc(Term::Apply(applied, input)).unwrap();
                let source = arena.alloc(Term::Splice(source)).unwrap();
                let source = arena.alloc(Term::Lambda(inner, source)).unwrap();
                sources.push(arena.alloc(Term::Quote(source)).unwrap());
            },
            Body::Double => {
                for input in [Natural(2), Natural(3)] {
                    let input = arena
                        .alloc(Term::Natural(Stage::Inner(model), input))
                        .unwrap();
                    let input = arena.alloc(Term::Quote(input)).unwrap();
                    sources.push(arena.alloc(Term::Apply(applied, input)).unwrap());
                }
            },
        }
    }
    Program {
        arena,
        context,
        sources,
        id: ProgramId(0),
    }
}

/// Allowances no fixture exhausts.
const AMPLE: Allowance = Allowance {
    normalizing: Budget(10_000_000),
    replaying: Budget(10_000_000),
    admitting: Budget(100_000_000),
};

/// A program checked on `fork` through `memo`, as debug text.
///
/// # Specification
/// trivial.
fn checked<F>(
    program: Program,
    memo: &mut Memo,
    allowance: Allowance,
    fork: &F,
) -> String
where
    F: Fork,
{
    format!(
        "{:?}",
        check(
            program,
            memo,
            PriceGate::Memoized,
            allowance,
            fork,
            &Stopped
        )
    )
}

/// A program checked on `fork` through a fresh memo with ample allowances.
///
/// # Specification
/// trivial.
fn fresh<F>(
    program: Program,
    fork: &F,
) -> Checked
where
    F: Fork,
{
    check(
        program,
        &mut Memo::default(),
        PriceGate::Memoized,
        AMPLE,
        fork,
        &Stopped,
    )
    .unwrap()
}

#[test]
fn every_width_checks_the_serial_program()
{
    let trace = [
        (Body::Power, Natural(0), Natural(8)),
        (Body::Double, Natural(0), Natural(8)),
        (Body::Power, Natural(0), Natural(8)),
        (Body::Double, Natural(2), Natural(12)),
    ];
    let mut serial = Memo::default();
    let mut scrambled = Memo::default();
    let mut halves = Memo::default();
    let mut backwards = Memo::default();
    for (body, low, high) in trace {
        let reference = check(
            program(body, low, high),
            &mut serial,
            PriceGate::Memoized,
            AMPLE,
            &Serial,
            &Stopped,
        )
        .unwrap();
        assert!(
            reference
                .readmissions
                .iter()
                .all(|readmission| *readmission == Readmission::Readmitted)
        );
        assert!(reference.admissions.iter().any(|admission| matches!(
            admission,
            Ok(FamilyReport {
                admission: crate::template::FamilyAdmission::Admitted { .. },
                ..
            })
        )));
        let reference = format!("{:?}", Ok::<_, ProgramError>(reference));
        assert_eq!(
            checked(program(body, low, high), &mut scrambled, AMPLE, &Scrambled),
            reference
        );
        assert_eq!(
            checked(program(body, low, high), &mut halves, AMPLE, &Halves),
            reference
        );
        assert_eq!(
            checked(program(body, low, high), &mut backwards, AMPLE, &Backwards),
            reference
        );
    }
}

#[test]
fn the_merged_arena_is_one_arena_normalization()
{
    let whole = Extent {
        terms: TermId(0),
        types: TypeId(0),
    };
    for (body, low, high) in [
        (Body::Power, Natural(0), Natural(8)),
        (Body::Double, Natural(0), Natural(8)),
    ] {
        let one = program(body, low, high);
        let mut arena = one.arena.clone();
        let certificates: Vec<Certificate> = one
            .sources
            .iter()
            .map(|source| {
                gandr_core_nbe::stage::normalize(&mut arena, *source, &mut Budget(10_000_000))
                    .unwrap()
            })
            .collect();
        let families = harvest(&arena, one.id, &certificates).unwrap();
        for forked in [
            fresh(program(body, low, high), &Serial),
            fresh(program(body, low, high), &Scrambled),
            fresh(program(body, low, high), &Halves),
            fresh(program(body, low, high), &Backwards),
        ] {
            assert_eq!(forked.arena.terms_above(whole), arena.terms_above(whole));
            assert_eq!(forked.arena.types_above(whole), arena.types_above(whole));
            assert_eq!(forked.certificates, certificates);
            assert_eq!(format!("{:?}", forked.families), format!("{families:?}"));
        }
    }
}

#[test]
fn exhausted_allowances_refuse_alike_at_every_width()
{
    let starved = Allowance {
        normalizing: Budget(1),
        ..AMPLE
    };
    let mut absent = program(Body::Double, Natural(0), Natural(3));
    let missing = TermId(usize::MAX);
    absent.sources.insert(3, missing);
    let unreplayed = Allowance {
        replaying: Budget(0),
        ..AMPLE
    };
    let unadmitted = Allowance {
        admitting: Budget(0),
        ..AMPLE
    };
    let width = |program: Program, allowance: Allowance| {
        let serial = checked(program.clone(), &mut Memo::default(), allowance, &Serial);
        assert_eq!(
            checked(program.clone(), &mut Memo::default(), allowance, &Scrambled),
            serial
        );
        assert_eq!(
            checked(program.clone(), &mut Memo::default(), allowance, &Halves),
            serial
        );
        assert_eq!(
            checked(program, &mut Memo::default(), allowance, &Backwards),
            serial
        );
        serial
    };
    assert_eq!(
        width(program(Body::Power, Natural(0), Natural(4)), starved),
        format!(
            "{:?}",
            Err::<Checked, _>(ProgramError::Normalized {
                source: SourceIndex(0),
                error: StageError::Exhausted,
            })
        )
    );
    assert_eq!(
        width(absent, AMPLE),
        format!(
            "{:?}",
            Err::<Checked, _>(ProgramError::Normalized {
                source: SourceIndex(3),
                error: StageError::UnknownTerm(missing),
            })
        )
    );
    width(program(Body::Double, Natural(0), Natural(4)), unreplayed);
    let replayed = check(
        program(Body::Double, Natural(0), Natural(4)),
        &mut Memo::default(),
        PriceGate::Memoized,
        unreplayed,
        &Scrambled,
        &Stopped,
    )
    .unwrap();
    assert!(
        replayed
            .readmissions
            .iter()
            .all(|readmission| *readmission == Readmission::Refused(StageError::Exhausted))
    );
    width(program(Body::Double, Natural(0), Natural(4)), unadmitted);
    let admitted = check(
        program(Body::Double, Natural(0), Natural(4)),
        &mut Memo::default(),
        PriceGate::Memoized,
        unadmitted,
        &Halves,
        &Stopped,
    )
    .unwrap();
    assert!(
        admitted
            .admissions
            .iter()
            .any(|admission| matches!(admission, Err(StageError::Exhausted)))
    );
}
