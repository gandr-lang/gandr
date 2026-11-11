use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_fork::activity::Activity;
use gandr_core_fork::activity::Core;
use gandr_core_fork::activity::Cores;
use gandr_core_fork::activity::Declared;
use gandr_core_fork::activity::Edge;
use gandr_core_fork::activity::Event;
use gandr_core_fork::activity::Fold;
use gandr_core_fork::activity::Mark;
use gandr_core_fork::activity::Nanos;
use gandr_core_fork::activity::Sequence;
use gandr_core_fork::activity::Slots;
use gandr_core_fork::activity::Task;
use gandr_core_fork::activity::World;
use serde_json::Value;
use serde_json::json;

use super::Ledger;
use super::PENDING;
use super::Run;
use super::rows;

/// The marks that the witness writes: four past the bound of a row.
const MARKED: usize = PENDING.saturating_add(4);

/// The events of [`MARKED`] marks on the one ring of `activity`, numbered
/// from zero: a start and an end of one task, again and again.
///
/// # Specification
/// trivial.
fn events(activity: &Activity) -> Vec<Event>
{
    let mut fold = Fold::new(activity);
    let worker = activity.worker(Core::from(0_u16)).expect("a ring");
    let mut events = Vec::with_capacity(MARKED);
    for at in 0 .. MARKED {
        let clock = Nanos::from(u64::try_from(events.len()).expect("a count fits"));
        worker.record(Mark {
            task: Task::Fork,
            edge: if at % 2 == 0 { Edge::Start } else { Edge::End },
            declaration: Declared::NONE,
            world: World::from(0_u32),
            clock,
        });
        events.extend_from_slice(fold.tick(activity, clock).events);
    }
    events
}

/// The sequence number of the last event of the state that `owed` holds, and
/// what the state carries: the sequence numbers of its events and its count
/// of drops.
///
/// # Specification
/// trivial.
fn state(owed: Option<(Sequence, String)>) -> (Sequence, Value)
{
    let (last, text) = owed.expect("the row owes a state");
    let state: Value = serde_json::from_str(&text).expect("a state is JSON");
    let sequences: Vec<Value> = state["events"]
        .as_array()
        .expect("a state lists its events")
        .iter()
        .map(|event| event["sequence"].clone())
        .collect();
    (last, json!([sequences, state["dropped"]]))
}

#[test]
fn a_row_keeps_its_bound_counts_each_drop_and_lets_go_of_what_was_taken()
{
    let activity = Activity::new(
        Cores::from(core::num::NonZeroU16::MIN),
        Slots::from(core::num::NonZeroUsize::MIN),
    );
    let heard = events(&activity);
    let (first, later, last) = (
        heard.get(.. PENDING.saturating_add(1)).expect("the events"),
        heard
            .get(PENDING.saturating_add(1) .. PENDING.saturating_add(3))
            .expect("the later events"),
        heard
            .get(PENDING.saturating_add(3) ..)
            .expect("the last event"),
    );
    let run = Run(7);
    let occupancy = rows(&[]);
    let mut ledger = Ledger::default();
    ledger.heard(first);
    let (sequence, carried) = state(ledger.owed(run, &occupancy));
    let sequences = carried[0].as_array().expect("the sequence numbers");
    assert_eq!(
        json!([
            sequences.len(),
            sequences.first(),
            u64::from(sequence),
            carried[1]
        ]),
        json!([PENDING, 1_u64, 4_096_u64, 1_u64]),
        "a row past its bound keeps its last events and counts the oldest as dropped"
    );
    assert!(
        ledger.owed(run, &occupancy).is_none(),
        "a row has one state in flight"
    );
    ledger.heard(later);
    ledger.spent();
    let (_, carried) = state(ledger.owed(run, &occupancy));
    let sequences = carried[0].as_array().expect("the sequence numbers");
    assert_eq!(
        json!([sequences.first(), sequences.last(), carried[1]]),
        json!([3_u64, 4_098_u64, 3_u64]),
        "the state after a spent one carries its events again, and the later ones, past the bound"
    );
    ledger.taken();
    assert!(
        ledger.owed(run, &occupancy).is_none(),
        "a take lets go of every event and drop that its state carried"
    );
    ledger.heard(last);
    assert_eq!(
        state(ledger.owed(run, &occupancy)).1,
        json!([[4_099_u64], 0_u64]),
        "the next state carries the events after the take, and no drop"
    );
}
