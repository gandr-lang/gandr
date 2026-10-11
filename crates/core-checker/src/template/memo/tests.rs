//! The controller's decisions under measured times, and the fresh-arm cap.

use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::Term;

use super::super::ProgramId;
use super::super::harvest;
use super::super::produce;
use super::*;

/// A clock that never advances: every draft is free, so the controller drafts
/// every family that has a template.
pub(in crate::template) struct Stopped;

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

/// A fixture count.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Count(usize);

/// Quote/splice cancellations of `members` inner numerals cycling over `arms`
/// bodies, one certificate each.
///
/// # Specification
/// - ensures: `members` certificates in one fresh arena.
/// - panics: fixture allocation or normalization failure, or zero arms.
///
/// # Adequacy
/// - hypothesis: L2 — the producer and the kernel judge the families harvested
///   from it independently of how they were built.
/// - witness: `template::memo::tests::the_fresh_arm_cap_withdraws_a_widening_that_costs_the_producers_time`
#[spec(requires: arms.0 > 0, ensures: |output| output.1.len() == members.0)]
fn cancellations(
    members: Count,
    arms: Count,
) -> (Arena, Vec<Certificate>)
{
    let mut arena = Arena::default();
    let mut certificates = Vec::with_capacity(members.0);
    for member in 0 .. members.0 {
        let value = member.checked_rem(arms.0).unwrap();
        let body = arena
            .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(value)))
            .unwrap();
        let quote = arena.alloc(Term::Quote(body)).unwrap();
        let source = arena.alloc(Term::Splice(quote)).unwrap();
        certificates.push(
            gandr_core_nbe::stage::normalize(&mut arena, source, &mut Budget(100_000)).unwrap(),
        );
    }
    (arena, certificates)
}

#[test]
fn the_controller_drafts_while_drafting_pays_and_probes_when_it_stops()
{
    let micros = Duration::from_micros;
    let mut switch = Memo::default().switch;
    let mut controls = Controls::fresh();
    assert_eq!(
        controls.decide(&mut switch),
        Decision::Draft,
        "nothing measured yet"
    );
    // A 100 µs producer against 10 µs drafts either way: the break-even is
    // 10 / (100 - 10 + 10) = 0.1, for the key and across the memo alike.
    controls.producing = Estimate::Measured(micros(100));
    controls.record(&mut switch, Acceptance::Accepted, micros(10));
    controls.record(&mut switch, Acceptance::Refused, micros(10));
    assert!(matches!(
        break_even(Share(0.1), Share(0.1)),
        Maybe::Present(bound) if (bound.0 - 0.1_f64).abs() < 1e-12_f64
    ));
    assert_eq!(controls.decide(&mut switch), Decision::Draft);
    // Each refusal moves both acceptances 8% of the way to zero; from 0.92
    // they fall to 0.1 after 27 more.
    let mut refusals = 0_usize;
    while controls.verdict() == Decision::Draft {
        controls.record(&mut switch, Acceptance::Refused, micros(10));
        refusals = refusals.checked_add(1).unwrap();
    }
    assert_eq!(refusals, 27);
    assert_eq!(
        controls.verdict(),
        Decision::Decline(Decline::BelowBreakEven)
    );
    assert_eq!(switch.off(), Decision::Decline(Decline::Off));
    // Switched off, the memo drafts every seventh family and declines the
    // rest.
    let decisions: Vec<Decision> = core::iter::repeat_with(|| controls.decide(&mut switch))
        .take(14)
        .collect();
    let probes: Vec<usize> = decisions
        .iter()
        .enumerate()
        .filter(|&(_, decision)| *decision == Decision::Draft)
        .map(|(index, _)| index)
        .collect();
    assert_eq!(probes, [6, 13]);
    assert!(
        decisions
            .iter()
            .all(|decision| matches!(decision, Decision::Draft | Decision::Decline(Decline::Off)))
    );
    // With the memo on, the key's own break-even decides, at the same duty.
    let mut on = Memo::default().switch;
    let decisions: Vec<Decision> = core::iter::repeat_with(|| controls.decide(&mut on))
        .take(7)
        .collect();
    assert!(
        decisions
            .iter()
            .take(6)
            .all(|decision| *decision == Decision::Decline(Decline::BelowBreakEven))
    );
    assert_eq!(decisions.last(), Some(&Decision::Draft));
    // One accepted draft lifts the key back above its break-even.
    controls.record(&mut on, Acceptance::Accepted, micros(10));
    assert_eq!(controls.verdict(), Decision::Draft);
    // A draft no faster than the producer never pays, whatever its acceptance.
    controls.record(&mut on, Acceptance::Accepted, micros(100));
    assert_eq!(controls.verdict(), Decision::Decline(Decline::NeverPays));
    // A clock that never advances makes every draft free.
    let mut stopped = Controls::fresh();
    stopped.producing = Estimate::Measured(Duration::ZERO);
    stopped.record(&mut on, Acceptance::Accepted, Duration::ZERO);
    stopped.record(&mut on, Acceptance::Refused, Duration::ZERO);
    assert_eq!(stopped.verdict(), Decision::Draft);
}

#[test]
fn the_fresh_arm_cap_withdraws_a_widening_that_costs_the_producers_time()
{
    let (arena, certificates) = cancellations(Count(64), Count(2));
    let families = harvest(&arena, ProgramId(0), &certificates).unwrap();
    let [ref family] = *families.as_slice()
    else {
        panic!("one cancellation family");
    };
    let Production::Go(template) = produce(
        &arena,
        &family.members,
        PriceGate::Unmemoized,
        &mut InheritanceCache::new(),
        &mut Budget(1_000_000),
    )
    .unwrap()
    else {
        panic!("two arms over 64 members pay");
    };
    let (arena, certificates) = cancellations(Count(64), Count(4));
    let families = harvest(&arena, ProgramId(0), &certificates).unwrap();
    let [ref wider] = *families.as_slice()
    else {
        panic!("one cancellation family");
    };
    let mut drafter = Drafter::default();
    let mut attempt = |cap: &mut Cap| {
        template
            .attempt(
                &arena,
                &wider.members,
                PriceGate::Unmemoized,
                cap,
                &mut drafter,
                &mut Stopped,
            )
            .unwrap()
    };
    // Two new arms at a measured second each against a 1 µs producer: the
    // widening is withdrawn before it imports anything.
    let mut cap = Cap {
        producing: Estimate::Measured(Duration::from_micros(1)),
        arm: Tracked::Sampled(Share(1.0)),
    };
    assert!(matches!(
        attempt(&mut cap),
        Attempt::Withdrawn(Drafting::Capped(ArmCount(2)))
    ));
    assert_eq!(
        cap.arm,
        Tracked::Sampled(Share(1.0)),
        "a withdrawn widening measures nothing"
    );
    // An unmeasured arm never caps; the finished widening samples its import,
    // which a stopped clock reads as free.
    let mut cap = Cap {
        producing: Estimate::Measured(Duration::from_micros(1)),
        arm: Tracked::Unsampled,
    };
    assert!(matches!(
        attempt(&mut cap),
        Attempt::Ready(_, DraftKind::Widened(ArmCount(2)))
    ));
    assert_eq!(cap.arm, Tracked::Sampled(Share(0.0)));
    // At that cost the same widening goes ahead.
    assert!(matches!(
        attempt(&mut cap),
        Attempt::Ready(_, DraftKind::Widened(ArmCount(2)))
    ));
}
