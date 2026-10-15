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
#[derive(Clone, Copy)]
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
    let record = |controls: &mut Controls, switch: &mut Switch, accepted, spent| {
        switch.absorb(Samples {
            arm: Tracked::Unsampled,
            draft: controls.observe(accepted, spent),
        });
    };
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
    record(&mut controls, &mut switch, Acceptance::Accepted, micros(10));
    record(&mut controls, &mut switch, Acceptance::Refused, micros(10));
    assert!(matches!(
        break_even(Share(0.1), Share(0.1)),
        Maybe::Present(bound) if (bound.0 - 0.1_f64).abs() < 1e-12_f64
    ));
    assert_eq!(controls.decide(&mut switch), Decision::Draft);
    // Each refusal moves both acceptances 8% of the way to zero; from 0.92
    // they fall to 0.1 after 27 more.
    let mut refusals = 0_usize;
    while controls.verdict() == Decision::Draft {
        record(&mut controls, &mut switch, Acceptance::Refused, micros(10));
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
    record(&mut controls, &mut on, Acceptance::Accepted, micros(10));
    assert_eq!(controls.verdict(), Decision::Draft);
    // A draft no faster than the producer never pays, whatever its acceptance.
    record(&mut controls, &mut on, Acceptance::Accepted, micros(100));
    assert_eq!(controls.verdict(), Decision::Decline(Decline::NeverPays));
    // A clock that never advances makes every draft free.
    let mut stopped = Controls::fresh();
    stopped.producing = Estimate::Measured(Duration::ZERO);
    record(&mut stopped, &mut on, Acceptance::Accepted, Duration::ZERO);
    record(&mut stopped, &mut on, Acceptance::Refused, Duration::ZERO);
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
        measured: Tracked::Unsampled,
    };
    assert!(matches!(
        attempt(&mut cap),
        Attempt::Withdrawn(Drafting::Capped(ArmCount(2)))
    ));
    assert_eq!(
        cap.measured,
        Tracked::Unsampled,
        "a withdrawn widening measures nothing"
    );
    // An unmeasured arm never caps; the finished widening measures its
    // import, which a stopped clock reads as free.
    let mut cap = Cap {
        producing: Estimate::Measured(Duration::from_micros(1)),
        arm: Tracked::Unsampled,
        measured: Tracked::Unsampled,
    };
    assert!(matches!(
        attempt(&mut cap),
        Attempt::Ready(_, DraftKind::Widened(ArmCount(2)))
    ));
    assert_eq!(cap.measured, Tracked::Sampled(Share(0.0)));
    assert_eq!(
        cap.arm,
        Tracked::Unsampled,
        "the memo folds the measurement"
    );
    cap.arm = cap.measured;
    // At that cost the same widening goes ahead.
    assert!(matches!(
        attempt(&mut cap),
        Attempt::Ready(_, DraftKind::Widened(ArmCount(2)))
    ));
}

/// A clock that advances one microsecond at every reading, so every timed
/// stretch measures a positive time.
#[repr(transparent)]
struct Ticking(Duration);

impl Clock for Ticking
{
    /// One microsecond past the last reading.
    ///
    /// # Specification
    /// trivial.
    fn now(&mut self) -> Duration
    {
        self.0 = self.0.saturating_add(Duration::from_micros(1));
        self.0
    }
}

/// The break-even is the refused share over the accepted saving plus the
/// refused share, and both the memo's switch and a key's verdict decline at
/// it exactly and draft just above it.
#[test]
fn drafting_stops_exactly_at_the_break_even()
{
    let bound = 0.25_f64 / (1.0_f64 - 0.5_f64 + 0.25_f64);
    assert_eq!(
        break_even(Share(0.5), Share(0.25)),
        Maybe::Present(Share(bound)),
        "a* = r / (1 - d + r)"
    );
    let above = Share(bound + 1.0e-9_f64);
    let mut switch = Memo::default().switch;
    switch.accepted = Tracked::Sampled(Share(0.5));
    switch.refused = Tracked::Sampled(Share(0.25));
    switch.acceptance = Share(bound);
    assert_eq!(
        switch.off(),
        Decision::Decline(Decline::Off),
        "the memo stops at the bound"
    );
    switch.acceptance = above;
    assert_eq!(switch.off(), Decision::Draft, "and drafts above it");
    let mut controls = Controls::fresh();
    controls.producing = Estimate::Measured(Duration::from_secs(4));
    controls.accepted = Estimate::Measured(Duration::from_secs(2));
    controls.refused = Estimate::Measured(Duration::from_secs(1));
    controls.acceptance = Share(bound);
    assert_eq!(
        controls.verdict(),
        Decision::Decline(Decline::BelowBreakEven),
        "a key stops at its bound"
    );
    controls.acceptance = above;
    assert_eq!(controls.verdict(), Decision::Draft, "and drafts above it");
}

/// A drafted family's time is sampled as a share of its key's producer time
/// only when that time is measured and positive.
#[test]
fn a_draft_is_sampled_against_a_positive_producer_time_only()
{
    let sampled = |producing| {
        let mut controls = Controls::fresh();
        controls.producing = producing;
        match controls.observe(Acceptance::Accepted, Duration::from_secs(1)) {
            DraftSample::Drafted { share, .. } => share,
            DraftSample::Undrafted => panic!("an observed draft is drafted"),
        }
    };
    assert_eq!(
        sampled(Estimate::Measured(Duration::from_secs(4))),
        Tracked::Sampled(Share(0.25))
    );
    assert_eq!(
        sampled(Estimate::Measured(Duration::ZERO)),
        Tracked::Unsampled,
        "a free producer gives no share"
    );
    assert_eq!(sampled(Estimate::Unmeasured), Tracked::Unsampled);
}

/// The fresh-arm cap weighs the fresh arms times the per-arm cost against
/// the producer's time, and a finished widening measures its import per arm.
#[test]
fn the_cap_weighs_arms_times_cost_and_measures_the_import_per_arm()
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
    // Two fresh arms at three seconds each cost six against a producer of
    // five and a half: capped, where their sum or quotient would not be.
    let mut cap = Cap {
        producing: Estimate::Measured(Duration::from_millis(5_500)),
        arm: Tracked::Sampled(Share(3.0)),
        measured: Tracked::Unsampled,
    };
    let attempt = template
        .attempt(
            &arena,
            &wider.members,
            PriceGate::Unmemoized,
            &mut cap,
            &mut Drafter::default(),
            &mut Stopped,
        )
        .unwrap();
    assert!(matches!(
        attempt,
        Attempt::Withdrawn(Drafting::Capped(ArmCount(2)))
    ));
    // Under a clock that advances, the import takes time, and the cap
    // measures it per fresh arm.
    let mut cap = Cap {
        producing: Estimate::Measured(Duration::from_secs(1)),
        arm: Tracked::Unsampled,
        measured: Tracked::Unsampled,
    };
    let mut drafter = Drafter::default();
    let attempt = template
        .attempt(
            &arena,
            &wider.members,
            PriceGate::Unmemoized,
            &mut cap,
            &mut drafter,
            &mut Ticking(Duration::ZERO),
        )
        .unwrap();
    assert!(matches!(
        attempt,
        Attempt::Ready(_, DraftKind::Widened(ArmCount(2)))
    ));
    let importing = drafter.importing().as_secs_f64();
    assert!(importing > 0.0_f64, "the import took time");
    assert_eq!(cap.measured, Tracked::Sampled(Share(importing / 2.0_f64)));
}
