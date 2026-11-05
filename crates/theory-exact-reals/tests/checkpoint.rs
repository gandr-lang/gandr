//! Checkpoints of a run of the refinement machine: a run resumed from its
//! checkpoint gives the certificates of a run that never stops, a cancelled
//! run hands back its checkpoint at the end of its quantum, and each
//! corruption of a checkpoint is refused by name.

use core::cell::Cell;
use core::num::NonZeroU32;

use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::Certificate;
use gandr_theory_exact_reals::CertificateCheck;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::DecodeError;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedCheckpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::NodeId;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::PlanError;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::ResumeError;
use gandr_theory_exact_reals::Root;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::Steps;
use gandr_theory_exact_reals::Stop;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::admit;
use gandr_theory_exact_reals::refine;
use gandr_theory_exact_reals::square_root_of_two;
use num_bigint::BigInt;
use proptest::prelude::*;

/// The laws evidence of every registered cut here.
///
/// # Specification
/// trivial.
fn laws() -> Evidence
{
    return Evidence::from(0_u32);
}

/// The plan whose root joins `45/32 < sqrt 2`, `sqrt 2 < sqrt 2` and `1 < 2`.
///
/// # Specification
/// trivial.
fn plan() -> ValidatedPlan
{
    let mut builder = PlanBuilder::new();
    let root = square_root_of_two(&mut builder, laws()).unwrap();
    let point = Dyadic::new(BigInt::from(45_u8), Exponent::from(-5_i32)).unwrap();
    let point = builder.real(Real::Constant(point)).unwrap();
    let one = builder.real(Real::Constant(Dyadic::from(1_i64))).unwrap();
    let two = builder.real(Real::Constant(Dyadic::from(2_i64))).unwrap();
    let settles = builder.open(Open::Less(point, root)).unwrap();
    let never = builder.open(Open::Less(root, root)).unwrap();
    let constants = builder.open(Open::Less(one, two)).unwrap();
    let joined = builder.open(Open::Join(settles, never)).unwrap();
    let joined = builder.open(Open::Join(joined, constants)).unwrap();
    let mut table = EvidenceTable::new();
    table.register(laws(), Judgement::CutLaws).unwrap();
    return admit(
        builder.finish(Root::Open(joined)).unwrap(),
        &Quotas::default(),
        &table,
    )
    .unwrap();
}

/// The nodes of `plan`: the cut, `45/32 < sqrt 2`, `sqrt 2 < sqrt 2` and
/// `1 < 2`.
///
/// # Specification
/// trivial.
fn nodes(plan: &ValidatedPlan) -> [NodeId; 4]
{
    let count = usize::from(plan.plan().node_count());
    let node = |id: NodeId| plan.plan().node(id).unwrap().clone();
    let real = |id: NodeId| match node(id) {
        Node::Real(real) => Some(real),
        Node::Open(_) | Node::Domain(_) => None,
    };
    let find = |wanted: &dyn Fn(NodeId) -> bool| {
        (0 .. count)
            .map(|index| NodeId::try_from(index).unwrap())
            .find(|&id| wanted(id))
            .unwrap()
    };
    let cut = find(&|id| matches!(real(id), Some(Real::Cut(_))));
    let less = |first: &dyn Fn(Option<Real>) -> bool, second: &dyn Fn(Option<Real>) -> bool| {
        find(
            &|id| matches!(node(id), Node::Open(Open::Less(left, right)) if first(real(left.node())) && second(real(right.node()))),
        )
    };
    let is_cut = |held: Option<Real>| matches!(held, Some(Real::Cut(_)));
    let is_constant = |held: Option<Real>| matches!(held, Some(Real::Constant(_)));
    let settles = less(&is_constant, &is_cut);
    let never = less(&is_cut, &is_cut);
    let constants = less(&is_constant, &is_constant);
    return [cut, settles, never, constants];
}

/// The quantum of `steps` steps.
///
/// # Specification
/// trivial.
fn quantum(steps: Steps) -> Quantum
{
    let steps = u32::try_from(u64::from(steps)).unwrap();
    return Quantum::from(NonZeroU32::new(steps).unwrap());
}

/// A budget that no test spends.
///
/// # Specification
/// trivial.
fn ample() -> Budget
{
    return Budget::from(u64::MAX);
}

/// The certificate of a certified outcome.
///
/// # Specification
/// trivial.
fn certificate(outcome: Option<Outcome<'_>>) -> Certificate
{
    let Some(Outcome::Certified(certificate)) = outcome
    else {
        panic!("the obligation is certified, not {outcome:?}");
    };
    return certificate.clone();
}

#[test]
fn a_resumed_run_certifies_as_an_unbroken_one()
{
    // The try-first: the square root of two refined to 2^-64, stopped after
    // one quantum of four steps and resumed from the checkpoint's bytes.
    let plan = plan();
    let [cut, ..] = nodes(&plan);
    let width = Exponent::from(-64_i32);
    let enclose = Obligation::new(&plan, cut, Demand::Encloses { width }).unwrap();
    let quotas = CheckerQuotas::default();
    let mut unbroken = Dovetail::new(&plan, [enclose], quantum(Steps::from(4_u64)), quotas);
    let whole = certificate(
        unbroken
            .run(ample(), Rounds::from(64_u64), || false)
            .outcome(Position::from(0)),
    );
    let mut stopped = Dovetail::new(&plan, [enclose], quantum(Steps::from(4_u64)), quotas);
    let bytes = {
        let report = stopped.run(ample(), Rounds::from(1_u64), || false);
        assert_eq!(report.outcome(Position::from(0)), Some(Outcome::Pending));
        report.checkpoint()
    };
    let mut resumed = Dovetail::resume(&plan, EncodedCheckpoint::from(&bytes)).unwrap();
    assert_eq!(
        resumed.checkpoint(),
        bytes,
        "a resumed checkpoint writes the same bytes"
    );
    assert_eq!(resumed.spent(Position::from(0)), Some(Steps::from(4_u64)));
    let finished = certificate(
        resumed
            .run(ample(), Rounds::from(64_u64), || false)
            .outcome(Position::from(0)),
    );
    assert_eq!(finished, whole);
    assert_eq!(finished, refine(&plan, cut, width, &quotas).unwrap());
    assert_eq!(
        resumed.spent(Position::from(0)),
        unbroken.spent(Position::from(0))
    );
}

#[test]
fn a_cancelled_run_hands_back_its_checkpoint_at_the_end_of_its_quantum()
{
    let plan = plan();
    let [_, settles, never_settles, _] = nodes(&plan);
    let obligations = [
        Obligation::new(&plan, never_settles, Demand::Holds).unwrap(),
        Obligation::new(&plan, settles, Demand::Holds).unwrap(),
    ];
    let quotas = CheckerQuotas::default();
    let mut unbroken = Dovetail::new(&plan, obligations, quantum(Steps::from(3_u64)), quotas);
    let whole = certificate(
        unbroken
            .run(ample(), Rounds::from(64_u64), || false)
            .outcome(Position::from(1)),
    );
    // The cancellation comes before the second turn: the first turn ends its
    // quantum of three steps, and the second obligation has had none.
    let asked = Cell::new(0_u32);
    let mut cancelled = Dovetail::new(&plan, obligations, quantum(Steps::from(3_u64)), quotas);
    let bytes = {
        let report = cancelled.run(ample(), Rounds::from(64_u64), || {
            asked.set(asked.get() + 1);
            asked.get() == 2
        });
        assert_eq!(report.stop(), Stop::Cancelled);
        assert_eq!(report.outcome(Position::from(0)), Some(Outcome::Cancelled));
        assert_eq!(report.outcome(Position::from(1)), Some(Outcome::Cancelled));
        report.checkpoint()
    };
    assert_eq!(
        (
            cancelled.spent(Position::from(0)),
            cancelled.spent(Position::from(1))
        ),
        (Some(Steps::from(3_u64)), Some(Steps::from(0_u64)))
    );
    let mut resumed = Dovetail::resume(&plan, EncodedCheckpoint::from(&bytes)).unwrap();
    // The next turn is the second obligation's, as it was before the
    // cancellation.
    let report = resumed.run(ample(), Rounds::from(1_u64), || false);
    assert_eq!(report.work().steps, 3);
    assert_eq!(
        (
            resumed.spent(Position::from(0)),
            resumed.spent(Position::from(1))
        ),
        (Some(Steps::from(3_u64)), Some(Steps::from(3_u64)))
    );
    let finished = certificate(
        resumed
            .run(ample(), Rounds::from(64_u64), || false)
            .outcome(Position::from(1)),
    );
    assert_eq!(finished, whole);
}

#[test]
fn a_corrupt_checkpoint_is_refused_by_name()
{
    let plan = plan();
    let [cut, settles, never_settles, _] = nodes(&plan);
    let width = Exponent::from(-16_i32);
    let enclose = Obligation::new(&plan, cut, Demand::Encloses { width }).unwrap();
    let mut dovetail = Dovetail::new(
        &plan,
        [enclose],
        quantum(Steps::from(2_u64)),
        CheckerQuotas::default(),
    );
    let bytes: Vec<u8> = dovetail
        .run(ample(), Rounds::from(1_u64), || false)
        .checkpoint()
        .into();
    // The layout: magic 0..4, version 4..6, quantum 6..10, step quota 10..18,
    // width quota 18..26, cursor 26..34, count 34..42, then the obligation:
    // its node 42..46, its demand 46..51, its spent steps 51..59, its step
    // count 59..67, then its first step, a `Witnesses` of the cut: its kind
    // at 67, the cut 68..72, the lower point's exponent 72..76, its length
    // 76..84 and its one byte at 84.
    let refused = |edited: &[u8]| Dovetail::resume(&plan, EncodedCheckpoint::from(edited)).err();
    let edit = |at: usize, value: &[u8]| {
        let mut edited = bytes.clone();
        edited.splice(at .. at + value.len(), value.iter().copied());
        edited
    };
    assert!(refused(&bytes).is_none(), "the checkpoint resumes");
    assert_eq!(
        refused(&edit(0, b"X")),
        Some(ResumeError::Decode(DecodeError::Magic))
    );
    assert_eq!(
        refused(&edit(4, &[9])),
        Some(ResumeError::Decode(DecodeError::Version))
    );
    assert_eq!(
        refused(&bytes[.. bytes.len() - 1]),
        Some(ResumeError::Decode(DecodeError::Truncated))
    );
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_eq!(
        refused(&trailing),
        Some(ResumeError::Decode(DecodeError::TrailingBytes))
    );
    assert_eq!(
        refused(&edit(6, &0_u32.to_le_bytes())),
        Some(ResumeError::Quantum)
    );
    assert_eq!(
        refused(&edit(26, &1_u64.to_le_bytes())),
        Some(ResumeError::Cursor)
    );
    assert_eq!(
        refused(&edit(46, &[0x4F])),
        Some(ResumeError::Decode(DecodeError::UnknownKind))
    );
    let past = u32::try_from(usize::from(plan.plan().node_count())).unwrap();
    assert_eq!(
        refused(&edit(42, &past.to_le_bytes())),
        Some(ResumeError::Obligation(PlanError::UnknownNode))
    );
    // A demand that holds of an open node, given to the cut: the node's sort
    // does not take it.
    let mut holds = bytes.clone();
    holds.splice(46 .. 51, [0x40]);
    assert_eq!(
        refused(&holds),
        Some(ResumeError::Obligation(PlanError::WrongSort))
    );
    // A width quota of one bit: the steps do not replay within it.
    let Some(ResumeError::Replay(refusal)) = refused(&edit(18, &1_u64.to_le_bytes()))
    else {
        panic!("a quota the steps exceed is refused at the replay");
    };
    assert_eq!(refusal.check, CertificateCheck::WidthQuota);
    // The lower point's one byte padded with a byte of zero: it reads as the
    // same point, so the bytes are not canonical.
    let mut padded = edit(76, &2_u64.to_le_bytes());
    padded.insert(85, 0);
    assert_eq!(
        refused(&padded),
        Some(ResumeError::Decode(DecodeError::NotCanonical))
    );
    // The steps of `45/32 < sqrt 2` given to `sqrt 2 < sqrt 2`: they replay,
    // but the first chain is not of the comparison's first operand.
    let mut comparison = Dovetail::new(
        &plan,
        [Obligation::new(&plan, settles, Demand::Holds).unwrap()],
        quantum(Steps::from(3_u64)),
        CheckerQuotas::default(),
    );
    let mut swapped: Vec<u8> = comparison
        .run(ample(), Rounds::from(1_u64), || false)
        .checkpoint()
        .into();
    swapped.splice(42 .. 46, u32::from(never_settles).to_le_bytes());
    assert_eq!(refused(&swapped), Some(ResumeError::Steps));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// A checkpoint after a generated number of rounds, under a generated
    /// quantum, resumes to the outcomes, the certificates and the spent steps
    /// of the run that never stops.
    #[test]
    fn every_checkpoint_resumes_to_the_unbroken_run(
        steps in 1_u32 .. 6_u32,
        stop in 0_u64 .. 24_u64,
        more in 0_u64 .. 24_u64,
        bits in 4_i32 .. 48_i32,
    ) {
        let plan = plan();
        let [cut, settles, never_settles, constants] = nodes(&plan);
        let width = Exponent::from(bits.checked_neg().unwrap());
        let obligations = [
            Obligation::new(&plan, cut, Demand::Encloses { width }).unwrap(),
            Obligation::new(&plan, settles, Demand::Holds).unwrap(),
            Obligation::new(&plan, never_settles, Demand::Holds).unwrap(),
            Obligation::new(&plan, constants, Demand::Fails).unwrap(),
            Obligation::new(&plan, settles, Demand::Fails).unwrap(),
        ];
        let quotas = CheckerQuotas::default();
        let mut unbroken = Dovetail::new(&plan, obligations, quantum(Steps::from(u64::from(steps))), quotas);
        let total = stop.checked_add(more).unwrap();
        let unbroken_outcomes: Vec<String> = {
            let report = unbroken.run(ample(), Rounds::from(total), || false);
            (0 .. obligations.len()).map(|index| format!("{:?}", report.outcome(Position::from(index)))).collect()
        };
        let mut first = Dovetail::new(&plan, obligations, quantum(Steps::from(u64::from(steps))), quotas);
        let (bytes, live) = {
            let report = first.run(ample(), Rounds::from(stop), || false);
            let live: Vec<usize> = (0 .. obligations.len())
                .filter(|&index| matches!(report.outcome(Position::from(index)), Some(Outcome::Pending)))
                .collect();
            (report.checkpoint(), live)
        };
        let mut resumed = Dovetail::resume(&plan, EncodedCheckpoint::from(&bytes)).unwrap();
        prop_assert_eq!(&resumed.checkpoint(), &bytes);
        let resumed_outcomes: Vec<String> = {
            let report = resumed.run(ample(), Rounds::from(more), || false);
            prop_assert_eq!(report.outcome(Position::from(live.len())), None);
            (0 .. live.len()).map(|position| format!("{:?}", report.outcome(Position::from(position)))).collect()
        };
        for (position, &index) in live.iter().enumerate() {
            prop_assert_eq!(&resumed_outcomes[position], &unbroken_outcomes[index]);
            prop_assert_eq!(resumed.spent(Position::from(position)), unbroken.spent(Position::from(index)));
        }
    }
}
