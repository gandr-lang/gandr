use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::MemoKey as _;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;

use super::BinderLevel;
use super::ConversionFault;
use super::DomainArena;
use super::DomainFault;
use super::GoalSupport;
use super::SupportSides;
use crate::Environment;

#[test]
fn opened_support_refuses_truncated_closures()
{
    let mut core = CoreArena::new();
    let value = core.value_unit();
    let body = core.computation_return(value);
    let mut domain = DomainArena::new();
    let floor = domain.watermark();
    let closure = domain.comp_closure_node(body, Environment::new());
    let sides = SupportSides::Opened(closure, closure);
    assert!(GoalSupport::new(&domain, sides, BinderLevel::FLOOR).is_ok());
    let first_only = domain.watermark();
    let second = domain.comp_closure_node(body, Environment::new());
    assert!(
        GoalSupport::new(
            &domain,
            SupportSides::Opened(closure, second),
            BinderLevel::FLOOR
        )
        .is_ok()
    );
    domain.truncate_to(first_only);
    for pair in [
        SupportSides::Opened(closure, second),
        SupportSides::Opened(second, closure),
    ] {
        assert_eq!(
            Err(ConversionFault::Domain(DomainFault::Dangling)),
            GoalSupport::new(&domain, pair, BinderLevel::FLOOR)
        );
    }
    domain.truncate_to(floor);
    assert_eq!(
        Err(ConversionFault::Domain(DomainFault::Dangling)),
        GoalSupport::new(&domain, sides, BinderLevel::FLOOR)
    );
}

#[test]
fn support_identity_and_digest_survive_forcing_without_conflating_inputs()
{
    let mut domain = DomainArena::new();
    let floor = domain.watermark();
    let first = domain.value_unit(crate::TermFace::Reduced);
    let second = domain.value_unit(crate::TermFace::Reduced);
    let level = BinderLevel::FLOOR;
    let forward = GoalSupport::new(
        &domain,
        SupportSides::Heads(crate::Glued::Value(first), crate::Glued::Value(second)),
        level,
    )
    .expect("both values live");
    let reverse = GoalSupport::new(
        &domain,
        SupportSides::Heads(crate::Glued::Value(second), crate::Glued::Value(first)),
        level,
    )
    .expect("both values live");
    assert_eq!(
        forward.digest(),
        reverse.digest(),
        "equal rigid contents share a bucket"
    );
    assert_eq!(
        ContentAgreement::Differ,
        forward.agreement(&reverse),
        "a bucket does not equate distinct inputs"
    );
    let raised = GoalSupport::new(&domain, forward.sides(), BinderLevel::from(1_u32))
        .expect("the values also live at the higher level");
    assert_eq!(ContentAgreement::Differ, forward.agreement(&raised));
    let repeated =
        GoalSupport::new(&domain, forward.sides(), level).expect("the same input remains live");
    assert_eq!(ContentAgreement::Agree, forward.agreement(&repeated));
    assert_eq!(forward.digest(), repeated.digest());

    let neutral = domain
        .neutral_node(
            crate::NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Vec::new(),
            crate::Unfolding::Unforced(GlobalIndex::from(0_u32)),
        )
        .expect("a constant may unfold");
    let value = domain
        .value_neutral(neutral, crate::TermFace::Reduced)
        .expect("an empty spine is a value");
    let computation = domain.comp_neutral(neutral, crate::CompTermFace::Reduced);
    let value_sides = SupportSides::Heads(crate::Glued::Value(value), crate::Glued::Value(value));
    let comp_sides = SupportSides::Heads(
        crate::Glued::Computation(computation),
        crate::Glued::Computation(computation),
    );
    let before = GoalSupport::new(&domain, value_sides, level).expect("the value neutral lives");
    let before_comp =
        GoalSupport::new(&domain, comp_sides, level).expect("the computation neutral lives");
    assert_eq!(
        ContentAgreement::Differ,
        before.agreement(&before_comp),
        "polarity is part of the input"
    );
    domain
        .force_neutral(neutral, crate::Glued::Value(first))
        .expect("the body was not forced before");
    let after =
        GoalSupport::new(&domain, value_sides, level).expect("forcing preserves the value node");
    let after_comp = GoalSupport::new(&domain, comp_sides, level)
        .expect("forcing preserves the computation node");
    assert_eq!(ContentAgreement::Agree, before.agreement(&after));
    assert_eq!(before.digest(), after.digest());
    assert_eq!(ContentAgreement::Agree, before_comp.agreement(&after_comp));
    assert_eq!(before_comp.digest(), after_comp.digest());

    domain.truncate_to(floor);
    for sides in [forward.sides(), value_sides, comp_sides] {
        assert_eq!(
            Err(ConversionFault::Domain(DomainFault::Dangling)),
            GoalSupport::new(&domain, sides, level)
        );
    }
}

#[test]
fn supports_of_different_content_are_remembered_in_different_buckets()
{
    use gandr_kernel_check_memo::CheckMemo as _;
    use gandr_kernel_check_memo::HashedMemo;
    use gandr_kernel_check_memo::MemoBucketCount;

    let mut core = CoreArena::new();
    let value = core.value_unit();
    let body = core.computation_return(value);
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(crate::TermFace::Reduced);
    let closure = domain.comp_closure_node(body, Environment::new());
    let level = BinderLevel::FLOOR;
    let mut memo = HashedMemo::<GoalSupport, ()>::new();
    for sides in [
        SupportSides::Heads(crate::Glued::Value(unit), crate::Glued::Value(unit)),
        SupportSides::Opened(closure, closure),
    ] {
        let support = GoalSupport::new(&domain, sides, level).expect("both sides live");
        let _recorded = memo.remember(support, ()).expect("the memo has room");
    }
    assert_eq!(
        MemoBucketCount::from(2_usize),
        memo.bucket_count(),
        "the digest spreads distinct content, so a recall scans only its own"
    );
}
