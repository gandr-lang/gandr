//! C result-code interpretation.

use gandr_runtime_compile_host::boundary::BoundaryResult;
use gandr_runtime_compile_host::boundary::BoundaryStatus;
use gandr_runtime_compile_host::boundary::RefusalStage;

#[test]
fn every_boundary_status_names_its_own_stage()
{
    assert_eq!(
        BoundaryResult::from(BoundaryStatus::from(0_i32)),
        BoundaryResult::Success
    );
    for (status, stage) in [
        (1_i32, RefusalStage::MalformedImage),
        (2_i32, RefusalStage::VerifierRejected),
        (3_i32, RefusalStage::LoweringFailed),
        (4_i32, RefusalStage::ConversionFailed),
        (5_i32, RefusalStage::ExecutionFailed),
        (6_i32, RefusalStage::ResultUnreadable),
        (7_i32, RefusalStage::LimitExceeded),
        (8_i32, RefusalStage::FixtureUnreadable),
        (100_i32, RefusalStage::BadCall),
    ] {
        assert_eq!(
            BoundaryResult::from(BoundaryStatus::from(status)),
            BoundaryResult::Refused(stage)
        );
    }
    for status in [i32::MIN, -1_i32, 9_i32, 42_i32, 99_i32, 101_i32, i32::MAX] {
        let status = BoundaryStatus::from(status);
        assert_eq!(
            BoundaryResult::from(status),
            BoundaryResult::Refused(RefusalStage::Unknown(status))
        );
    }
}
