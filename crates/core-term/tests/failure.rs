//! Whose fact a refusal records, where an unimplemented one is tracked, and
//! how the native and effect refusals read.

use alloc::collections::BTreeSet;
use alloc::string::ToString as _;

use gandr_core_term::FailureClass;
use gandr_core_term::TrackingIssue;
use gandr_core_term::effect::EffectConflict;
use gandr_core_term::effect::EffectLabel;
use gandr_core_term::effect::OperationName;
use gandr_core_term::primitive::PrimitiveError;
use gandr_core_term::row::Label;
use quenchant_shape::shape::Maybe;

/// Only an unimplemented refusal is tracked, by the issue it carries, and
/// each other class gives its own reason for having none. The four classes
/// read apart. An issue writes its number after `#`, and its page ends with
/// that number.
#[test]
fn only_an_unimplemented_refusal_is_tracked_and_each_class_reads_apart()
{
    let issue = TrackingIssue::KERNEL_EFFECTS;
    assert_eq!(
        FailureClass::Unimplemented(issue).tracking(),
        Maybe::Present(issue)
    );
    let reasons: BTreeSet<_> = [
        FailureClass::UserAbsence,
        FailureClass::MalformedSource,
        FailureClass::EngineFault,
    ]
    .into_iter()
    .map(|class| match class.tracking() {
        Maybe::Present(tracked) => panic!("{class} is tracked by {tracked}"),
        Maybe::Absent(reason) => reason,
    })
    .collect();
    assert_eq!(reasons.len(), 3, "each untracked class says why");

    let written: BTreeSet<_> = [
        FailureClass::UserAbsence,
        FailureClass::Unimplemented(issue),
        FailureClass::MalformedSource,
        FailureClass::EngineFault,
    ]
    .iter()
    .map(ToString::to_string)
    .collect();
    assert_eq!(written.len(), 4, "{written:?}");

    let number = issue.to_string();
    let digits = number.strip_prefix('#').expect("an issue writes `#` first");
    assert!(
        !digits.is_empty() && digits.chars().all(|digit| digit.is_ascii_digit()),
        "{number}"
    );
    assert!(
        issue.url().ends_with(&format!("/{digits}")),
        "{}",
        issue.url()
    );
    assert_ne!(
        TrackingIssue::KERNEL_MEMORY.to_string(),
        number,
        "two issues write two numbers"
    );
}

/// The four native failures read apart, and an effect conflict names the
/// operation or the interface it is about.
#[test]
fn native_and_effect_refusals_read_apart_and_name_what_they_carry()
{
    let native: BTreeSet<_> = [
        PrimitiveError::Arity,
        PrimitiveError::ArgumentType,
        PrimitiveError::DivisionByZero,
        PrimitiveError::InvalidInteger,
    ]
    .iter()
    .map(ToString::to_string)
    .collect();
    assert_eq!(native.len(), 4, "{native:?}");

    let operation = EffectConflict::DuplicateOperation(OperationName::from("ask")).to_string();
    let interface =
        EffectConflict::Signature(EffectLabel::Interface(Label::from("Probe"))).to_string();
    assert!(operation.ends_with("ask"), "{operation}");
    assert!(interface.ends_with("Probe"), "{interface}");
    assert_ne!(
        operation.strip_suffix("ask"),
        interface.strip_suffix("Probe"),
        "an operation conflict reads apart from an interface conflict"
    );
}
