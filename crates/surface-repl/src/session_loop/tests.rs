use alloc::string::String;
use alloc::string::ToString as _;
use std::io;

use rustyline::error::ReadlineError;

use super::Faulted;
use super::LoopError;
use crate::batch::Fault;

/// What stops a face carries its cause: a session fault ends with the
/// fault's own rendering whether the loop or the face reports it, and an
/// input or editor failure ends with the error it met. The three reasons
/// read apart.
#[test]
fn a_fault_carries_its_cause()
{
    let fault = Faulted(String::from("the revision's checkpoint is gone"));
    let stopped = LoopError::Fault(fault.clone());
    assert!(stopped.to_string().ends_with(&fault.to_string()));
    assert_eq!(fault.to_string(), "the revision's checkpoint is gone");
    let input = io::Error::new(
        io::ErrorKind::InvalidData,
        "stream did not contain valid UTF-8",
    );
    let reasons = [
        (Fault::Session(stopped.clone()), stopped.to_string()),
        (
            Fault::Input(input),
            String::from("stream did not contain valid UTF-8"),
        ),
        (
            Fault::Editor(ReadlineError::Eof),
            ReadlineError::Eof.to_string(),
        ),
    ];
    for &(ref reason, ref cause) in &reasons {
        assert!(reason.to_string().ends_with(cause.as_str()), "{reason}");
    }
    assert_ne!(reasons[1].0.to_string(), reasons[2].0.to_string());
    assert_ne!(reasons[0].0.to_string(), reasons[1].0.to_string());
}
