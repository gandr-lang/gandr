//! An interrupted call against each subject: a read that waits on a socket
//! with no bytes, and a signal that the process handles with no restart. The
//! read is refused with `EINTR`, and the caller decides: the next read of the
//! same descriptor gives the bytes that arrive after the signal.
//!
//! The witness sets a handler of `SIGUSR1` for the whole process. The handler
//! does nothing, and no other witness sends that signal, so the witness shares
//! its target with the other witnesses.

use core::ffi::c_int;
use core::num::NonZeroU16;
use core::time::Duration;
use std::io::Write as _;
use std::os::fd::AsRawFd as _;
use std::os::unix::net::UnixStream;
use std::sync::mpsc;
use std::sync::mpsc::RecvTimeoutError;
use std::time::Instant;

use gandr_boot_core::Length;
use gandr_boot_core::Place;
use gandr_boot_io::Descriptor;
use gandr_boot_io::ErrorNumber;
use gandr_boot_io::Operation;
use nix::sys::pthread::pthread_kill;
use nix::sys::pthread::pthread_self;
use nix::sys::signal::SaFlags;
use nix::sys::signal::SigAction;
use nix::sys::signal::SigHandler;
use nix::sys::signal::SigSet;
use nix::sys::signal::Signal;
use nix::sys::signal::sigaction;

use crate::harness::PAGE;
use crate::harness::SUBJECTS;
use crate::harness::started;

/// The error number of a call that a signal interrupts.
const EINTR: ErrorNumber = ErrorNumber(NonZeroU16::new(4).expect("4 is not zero"));

/// The time between two signals to the thread of the read.
const PAUSE: Duration = Duration::from_millis(1);

/// The time after which the witness sends no more signals and ends the wait of
/// the read with a byte, so a read that no signal interrupts fails the witness
/// and does not wait for all time.
const LIMIT: Duration = Duration::from_secs(10);

/// The bytes that arrive after the interrupted read.
const LATER: &[u8] = b"gandr";

/// The handler of the signal. It does nothing: its run alone ends the wait of
/// the read.
///
/// # Specification
/// trivial.
extern "C" fn nothing(_signal: c_int)
{
}

/// A read that waits on a socket with no bytes is refused under the name
/// `read` with `EINTR` when a handled signal arrives, because the crate does
/// not repeat the call. The descriptor stays open: the next read gives the
/// bytes that the other end writes after the signal.
///
/// A thread of the witness reads. The main thread sends `SIGUSR1` to it until
/// the read answers, so a signal that arrives before the read waits does not
/// end the witness.
#[test]
fn a_signal_refuses_a_read_that_waits_with_eintr()
{
    let action = SigAction::new(
        SigHandler::Handler(nothing),
        SaFlags::empty(),
        SigSet::empty(),
    );
    // SAFETY: the handler does nothing, so it is safe at each point of each
    // thread.
    let _before =
        unsafe { sigaction(Signal::SIGUSR1, &action) }.expect("the host sets the handler");
    for subject in &SUBJECTS {
        let name = subject.name;
        let (mut writer, reader) = UnixStream::pair().expect("the host makes a socket pair");
        let descriptor = Descriptor(reader.as_raw_fd());
        let io = started(subject);
        let handle = &io;
        let first = std::thread::scope(|scope| {
            let (thread_sender, thread_receiver) = mpsc::channel();
            let (answer_sender, answer_receiver) = mpsc::channel();
            let _reader = scope.spawn(move || {
                thread_sender
                    .send(pthread_self())
                    .expect("the main thread waits for the name of the thread");
                let mut page = [0_u8; PAGE];
                // SAFETY: the place is a live array, and nothing else reads it
                // during the call.
                let read =
                    unsafe { (subject.read)(handle, descriptor, Place::from(page.as_mut_slice())) };
                answer_sender
                    .send(read)
                    .expect("the main thread waits for the answer");
            });
            let thread = thread_receiver
                .recv()
                .expect("the thread of the read gives its name");
            let begin = Instant::now();
            loop {
                pthread_kill(thread, Signal::SIGUSR1).expect("the host signals the thread");
                match answer_receiver.recv_timeout(PAUSE) {
                    Ok(read) => break read,
                    Err(RecvTimeoutError::Timeout) if begin.elapsed() < LIMIT => {},
                    Err(_) => {
                        writer
                            .write_all(LATER)
                            .expect("the other end ends the wait of the read");
                        break answer_receiver
                            .recv()
                            .expect("the thread of the read answers after the bytes");
                    },
                }
            }
        });
        assert_eq!(
            Err((Operation::Read, EINTR)),
            first.map_err(|refused| (refused.operation(), refused.number())),
            "{name}: the interrupted read"
        );
        writer
            .write_all(LATER)
            .expect("the other end writes after the signal");
        let mut page = [0_u8; PAGE];
        // SAFETY: the place is a live array, and nothing else reads it during
        // the call.
        let count = unsafe { (subject.read)(&io, descriptor, Place::from(page.as_mut_slice())) };
        assert_eq!(
            Ok(Length(LATER.len())),
            count,
            "{name}: the read after the signal"
        );
        assert_eq!(
            Some(LATER),
            page.get(.. LATER.len()),
            "{name}: the bytes after the signal"
        );
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}
