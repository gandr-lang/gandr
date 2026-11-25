//! An interrupted call against each subject: a read that waits on a socket
//! with no bytes, and a write that waits on a socket that is full. A signal
//! that the process handles with no restart refuses the call with `EINTR`,
//! and the caller decides: the next call on the same descriptor completes.
//!
//! The witnesses set a handler of `SIGUSR1` for the whole process. The handler
//! does nothing, and no other witness sends that signal, so the witnesses share
//! their target with the other witnesses.

use core::ffi::c_int;
use core::num::NonZeroU16;
use core::time::Duration;
use std::io::ErrorKind;
use std::io::Read as _;
use std::io::Write as _;
use std::os::fd::AsRawFd as _;
use std::os::unix::net::UnixStream;
use std::sync::mpsc;
use std::sync::mpsc::RecvTimeoutError;
use std::time::Instant;

use gandr_boot_core::Length;
use gandr_boot_core::Place;
use gandr_boot_core::Range;
use gandr_boot_io::Descriptor;
use gandr_boot_io::ErrorNumber;
use gandr_boot_io::Operation;
use gandr_boot_io::Refused;
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

/// The time between two signals to the thread of the call.
const PAUSE: Duration = Duration::from_millis(1);

/// The time after which the witness sends no more signals and ends the wait of
/// the call by the other end, so a call that no signal interrupts fails the
/// witness and does not wait for all time.
const LIMIT: Duration = Duration::from_secs(10);

/// The bytes that arrive after the interrupted read.
const LATER: &[u8] = b"gandr";

/// The handler of the signal. It does nothing: its run alone ends the wait of
/// the call.
///
/// # Specification
/// trivial.
extern "C" fn nothing(_signal: c_int)
{
}

/// Sets [`nothing`] as the handler of `SIGUSR1`, with no restart of a call.
///
/// # Specification
/// trivial.
fn handled()
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
}

/// The answer of `call`, which runs on a thread of its own. The main thread
/// sends `SIGUSR1` to that thread each [`PAUSE`] until the call answers, so a
/// signal that arrives before the call waits does not end the witness. After
/// [`LIMIT`], `release` ends the wait of the call by the other end.
///
/// # Specification
/// trivial.
fn signalled<Answer>(
    call: impl FnOnce() -> Answer + Send,
    release: impl FnOnce(),
) -> Answer
where
    Answer: Send,
{
    std::thread::scope(|scope| {
        let (thread_sender, thread_receiver) = mpsc::channel();
        let (answer_sender, answer_receiver) = mpsc::channel();
        let _caller = scope.spawn(move || {
            thread_sender
                .send(pthread_self())
                .expect("the main thread waits for the name of the thread");
            answer_sender
                .send(call())
                .expect("the main thread waits for the answer");
        });
        let thread = thread_receiver
            .recv()
            .expect("the thread of the call gives its name");
        let begin = Instant::now();
        loop {
            pthread_kill(thread, Signal::SIGUSR1).expect("the host signals the thread");
            match answer_receiver.recv_timeout(PAUSE) {
                Ok(answer) => return answer,
                Err(RecvTimeoutError::Timeout) if begin.elapsed() < LIMIT => {},
                Err(_) => {
                    release();
                    return answer_receiver
                        .recv()
                        .expect("the thread of the call answers after the release");
                },
            }
        }
    })
}

/// Reads each byte that `reader` holds, and no more.
///
/// # Specification
/// trivial.
fn drained(reader: &mut UnixStream)
{
    reader
        .set_nonblocking(true)
        .expect("the host makes the other end not wait");
    let mut page = [0_u8; PAGE];
    loop {
        match reader.read(&mut page) {
            Ok(0) => return,
            Ok(_) => {},
            Err(error) if error.kind() == ErrorKind::WouldBlock => return,
            Err(error) => panic!("the other end reads: {error}"),
        }
    }
}

/// The operation and the error number of `refused`.
///
/// # Specification
/// trivial.
fn named(refused: Refused) -> (Operation, ErrorNumber)
{
    (refused.operation(), refused.number())
}

/// A read that waits on a socket with no bytes is refused under the name
/// `read` with `EINTR` when a handled signal arrives, because the crate does
/// not repeat the call. The descriptor stays open: the next read gives the
/// bytes that the other end writes after the signal.
#[test]
fn a_signal_refuses_a_read_that_waits_with_eintr()
{
    handled();
    for subject in &SUBJECTS {
        let name = subject.name;
        let (mut writer, reader) = UnixStream::pair().expect("the host makes a socket pair");
        let descriptor = Descriptor(reader.as_raw_fd());
        let io = started(subject);
        let handle = &io;
        let mut release = writer.try_clone().expect("the host copies the descriptor");
        let first = signalled(
            move || {
                let mut page = [0_u8; PAGE];
                // SAFETY: the place is a live array, and nothing else reads it
                // during the call.
                unsafe { (subject.read)(handle, descriptor, Place::from(page.as_mut_slice())) }
            },
            move || {
                release
                    .write_all(LATER)
                    .expect("the other end ends the wait of the read");
            },
        );
        assert_eq!(
            Err((Operation::Read, EINTR)),
            first.map_err(named),
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

/// A write that waits on a full socket is refused under the name `write` with
/// `EINTR` when a handled signal arrives before the kernel takes a byte,
/// because the crate does not repeat the call. The descriptor stays open:
/// after the other end reads each byte, the next write takes its whole range.
#[test]
fn a_signal_refuses_a_write_that_waits_with_eintr()
{
    handled();
    let sent = [7_u8; PAGE];
    for subject in &SUBJECTS {
        let name = subject.name;
        let (mut writer, mut reader) = UnixStream::pair().expect("the host makes a socket pair");
        writer
            .set_nonblocking(true)
            .expect("the host makes the socket not wait");
        loop {
            match writer.write(&sent) {
                Ok(_) => {},
                Err(error) if error.kind() == ErrorKind::WouldBlock => break,
                Err(error) => panic!("{name}: the host fills the socket: {error}"),
            }
        }
        writer
            .set_nonblocking(false)
            .expect("the host makes the socket wait");
        let descriptor = Descriptor(writer.as_raw_fd());
        let io = started(subject);
        let handle = &io;
        let mut release = reader.try_clone().expect("the host copies the descriptor");
        let first = signalled(
            move || {
                // SAFETY: the range is a live array, and nothing writes it
                // during the call.
                unsafe { (subject.write)(handle, descriptor, Range::from(sent.as_slice())) }
            },
            move || drained(&mut release),
        );
        assert_eq!(
            Err((Operation::Write, EINTR)),
            first.map_err(named),
            "{name}: the interrupted write"
        );
        drained(&mut reader);
        // SAFETY: the range is a live array, and nothing writes it during the
        // call.
        let count = unsafe { (subject.write)(&io, descriptor, Range::from(sent.as_slice())) };
        assert_eq!(
            Ok(Length(PAGE)),
            count,
            "{name}: the write after the signal"
        );
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}
