//! The line of the standard console on Linux x86-64: a line and its newline
//! to a descriptor, by the system call of the IO core of the bootstrap. A
//! socket of the host's `std` is the descriptor, and the oracle of the bytes.

#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use core::ffi::c_int;
use core::time::Duration;
use std::io::ErrorKind;
use std::io::Read as _;
use std::io::Write as _;
use std::os::fd::AsRawFd as _;
use std::os::fd::FromRawFd as _;
use std::os::fd::IntoRawFd as _;
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::sync::mpsc;

use gandr_boot_io::Descriptor;
use gandr_surface_dispatcher::Line;
use gandr_surface_dispatcher::Printed;
use gandr_surface_dispatcher::fixture::line_to;
use nix::sys::pthread::pthread_kill;
use nix::sys::pthread::pthread_self;
use nix::sys::signal::SaFlags;
use nix::sys::signal::SigAction;
use nix::sys::signal::SigHandler;
use nix::sys::signal::SigSet;
use nix::sys::signal::Signal;
use nix::sys::signal::sigaction;

/// The bytes of one page, the step of a fill.
const PAGE: usize = 4096;

/// The signals that the witness of an interrupt sends.
const SIGNALS: usize = 20;

/// The time between two signals.
const PAUSE: Duration = Duration::from_millis(1);

/// The handler of the signal. It does nothing: its run alone ends the wait of
/// the call.
///
/// # Specification
/// trivial.
extern "C" fn nothing(_signal: c_int)
{
}

/// A line reaches its descriptor with one newline after it.
#[test]
fn a_line_reaches_its_descriptor_with_its_newline()
{
    let (writer, mut reader) = UnixStream::pair().expect("the host makes a socket pair");
    assert_eq!(
        Printed::Written,
        line_to(Descriptor(writer.as_raw_fd()), Line::from("hello, world!")),
        "the line"
    );
    drop(writer);
    let mut received = String::new();
    reader
        .read_to_string(&mut received)
        .expect("the other end reads the line");
    assert_eq!("hello, world!\n", received, "the bytes at the other end");
}

/// A line longer than a page, which goes in a call of its own, reaches its
/// descriptor whole, with its newline after it.
#[test]
fn a_line_longer_than_a_page_reaches_its_descriptor_whole()
{
    let line = "gandr ".repeat(16 * PAGE);
    let (writer, mut reader) = UnixStream::pair().expect("the host makes a socket pair");
    let received = std::thread::scope(|scope| {
        let other_end = scope.spawn(move || {
            let mut received = String::new();
            reader
                .read_to_string(&mut received)
                .expect("the other end reads the line");
            received
        });
        assert_eq!(
            Printed::Written,
            line_to(Descriptor(writer.as_raw_fd()), Line::from(line.as_str())),
            "the line"
        );
        drop(writer);
        other_end.join().expect("the other end reads to the end")
    });
    assert!(
        received.strip_suffix('\n') == Some(line.as_str()),
        "the line and its newline at the other end"
    );
}

/// A line to a descriptor that the process does not hold is written, as
/// `std` takes a write to a closed standard stream: a run with a closed
/// standard output does not stop at its first line.
#[test]
fn a_line_to_a_closed_descriptor_is_written_as_std_writes_it()
{
    let (writer, _reader) = UnixStream::pair().expect("the host makes a socket pair");
    let number = writer.into_raw_fd();
    // SAFETY: the number is the descriptor of the socket that `into_raw_fd`
    // gave up, and no other value of the process owns it.
    drop(unsafe { OwnedFd::from_raw_fd(number) });
    assert_eq!(
        Printed::Written,
        line_to(Descriptor(number), Line::from("lost")),
        "the line to a closed descriptor"
    );
}

/// A line to a socket whose other end is gone fails, as the write of `std`
/// to a pipe with no reader does.
#[test]
fn a_line_whose_reader_is_gone_fails()
{
    let (writer, reader) = UnixStream::pair().expect("the host makes a socket pair");
    drop(reader);
    assert_eq!(
        Printed::Failed,
        line_to(Descriptor(writer.as_raw_fd()), Line::from("lost")),
        "the line with no reader"
    );
}

/// Signals with no restart, sent while a line waits on a full socket, leave
/// the line whole: the console makes an interrupted call again and gives the
/// rest of a short write. After the other end reads, the line arrives with its
/// newline after the bytes that filled the socket.
#[test]
fn signals_while_a_line_waits_leave_the_line_whole()
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
    let (mut writer, mut reader) = UnixStream::pair().expect("the host makes a socket pair");
    writer
        .set_nonblocking(true)
        .expect("the host makes the socket not wait");
    let fill = [7_u8; PAGE];
    let mut filled = 0_usize;
    loop {
        match writer.write(&fill) {
            Ok(count) => filled = filled.saturating_add(count),
            Err(error) if error.kind() == ErrorKind::WouldBlock => break,
            Err(error) => panic!("the host fills the socket: {error}"),
        }
    }
    writer
        .set_nonblocking(false)
        .expect("the host makes the socket wait");
    let line = "gandr ".repeat(100);
    let descriptor = Descriptor(writer.as_raw_fd());
    let (printed, received) = std::thread::scope(|scope| {
        let (thread_sender, thread_receiver) = mpsc::channel();
        let text = line.as_str();
        let caller = scope.spawn(move || {
            thread_sender
                .send(pthread_self())
                .expect("the main thread waits for the name of the thread");
            line_to(descriptor, Line::from(text))
        });
        let thread = thread_receiver
            .recv()
            .expect("the thread of the line gives its name");
        for _ in 0 .. SIGNALS {
            pthread_kill(thread, Signal::SIGUSR1).expect("the host signals the thread");
            std::thread::sleep(PAUSE);
        }
        let mut received = vec![0_u8; filled.saturating_add(line.len()).saturating_add(1)];
        reader
            .read_exact(&mut received)
            .expect("the other end reads the fill and the line");
        (
            caller.join().expect("the thread of the line answers"),
            received,
        )
    });
    assert_eq!(Printed::Written, printed, "the line under signals");
    let mut expected = line.into_bytes();
    expected.push(b'\n');
    assert_eq!(
        Some(expected.as_slice()),
        received.get(filled ..),
        "the line and its newline after the fill"
    );
}
