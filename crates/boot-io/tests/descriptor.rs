//! A file that has the descriptor 0 reads as each other file, and a socket
//! that has it takes a write as each other socket. The test closes the
//! standard input of the whole process, so this target holds this one test
//! alone.
//!
//! The test calls the system calls of Linux on x86-64. On each other target
//! this test target is empty.

#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

#[cfg(test)]
mod harness;

#[cfg(test)]
mod zero
{
    use std::io::Read as _;
    use std::os::fd::AsRawFd as _;
    use std::os::unix::net::UnixStream;

    use gandr_boot_core::Length;
    use gandr_boot_core::Range;
    use gandr_boot_io::Descriptor;

    use crate::harness::Path;
    use crate::harness::SUBJECTS;
    use crate::harness::Text;
    use crate::harness::Whole;
    use crate::harness::opened;
    use crate::harness::read_whole;
    use crate::harness::started;

    /// With descriptor 0 closed, the kernel gives the next file the number 0.
    /// Each subject opens that file, reads it whole, closes it and stops. The
    /// bytes equal the bytes that the host reads, so the word 0 of a
    /// descriptor is no refusal. After the close, the kernel gives 0 to one
    /// end of a socket, and a write to it reaches the other end.
    #[test]
    fn with_descriptor_zero_closed_a_file_takes_it_and_reads_whole_and_a_socket_takes_a_write()
    {
        use std::os::fd::FromRawFd as _;
        use std::os::fd::OwnedFd;
        let text = concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml");
        let expected = std::fs::read(text).expect("the host reads the manifest of the crate");
        let path = Path::new(Text(text));
        // SAFETY: descriptor 0 is the standard input, and no other value of the
        // process owns it. The drop closes it; a descriptor 0 that is not open
        // gives a close that refuses, which the drop ignores.
        drop(unsafe { OwnedFd::from_raw_fd(0) });
        for subject in &SUBJECTS {
            let name = subject.name;
            let io = started(subject);
            let descriptor = opened(subject, &io, &path);
            assert_eq!(Descriptor(0), descriptor, "{name}: the descriptor");
            let Whole(whole) = read_whole(subject, &io, descriptor);
            assert_eq!(expected, whole, "{name}: the bytes of the file");
            assert_eq!(Ok(()), (subject.close)(&io, descriptor), "{name}: close");
            let (writer, mut reader) = UnixStream::pair().expect("the host makes a socket pair");
            assert_eq!(
                Descriptor(0),
                Descriptor(writer.as_raw_fd()),
                "{name}: the descriptor of the socket"
            );
            // SAFETY: the range is a live vector, and nothing writes it during
            // the call.
            let count =
                unsafe { (subject.write)(&io, Descriptor(0), Range::from(expected.as_slice())) };
            assert_eq!(
                Ok(Length(expected.len())),
                count,
                "{name}: the count of the write"
            );
            let mut received = vec![0_u8; expected.len()];
            reader
                .read_exact(&mut received)
                .expect("the other end reads the bytes of the write");
            assert_eq!(expected, received, "{name}: the bytes at the other end");
            assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
        }
    }
}
