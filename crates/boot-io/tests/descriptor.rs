//! A file that has the descriptor 0 reads as each other file. The test closes
//! the standard input of the whole process, so this target holds this one test
//! alone.

#[cfg(test)]
mod harness;

#[cfg(test)]
mod zero
{
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
    /// descriptor is no refusal.
    #[test]
    fn with_descriptor_zero_closed_a_file_takes_it_and_reads_whole()
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
            assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
        }
    }
}
