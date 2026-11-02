//! The running build: the identity a hub's socket and a save's checkpoints
//! are keyed by.
//!
//! Two builds of the driver judge differently, so nothing one judged or
//! serves may reach a client of the other. The identity that keeps them
//! apart is the BLAKE3 digest of the running executable's bytes, read once
//! per process. A save keys the checkpoints it keeps by it, and the hub's
//! socket is named by it beside the workspace, so a client reaches only a
//! hub of its own build.

use std::sync::OnceLock;

use gandr_core_incremental::BackendArtifact;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why the running build has no identity.
    pub mod unidentified {
        /// The reason none is known.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The platform does not say where the executable is.
            Unlocated,
            /// The executable could not be read.
            Unread,
        }
    }
}

impl core::fmt::Display for unidentified::Absent
{
    /// Writes why the running build has no identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::Unlocated => "the running executable cannot be located",
            Self::Unread => "the running executable cannot be read",
        })
    }
}

/// The identity of one build: the BLAKE3 digest of its executable.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Build(pub [u8; 32]);

impl From<Build> for BackendArtifact
{
    /// The checkpoint key of what `build` judged: the digest of its identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(build: Build) -> Self
    {
        Self::from(build.0.as_slice())
    }
}

/// The identity of the running build, read once per process.
static RUNNING: OnceLock<Maybe<Build, unidentified::Absent>> = OnceLock::new();

/// The identity of the running build, read the first time it is asked for.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the same answer on every call in a process; the digest of the
///   bytes of the executable the process runs when it can be read.
/// - provides: `unidentified::Absent` naming why it cannot.
/// - panics: none.
/// - executable: none — restating the digest rereads the whole executable.
///
/// # Adequacy
/// - hypothesis: L3 — a set a save keyed by it restores in the same build, and
///   a record keyed by another identity is pruned.
/// - witness: `server::tests::a_saved_copy_reopens_adopting_what_the_save_judged_1816`
/// - witness: `server::tests::a_save_prunes_what_another_build_judged_1816`
#[inline]
pub fn running() -> Maybe<Build, unidentified::Absent>
{
    *RUNNING.get_or_init(|| {
        let Ok(path) = std::env::current_exe()
        else {
            return Maybe::Absent(unidentified::Absent::Unlocated);
        };
        let Ok(mut file) = std::fs::File::open(path)
        else {
            return Maybe::Absent(unidentified::Absent::Unread);
        };
        let mut hasher = blake3::Hasher::new();
        let mut buffer = alloc::vec![0_u8; 1 << 16];
        loop {
            match std::io::Read::read(&mut file, &mut buffer) {
                Ok(0) => break,
                Ok(read) => {
                    let _hashed = hasher.update(buffer.get(.. read).unwrap_or_default());
                },
                Err(ref error) if error.kind() == std::io::ErrorKind::Interrupted => {},
                Err(_error) => return Maybe::Absent(unidentified::Absent::Unread),
            }
        }
        Maybe::Present(Build(*hasher.finalize().as_bytes()))
    })
}
