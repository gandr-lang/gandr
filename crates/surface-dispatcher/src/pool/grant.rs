//! The host's grant: the tokens that a process runs its parts on.
//!
//! **A worker runs a part only while it holds a token.** The grant is the
//! jobserver of the build tools: a pipe or a FIFO that holds one byte for each
//! token of the host's budget. `CARGO_MAKEFLAGS` or `MAKEFLAGS` names it, as
//! `--jobserver-auth=fifo:<path>` or `--jobserver-auth=<read>,<write>`. Cargo
//! and a gate hand it down to each process that they start. A party reads a
//! token before it hands a part to a worker, and that read does not wait. The
//! worker writes the byte back when the part ends. A party that finds no token
//! runs the part itself. The calling thread runs on the process's own token,
//! which the parent took for the process, as the protocol states.
//!
//! **A party lends its token while it parks.** A party that waits for the
//! parts of its fork writes a token back before it parks. It reads a token
//! again when it wakes. So a parked party holds no token, and a nested fork
//! keeps no part of the budget idle.
//!
//! **No jobserver, no token.** A process that no jobserver bounds runs as
//! before: at the host's count, capped by `-j` or `GANDR_JOBS`. A jobserver
//! that refuses a read leaves each part on the party that forks it.
//!
//! **Two reads for each jobserver.** The grant opens the jobserver's read end
//! twice: once with `O_NONBLOCK` for the read that does not wait, and once
//! without it for the party that waits when it wakes. On Linux, a pipe that the
//! parent hands down by descriptor opens again through `/dev/fd` with a file
//! description of its own. On macOS, that open shares the parent's
//! description, so a read that does not wait would change the parent's pipe.
//! There the grant reads no pipe by descriptor, and the process runs as with no
//! jobserver. A FIFO opens by its path on each host.
//!
//! **Alternatives.** The `jobserver` crate, which cargo and rustc use, reads
//! the environment through an `unsafe` call. It opens no FIFO by a path that
//! the process reads from a file, and its helper thread installs a handler of
//! `SIGUSR1` for the whole process. A token taken for each worker when the
//! pool starts would hold the budget while the worker parks. Reversal: a
//! `jobserver` release that opens a FIFO by its path and reads the environment
//! safely.
//!
//! # References
//!
//! - `vault:01a1d2ce-8890-7cf2-a94b-b73109f5689a` — anchor: the shared pool
//!   page, § pool-tokens: the FIFO of the build tools' protocol beside the
//!   host's counter, with one token for each hand-off, so the build tools and
//!   gandr draw on one budget.

use std::fs::File;
use std::fs::OpenOptions;
use std::io::Read as _;
use std::io::Write as _;
#[cfg(unix)]
use std::os::unix::fs::FileTypeExt as _;
#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt as _;
use std::path::Path;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use super::host::Host;
use super::host::runtime_directory;

quenchant_shape::reason_enum! {
    /// Why no jobserver and no hub's counter bounds a process.
    pub mod ungranted {
        /// The reason the process runs as with no jobserver.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No variable of the environment names a jobserver, and no hub
            /// owns the host's counter.
            Unnamed,
            /// The named jobserver does not open as a pipe or a FIFO.
            Unopened,
            /// The jobserver is a pipe that the parent hands down by
            /// descriptor, and a read that does not wait would change the
            /// parent's pipe.
            Shared,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a take gave no token.
    pub mod untaken {
        /// The reason the party holds no token.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Each token is in use.
            Busy,
            /// The jobserver refused the read.
            Refused,
        }
    }
}

/// What bounds the parts that a process runs at once: the tokens of the
/// host's jobserver or of the hub's counter, or nothing when neither stands.
///
/// # Specification
/// - provides: the tokens that the workers of a pool take, one for each part.
/// - panics: none.
/// - executable: none — the tokens are the jobserver's, which other processes
///   share.
///
/// # Adequacy
/// - hypothesis: L3 — a pool of 16 threads under a jobserver of two tokens runs
///   at most two parts at once, and gives each token back.
/// - witness: `pool::tests::a_granted_pool_runs_as_many_parts_as_it_holds_tokens`
#[derive(Debug)]
#[repr(transparent)]
pub struct Grant(Maybe<Tokens, ungranted::Absent>);

impl Grant
{
    /// The grant that the process's environment names: the jobserver of the
    /// first of `CARGO_MAKEFLAGS`, `MAKEFLAGS` and `MFLAGS` that names one.
    /// With no jobserver named, the host's counter, while a hub owns it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tokens of the named jobserver, when it opens; else the
    ///   tokens of the hub's counter in the runtime directory; else no grant,
    ///   so the process runs as with no jobserver. A jobserver that a parent
    ///   names stands before the hub's counter, since the parent bounds the
    ///   process.
    /// - panics: none.
    /// - executable: none — the answer is the environment's and the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the flags are read as the build tools write them, a
    ///   FIFO that a test makes opens as a jobserver, and a counter that a test
    ///   hub owns takes a joiner.
    /// - witness: `pool::grant::tests::the_flags_name_the_last_jobserver`
    /// - witness: `pool::tests::a_granted_pool_runs_as_many_parts_as_it_holds_tokens`
    /// - witness: `pool::tests::a_hosted_pool_runs_as_many_parts_as_it_holds_tokens`
    #[inline]
    #[must_use]
    pub fn of_process() -> Self
    {
        for name in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
            let Some(flags) = std::env::var_os(name)
            else {
                continue;
            };
            let Some(flags) = flags.to_str()
            else {
                continue;
            };
            if let Maybe::Present(named) = named(Flags::from(flags)) {
                return Self(opened(named));
            }
        }
        Self(hosted(&runtime_directory()))
    }

    /// The grant of the jobserver that a FIFO at `path` holds.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Returns the host's error when the FIFO does not open, or the file at
    /// `path` is no FIFO.
    #[inline]
    pub fn fifo(path: &Path) -> std::io::Result<Self>
    {
        Fifo::open(path).map(|fifo| Self(Maybe::Present(Tokens::Fifo(fifo))))
    }

    /// The grant of the counter in `directory`, while a hub owns it; no grant
    /// otherwise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn hosted(directory: &Path) -> Self
    {
        Self(hosted(directory))
    }

    /// The tokens of the grant, when a jobserver or a hub's counter bounds the
    /// process.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn into_tokens(self) -> Maybe<Tokens, ungranted::Absent>
    {
        self.0
    }
}

impl Default for Grant
{
    /// No grant: the process runs as with no jobserver.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self(Maybe::Absent(ungranted::Absent::Unnamed))
    }
}

/// The tokens of a grant: the jobserver's FIFO or pipe, or the host's counter.
///
/// # Specification
/// - provides: a take with no wait, a take that waits, and a give, on the one
///   source of the grant.
/// - panics: none.
/// - executable: none — other processes share the tokens.
#[derive(Debug)]
pub enum Tokens
{
    /// The jobserver of the build tools.
    Fifo(Fifo),
    /// The host's counter, which a hub owns.
    Host(Host),
}

impl Tokens
{
    /// A token, when one is free, with no wait: as [`Fifo::take_now`] or
    /// [`Host::take_now`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn take_now(&self) -> Maybe<Token, untaken::Absent>
    {
        match *self {
            Self::Fifo(ref fifo) => fifo.take_now(),
            Self::Host(ref host) => host.take_now(),
        }
    }

    /// A token, after a wait for one: as [`Fifo::take`] or [`Host::take`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn take(&self) -> Maybe<Token, untaken::Absent>
    {
        match *self {
            Self::Fifo(ref fifo) => fifo.take(),
            Self::Host(ref host) => host.take(),
        }
    }

    /// Give `token` back: as [`Fifo::give`] or [`Host::give`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn give(
        &self,
        token: Token,
    )
    {
        match *self {
            Self::Fifo(ref fifo) => fifo.give(token),
            Self::Host(ref host) => host.give(token),
        }
    }
}

/// The ends of one jobserver.
///
/// # Specification
/// - provides: a read that does not wait, a read that waits, and a write that
///   gives a token back.
/// - panics: none.
/// - executable: none — the ends are the host's.
#[derive(Debug)]
pub struct Fifo
{
    /// The read end, read without a wait.
    ready: File,
    /// The read end, read with a wait for a token.
    waiting: File,
    /// The write end.
    back: File,
}

/// One token: the byte that the jobserver gave, which goes back unchanged.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Token(u8);

impl Token
{
    /// The token that a party lends while it parks: `+`, the byte that make
    /// writes for a token.
    pub const LENT: Self = Self(b'+');

    /// A token of the host's counter, which carries no byte of its own.
    pub const COUNTED: Self = Self(b'+');
}

/// The bit above a token's byte that marks a stored token, so a stored token
/// is never zero.
const STORED: u16 = 0x100;

/// What a part runs on: a token of the grant, or none, when no jobserver
/// bounds the pool or the part is a trip of the park's measure.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Right
{
    /// A token of the jobserver, which goes back as the part ends.
    Token(Token),
    /// No token.
    Free,
}

impl From<Right> for u16
{
    /// The part's token as a seat stores it: zero for no token, else the
    /// token's byte under the bit that marks a stored token.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(held: Right) -> Self
    {
        match held {
            Right::Token(token) => STORED | Self::from(token.0),
            Right::Free => 0,
        }
    }
}

impl From<u16> for Right
{
    /// The token that a seat stores as `stored`, or none.
    ///
    /// # Specification
    /// - ensures: the token whose store is `stored`, or [`Right::Free`] when
    ///   the bit that marks a stored token is clear.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a token stored and read again is the same byte.
    /// - witness: `pool::grant::tests::a_stored_token_reads_back_unchanged`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Self::Token(token) => stored & STORED != 0 && token.0 == stored.to_le_bytes()[0],
        Self::Free => stored & STORED == 0,
    })]
    fn from(stored: u16) -> Self
    {
        let [byte, held] = stored.to_le_bytes();
        if held == 0 {
            Self::Free
        }
        else {
            Self::Token(Token(byte))
        }
    }
}

impl Fifo
{
    /// The jobserver that a FIFO at `path` holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: three ends of the FIFO, each opened for reads and writes, so
    ///   no open waits for a peer.
    /// - fails: the host's error, or [`std::io::ErrorKind::InvalidInput`] when
    ///   the file at `path` is no FIFO.
    /// - panics: none.
    /// - executable: none — the FIFO is the host's.
    ///
    /// # Errors
    /// Returns the host's error for an open that fails, and
    /// [`std::io::ErrorKind::InvalidInput`] for a file that is no FIFO.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Grant`].
    /// - witness: `pool::tests::a_granted_pool_runs_as_many_parts_as_it_holds_tokens`
    fn open(path: &Path) -> std::io::Result<Self>
    {
        Ok(Self {
            ready: end(path, Opening::Ready)?,
            waiting: end(path, Opening::Both)?,
            back: end(path, Opening::Both)?,
        })
    }

    /// The jobserver whose ends the parent hands down as the descriptors that
    /// `spelled` spells, each opened again through `/dev/fd`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: three ends with descriptions of their own, each a pipe.
    /// - fails: [`std::io::ErrorKind::InvalidInput`] for a spelling of no
    ///   descriptor or a descriptor of no pipe, else the host's error.
    /// - panics: none.
    /// - executable: none — the descriptors are the parent's.
    ///
    /// # Errors
    /// Returns [`std::io::ErrorKind::InvalidInput`] for a spelling of no
    /// descriptor or a descriptor of no pipe, and the host's error for an
    /// open that fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the descriptors that cargo hands down open again as
    ///   the ends of its pipe.
    /// - witness: `pool::grant::tests::a_pipe_handed_down_by_descriptor_opens_again`
    #[cfg(target_os = "linux")]
    fn descriptors(spelled: Descriptors<'_>) -> std::io::Result<Self>
    {
        let invalid = |_| std::io::Error::from(std::io::ErrorKind::InvalidInput);
        // No trait reads a descriptor from the flags' text, so the two
        // spellings are read here, at the one site that opens them.
        let read = spelled.read.parse::<u32>().map_err(invalid)?;
        let write = spelled.write.parse::<u32>().map_err(invalid)?;
        let read = alloc::format!("/dev/fd/{read}");
        let write = alloc::format!("/dev/fd/{write}");
        Ok(Self {
            ready: end(Path::new(&read), Opening::Ready)?,
            waiting: end(Path::new(&read), Opening::Read)?,
            back: end(Path::new(&write), Opening::Write)?,
        })
    }

    /// The jobserver of a pipe that the parent hands down by descriptor: none
    /// off Linux, where a read that does not wait would change the parent's
    /// pipe.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Returns [`std::io::ErrorKind::Unsupported`] always.
    #[cfg(not(target_os = "linux"))]
    fn descriptors(_spelled: Descriptors<'_>) -> std::io::Result<Self>
    {
        Err(std::io::ErrorKind::Unsupported.into())
    }

    /// A token, when one is free, with no wait.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a token that the jobserver gave, or [`untaken::Absent::Busy`]
    ///   when none is free now.
    /// - fails: [`untaken::Absent::Refused`] when the jobserver refuses the
    ///   read.
    /// - panics: none.
    /// - executable: none — the tokens are the jobserver's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Grant`].
    /// - witness: `pool::tests::a_granted_pool_runs_as_many_parts_as_it_holds_tokens`
    #[inline]
    pub fn take_now(&self) -> Maybe<Token, untaken::Absent>
    {
        token(&self.ready)
    }

    /// A token, after a wait for one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a token that the jobserver gave.
    /// - fails: [`untaken::Absent::Refused`] when the jobserver refuses the
    ///   read.
    /// - panics: none.
    /// - executable: none — the tokens are the jobserver's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a party that parks lends its token and takes one
    ///   again, and the jobserver holds each token once the fork ends.
    /// - witness: `pool::tests::a_granted_pool_runs_as_many_parts_as_it_holds_tokens`
    #[inline]
    pub fn take(&self) -> Maybe<Token, untaken::Absent>
    {
        token(&self.waiting)
    }

    /// Give `token` back to the jobserver.
    ///
    /// # Specification
    /// - requires: the token came from this jobserver.
    /// - ensures: the jobserver holds the token again, unless it refuses the
    ///   write.
    /// - panics: none.
    /// - executable: none — the tokens are the jobserver's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Fifo::take`].
    /// - witness: `pool::tests::a_granted_pool_runs_as_many_parts_as_it_holds_tokens`
    #[inline]
    pub fn give(
        &self,
        token: Token,
    )
    {
        // A write that the jobserver refuses loses the token for the host's
        // budget: the process can do nothing more with it.
        drop((&self.back).write_all(&[token.0]));
    }
}

/// How an end of a jobserver opens.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Opening
{
    /// For reads and writes, with no wait on a read.
    Ready,
    /// For reads and writes, with a wait on a read.
    Both,
    /// For reads alone, with a wait on a read.
    #[cfg_attr(
        not(target_os = "linux"),
        expect(dead_code, reason = "only Linux opens a pipe again by descriptor")
    )]
    Read,
    /// For writes alone.
    #[cfg_attr(
        not(target_os = "linux"),
        expect(dead_code, reason = "only Linux opens a pipe again by descriptor")
    )]
    Write,
}

/// The end of the jobserver at `path`, opened as `opening` states.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an end that is a pipe or a FIFO.
/// - fails: the host's error, or [`std::io::ErrorKind::InvalidInput`] for a
///   file that is neither.
/// - panics: none.
/// - executable: none — the file is the host's.
///
/// # Errors
/// Returns the host's error for an open that fails, and
/// [`std::io::ErrorKind::InvalidInput`] for a file that is no pipe or FIFO.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Grant`].
/// - witness: `pool::tests::a_granted_pool_runs_as_many_parts_as_it_holds_tokens`
#[cfg(unix)]
fn end(
    path: &Path,
    opening: Opening,
) -> std::io::Result<File>
{
    let mut options = OpenOptions::new();
    let _opened = match opening {
        Opening::Ready => options
            .read(true)
            .write(true)
            .custom_flags(libc::O_NONBLOCK),
        Opening::Both => options.read(true).write(true),
        Opening::Read => options.read(true),
        Opening::Write => options.write(true),
    };
    let file = options.open(path)?;
    if file.metadata()?.file_type().is_fifo() {
        Ok(file)
    }
    else {
        Err(std::io::ErrorKind::InvalidInput.into())
    }
}

/// The end of a jobserver: none on a host with no FIFO.
///
/// # Specification
/// trivial.
///
/// # Errors
/// Returns [`std::io::ErrorKind::Unsupported`] always.
#[cfg(not(unix))]
fn end(
    _path: &Path,
    _opening: Opening,
) -> std::io::Result<File>
{
    Err(std::io::ErrorKind::Unsupported.into())
}

/// One token read from `end`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the byte read, or [`untaken::Absent::Busy`] when a read that does
///   not wait finds none; a read that a signal ends is tried again.
/// - fails: [`untaken::Absent::Refused`] for an end of file or another error.
/// - panics: none.
/// - executable: none — the byte is the jobserver's.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Grant`].
/// - witness: `pool::tests::a_granted_pool_runs_as_many_parts_as_it_holds_tokens`
fn token(mut end: &File) -> Maybe<Token, untaken::Absent>
{
    let mut byte = [0_u8];
    loop {
        match end.read(&mut byte) {
            Ok(1) => {
                let [read] = byte;
                return Maybe::Present(Token(read));
            },
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {},
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                return Maybe::Absent(untaken::Absent::Busy);
            },
            // An end of file or another error: the jobserver gives no token.
            Ok(_) | Err(_) => return Maybe::Absent(untaken::Absent::Refused),
        }
    }
}

/// The text of a variable of the build tools' flags, as `MAKEFLAGS`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Flags<'text>(&'text str);

impl<'text> From<&'text str> for Flags<'text>
{
    /// The flags that `text` spells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

/// The two descriptors of a pipe as the flags spell them, read end first.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Descriptors<'flags>
{
    /// The spelling of the read end.
    read: &'flags str,
    /// The spelling of the write end.
    write: &'flags str,
}

/// A jobserver as the flags of the build tools name it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Named<'flags>
{
    /// A FIFO at this path.
    Fifo(&'flags Path),
    /// A pipe whose ends are these two descriptors.
    Descriptors(Descriptors<'flags>),
}

/// The jobserver that `flags` names: the last `--jobserver-auth=` or
/// `--jobserver-fds=` argument.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a FIFO for `fifo:<path>`, two descriptors for `<read>,<write>`.
/// - fails: [`ungranted::Absent::Unnamed`] when no argument names a jobserver,
///   and [`ungranted::Absent::Unopened`] for a value of neither form.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — make's spelling, cargo's two spellings, a later argument
///   over an earlier one, flags with none, and a value of neither form.
/// - witness: `pool::grant::tests::the_flags_name_the_last_jobserver`
#[spec(ensures: |ref ret| !matches!(*ret, Maybe::Present(_)) || flags.0.contains("--jobserver-"))]
fn named(flags: Flags<'_>) -> Maybe<Named<'_>, ungranted::Absent>
{
    // No trait splits the flags into words, so the text is read here, at the
    // one site that names the jobserver.
    let value = flags
        .0
        .split_ascii_whitespace()
        .filter_map(|word| {
            word.strip_prefix("--jobserver-auth=")
                .or_else(|| word.strip_prefix("--jobserver-fds="))
        })
        .next_back();
    let Some(value) = value
    else {
        return Maybe::Absent(ungranted::Absent::Unnamed);
    };
    if let Some(path) = value.strip_prefix("fifo:") {
        return Maybe::Present(Named::Fifo(Path::new(path)));
    }
    match value.split_once(',') {
        Some((read, write)) => Maybe::Present(Named::Descriptors(Descriptors { read, write })),
        None => Maybe::Absent(ungranted::Absent::Unopened),
    }
}

/// The tokens of the jobserver that `named` names, when it opens.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the tokens of a FIFO that opens; on Linux, the tokens of a pipe
///   whose descriptors open again through `/dev/fd`.
/// - fails: [`ungranted::Absent::Unopened`] for an end that does not open or is
///   no pipe; [`ungranted::Absent::Shared`] for descriptors off Linux.
/// - panics: none.
/// - executable: none — the answer is the host's.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Grant`].
/// - witness: `pool::tests::a_granted_pool_runs_as_many_parts_as_it_holds_tokens`
fn opened(named: Named<'_>) -> Maybe<Tokens, ungranted::Absent>
{
    let opened = match named {
        Named::Fifo(path) => Fifo::open(path),
        Named::Descriptors(spelled) => Fifo::descriptors(spelled),
    };
    match opened {
        Ok(fifo) => Maybe::Present(Tokens::Fifo(fifo)),
        Err(error) if error.kind() == std::io::ErrorKind::Unsupported => {
            Maybe::Absent(ungranted::Absent::Shared)
        },
        Err(_) => Maybe::Absent(ungranted::Absent::Unopened),
    }
}

/// The tokens of the counter in `directory`, while a hub owns it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the counter's tokens when the process joins it; else
///   [`ungranted::Absent::Unnamed`], as with no jobserver.
/// - panics: none.
/// - executable: none — the hub is another process.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Host::join`].
/// - witness: `pool::tests::a_hosted_pool_runs_as_many_parts_as_it_holds_tokens`
fn hosted(directory: &Path) -> Maybe<Tokens, ungranted::Absent>
{
    match Host::join(directory) {
        Maybe::Present(host) => Maybe::Present(Tokens::Host(host)),
        Maybe::Absent(_) => Maybe::Absent(ungranted::Absent::Unnamed),
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use quenchant_shape::shape::Maybe;

    use super::Descriptors;
    use super::Flags;
    use super::Named;
    use super::Right;
    use super::Token;
    use super::named;
    use super::ungranted;

    #[test]
    fn the_flags_name_the_last_jobserver()
    {
        assert_eq!(
            named(Flags::from("-j8 --jobserver-auth=fifo:/tmp/gate-jobs")),
            Maybe::Present(Named::Fifo(Path::new("/tmp/gate-jobs"))),
            "make's spelling of a FIFO"
        );
        assert_eq!(
            named(Flags::from("-j --jobserver-fds=3,4 --jobserver-auth=3,4")),
            Maybe::Present(Named::Descriptors(Descriptors {
                read: "3",
                write: "4"
            })),
            "cargo's two spellings of one pipe"
        );
        assert_eq!(
            named(Flags::from(
                "--jobserver-auth=5,6 -j2 --jobserver-auth=fifo:/run/pool"
            )),
            Maybe::Present(Named::Fifo(Path::new("/run/pool"))),
            "a later argument stands over an earlier one"
        );
        assert_eq!(
            named(Flags::from("-s -j4")),
            Maybe::Absent(ungranted::Absent::Unnamed),
            "flags that name no jobserver"
        );
        assert_eq!(
            named(Flags::from("--jobserver-auth=sem:gandr")),
            Maybe::Absent(ungranted::Absent::Unopened),
            "a semaphore, the form of Windows, opens on no host here"
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn a_pipe_handed_down_by_descriptor_opens_again()
    {
        use std::os::fd::AsRawFd as _;

        use super::Fifo;
        use super::untaken;

        let (read, write) = std::io::pipe().unwrap();
        let read = read.as_raw_fd().to_string();
        let write = write.as_raw_fd().to_string();
        let tokens = Fifo::descriptors(Descriptors {
            read: &read,
            write: &write,
        })
        .unwrap();
        tokens.give(Token(b'x'));
        assert_eq!(
            tokens.take_now(),
            Maybe::Present(Token(b'x')),
            "the token written through one end reads back through the other"
        );
        assert_eq!(
            tokens.take_now(),
            Maybe::Absent(untaken::Absent::Busy),
            "an empty pipe gives no token and does not wait"
        );
        assert_eq!(
            Fifo::descriptors(Descriptors {
                read: "three",
                write: &write,
            })
            .map(drop)
            .map_err(|error| error.kind()),
            Err(std::io::ErrorKind::InvalidInput),
            "a spelling of no descriptor opens nothing"
        );
    }

    #[test]
    fn a_stored_token_reads_back_unchanged()
    {
        for byte in [0_u8, b'+', b'|', u8::MAX] {
            assert_eq!(
                Right::from(u16::from(Right::Token(Token(byte)))),
                Right::Token(Token(byte)),
                "the byte {byte} goes back unchanged"
            );
        }
        assert_eq!(
            Right::from(u16::from(Right::Free)),
            Right::Free,
            "zero stores no token"
        );
    }
}
