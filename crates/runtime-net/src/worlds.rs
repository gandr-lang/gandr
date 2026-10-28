//! The world wire: a migration shipped to the host its world is bound to,
//! run there, and its answer returned, on one connection under
//! [`WORLDS_ALPN`].
//!
//! The asker sends the migration's [`Configuration`] — the bytes naming the
//! code it runs, the world it names, and the manifest of each capture — and
//! finishes its side. The far host fetches each capture's chunks it lacks
//! from the asker over the same connection, as the chunk wire fetches, runs
//! the code, commits its answer, and answers with the answer's manifest or
//! with the [`Refusal`] that ran nothing. The asker then fetches the answer's
//! chunks over the connection, naming its captures held, and closes it:
//!
//! ```text
//! configuration := part(code) part(world) part(capture)*
//! answer        := part(ANSWERED) part(manifest) | part(refusal)
//! ```
//!
//! # Boundaries
//!
//! - **Code is the far host's to read.** The wire carries the bytes naming the
//!   code; that both hosts read them as one body rests on both holding one
//!   program.
//! - **The far host never dials the asker.** Every fetch rides the connection
//!   the configuration came on, so an asker needs no address its far host can
//!   reach.
//! - **One migration a connection.** Each migration dials afresh, and its
//!   connection closes once the answer's chunks are held.
//! - **The asker waits for the answer.** Its thread waits however long the far
//!   run takes; a far host that never answers holds it until either endpoint
//!   closes.
//!
//! # References
//!
//! - `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage
//!   programme, § storage-programme-worlds-sessions: a migration ships its
//!   configuration by content and its answer crosses back the same way.

use core::fmt;

use anodized::spec;
use gandr_storage_values::ValueManifest;

use crate::chunks::Framed;
use crate::chunks::Malformed;
use crate::chunks::Part;
use crate::chunks::Parts;
use crate::endpoint::Fault;
use crate::peer::NodeId;

/// The protocol name a host takes migrations under, offered beside
/// [`ALPN`](crate::ALPN) by every endpoint.
pub const WORLDS_ALPN: &[u8] = b"gandr/worlds/0";

/// The tag an answer carrying a value's manifest opens with.
const ANSWERED: u8 = 0;

/// The tag of [`Refusal::Unheld`].
const UNHELD: u8 = 1;

/// The tag of [`Refusal::Unserved`].
const UNSERVED: u8 = 2;

/// The tag of [`Refusal::Unfetched`].
const UNFETCHED: u8 = 3;

/// The tag of [`Refusal::Unanswered`].
const UNANSWERED: u8 = 4;

/// The bytes naming the code a migration runs, which only the far host reads.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Code(Vec<u8>);

impl From<Vec<u8>> for Code
{
    /// The code `bytes` name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for Code
{
    /// The bytes, borrowed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// A world's name, as its declaration spells it.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct WorldName(String);

impl From<&str> for WorldName
{
    /// The world `name` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(String::from(name))
    }
}

impl AsRef<str> for WorldName
{
    /// The name, borrowed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for WorldName
{
    /// The name as its declaration spells it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// A migration as the wire carries it: the code it runs, the world it names,
/// and each capture by the manifest it was committed under, in the order the
/// code binds them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Configuration
{
    /// The code.
    code: Code,
    /// The world.
    world: WorldName,
    /// The captures, by content.
    captures: Vec<ValueManifest>,
}

impl Configuration
{
    /// The migration of `code` to `world` over `captures`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        code: Code,
        world: WorldName,
        captures: Vec<ValueManifest>,
    ) -> Self
    {
        Self {
            code,
            world,
            captures,
        }
    }

    /// The code the migration runs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn code(&self) -> &Code
    {
        &self.code
    }

    /// The world the migration names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn world(&self) -> &WorldName
    {
        &self.world
    }

    /// Each capture's manifest, in the order the code binds them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn captures(&self) -> &[ValueManifest]
    {
        &self.captures
    }

    /// The configuration framed as the wire carries it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, a part for the code, one for the world's name,
    ///   then one for each capture's manifest image, in order.
    /// - fails: [`Fault::Oversized`] for a code, a name or an image longer than
    ///   a part.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Fault::Oversized`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a configuration of two captures reads back equal at
    ///   the far end, and its migration runs there.
    /// - witness: `tests::worlds::a_migration_runs_at_the_far_host_and_its_answer_comes_back`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |framed| Parts(framed.as_ref()).count() == self.captures.len().saturating_add(2)))]
    pub(super) fn framed(&self) -> Result<Framed, Fault>
    {
        let mut framed = Framed::default();
        framed.push(&[Part(self.code.as_ref())])?;
        framed.push(&[Part(self.world.0.as_bytes())])?;
        for capture in &self.captures {
            let image = capture.encode();
            framed.push(&[Part(image.as_ref())])?;
        }
        Ok(framed)
    }

    /// The configuration `framed` carries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, the configuration whose [`Self::framed`] is
    ///   `framed`.
    /// - fails: [`Malformed`] for bytes that do not frame, a world's name that
    ///   is not UTF-8, or a capture that does not decode.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Malformed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a framed configuration reads back equal; an unframed
    ///   one closes its connection unanswered.
    /// - witness: `tests::worlds::a_migration_runs_at_the_far_host_and_its_answer_comes_back`
    /// - witness: `tests::worlds::a_configuration_that_does_not_frame_is_never_offered`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |read| read.framed().is_ok_and(|again| again == *framed)))]
    pub(super) fn read(framed: &Framed) -> Result<Self, Malformed>
    {
        let mut parts = Parts(framed.as_ref());
        let code = parts.next().ok_or(Malformed)??;
        let world = parts.next().ok_or(Malformed)??;
        let world = core::str::from_utf8(world.0).map_err(|_unreadable| Malformed)?;
        let captures = parts
            .map(|part| {
                let part = part?;
                ValueManifest::decode(part.manifest()).map_err(|_undecoded| Malformed)
            })
            .collect::<Result<Vec<ValueManifest>, Malformed>>()?;
        Ok(Self {
            code: Code(code.0.to_vec()),
            world: WorldName::from(world),
            captures,
        })
    }
}

/// Why a far host ran no migration.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Refusal
{
    /// The host holds no code the configuration names.
    Unheld,
    /// The host does not stand at the world the configuration names.
    Unserved,
    /// A capture's chunks did not reach the host whole.
    Unfetched,
    /// The run answered no value, or its answer did not cross.
    Unanswered,
}

impl fmt::Display for Refusal
{
    /// Why the far host ran nothing, in a sentence fragment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Unheld => "the far host holds no code the migration names",
            Self::Unserved => "the far host does not stand at the world",
            Self::Unfetched => "a capture did not reach the far host whole",
            Self::Unanswered => "the far run answered no value that crosses",
        })
    }
}

/// What a far host answered a migration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Answer
{
    /// The run's answer, by the manifest the far host committed it under.
    Answered(ValueManifest),
    /// Why it ran nothing.
    Refused(Refusal),
}

impl Answer
{
    /// The answer framed as the wire carries it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, one part holding the answer's tag, then the
    ///   manifest's image for an answered value.
    /// - fails: [`Fault::Oversized`] for a manifest image longer than a part.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Fault::Oversized`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an answered value and a refusal read back equal at
    ///   the asker.
    /// - witness: `tests::worlds::a_migration_runs_at_the_far_host_and_its_answer_comes_back`
    /// - witness: `tests::worlds::a_refusal_crosses_back_and_nothing_is_fetched`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |framed| Parts(framed.as_ref()).count() == match *self {
        Self::Answered(_) => 2,
        Self::Refused(_) => 1,
    }))]
    pub(super) fn framed(&self) -> Result<Framed, Fault>
    {
        let mut framed = Framed::default();
        let tag = match *self {
            Self::Answered(_) => ANSWERED,
            Self::Refused(Refusal::Unheld) => UNHELD,
            Self::Refused(Refusal::Unserved) => UNSERVED,
            Self::Refused(Refusal::Unfetched) => UNFETCHED,
            Self::Refused(Refusal::Unanswered) => UNANSWERED,
        };
        framed.push(&[Part(&[tag])])?;
        if let Self::Answered(manifest) = *self {
            let image = manifest.encode();
            framed.push(&[Part(image.as_ref())])?;
        }
        Ok(framed)
    }

    /// The answer `framed` carries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, the answer whose [`Self::framed`] is `framed`.
    /// - fails: [`Malformed`] for bytes that do not frame, a tag no answer
    ///   carries, a manifest that does not decode, or a part past the answer.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Malformed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::framed`].
    /// - witness: `tests::worlds::a_migration_runs_at_the_far_host_and_its_answer_comes_back`
    /// - witness: `tests::worlds::a_refusal_crosses_back_and_nothing_is_fetched`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |read| read.framed().is_ok_and(|again| again == *framed)))]
    pub(super) fn read(framed: &Framed) -> Result<Self, Malformed>
    {
        let mut parts = Parts(framed.as_ref());
        let tag = parts.next().ok_or(Malformed)??;
        let answer = match *tag.0 {
            [ANSWERED] => {
                let manifest = parts.next().ok_or(Malformed)??;
                Self::Answered(
                    ValueManifest::decode(manifest.manifest()).map_err(|_undecoded| Malformed)?,
                )
            },
            [UNHELD] => Self::Refused(Refusal::Unheld),
            [UNSERVED] => Self::Refused(Refusal::Unserved),
            [UNFETCHED] => Self::Refused(Refusal::Unfetched),
            [UNANSWERED] => Self::Refused(Refusal::Unanswered),
            _ => return Err(Malformed),
        };
        match parts.next() {
            None => Ok(answer),
            Some(_) => Err(Malformed),
        }
    }
}

/// A migration an endpoint holds until its owner answers it, by the name it
/// minted.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ArrivalId(u64);

impl From<u64> for ArrivalId
{
    /// The arrival named `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: u64) -> Self
    {
        Self(name)
    }
}

impl fmt::Display for ArrivalId
{
    /// The arrival's name in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "arrival {}", self.0)
    }
}

/// A migration that reached this endpoint: the key its asker proved, its
/// configuration, and the name the endpoint holds it by until answered.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Arrival
{
    /// The asker.
    pub from: NodeId,
    /// What it asked to run.
    pub configuration: Configuration,
    /// The name the endpoint holds the migration by.
    pub id: ArrivalId,
}
