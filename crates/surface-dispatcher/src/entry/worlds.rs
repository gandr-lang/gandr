//! The worlds that a run's host binds: its world bindings, the key of the
//! program that both hosts of a migration hold, and the count of the
//! migrations that it answers.
//!
//! The run stage ships and hosts the migrations (`evaluate::worlds`). The
//! driver reads a binding from `--world`, and the script gives the bindings to
//! a run, so these types stay below the run stage.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::str::FromStr;

use anodized::spec;
use gandr_core_sequent::CommandId;
use gandr_runtime_net::Code;
use gandr_runtime_net::Peer;
use gandr_runtime_net::PeerError;
use gandr_runtime_net::WorldName;
use gandr_surface_syntax::SourceText;

/// The bytes of a program's key.
const KEY_BYTES: usize = 32_usize;

/// The bytes of a migration's place in its program.
const PLACE_BYTES: usize = 4_usize;

/// A world's name bound to the host it runs at, as the driver's `--world`
/// spells it: `<world>=<key>@<ip:port>`.
#[derive(Clone, Debug)]
pub struct WorldBinding
{
    /// The world.
    world: WorldName,
    /// The host.
    peer: Peer,
}

impl FromStr for WorldBinding
{
    type Err = WorldBindingError;

    /// The binding `text` spells: a world's name, `=`, and a peer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the world named before the first `=` bound to the peer
    ///   spelled after it.
    /// - fails: [`WorldBindingError`] for text with no `=`, an empty name, or a
    ///   peer that does not parse.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WorldBindingError`], naming what refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the driver's two-process case binds `seat` to the
    ///   hosting process's key and socket, and an unbound world is refused.
    /// - witness: `tests::run::a_world_binding_reads_its_name_and_its_peer`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |binding| text.starts_with(binding.world.as_ref())))]
    #[inline]
    fn from_str(text: &str) -> Result<Self, WorldBindingError>
    {
        let Some((world, peer)) = text.split_once('=')
        else {
            return Err(WorldBindingError::Unbound(String::from(text)));
        };
        if world.is_empty() {
            return Err(WorldBindingError::Unnamed(String::from(text)));
        }
        let peer = Peer::from_str(peer).map_err(WorldBindingError::Peer)?;
        Ok(Self {
            world: WorldName::from(world),
            peer,
        })
    }
}

/// Why a world's binding did not read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WorldBindingError
{
    /// No `=` binds the name to a peer.
    Unbound(String),
    /// Nothing names the world before the `=`.
    Unnamed(String),
    /// The peer after the `=` did not parse.
    Peer(PeerError),
}

impl fmt::Display for WorldBindingError
{
    /// What refused, and the spelling that reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unbound(ref text) => {
                write!(f, "`{text}` binds no peer: `<world>=<key>@<ip:port>`")
            },
            Self::Unnamed(ref text) => {
                write!(f, "`{text}` names no world: `<world>=<key>@<ip:port>`")
            },
            Self::Peer(ref refused) => write!(f, "the peer did not read: {refused}"),
        }
    }
}

impl core::error::Error for WorldBindingError
{
}

/// A host's world bindings: each world it binds, by name, to the host it runs
/// at.
#[derive(Clone, Debug, Default)]
#[repr(transparent)]
pub struct WorldBindings(BTreeMap<WorldName, Peer>);

impl WorldBindings
{
    /// The world bindings `bindings` make; a world bound twice keeps its last
    /// host.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(bindings: Vec<WorldBinding>) -> Self
    {
        Self(
            bindings
                .into_iter()
                .map(|binding| (binding.world, binding.peer))
                .collect(),
        )
    }

    /// The host `world` is bound to, if a binding names it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn peer(
        &self,
        world: &WorldName,
    ) -> Option<&Peer>
    {
        self.0.get(world)
    }
}

impl FromIterator<(WorldName, Peer)> for WorldBindings
{
    /// The world bindings `iter` makes, each world to its host; a world bound
    /// twice keeps its last host.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_iter<Bindings>(iter: Bindings) -> Self
    where
        Bindings: IntoIterator<Item = (WorldName, Peer)>,
    {
        Self(iter.into_iter().collect())
    }
}

/// The key of a program both hosts of a migration hold: the BLAKE3 digest of
/// the text its source composes to.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct ProgramKey([u8; KEY_BYTES]);

impl ProgramKey
{
    /// The key of the program `text` composes to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of(text: SourceText<'_>) -> Self
    {
        Self(*blake3::hash(text.as_ref().as_bytes()).as_bytes())
    }

    /// The code naming the migration at `at` of this program: the key, then
    /// the migration's place, little-endian.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn code(
        self,
        at: CommandId,
    ) -> Code
    {
        let mut bytes = Vec::with_capacity(KEY_BYTES.saturating_add(PLACE_BYTES));
        bytes.extend_from_slice(&self.0);
        bytes.extend_from_slice(&u32::from(at).to_le_bytes());
        Code::from(bytes)
    }

    /// The migration `code` names, when it names one of this program.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn place(
        self,
        code: &Code,
    ) -> Option<CommandId>
    {
        let (key, place) = code.as_ref().split_first_chunk::<KEY_BYTES>()?;
        let place = <[u8; PLACE_BYTES]>::try_from(place).ok()?;
        (*key == self.0).then(|| CommandId::from(u32::from_le_bytes(place)))
    }
}

/// What a host with world bindings holds: the bindings, and the key of the
/// program it runs.
#[derive(Clone, Copy, Debug)]
pub struct Worlds<'host>
{
    /// The world bindings.
    pub bindings: &'host WorldBindings,
    /// The program's key.
    pub program: ProgramKey,
}

/// What hosting a program's worlds came to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Hosted
{
    /// Every migration asked for was answered, ran or refused.
    Answered(MigrationCount),
    /// The network failed before then.
    Faulted
    {
        /// The migrations answered first.
        answered: MigrationCount,
    },
}

/// How many migrations a host answered.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MigrationCount(usize);

impl From<usize> for MigrationCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<MigrationCount> for usize
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: MigrationCount) -> Self
    {
        count.0
    }
}
