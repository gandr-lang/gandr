//! The worlds a run's host binds: its world bindings, each declared world's
//! name bound to the key of the host it runs at, and the migrations it ships
//! to those hosts and takes from them.
//!
//! A host given no bindings runs every migration in its own process. A host
//! given some runs a migration whose world they bind to its own key in its
//! process too, ships one bound to another host over the world wire
//! (`gandr-runtime-net`'s `worlds`), and refuses one they do not bind before
//! anything is sent: the entry of a run is refused
//! [`Unrunnable::UnboundWorld`](super::Unrunnable::UnboundWorld) when it holds
//! a capability for a world no binding names. A host hosting its worlds
//! ([`Program::host`]) runs each migration shipped to a world its bindings
//! bind to its own key.
//!
//! A migration's code is named by the [`ProgramKey`] of the program both
//! hosts hold and the migration's place in it; each capture and the answer
//! cross by content, committed to the network's chunks and fetched over the
//! migration's connection.
//!
//! # Boundaries
//!
//! - **Two processes, one program.** A far host runs only a migration of the
//!   program its own source composes to, which it tells by the program's key;
//!   one of any other program is unheld. Both hosts run one build of `gandr`,
//!   whose focusing places each migration alike.
//! - **A far run has no host.** A migration's body runs at the far host with no
//!   console, network or bindings: one that performs an operation is
//!   unanswered.
//! - **A far host fetches what it lacks.** A capture whose chunks it holds
//!   whole is not fetched, and a fetch names every capture and answer the host
//!   holds as held, so a second migration of an edited value carries only the
//!   chunks the edit changed.
//! - **Every failure declines the caller.** A far host unreached, a refusal,
//!   and an answer that does not cross each decline the caller's run at the
//!   migration, by the reason's name; a failing far run is no branch of the
//!   caller's.
//!
//! # References
//!
//! - `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage
//!   programme, § storage-programme-worlds-sessions: a world a locus the host
//!   binds, and a migration shipped by content and run at the destination.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::str::FromStr;

use anodized::spec;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Store;
use gandr_core_term::world::Unmigrated;
use gandr_core_term::world::World;
use gandr_kernel_term::ConstantIndex;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_emitter::Migrated;
use gandr_runtime_emitter::MigrationRequest;
use gandr_runtime_emitter::crossing;
use gandr_runtime_emitter::world;
use gandr_runtime_net::Answer;
use gandr_runtime_net::Arrival;
use gandr_runtime_net::Code;
use gandr_runtime_net::Configuration;
use gandr_runtime_net::Net;
use gandr_runtime_net::Peer;
use gandr_runtime_net::PeerError;
use gandr_runtime_net::WorldName;
use gandr_storage_values::ChunkCount;
use gandr_storage_values::ValueManifest;
use gandr_surface_syntax::SourceText;

use super::Console;
use super::Line;
use super::Program;
use super::RUN_BUDGET;

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
    fn code(
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
    fn place(
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

/// Decide the migration `request` offers, as a host holding `worlds` and the
/// world names `names` decides it, shipping it on `net` when its world is
/// bound to another host.
///
/// # Specification
/// - requires: `names` are the run's program's names, by admission position.
/// - ensures: [`Migrated::Here`] for the host's own world and for a world the
///   bindings bind to `net`'s key; [`Migrated::Refused`] with
///   [`Unmigrated::UnboundWorld`] for a world no binding names, with nothing
///   sent. A world bound to another host: each capture committed to `net`'s
///   chunks, the configuration shipped, and the answer read back into `values`'
///   store as [`Migrated::Answered`]; a refusal the far host names by its
///   reason, [`Unmigrated::Unreached`] for a network fault or no network, and
///   [`Unmigrated::Unanswered`] for a capture or an answer that does not cross.
/// - fails: never; every failure is a refusal.
/// - panics: none.
/// - executable: none — the answer is the far host's, across the network.
///
/// # Adequacy
/// - hypothesis: L3 — four migrations bound to hosting endpoints answer 42
///   there, as the same run does in one process, two of them over captures; a
///   world bound to this host runs here with no host elsewhere.
/// - witness: `tests::run::a_second_migration_of_an_edited_list_fetches_what_changed_3365`
/// - witness: `tests::run::a_world_bound_to_this_host_runs_here`
pub(super) fn shipped(
    (worlds, names): (Worlds<'_>, &[String]),
    net: Option<&mut Net>,
    request: MigrationRequest<'_>,
    values: &mut HostValues<'_>,
) -> Migrated
{
    let World::Declared(constant) = request.world
    else {
        return Migrated::Here;
    };
    let Some(name) = names.get(usize::from(constant))
    else {
        return Migrated::Refused(Unmigrated::UnboundWorld);
    };
    let world = WorldName::from(name.as_str());
    let Some(peer) = worlds.bindings.peer(&world)
    else {
        return Migrated::Refused(Unmigrated::UnboundWorld);
    };
    let Some(net) = net
    else {
        return Migrated::Refused(Unmigrated::Unreached);
    };
    if peer.id() == net.node_id() {
        return Migrated::Here;
    }
    let params = world::chunking();
    let committed = {
        let mut chunks = net.chunks().lock();
        request
            .captures
            .iter()
            .map(|&capture| values.commit(capture, params, &mut *chunks))
            .collect::<Result<Vec<ValueManifest>, _>>()
    };
    let Ok(captures) = committed
    else {
        return Migrated::Refused(Unmigrated::Unanswered);
    };
    let configuration = Configuration::new(worlds.program.code(request.at), world, captures);
    match net.migrate(peer, &configuration) {
        Ok(Answer::Answered(manifest)) => {
            let answered = values.deref(&manifest, params, &*net.chunks().lock());
            answered.map_or(
                Migrated::Refused(Unmigrated::Unanswered),
                Migrated::Answered,
            )
        },
        Ok(Answer::Refused(why)) => Migrated::Refused(why),
        Err(_fault) => Migrated::Refused(Unmigrated::Unreached),
    }
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

impl Program<'_>
{
    /// Host this program's worlds on `net`: answer each migration shipped to
    /// it until `migrations` are answered, running each whose world `worlds`'
    /// bindings bind to `net`'s key, and print a line for each on `console`.
    ///
    /// # Specification
    /// - requires: `worlds` holds the key of the text this program was composed
    ///   from.
    /// - ensures: each migration answered: run here, its captures fetched over
    ///   its connection unless held whole, and its answer committed to `net`'s
    ///   chunks, printing `ran a migration at <world>, fetching <n> chunks`,
    ///   `n` the chunks its captures' fetches carried; or refused, printing
    ///   `refused a migration at <world>: <reason>` — unheld when its code
    ///   names no migration of this program, unserved when no binding binds its
    ///   world to `net`'s key or the migration names another world, unfetched
    ///   when a capture does not reach this host, unanswered when its body
    ///   answers no value that crosses.
    /// - fails: never; a network fault ends the hosting as [`Hosted::Faulted`].
    /// - panics: none.
    /// - executable: none — the migrations are the askers', across the network.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a host answers two migrations over captures it made
    ///   itself, fetching nothing; the host that takes its place fetches a list
    ///   whole, then only the chunks of its edit, and each prints a line for
    ///   each migration.
    /// - witness: `tests::run::a_second_migration_of_an_edited_list_fetches_what_changed_3365`
    #[inline]
    pub fn host(
        &self,
        worlds: Worlds<'_>,
        net: &mut Net,
        migrations: MigrationCount,
        console: &mut dyn Console,
    ) -> Hosted
    {
        let mut held: Vec<ValueManifest> = Vec::new();
        let mut answered = MigrationCount::default();
        while answered < migrations {
            let arrival = match net.arrive() {
                Ok(arrival) => arrival,
                Err(_fault) => return Hosted::Faulted { answered },
            };
            let mut fetched = ChunkCount::from(0_usize);
            let answer = self.arrived(worlds, net, &arrival, (&mut held, &mut fetched));
            let line = match answer {
                Answer::Answered(_) => format!(
                    "ran a migration at {}, fetching {} chunks",
                    arrival.configuration.world(),
                    usize::from(fetched)
                ),
                Answer::Refused(refusal) => format!(
                    "refused a migration at {}: {refusal}",
                    arrival.configuration.world()
                ),
            };
            if net.answer(arrival.id, &answer).is_err() {
                return Hosted::Faulted { answered };
            }
            answered = MigrationCount(answered.0.saturating_add(1));
            match console.print(Line::from(line.as_str())) {
                super::Printed::Written | super::Printed::Failed => {},
            }
        }
        Hosted::Answered(answered)
    }

    /// Run `arrival` here, as [`Self::host`] answers it, keeping in `held`
    /// each capture and answer this host holds whole and adding to `fetched`
    /// the chunks its captures' fetches carry.
    ///
    /// # Specification
    /// trivial.
    fn arrived(
        &self,
        worlds: Worlds<'_>,
        net: &mut Net,
        arrival: &Arrival,
        (held, fetched): (&mut Vec<ValueManifest>, &mut ChunkCount),
    ) -> Answer
    {
        let configuration = &arrival.configuration;
        let Some(at) = worlds.program.place(configuration.code())
        else {
            return Answer::Refused(Unmigrated::Unheld);
        };
        let served = worlds
            .bindings
            .peer(configuration.world())
            .is_some_and(|peer| peer.id() == net.node_id());
        let Some(world) = self.world_named(configuration.world()).filter(|_| served)
        else {
            return Answer::Refused(Unmigrated::Unserved);
        };
        let params = world::chunking();
        for capture in configuration.captures() {
            let whole = capture.closure(&*net.chunks().lock()).is_ok();
            if !whole {
                match net.fetch_arrived(arrival.id, capture, held) {
                    Ok(carried) => {
                        *fetched = ChunkCount::from(
                            usize::from(*fetched).saturating_add(usize::from(carried.chunks)),
                        );
                    },
                    Err(_fault) => return Answer::Refused(Unmigrated::Unfetched),
                }
            }
            held.push(*capture);
        }
        let mut store = Store::new();
        let captures = {
            let chunks = net.chunks().lock();
            configuration
                .captures()
                .iter()
                .map(|capture| crossing::deref(capture, params, &*chunks, &mut store))
                .collect::<Result<Vec<HeapValueId>, _>>()
        };
        let Ok(captures) = captures
        else {
            return Answer::Refused(Unmigrated::Unfetched);
        };
        let answer = match world::arrive(
            (&self.arena, &self.definitions),
            (at, world),
            Fuel::from(RUN_BUDGET),
            (&mut store, &captures),
        ) {
            Ok(answer) => answer,
            Err(why) => return Answer::Refused(why),
        };
        let committed = crossing::commit(&store, answer, params, &mut *net.chunks().lock());
        match committed {
            Ok(manifest) => {
                held.push(manifest);
                Answer::Answered(manifest)
            },
            Err(_uncrossed) => Answer::Refused(Unmigrated::Unanswered),
        }
    }

    /// The world this program declares under `name`, its last declaration of
    /// that name.
    ///
    /// # Specification
    /// trivial.
    fn world_named(
        &self,
        name: &WorldName,
    ) -> Option<World>
    {
        self.declarations
            .iter()
            .rev()
            .find(|&(_, declared)| declared.name.as_ref() == name.as_ref())
            .map(|(&constant, _)| World::Declared(constant))
    }

    /// The first world the entry holds a capability for that `bindings`
    /// bind to no host.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn unbound(
        &self,
        bindings: &WorldBindings,
    ) -> Option<ConstantIndex>
    {
        self.reaches.iter().copied().find(|&world| {
            self.names
                .get(usize::from(world))
                .is_none_or(|name| bindings.peer(&WorldName::from(name.as_str())).is_none())
        })
    }
}
