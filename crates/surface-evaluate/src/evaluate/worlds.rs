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
//! ([`Runs::host`](crate::Runs::host)) runs each migration shipped to a world
//! its bindings bind to its own key; one given no bindings binds every world
//! its entry holds a capability for to its own key (`Program::here`).
//!
//! A migration's code is named by the
//! [`ProgramKey`](gandr_surface_dispatcher::ProgramKey) of the program both
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
//! - **A far run's host is the far host, attenuated to the world's row.** An
//!   operation of a migration's body that no handler inside it answers goes to
//!   the host that runs it, as an entry's operation goes, when its interface is
//!   one the world's requirement row names: its console, network, reals and
//!   entropy. Any other operation reaches no handler, and #3545 refuses it at
//!   check. A nested migration goes where the host's own bindings bind its
//!   world. Nothing of the caller's host crosses. A world's labels have no
//!   handler yet (#6546).
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
//! - `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — lineage: the compilation
//!   ruling, § compilation-recipe-refinements: a deployment binds a world to
//!   the host that serves it and never enters the program's identity, so the
//!   far host answers a migration with its own handler, beside the program.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Store;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::world::Unmigrated;
use gandr_core_term::world::World;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_emitter::Migrated;
use gandr_runtime_emitter::MigrationRequest;
use gandr_runtime_emitter::crossing;
use gandr_runtime_emitter::world;
use gandr_runtime_emitter::world::Attenuated;
use gandr_runtime_net::Answer;
use gandr_runtime_net::Arrival;
use gandr_runtime_net::Configuration;
use gandr_runtime_net::Net;
use gandr_runtime_net::WorldName;
use gandr_storage_values::ChunkCount;
use gandr_storage_values::ValueManifest;
use gandr_surface_dispatcher::Console;
use gandr_surface_dispatcher::Hosted;
use gandr_surface_dispatcher::Line;
use gandr_surface_dispatcher::MigrationCount;
use gandr_surface_dispatcher::Printed;
use gandr_surface_dispatcher::RealsProfile;
use gandr_surface_dispatcher::Worlds;

use super::Machine;
use super::entry::EntryHost;

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
/// - witness: `gandr-surface-dispatcher::tests::run::a_second_migration_of_an_edited_list_fetches_what_changed_3365`
/// - witness: `gandr-surface-dispatcher::tests::run::a_world_bound_to_this_host_runs_here`
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
        let mut chunks = net.chunks();
        request
            .captures
            .iter()
            .map(|&capture| values.commit(capture, params, &mut chunks))
            .collect::<Result<Vec<ValueManifest>, _>>()
    };
    let Ok(captures) = committed
    else {
        return Migrated::Refused(Unmigrated::Unanswered);
    };
    let configuration = Configuration::new(worlds.program.code(request.at), world, captures);
    match net.migrate(peer, &configuration) {
        Ok(Answer::Answered(manifest)) => {
            let answered = values.deref(&manifest, params, &net.chunks());
            answered.map_or(
                Migrated::Refused(Unmigrated::Unanswered),
                Migrated::Answered,
            )
        },
        Ok(Answer::Refused(why)) => Migrated::Refused(why),
        Err(_fault) => Migrated::Refused(Unmigrated::Unreached),
    }
}

impl Machine<'_, '_>
{
    /// Host this program's worlds on `net`: answer each migration shipped to
    /// it until `migrations` are answered, running each whose world `worlds`'
    /// bindings bind to `net`'s key, and print a line for each on `console`.
    ///
    /// # Specification
    /// - requires: `worlds` holds the key of the text this program was composed
    ///   from.
    /// - ensures: each migration answered: run here, its captures fetched over
    ///   its connection unless held whole, each operation its body leaves
    ///   unhandled whose interface its world's row names served as an entry's
    ///   is — `Console.print` on `console`, `Net` on `net`, `Reals` under
    ///   `profile` on tables the migration owns, `Rand` from the entropy source
    ///   — and any other declined, a nested migration sent where `worlds` binds
    ///   its world, and its answer committed to `net`'s chunks, printing, after
    ///   each line the body printed, `ran a migration at <world>, fetching <n>
    ///   chunks`, `n` the chunks its captures' fetches carried; or refused,
    ///   printing `refused a migration at <world>: <reason>` — unheld when its
    ///   code names no migration of this program, unserved when no binding
    ///   binds its world to `net`'s key or the migration names another world,
    ///   unfetched when a capture does not reach this host, unanswered when its
    ///   body answers no value that crosses.
    /// - fails: never; a network fault ends the hosting as [`Hosted::Faulted`].
    /// - panics: none.
    /// - executable: none — the migrations are the askers', across the network.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a host answers two migrations over captures it made
    ///   itself, fetching nothing; the host that takes its place fetches a list
    ///   whole, then only the chunks of its edit, and each prints a line for
    ///   each migration; a host prints on its own console the line a
    ///   migration's body prints.
    /// - witness: `gandr-surface-dispatcher::tests::run::a_second_migration_of_an_edited_list_fetches_what_changed_3365`
    /// - witness: `gandr-surface-dispatcher::tests::run::a_host_prints_the_line_its_migration_prints_3546`
    #[inline]
    pub fn host(
        &self,
        worlds: Worlds<'_>,
        net: &mut Net,
        (migrations, profile): (MigrationCount, RealsProfile),
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
            let answer = self.arrived(
                (worlds, &mut *net),
                &arrival,
                (&mut held, &mut fetched),
                (&mut *console, profile),
            );
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
            answered = MigrationCount::from(usize::from(answered).saturating_add(1));
            match console.print(Line::from(line.as_str())) {
                Printed::Written | Printed::Failed => {},
            }
        }
        Hosted::Answered(answered)
    }

    /// Run `arrival` here, as [`Self::host`] answers it, keeping in `held`
    /// each capture and answer this host holds whole and adding to `fetched`
    /// the chunks its captures' fetches carry; the body's operations go to an
    /// [`EntryHost`] over `console`, `net` and `worlds`, its reals under
    /// `profile`, attenuated to the row of the migration's world.
    ///
    /// # Specification
    /// trivial.
    fn arrived(
        &self,
        (worlds, net): (Worlds<'_>, &mut Net),
        arrival: &Arrival,
        (held, fetched): (&mut Vec<ValueManifest>, &mut ChunkCount),
        (console, profile): (&mut dyn Console, RealsProfile),
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
            let whole = capture.closure(&net.chunks()).is_ok();
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
            let chunks = net.chunks();
            configuration
                .captures()
                .iter()
                .map(|capture| crossing::deref(capture, params, &chunks, &mut store))
                .collect::<Result<Vec<HeapValueId>, _>>()
        };
        let Ok(captures) = captures
        else {
            return Answer::Refused(Unmigrated::Unfetched);
        };
        let unrequired = EffectRow::default();
        let row = match world {
            World::Declared(constant) => self.rows.get(&constant),
            World::Host => None,
        };
        let mut entry = EntryHost::new(
            console,
            Some(&mut *net),
            profile,
            Some((worlds, self.names.as_slice())),
        );
        let answer = match world::arrive(
            (self.arena, self.definitions),
            (at, world),
            gandr_runtime_emitter::budget::bound(),
            (&mut store, &captures),
            &mut Attenuated {
                host: &mut entry,
                row: row.unwrap_or(&unrequired),
            },
        ) {
            Ok(answer) => answer,
            Err(why) => return Answer::Refused(why),
        };
        let committed = crossing::commit(&store, answer, params, &mut net.chunks());
        match committed {
            Ok(manifest) => {
                held.push(manifest);
                Answer::Answered(manifest)
            },
            Err(_uncrossed) => Answer::Refused(Unmigrated::Unanswered),
        }
    }
}
