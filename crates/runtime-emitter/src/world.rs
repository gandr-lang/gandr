//! Worlds: where a migration runs, and how what it takes and answers
//! crosses.
//!
//! In this process a migration's body runs at its world over a store of its
//! own, and what crosses between the caller's store
//! and the world's — each capture in, the answer back — crosses by content
//! through a chunk store of that crossing alone, committed then dereferenced
//! ([`crate::crossing`]). A host that binds the world to another process runs
//! the migration there instead ([`crate::HostHandler::migrate`]), and
//! [`arrive`] runs one another host shipped here, under this host's handler.
//!
//! # Boundaries
//!
//! - **A world run here is a fresh store.** The world a migration names picks
//!   no place in one process: each migration the host runs here runs over a
//!   store it starts, on the caller's thread, and nothing its body leaves there
//!   outlives the migration.
//! - **The run's host answers the body.** An operation of the body that no
//!   handler inside the body answers goes to the host of the caller's run, as
//!   an operation of the caller goes. So a draw at a world takes the next bit
//!   of the run's path (#5712). A migration another host shipped here goes to
//!   the handler of the host that runs it, and nothing of the caller's host
//!   crosses (#3546).
//! - **The budget is the caller's.** The body runs on the jumps that the
//!   caller's run has left, under the same origin, so a divergent body stops.
//!   The run does not charge back what the body spends.
//! - **A far run that answers nothing declines.** A body whose run ends stuck
//!   or declined, a value that does not cross, or a host's refusal, declines
//!   the caller's run at the migration: a failing far run is no branch of the
//!   caller's yet.
//! - **A crossing's chunk store is its own.** Each crossing commits into a
//!   chunk store that it starts and derefs from it, on the caller's thread, so
//!   a crossing takes no lock and its chunks go with it. The process keeps no
//!   chunk store that grows with its crossings.
//!
//! # References
//!
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: § 5's
//!   two local memories joined by one content-addressed memory, each world a
//!   local memory and every crossing a commit then a deref through the one.
//! - `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage
//!   programme, § storage-programme-worlds-sessions: a world a locus the host
//!   binds, and a crossing between two a commit at the source then a deref at
//!   the destination.
//! - `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — lineage: the store's single
//!   writer plan, which removes every lock around a chunk store: a crossing's
//!   commit and deref share no store with another crossing.

use alloc::vec::Vec;
use core::num::NonZeroU64;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Store;
use gandr_core_term::effect::EffectLabel;
use gandr_core_term::effect::EffectPresence;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::row::Label;
use gandr_core_term::world::Unmigrated;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::InMemoryChunkStore;

use crate::budget::Budget;
use crate::crossing::CrossingRefusal;
use crate::crossing::commit;
use crate::crossing::deref;
use crate::lower::Lowered;
use crate::lower::lower_suspended;
use crate::run::Choice;
use crate::run::Ran;
use crate::run::RunInputs;
use crate::run::Tier;
use crate::run::lowered_on_with_host;
use crate::run::on_tier;
use crate::seam::HostHandler;
use crate::seam::HostOutcome;
use crate::seam::HostReply;
use crate::seam::HostRequest;
use crate::seam::HostValues;
use crate::seam::Migrated;
use crate::seam::MigrationRequest;
use crate::seam::Offer;
use crate::seam::Spawning;
use crate::seam::TaskOrder;

/// The chunker's expected boundary events per cut a crossing in this process
/// runs under: the constant the codec's own suite reads under.
const KAPPA: NonZeroU64 = match NonZeroU64::new(4) {
    Some(kappa) => kappa,
    None => NonZeroU64::MIN,
};

/// The most tokens a chunk of a crossing in this process holds: the cap the
/// codec's own suite reads under.
const CAP: NonZeroU64 = match NonZeroU64::new(64) {
    Some(cap) => cap,
    None => NonZeroU64::MIN,
};

/// The chunker's constants every crossing between worlds commits and reads
/// under, in this process and between hosts.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn chunking() -> TypedChunkerParams
{
    TypedChunkerParams::new(Kappa::from(KAPPA), TokenCap::from(CAP))
}

/// Run `body` at its world on `tier`, closed over `captures`, values of
/// `store`, and answer its answer laid out in `store`. An operation of the
/// body that no handler inside it answers goes to `offer`, the host of the
/// caller's run.
///
/// # Specification
/// - requires: `body` was lowered from `arena` over `definitions` to run closed
///   over as many captures as `captures` holds, innermost first.
/// - ensures: on success a value freshly laid out in `store`, equal to the
///   value `body` halts with over a fresh store each capture crossed into, its
///   operations offered to `offer`, within `budget`; nothing when a capture or
///   the answer does not cross, or the body's run ends with no value.
/// - executable: none — the answer is observed by running the body.
///
/// # Adequacy
/// - hypothesis: L2 — a pair held twice, answered by a migration on both tiers,
///   reads back as it does in place but as two values where in place it is one:
///   the answer crossed back by content, never handed over by address. L3 — a
///   capture that does not cross declines the run at its migration; a body that
///   performs an operation takes the reply of the caller's host.
/// - witness: `tests::world::a_migration_crosses_its_capture_in_and_its_answer_back`
/// - witness: `tests::world::a_capture_that_does_not_cross_declines_at_its_migration`
/// - witness: `tests::world::a_migrated_body_s_operation_reaches_the_caller_s_host_5712`
#[inline]
pub(crate) fn migrate(
    tier: Tier,
    (arena, definitions, body): (&CommandArena, &Definitions, &Lowered),
    budget: Budget,
    (store, captures): (&mut Store, &[HeapValueId]),
    offer: Option<&mut (dyn Offer + '_)>,
) -> Option<HeapValueId>
{
    let mut there = Store::new();
    let captured = captures
        .iter()
        .map(|&capture| cross(store, capture, &mut there).ok())
        .collect::<Option<Vec<HeapValueId>>>()?;
    let inputs = RunInputs::new(&mut there).closed_over(&captured);
    let ended = match offer {
        Some(offer) => on_tier(
            tier,
            body,
            (arena, definitions),
            budget,
            inputs.offered(offer),
        ),
        None => on_tier(tier, body, (arena, definitions), budget, inputs),
    };
    match ended {
        Ok(Ran::Ended(Outcome::Halted(answer))) => cross(&there, answer, store).ok(),
        Ok(Ran::Ended(Outcome::Stuck(_)) | Ran::Aborted) | Err(_) => None,
    }
}

/// Run here a migration another host shipped to `world`, under `host`.
///
/// The migration at `at` of `arena`, closed over `captures`, values of
/// `store`, runs on the tier the policy picks, and its answer is a value of
/// `store`. `at` is the migration's place in the program that both hosts
/// hold, and the caller reads the shipped captures into a fresh `store`. An
/// operation of the body that no handler inside it answers goes to `host`,
/// the host that runs it, never to the host that shipped it.
/// [`Unmigrated`], of `gandr-core-term`, names why a migration runs nowhere.
///
/// # Specification
/// - requires: `captures` are the values the migration's body binds, in the
///   order its lowering binds them, as the shipping host gathered them.
/// - ensures: on success, the value the body halts with over `store` within
///   `budget`, each operation it leaves unhandled offered to `host`; nothing
///   runs unless `at` is a migration to `world` whose body lowers closed over
///   as many captures as `captures` holds.
/// - fails: [`Unmigrated::Unheld`] when `at` is no migration or its body does
///   not lower over `captures`; [`Unmigrated::Unserved`] when it migrates to
///   another world; [`Unmigrated::Unanswered`] when the run ends stuck,
///   declined or aborted by `host`.
/// - panics: none.
/// - executable: none — the answer is observed by running the body.
///
/// # Errors
/// As the failures above.
///
/// # Adequacy
/// - hypothesis: L3 — a migration of `(x, y)` over two captures answers their
///   pair; the same command named at another world, a command that is no
///   migration, and too few captures each refuse by name before anything runs;
///   a draw in a shipped body takes the reply of the host that runs it, and a
///   host that declines it leaves the migration unanswered.
/// - witness: `tests::world::a_shipped_migration_runs_here_only_as_the_migration_it_names`
/// - witness: `tests::world::a_shipped_body_s_operation_reaches_the_host_that_runs_it_3546`
#[inline]
pub fn arrive<Host>(
    (arena, definitions): (&CommandArena, &Definitions),
    (at, world): (CommandId, World),
    budget: Budget,
    (store, captures): (&mut Store, &[HeapValueId]),
    host: &mut Host,
) -> Result<HeapValueId, Unmigrated>
where
    Host: HostHandler,
{
    let Some(&CommandNode::World {
        form: WorldForm::Migrate { world: to, body },
        ..
    }) = arena.command(at)
    else {
        return Err(Unmigrated::Unheld);
    };
    if to != world {
        return Err(Unmigrated::Unserved);
    }
    let lowered = lower_suspended(arena, definitions, body).map_err(|_form| Unmigrated::Unheld)?;
    if lowered.captures.len() != captures.len() {
        return Err(Unmigrated::Unheld);
    }
    match lowered_on_with_host(
        Choice::Policy,
        &lowered,
        (arena, definitions),
        (budget, RunInputs::new(store).closed_over(captures)),
        host,
    ) {
        Ok(HostOutcome::Completed(Outcome::Halted(answer))) => Ok(answer),
        Ok(HostOutcome::Completed(Outcome::Stuck(_)) | HostOutcome::Aborted(_)) | Err(_) => {
            Err(Unmigrated::Unanswered)
        },
    }
}

/// A host attenuated to a world's row.
///
/// An operation of an interface the row names goes to the host, and every
/// other operation is declined, so the run is stuck at it. A host that runs a
/// migration another host shipped answers the body through one, so the body
/// reaches only the interfaces its world requires (#3546).
#[derive(Debug)]
pub struct Attenuated<'host, Host>
{
    /// The host the row attenuates.
    pub host: &'host mut Host,
    /// The row of the world the run stands at.
    pub row: &'host EffectRow,
}

impl<Host> HostHandler for Attenuated<'_, Host>
where
    Host: HostHandler,
{
    type Abort = Host::Abort;

    /// Hand the operation to the host when the row names its interface, and
    /// decline it otherwise.
    ///
    /// # Specification
    /// - ensures: the host's reply for an operation whose interface the row
    ///   names as its default instance; [`HostReply::Decline`] for any other,
    ///   which the host is never offered.
    /// - executable: none — the reply is the host's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shipped draw under a row that names the entropy
    ///   source takes the host's reply; under a row that names only the
    ///   console, the host is never offered it and the migration answers
    ///   nothing.
    /// - witness: `tests::world::an_operation_outside_its_world_s_row_reaches_no_handler_3546`
    #[inline]
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        let label = EffectLabel::Interface(Label::from(request.signature.name()));
        match self.row.contains(&label) {
            EffectPresence::Present => self.host.handle(request, values),
            EffectPresence::Absent => HostReply::Decline,
        }
    }

    /// Ask the host: a migration is no interface of the row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn migrate(
        &mut self,
        request: MigrationRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> Migrated
    {
        self.host.migrate(request, values)
    }

    /// Ask the host.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn spawning(&mut self) -> Spawning
    {
        self.host.spawning()
    }

    /// Ask the host.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn task_order(&mut self) -> TaskOrder
    {
        self.host.task_order()
    }
}

/// Cross the value `from` binds at `value` into `to`, committed then
/// dereferenced through a chunk store of this crossing alone.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`commit`] and [`deref()`].
pub(crate) fn cross(
    from: &Store,
    value: HeapValueId,
    to: &mut Store,
) -> Result<HeapValueId, CrossingRefusal>
{
    let params = chunking();
    let mut cam = InMemoryChunkStore::new();
    let manifest = commit(from, value, params, &mut cam)?;
    deref(&manifest, params, &cam, to)
}
