//! Worlds: where a migration runs, and how what it takes and answers
//! crosses.
//!
//! In this process a migration's body runs at its world over a store of its
//! own, and what crosses between the caller's store
//! and the world's — each capture in, the answer back — crosses by content
//! through the one chunk store the process holds, committed then dereferenced
//! ([`crate::crossing`]). A host that binds the world to another process runs
//! the migration there instead ([`crate::HostHandler::migrate`]), and
//! [`arrive`] runs one another host shipped here.
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
//!   of the run's path (#5712).
//! - **The budget is the caller's.** The body runs on the jumps that the
//!   caller's run has left, under the same origin, so a divergent body stops.
//!   The run does not charge back what the body spends.
//! - **A far run that answers nothing declines.** A body whose run ends stuck
//!   or declined, a value that does not cross, or a host's refusal, declines
//!   the caller's run at the migration: a failing far run is no branch of the
//!   caller's yet.
//! - **The chunk store only grows.** A crossing's chunks stay for the process's
//!   life, as a content-addressed memory keeps what it was given.
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

use alloc::vec::Vec;
use core::num::NonZeroU64;
use std::sync::LazyLock;
use std::sync::Mutex;
use std::sync::PoisonError;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Store;
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
use crate::run::Ran;
use crate::run::RunInputs;
use crate::run::Tier;
use crate::run::by_policy;
use crate::run::on_tier;
use crate::seam::Offer;

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

/// The process's chunk store, which every world reaches.
static CAM: LazyLock<Mutex<InMemoryChunkStore>> =
    LazyLock::new(|| Mutex::new(InMemoryChunkStore::new()));

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

/// Run here a migration another host shipped to `world`.
///
/// The migration at `at` of `arena`, closed over `captures`, values of
/// `store`, runs on the tier the policy picks, and its answer is a value of
/// `store`.
///
/// # Specification
/// - requires: `captures` are the values the migration's body binds, in the
///   order its lowering binds them, as the shipping host gathered them.
/// - ensures: on success, the value the body halts with over `store` within
///   `budget`; nothing runs unless `at` is a migration to `world` whose body
///   lowers closed over as many captures as `captures` holds.
/// - fails: [`Unmigrated::Unheld`] when `at` is no migration or its body does
///   not lower over `captures`; [`Unmigrated::Unserved`] when it migrates to
///   another world; [`Unmigrated::Unanswered`] when the run ends stuck, aborted
///   or declined.
/// - panics: none.
/// - executable: none — the answer is observed by running the body.
///
/// # Errors
/// As the failures above.
///
/// # Adequacy
/// - hypothesis: L3 — a migration of `(x, y)` over two captures answers their
///   pair; the same command named at another world, a command that is no
///   migration, and too few captures each refuse by name before anything runs.
/// - witness: `tests::world::a_shipped_migration_runs_here_only_as_the_migration_it_names`
#[inline]
pub fn arrive(
    (arena, definitions): (&CommandArena, &Definitions),
    (at, world): (CommandId, World),
    budget: Budget,
    (store, captures): (&mut Store, &[HeapValueId]),
) -> Result<HeapValueId, Unmigrated>
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
    match by_policy(
        &lowered,
        (arena, definitions),
        budget,
        RunInputs::new(store).closed_over(captures),
    ) {
        Ok(Ran::Ended(Outcome::Halted(answer))) => Ok(answer),
        Ok(Ran::Ended(Outcome::Stuck(_)) | Ran::Aborted) | Err(_) => Err(Unmigrated::Unanswered),
    }
}

/// Cross the value `from` binds at `value` into `to`, committed then
/// dereferenced through the process's chunk store.
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
    let mut cam = CAM.lock().unwrap_or_else(PoisonError::into_inner);
    let manifest = commit(from, value, params, &mut *cam)?;
    deref(&manifest, params, &*cam, to)
}
