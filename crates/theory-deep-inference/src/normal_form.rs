//! The tracelet normal form: a canonical form on certificate data, and a
//! decidable sound under-approximation of replay-equality.
//!
//! The tracelet algebra's shift quotient is free on its primitives (Behr and
//! Kock, *Tracelet Hopf Algebras and Decomposition Spaces*), and this module
//! reads that statement on certificate data: a derivation factors uniquely
//! into content-addressed primitives carrying integer multiplicities,
//! scheduled canonically. Nothing algebraic ships, no vector space, formal sum
//! or antipode; what is built is the canonical form the algebra licenses.
//!
//! # The one contract that must not be misread
//!
//! Normal-form-equal implies replay-equal. The converse is never claimed, and
//! is false.
//!
//! [`nf_equal`] is a sufficient condition for two derivations to be the same
//! transformation, never a necessary one. Two derivations reaching one
//! boundary by different primitive factorizations are replay-equal and
//! normal-form-distinct, and that is intended:
//! [`replay_equivalent`](gandr_theory_coherent_resolutions::replay_equivalent)
//! remains the semantic oracle. The engine's
//! [`derive_fused`](gandr_theory_coherent_resolutions::derive_fused) witnesses
//! the asymmetry: one boundary whose `path_a` is a two-step derivation and
//! whose `path_b` is a single fused step, the same transformation with two
//! normal forms.
//!
//! # Why the soundness argument is local
//!
//! [`normalize`] does not reason about a recorded path; it runs it, under the
//! skolemization replay uses ([`CellAlphabet::skolemize`]), and refuses
//! anything it cannot confirm. A returned [`TraceletNf`] is therefore a replay
//! receipt: the recorded path fired step by step from the skolemized peak and
//! landed on the skolemized join, and the normal form records that boundary.
//! So two equal normal forms give peak equality, join equality and "each
//! replays", which is exactly replay-equivalence, with no appeal to a chain of
//! commutations. The factorization and the schedule make the relation finer
//! than boundary equality, and finer is still sound; what they buy is that the
//! answer is precomputable.
//!
//! # The three quotients
//!
//! - **Content addressing.** Two occurrences of one primitive are one primitive
//!   with multiplicity two. The address ([`PrimId`]) is a digest over the
//!   resolved cell's content and the position, never the store index. It orders
//!   the factorization and is nowhere the identity witness: a collision inside
//!   one normal form is refused
//!   ([`NormalFormObstruction::ContentAddressCollision`]), and across two
//!   normal forms the map values carry the [`PrimCert`]s [`nf_equal`] compares.
//! - **Unit elimination.** A step that fires and leaves the term unchanged is
//!   dropped; dropping it cannot move the endpoint.
//! - **The shift quotient.** Adjacent applications the shift guard licenses
//!   commute. This module does not restate the guard; the causal order asks it
//!   and reads any refusal as dependence.
//!
//! # The canonical schedule
//!
//! The schedule is the causal layering of [`EventOrder`], flattened: each
//! surviving occurrence takes the depth one more than the deepest earlier
//! occurrence it depends on, and the occurrences are sorted by
//! `(depth, key)`. A licensed transposition swaps two occurrences with no
//! dependence edge between them, so it changes no depth, which is why two
//! derivations related by licensed transpositions sort to one sequence.
//!
//! # The receipt is a value
//!
//! [`TraceletNf`] has public fields and is `Clone`, so its receipt property is
//! [`nf_equal`]'s precondition, discharged by the caller's bookkeeping.
//! [`ReplayWitness`] has private fields and one constructor,
//! [`normalize_certified`]: possessing one is possessing the receipt, and
//! [`certified_nf_equal`] compares two of them. Two normal forms taken against
//! different stores are compared by [`nf_equal_across_stores`], which resolves
//! each side's cells in its own store and compares content rather than
//! handles.
//!
//! # The canonicalization is checked
//!
//! The canonical schedule is replayed from the peak before the normal form is
//! returned. A schedule that does not fire, or fires and reaches something
//! other than the recorded join, is refused
//! ([`NormalFormObstruction::ShiftedScheduleDoesNotFire`],
//! [`NormalFormObstruction::ShiftedScheduleMissesTheJoin`]). Either refusal is
//! the kill signal: the independence relation licensed a commutation the
//! semantics does not have, a soundness defect in position or overlap
//! bookkeeping and never a case to work around.
//!
//! Neither refusal is reachable over the shipped alphabets, which compute
//! position order from the path and splice locally; both are witnessed over
//! adversarial alphabets in the integration suite. The second matters most: a
//! non-local splice satisfies every conjunct of the guard honestly, because
//! the guard reads positions and cell contents and locality of the term
//! algebra is neither.
//!
//! The certificate-level entry point [`tracelets_nf_equal`] collapses every
//! obstruction to a negative answer, kill signals included, because its return
//! type has nowhere to put one: safe for the equality, wrong for the signal. A
//! consumer that must see the signal calls [`normalize`].
//!
//! # Content addresses are build-local
//!
//! Every digest here is FNV-1a over [`core::hash::Hash`] writes, whose integer
//! writers are native-endian at the target's word width. An address is stable
//! for one build of one target and no further; it orders and keys within one
//! process, and nothing persists or transmits one.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::btree_map::Entry;
use alloc::vec::Vec;

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::rewrite_at;
use quenchant_shape::shape::Maybe;

use crate::boundary::CausalDepth;
use crate::boundary::NormalFormEquality;
use crate::boundary::PrimMultiplicity;
use crate::boundary::ReplayLevel;
use crate::causal::DerivationEvent;
use crate::causal::EventOrder;

/// The FNV-1a offset basis of the 128-bit content digest.
const CONTENT_BASIS: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;

/// The FNV-1a prime of the 128-bit content digest.
const CONTENT_PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b;

/// The domain separator mixed in before a primitive's content.
const PRIMITIVE_DOMAIN: &[u8] = b"gandr.tracelet.primitive.v1";

/// The domain separator mixed in before a cell's content, so a position-free
/// cell address cannot collide with a primitive address over the same cell at
/// the root.
const CELL_DOMAIN: &[u8] = b"gandr.tracelet.cell.v1";

/// The domain separator mixed in before an event's labeled causal past, so a
/// past digest cannot collide with either address domain.
const CAUSAL_DOMAIN: &[u8] = b"gandr.tracelet.causal-past.v1";

quenchant_shape::reason_enum! {
    /// Why a normal form's schedule does not resolve to a path.
    pub mod schedule_resolution {
        /// The reason the schedule has no runnable path.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The schedule names an address the factorization does not hold,
            /// which [`normalize`](super::normalize) cannot produce.
            UnfactoredAddress,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a replay plan ran no level.
    pub mod replay_fuel {
        /// The reason the plan declined to replay.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The fuel offered is below the plan's critical path.
            InsufficientFuel,
        }
    }
}

/// The content address of a primitive certificate: a 128-bit digest over the
/// resolved cell's content and the position it fires at.
///
/// It orders the primitive factorization and breaks the canonical schedule's
/// ties. It is not an identity witness, and it is build-local: nothing
/// persists or transmits one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PrimId(u128);

/// The content address of a cell: a 128-bit digest over the resolved cell's
/// content alone, with no position in it.
///
/// It is distinct from [`PrimId`] because the two name different things: a
/// primitive is a cell together with where it fired, while a cell address
/// names the cell and nothing else. The two digests are domain-separated and
/// the types stop one being passed where the other is meant. Neither is an
/// identity witness and neither leaves the process.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CellAddress(u128);

/// A digest of an event's labeled causal past: its own primitive address
/// folded with the past digests of the events it directly depends on.
///
/// It refines [`PrimId`] into a key that separates two events a shared address
/// cannot, and it is a function of the labeled causal order alone: the fold is
/// taken over the sorted predecessor digests, so it cannot see which linear
/// extension was recorded. It is build-local, like every address here.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CausalPast(u128);

/// A primitive certificate: one indecomposable factor of a normalized
/// derivation.
///
/// Representationally a recorded step; distinct from one, because a
/// [`CellApp`] is a step of a path (which may be a unit, placed where it was
/// recorded) while a primitive is a factor of a normal form (never a unit,
/// placed by the canonical schedule).
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct PrimCert<A: CellAlphabet = SequentAlphabet>(pub CellApp<A>);

impl<A: CellAlphabet> PrimCert<A>
{
    /// The recorded step this primitive applies.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn step(&self) -> &CellApp<A>
    {
        &self.0
    }
}

/// The tracelet normal form of one recorded derivation: its boundary, its
/// graded primitive factorization, and its canonical schedule.
///
/// A value [`normalize`] returns is a replay receipt as well as a canonical
/// form. That is a property of `normalize`'s outputs and not an invariant of
/// this type: the fields are public and the struct is `Clone`, so a value can
/// be assembled or edited with no replay behind it, and the receipt property is
/// [`nf_equal`]'s precondition. [`ReplayWitness`] is the type that carries it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraceletNf<A: CellAlphabet = SequentAlphabet>
{
    /// The term the derivation starts from, as recorded; replay skolemizes it.
    pub peak: A::Cmd,
    /// The term the derivation reaches, as recorded.
    pub joins_at: A::Cmd,
    /// The warrant the shift quotient's convexity conjunct was decided under:
    /// which independence relation the normal form was taken with respect to.
    pub convexity: ConvexityDischarge,
    /// The unique primitive factorization: each primitive once, under its
    /// content address, with the number of times it occurs.
    pub primitives: BTreeMap<PrimId, (PrimCert<A>, PrimMultiplicity)>,
    /// The canonical schedule, as content addresses: the causal layering
    /// flattened. Its length is the sum of the multiplicities.
    pub schedule: Vec<PrimId>,
}

impl<A: CellAlphabet> TraceletNf<A>
{
    /// The canonical schedule as a runnable path.
    ///
    /// # Specification
    /// - ensures: the schedule's addresses resolved through the factorization,
    ///   in schedule order: the path [`normalize`] already replayed.
    /// - provides: [`schedule_resolution::Absent::UnfactoredAddress`] for a
    ///   normal form whose schedule names an address its factorization does not
    ///   hold.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decompressed path is checked against the input
    ///   rather than a predicted answer: it is replayed and must reach the
    ///   normal form's own join.
    /// - witness: `normal_form::tests::the_canonical_path_replays_to_the_recorded_join`
    #[inline]
    pub fn canonical_path(&self) -> Maybe<Vec<CellApp<A>>, schedule_resolution::Absent>
    {
        let mut path = Vec::with_capacity(self.schedule.len());
        for address in &self.schedule {
            let Some(graded) = self.primitives.get(address)
            else {
                return Maybe::Absent(schedule_resolution::Absent::UnfactoredAddress);
            };
            path.push(graded.0.0.clone());
        }
        Maybe::Present(path)
    }
}

/// A replay receipt for one recorded derivation: its normal form, its causal
/// structure, and the fact that [`normalize_certified`] confirmed both.
///
/// Its fields are private, [`normalize_certified`] is its only constructor,
/// and no method hands out a mutable interior, so possessing one is possessing
/// the receipt. It is still a receipt against one store, because a
/// [`PrimCert`] names its cell by store identifier; two receipts taken against
/// different stores are compared by [`nf_equal_across_stores`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayWitness<A: CellAlphabet = SequentAlphabet>
{
    /// The normal form the recorded derivation was confirmed to have.
    normal_form: TraceletNf<A>,
    /// The causal structure the canonical schedule is a linear extension of.
    order: EventOrder<A>,
}

impl<A: CellAlphabet> ReplayWitness<A>
{
    /// The normal form this receipt certifies.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn normal_form(&self) -> &TraceletNf<A>
    {
        &self.normal_form
    }

    /// The normal form, taken out of the receipt.
    ///
    /// The receipt is consumed, so a caller that wants the data alone gives up
    /// the provenance in the same expression.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_normal_form(self) -> TraceletNf<A>
    {
        self.normal_form
    }

    /// The finite event partial order of the certified derivation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn event_order(&self) -> &EventOrder<A>
    {
        &self.order
    }

    /// The term the certified derivation starts from, as recorded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn peak(&self) -> &A::Cmd
    {
        &self.normal_form.peak
    }

    /// The term the certified derivation reaches, as recorded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn joins_at(&self) -> &A::Cmd
    {
        &self.normal_form.joins_at
    }

    /// The canonical schedule as a runnable path, read off the event order.
    ///
    /// Unlike [`TraceletNf::canonical_path`] this is total: it reads the event
    /// order rather than resolving addresses through the factorization.
    ///
    /// # Specification
    /// - ensures: the steps of [`EventOrder::canonical_order`], in that order:
    ///   the path [`normalize_certified`] replayed before handing out this
    ///   receipt.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — checked against the independently computed
    ///   [`TraceletNf::canonical_path`] on the same receipt, so a divergence
    ///   between the two spellings fails.
    /// - witness: `normal_form::tests::a_replay_witness_carries_its_own_boundary_and_order`
    #[inline]
    #[must_use]
    pub fn canonical_path(&self) -> Vec<CellApp<A>>
    {
        self.order
            .canonical_order()
            .into_iter()
            .filter_map(|index| match self.order.event(index) {
                | Maybe::Present(event) => Some(event.step().clone()),
                | Maybe::Absent(_) => None,
            })
            .collect()
    }

    /// Project the certified derivation into deterministic replay levels.
    ///
    /// # Specification
    /// - ensures: one level per layer of the event order, in dependency order;
    ///   each level is an antichain of the order, its steps in canonical order;
    ///   the critical path is the number of levels.
    /// - provides: the batches a parallel or on-demand replay executes, and the
    ///   fuel a complete replay consumes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fused fixture's two certificate paths are planned
    ///   and replayed level by level, on demand, and against the critical-path
    ///   fuel, each agreeing with the sequential replay of the canonical path.
    /// - witness: `normal_form::tests::a_fused_fixture_replays_both_certificate_paths_through_its_critical_path_plan`
    /// - witness: `tests::normal_form::a_two_member_replay_level_reaches_one_term_in_both_permitted_orders`
    #[inline]
    #[must_use]
    pub fn replay_plan(&self) -> ReplayPlan<A>
    {
        let levels: Vec<Vec<CellApp<A>>> = self
            .order
            .layers()
            .into_iter()
            .map(|layer| {
                layer
                    .into_iter()
                    .filter_map(|index| match self.order.event(index) {
                        | Maybe::Present(event) => Some(event.step().clone()),
                        | Maybe::Absent(_) => None,
                    })
                    .collect()
            })
            .collect();
        ReplayPlan {
            peak: self.normal_form.peak.clone(),
            critical_path: CausalDepth::from(levels.len()),
            levels,
        }
    }
}

/// A deterministic antichain schedule for replaying a certified derivation:
/// its levels, in dependency order, and the fuel a complete replay consumes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayPlan<A: CellAlphabet = SequentAlphabet>
{
    /// The term the plan replays from, as the certified witness recorded it.
    peak: A::Cmd,
    /// The antichain levels, in dependency order.
    levels: Vec<Vec<CellApp<A>>>,
    /// The fuel a complete replay consumes: the number of levels.
    critical_path: CausalDepth,
}

impl<A: CellAlphabet> ReplayPlan<A>
{
    /// The antichain levels, in dependency order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn levels(&self) -> &[Vec<CellApp<A>>]
    {
        &self.levels
    }

    /// The critical-path fuel required to finish the plan: the number of
    /// levels.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn critical_path(&self) -> CausalDepth
    {
        self.critical_path
    }

    /// Replay one level from an already-replayed command.
    ///
    /// # Specification
    /// - ensures: the term reached by firing the requested level's steps from
    ///   `current`, in their within-level order; no other level runs.
    /// - fails: [`NormalFormObstruction::InvalidReplayLevel`] when `level` is
    ///   outside the plan; [`NormalFormObstruction::UnknownCell`] for a stale
    ///   identifier and [`NormalFormObstruction::ShiftedScheduleDoesNotFire`]
    ///   for a scheduled step carrying no redex.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every level of a fused fixture's plan replays on
    ///   demand to the sequential replay's term, and the level past the last is
    ///   refused by name.
    /// - witness: `normal_form::tests::a_fused_fixture_replays_both_certificate_paths_through_its_critical_path_plan`
    /// - witness: `tests::normal_form::a_two_member_replay_level_reaches_one_term_in_both_permitted_orders`
    #[inline]
    pub fn replay_level(
        &self,
        store: &CellStore<A>,
        current: &A::Cmd,
        level: ReplayLevel,
    ) -> Result<A::Cmd, NormalFormObstruction<A>>
    {
        let Some(steps) = self.levels.get(usize::from(level))
        else {
            return Err(NormalFormObstruction::InvalidReplayLevel {
                level,
                levels: CausalDepth::from(self.levels.len()),
            });
        };
        run_schedule(store, current, steps)
    }

    /// Replay every level when `fuel` covers the critical path.
    ///
    /// # Specification
    /// - ensures: the term reached by replaying the levels in dependency order
    ///   from the skolemized peak, keeping the batch boundaries rather than
    ///   flattening them into one schedule.
    /// - provides: [`replay_fuel::Absent::InsufficientFuel`] when `fuel` is
    ///   below the critical path, a defined decline rather than a failure.
    /// - fails: the step refusals of [`ReplayPlan::replay_level`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both paths of a fused fixture replay under their
    ///   critical-path fuel to the sequential replay's term, and zero fuel
    ///   declines.
    /// - witness: `normal_form::tests::a_fused_fixture_replays_both_certificate_paths_through_its_critical_path_plan`
    /// - witness: `tests::normal_form::a_two_member_replay_level_reaches_one_term_in_both_permitted_orders`
    #[inline]
    pub fn replay_with_fuel(
        &self,
        store: &CellStore<A>,
        fuel: CausalDepth,
    ) -> Result<Maybe<A::Cmd, replay_fuel::Absent>, NormalFormObstruction<A>>
    {
        if fuel < self.critical_path {
            return Ok(Maybe::Absent(replay_fuel::Absent::InsufficientFuel));
        }
        let mut current = A::skolemize(&self.peak);
        for level in &self.levels {
            let next = run_schedule(store, &current, level)?;
            current = next;
        }
        Ok(Maybe::Present(current))
    }
}

/// Why a recorded derivation was refused a normal form.
///
/// The two shifted-schedule variants are the kill signal, documented at their
/// declarations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NormalFormObstruction<A: CellAlphabet = SequentAlphabet>
{
    /// A replay caller requested a level outside the plan.
    InvalidReplayLevel
    {
        /// The requested zero-based level.
        level: ReplayLevel,
        /// The number of levels the plan holds, which is also its
        /// critical-path fuel: a count, never an index.
        levels: CausalDepth,
    },
    /// A recorded step names a cell the store does not hold.
    UnknownCell
    {
        /// The identifier that resolved to nothing.
        cell: CellId,
    },
    /// A recorded step does not fire at its recorded position, so the path is
    /// not a derivation and there is nothing to normalize.
    StepDoesNotFire
    {
        /// The step that failed to fire.
        step: Box<CellApp<A>>,
    },
    /// The recorded path fires throughout and lands somewhere other than the
    /// recorded join: the certificate does not replay.
    PathMissesTheJoin
    {
        /// The term the recorded path reached.
        reached: Box<A::Cmd>,
    },
    /// Two distinct primitives share a content address inside one normal form.
    ///
    /// Identity never rests on the address, so the honest outcome is to
    /// decline the normal form rather than merge the two.
    ContentAddressCollision
    {
        /// The address both primitives hashed to.
        address: PrimId,
        /// The primitive already recorded under it.
        held: Box<PrimCert<A>>,
        /// The primitive that collided with it.
        offered: Box<PrimCert<A>>,
    },
    /// The kill signal: the canonical schedule contains a step that does not
    /// fire, although the recorded path did.
    ///
    /// The independence relation licensed a transposition the semantics does
    /// not have.
    ShiftedScheduleDoesNotFire
    {
        /// The canonical step that failed to fire.
        step: Box<CellApp<A>>,
    },
    /// Two distinct events tie on the canonical sort key.
    ///
    /// The canonical order would then fall back on the sort's stability, and so
    /// on the recorded sequentialization. Separating events that differ only in
    /// their future would need a canonical form for labeled posets, which this
    /// module does not attempt; the key refines the address by the labeled
    /// causal past, and this arm is what happens when even that does not
    /// separate them.
    CanonicalKeyCollision
    {
        /// The earlier of the two tying events, as a primitive.
        earlier: Box<PrimCert<A>>,
        /// The later of them.
        later: Box<PrimCert<A>>,
        /// The depth both sit at.
        depth: CausalDepth,
    },
    /// The kill signal: the canonical schedule fires throughout and reaches a
    /// term other than the one the recorded path reached.
    ShiftedScheduleMissesTheJoin
    {
        /// The term the canonical schedule reached.
        reached: Box<A::Cmd>,
    },
}

/// The content address of a primitive: a digest over the cell's content and
/// the position, never over the store index.
///
/// # Specification
/// - requires: `cell` is the cell a [`PrimCert`]'s [`CellId`] resolves to in
///   the store the certificate is read against.
/// - ensures: equal `(cell content, position)` pairs give equal addresses,
///   deterministically and without session state: the [`CellAlphabet`] contract
///   pins [`core::hash::Hash`] to structural content identity.
/// - provides: the total order a factorization keyed by address needs, which
///   neither `A::Pos` nor `A::Cmd` supplies.
/// - panics: none.
/// - intension: FNV-1a over 128 bits, domain-separated. Distinct inputs may
///   collide; no caller treats an address as proof of identity, and
///   [`normalize`] refuses a collision. The digest is stable for one build of
///   one target and no further.
///
/// # Adequacy
/// - hypothesis: L3 — same content, same address; different content or
///   position, different address; separated by two cells, one cell at two
///   positions, and one cell interned under two identifiers in two stores.
/// - witness: `normal_form::tests::the_content_address_is_taken_over_content`
#[inline]
#[must_use]
pub fn prim_address<A>(
    cell: &Cell<A>,
    at: &A::Pos,
) -> PrimId
where
    A: CellAlphabet,
{
    let mut hasher = ContentHasher::new();
    core::hash::Hasher::write(&mut hasher, PRIMITIVE_DOMAIN);
    core::hash::Hash::hash(cell, &mut hasher);
    core::hash::Hash::hash(at, &mut hasher);
    PrimId(hasher.state)
}

/// The position-free content address of a cell: the same digest as
/// [`prim_address`] over the resolved cell's content alone.
///
/// It exists for the flow projection, whose vertex labels name the cell and
/// not where it fired: labelling a vertex with a primitive address would
/// re-import the position the projection discards.
///
/// # Specification
/// - ensures: equal for two cells with equal content, independent of any
///   position; domain-separated from [`prim_address`].
/// - panics: none.
/// - intension: stable for one build of one target and no further.
///
/// # Adequacy
/// - hypothesis: L3 — same content, same address, and never the position;
///   separated by two cells differing in content and by one cell whose address
///   is compared with its primitive addresses at two positions.
/// - witness: `flow::tests::the_cell_address_forgets_the_position`
/// - witness: `normal_form::tests::the_two_address_domains_are_separated_by_type_and_by_digest`
#[inline]
#[must_use]
pub fn cell_address<A>(cell: &Cell<A>) -> CellAddress
where
    A: CellAlphabet,
{
    let mut hasher = ContentHasher::new();
    core::hash::Hasher::write(&mut hasher, CELL_DOMAIN);
    core::hash::Hash::hash(cell, &mut hasher);
    CellAddress(hasher.state)
}

/// The labeled causal past digest of one event, from its own address and the
/// past digests of the events it directly depends on.
///
/// # Specification
/// - requires: `predecessors` are the past digests of exactly the events
///   `address`'s event depends on directly.
/// - ensures: equal `(address, predecessor multiset)` pairs give equal digests,
///   whatever order `predecessors` arrives in: the fold sorts a copy first, so
///   the result is a function of the labeled causal order rather than of the
///   recorded one.
/// - provides: the refinement of [`PrimId`] the canonical order breaks its
///   remaining ties with.
/// - panics: none.
/// - intension: FNV-1a over 128 bits, domain-separated, and a sort of the
///   direct predecessors; stable for one build of one target and no further.
///
/// # Adequacy
/// - hypothesis: L3 — one address against two predecessor sets, two addresses
///   against one set, and one set offered in both orders.
/// - witness: `normal_form::tests::the_causal_past_digest_reads_the_multiset_and_not_the_order`
#[inline]
#[must_use]
pub fn causal_past_address(
    address: PrimId,
    predecessors: &[CausalPast],
) -> CausalPast
{
    let mut sorted = predecessors.to_vec();
    sorted.sort_unstable();
    let mut hasher = ContentHasher::new();
    core::hash::Hasher::write(&mut hasher, CAUSAL_DOMAIN);
    core::hash::Hash::hash(&address, &mut hasher);
    for past in &sorted {
        core::hash::Hash::hash(past, &mut hasher);
    }
    CausalPast(hasher.state)
}

/// Normalize a recorded derivation to its tracelet normal form, or refuse it.
///
/// The recorded path is run and its unit steps dropped, the survivors are
/// content-addressed and graded, and the canonical schedule is computed by
/// causal layering under the shift guard and then replayed before the normal
/// form is returned. This is [`normalize_certified`] with the receipt
/// projected away, so the two cannot diverge.
///
/// # Specification
/// - requires: `path` is the derivation recorded from `peak` to `joins_at`
///   against `store`, the triple a certificate replay would be given.
/// - ensures: a normal form only when the recorded path fires step by step from
///   the skolemized `peak` and reaches the skolemized `joins_at`, and the
///   canonical schedule does the same; it records that boundary verbatim, its
///   factorization graded by occurrence count and its schedule the causal
///   layering flattened.
/// - provides: the sound under-approximation of replay-equality: success on
///   both sides plus [`nf_equal`] implies replay-equivalence. The converse does
///   not hold and is not claimed.
/// - fails: [`NormalFormObstruction`]: a stale identifier, a recorded step that
///   does not fire, a recorded path that misses the join, a content-address or
///   canonical-key collision, or (the kill signal) a canonical schedule that
///   does not fire or misses the join.
/// - panics: none.
/// - intension: one replay of the recorded path, one of the canonical schedule,
///   and a quadratic number of independence questions in the surviving path
///   length.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the normal form is checked against the input (its
///   canonical path is replayed and must reach its own join), and each failure
///   mode is separated by a fixture triggering only it: three over a shipped
///   alphabet (a fabricated identifier, a position carrying no redex, a
///   retargeted join) and three over adversarial alphabets, since each fires
///   only when an alphabet answers what no shipped one can: a nesting pair
///   called incomparable, a non-local splice, and an orientation tag the digest
///   cannot see.
/// - witness: `normal_form::tests::a_recorded_derivation_normalizes_to_a_replay_receipt`
/// - witness: `normal_form::tests::an_unknown_cell_identifier_is_refused`
/// - witness: `normal_form::tests::a_step_that_does_not_fire_is_refused`
/// - witness: `normal_form::tests::a_path_that_misses_its_join_is_refused`
/// - witness: `normal_form::tests::a_unit_step_is_eliminated`
/// - witness: `normal_form::tests::the_canonical_path_replays_to_the_recorded_join`
/// - witness: `normal_form::tests::the_shift_quotient_is_empty_over_the_sequent_alphabet`
/// - witness: `tests::normal_form::a_derivation_from_a_different_peak_is_nf_distinct`
/// - witness: `tests::normal_form::an_alphabet_that_calls_nesting_incomparable_trips_the_kill_signal`
/// - witness: `tests::normal_form::a_non_local_term_algebra_trips_the_kill_signal_at_the_join`
/// - witness: `tests::normal_form::two_primitives_sharing_a_content_address_are_refused_rather_than_merged`
/// - witness: `tests::normal_form::a_withheld_convexity_warrant_empties_the_shift_quotient`
#[inline]
pub fn normalize<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    joins_at: &A::Cmd,
    path: &[CellApp<A>],
) -> Result<TraceletNf<A>, NormalFormObstruction<A>>
where
    A: CellAlphabet,
{
    let witness = normalize_certified(store, peak, joins_at, path)?;
    Ok(witness.into_normal_form())
}

/// Normalize a recorded derivation to a [`ReplayWitness`], or refuse it.
///
/// # Specification
/// - requires: `path` is the derivation recorded from `peak` to `joins_at`
///   against `store`.
/// - ensures: a witness only under [`normalize`]'s conditions; it also carries
///   the derivation's [`EventOrder`], the causal structure the canonical
///   schedule is a linear extension of.
/// - provides: an unforgeable replay receipt: the type's fields are private and
///   this is its only constructor.
/// - fails: [`NormalFormObstruction`], exactly as [`normalize`] does.
/// - panics: none.
/// - intension: as [`normalize`].
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — what this adds over [`normalize`] is the provenance of
///   the returned value, carried by the type; it is separated by the witness's
///   boundary and canonical path agreeing with the normal form's, and by two
///   receipts comparing equal exactly when their normal forms do.
/// - witness: `normal_form::tests::a_replay_witness_carries_its_own_boundary_and_order`
/// - witness: `normal_form::tests::a_certified_pair_is_equal_exactly_when_its_normal_forms_are`
#[inline]
pub fn normalize_certified<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    joins_at: &A::Cmd,
    path: &[CellApp<A>],
) -> Result<ReplayWitness<A>, NormalFormObstruction<A>>
where
    A: CellAlphabet,
{
    let start = A::skolemize(peak);
    let target = A::skolemize(joins_at);
    let survivors = run_recording(store, &start, path)?;
    if survivors.reached != target {
        return Err(NormalFormObstruction::PathMissesTheJoin {
            reached: Box::new(survivors.reached),
        });
    }
    let convexity = A::convexity_discharge(store);
    let order = EventOrder::of_events(store, survivors.steps, convexity);
    refuse_key_collisions(&order)?;
    let canonical_order = order.canonical_order();
    let mut primitives: BTreeMap<PrimId, (PrimCert<A>, PrimMultiplicity)> = BTreeMap::new();
    let mut schedule = Vec::with_capacity(canonical_order.len());
    let mut canonical = Vec::with_capacity(canonical_order.len());
    for index in canonical_order {
        let Maybe::Present(event) = order.event(index)
        else {
            continue;
        };
        let cert = PrimCert(event.step().clone());
        match primitives.entry(event.address()) {
            | Entry::Vacant(slot) => {
                slot.insert((cert, PrimMultiplicity::from(1_u32)));
            },
            | Entry::Occupied(mut slot) => {
                let graded = slot.get_mut();
                if graded.0 != cert {
                    return Err(NormalFormObstruction::ContentAddressCollision {
                        address: event.address(),
                        held: Box::new(graded.0.clone()),
                        offered: Box::new(cert),
                    });
                }
                graded.1 = PrimMultiplicity::from(u32::from(graded.1).saturating_add(1_u32));
            },
        }
        schedule.push(event.address());
        canonical.push(event.step().clone());
    }
    let shifted = run_schedule(store, &start, &canonical)?;
    if shifted != target {
        return Err(NormalFormObstruction::ShiftedScheduleMissesTheJoin {
            reached: Box::new(shifted),
        });
    }
    Ok(ReplayWitness {
        normal_form: TraceletNf {
            peak: peak.clone(),
            joins_at: joins_at.clone(),
            convexity,
            primitives,
            schedule,
        },
        order,
    })
}

/// The finite event partial order of a recorded derivation, without
/// normalizing it.
///
/// The order needs no join: it reads the steps that moved the term and the
/// independence relation between them. A caller that also wants the boundary
/// checked calls [`normalize_certified`] and reads
/// [`ReplayWitness::event_order`].
///
/// # Specification
/// - requires: `path` is the derivation recorded from `peak` against `store`.
/// - ensures: the order over the steps of `path` that moved the term, in
///   recorded order, when every recorded step's cell resolves and fires.
/// - provides: the causal structure of one derivation: its events, dependence
///   edges, precedence order, layers, and the exchange witnesses between its
///   sequentializations.
/// - fails: [`NormalFormObstruction::UnknownCell`] for a stale identifier,
///   [`NormalFormObstruction::StepDoesNotFire`] for a position carrying no
///   redex, and [`NormalFormObstruction::CanonicalKeyCollision`] for two events
///   tying on the canonical key.
/// - panics: none.
/// - intension: one replay of the recorded path and a quadratic number of
///   independence questions.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the order is built from a run of the recorded path; that
///   it is the same order the normalizer layers by is separated by comparing
///   its canonical order with the schedule [`normalize`] produced from the same
///   derivation.
/// - witness: `tests::normal_form::the_order_taken_alone_agrees_with_the_normalizers`
/// - witness: `causal::tests::a_dependent_chain_is_its_own_canonical_order`
#[inline]
pub fn event_order<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    path: &[CellApp<A>],
) -> Result<EventOrder<A>, NormalFormObstruction<A>>
where
    A: CellAlphabet,
{
    let start = A::skolemize(peak);
    let survivors = run_recording(store, &start, path)?;
    let convexity = A::convexity_discharge(store);
    let order = EventOrder::of_events(store, survivors.steps, convexity);
    refuse_key_collisions(&order)?;
    Ok(order)
}

/// Refuse an event order whose canonical sort key is not a strict total order,
/// resolving the tying indices to the primitives they apply.
///
/// Both public constructors of an [`EventOrder`] run it, so an order this crate
/// hands out has passed the check.
///
/// # Specification
/// - ensures: success exactly when the order's own collision check accepts it.
/// - fails: [`NormalFormObstruction::CanonicalKeyCollision`], carrying both
///   primitives and the depth they share.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn refuse_key_collisions<A>(order: &EventOrder<A>) -> Result<(), NormalFormObstruction<A>>
where
    A: CellAlphabet,
{
    let Err(collision) = order.refuse_key_collisions()
    else {
        return Ok(());
    };
    let (Maybe::Present(earlier), Maybe::Present(later)) =
        (order.event(collision.earlier), order.event(collision.later))
    else {
        return Ok(());
    };
    Err(NormalFormObstruction::CanonicalKeyCollision {
        earlier: Box::new(PrimCert(earlier.step().clone())),
        later: Box::new(PrimCert(later.step().clone())),
        depth: collision.depth,
    })
}

/// Whether two normal forms are the same normal form.
///
/// # Specification
/// - requires: both normal forms were produced by [`normalize`] against the
///   same store, because a [`PrimCert`] names its cell by store identifier.
/// - ensures: positive exactly when the two agree on peak, join, convexity
///   warrant, graded factorization and canonical schedule.
/// - provides: the sound direction only: a positive answer means the two
///   derivations are the same transformation; a negative answer means nothing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the positive direction is confirmed by replay, the
///   negative is pinned as uninformative by a pair that is replay-equal and
///   normal-form-distinct, and the peak conjunct by an erasing rule carrying
///   two peaks to one join under one schedule. Dropping the join, the
///   factorization or the warrant is an equivalent mutation against one store
///   and is not claimed separable.
/// - witness: `normal_form::tests::one_derivation_is_nf_equal_to_itself`
/// - witness: `normal_form::tests::replay_equal_derivations_may_be_nf_distinct`
/// - witness: `tests::normal_form::a_derivation_from_a_different_peak_is_nf_distinct`
#[inline]
#[must_use]
pub fn nf_equal<A>(
    left: &TraceletNf<A>,
    right: &TraceletNf<A>,
) -> NormalFormEquality
where
    A: CellAlphabet,
{
    NormalFormEquality::from(left == right)
}

/// Whether two receipts certify the same normal form.
///
/// This is [`nf_equal`] with its precondition discharged by the types: a
/// [`ReplayWitness`] cannot be assembled, so both sides are values
/// [`normalize_certified`] returned.
///
/// # Specification
/// - requires: both receipts were taken against the same store.
/// - ensures: positive exactly when [`nf_equal`] holds of the two normal forms.
/// - provides: the sound direction only, as [`nf_equal`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the oracle is [`nf_equal`] on the projected normal forms,
///   separated by a receipt pair that agrees and one that does not.
/// - witness: `normal_form::tests::a_certified_pair_is_equal_exactly_when_its_normal_forms_are`
#[inline]
#[must_use]
pub fn certified_nf_equal<A>(
    left: &ReplayWitness<A>,
    right: &ReplayWitness<A>,
) -> NormalFormEquality
where
    A: CellAlphabet,
{
    nf_equal(&left.normal_form, &right.normal_form)
}

/// Whether two normal forms taken against different stores are the same
/// normal form.
///
/// [`nf_equal`] compares [`PrimCert`]s, which name their cells by insertion-
/// order [`CellId`]; two stores holding one cell in a different order give it
/// different identifiers. This resolves each side's cells in its own store and
/// compares their content, so the answer depends on what the cells are. Every
/// matching factorization key has its two primitives' positions and resolved
/// cells compared as well, so a digest collision costs a negative answer,
/// never a false positive.
///
/// # Specification
/// - requires: `left` came from [`normalize`] against `left_store` and `right`
///   against `right_store`.
/// - ensures: positive exactly when the two agree on peak, join, convexity
///   warrant, canonical schedule, and a factorization compared by multiplicity,
///   position and resolved cell content.
/// - provides: the sound direction only: replay reads a cell's content and
///   never its handle, so content-identical factorizations over equal
///   boundaries replay identically.
/// - fails: [`NormalFormObstruction::UnknownCell`] when a factor names a cell
///   its own store does not hold.
/// - panics: none.
/// - intension: one map walk with two store lookups per shared factor; no
///   replay, because both sides are receipts.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L2 — agrees with [`nf_equal`] whenever both sides are read
///   against one store; L3 — one derivation built in two stores numbering its
///   rule differently compares equal here and unequal under [`nf_equal`], two
///   stores holding different cells at one handle compare unequal, and a factor
///   naming an absent cell is refused.
/// - witness: `normal_form::tests::one_derivation_built_in_two_stores_compares_equal_across_them`
/// - witness: `normal_form::tests::across_stores_agrees_with_nf_equal_on_one_store`
/// - witness: `normal_form::tests::two_stores_holding_different_cells_at_one_handle_compare_unequal`
/// - witness: `normal_form::tests::a_factor_naming_an_absent_cell_is_refused_across_stores`
#[inline]
pub fn nf_equal_across_stores<A>(
    left_store: &CellStore<A>,
    left: &TraceletNf<A>,
    right_store: &CellStore<A>,
    right: &TraceletNf<A>,
) -> Result<NormalFormEquality, NormalFormObstruction<A>>
where
    A: CellAlphabet,
{
    if left.peak != right.peak
        || left.joins_at != right.joins_at
        || left.convexity != right.convexity
        || left.schedule != right.schedule
        || left.primitives.len() != right.primitives.len()
    {
        return Ok(NormalFormEquality::from(false));
    }
    for (address, graded) in &left.primitives {
        let Some(counterpart) = right.primitives.get(address)
        else {
            return Ok(NormalFormEquality::from(false));
        };
        let (held_step, offered_step) = (graded.0.step(), counterpart.0.step());
        if graded.1 != counterpart.1 || held_step.at != offered_step.at {
            return Ok(NormalFormEquality::from(false));
        }
        let Maybe::Present(held) = left_store.get(held_step.cell)
        else {
            return Err(NormalFormObstruction::UnknownCell {
                cell: held_step.cell,
            });
        };
        let Maybe::Present(offered) = right_store.get(offered_step.cell)
        else {
            return Err(NormalFormObstruction::UnknownCell {
                cell: offered_step.cell,
            });
        };
        if held != offered {
            return Ok(NormalFormEquality::from(false));
        }
    }
    Ok(NormalFormEquality::from(true))
}

/// The certificate-level fast path: whether two tracelets are certified equal
/// by their normal forms.
///
/// # Specification
/// - requires: both tracelets are read against `store`.
/// - ensures: positive exactly when all four recorded paths normalize and the
///   two tracelets' normal forms agree path for path, which forces equal peaks,
///   equal joins and successful replay of both, and so forces
///   replay-equivalence.
/// - provides: the sound direction only: a negative answer is the absence of a
///   cheap proof, and the caller falls back to the replay oracle.
/// - panics: none.
/// - intension: two replays per path, no cache. Every obstruction any of the
///   four normalizations raises collapses to a negative, the kill signals
///   included, so this is the wrong entry point for observing them.
///
/// # Adequacy
/// - hypothesis: L2 — the oracle is external (replay-equivalence) and the
///   implication is asserted over generated derivation pairs; L3 — the
///   direction an obstruction collapses in is separated by a certificate that
///   does not replay, and the conjunction over both legs by a pair agreeing on
///   one leg only.
/// - witness: `normal_form::tests::nf_equal_certificates_are_replay_equivalent`
/// - witness: `tests::normal_form::every_nf_equal_pair_is_replay_equivalent`
/// - witness: `tests::normal_form::a_certificate_that_does_not_replay_is_not_certified`
/// - witness: `tests::normal_form::a_tracelet_pair_agreeing_only_on_its_first_leg_is_not_certified`
#[inline]
#[must_use]
pub fn tracelets_nf_equal<A>(
    store: &CellStore<A>,
    left: &Tracelet<A>,
    right: &Tracelet<A>,
) -> NormalFormEquality
where
    A: CellAlphabet,
{
    let legs = [(&left.path_a, &right.path_a), (&left.path_b, &right.path_b)];
    let agreed = legs.into_iter().all(|(left_path, right_path)| {
        let left_nf = normalize(store, &left.overlap.peak, &left.joins_at, left_path);
        let right_nf = normalize(store, &right.overlap.peak, &right.joins_at, right_path);
        match (left_nf, right_nf) {
            | (Ok(left_nf), Ok(right_nf)) => bool::from(nf_equal(&left_nf, &right_nf)),
            | (Err(_), _) | (_, Err(_)) => false,
        }
    });
    NormalFormEquality::from(agreed)
}

/// The outcome of running a recorded path: the surviving steps, as events, and
/// the term reached.
#[derive(Clone, Debug)]
struct RunSurvivors<A: CellAlphabet>
{
    /// The steps that moved the term, in recorded order, units dropped.
    steps: Vec<DerivationEvent<A>>,
    /// The term the whole recorded path reached.
    reached: A::Cmd,
}

/// Run `path` from `start`, dropping the steps that leave the term unchanged.
///
/// Unit elimination is decided by observation rather than by a syntactic test:
/// a step is a unit exactly when firing it is a no-op.
///
/// # Specification
/// - ensures: when every recorded step's cell resolves and fires at its
///   recorded position, the term the whole path reached and the steps that
///   changed it.
/// - fails: [`NormalFormObstruction::UnknownCell`] for a stale identifier and
///   [`NormalFormObstruction::StepDoesNotFire`] for a position carrying no
///   redex.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the unit test is separated by a reflexive cell that fires
///   and moves nothing beside one that moves the term, on both alphabets; the
///   failure modes by a fabricated identifier and a position carrying no redex.
/// - witness: `normal_form::tests::a_unit_step_is_eliminated`
/// - witness: `normal_form::tests::an_unknown_cell_identifier_is_refused`
/// - witness: `normal_form::tests::a_step_that_does_not_fire_is_refused`
/// - witness: `tests::normal_form::a_unit_step_is_eliminated_over_the_toy_alphabet`
fn run_recording<A>(
    store: &CellStore<A>,
    start: &A::Cmd,
    path: &[CellApp<A>],
) -> Result<RunSurvivors<A>, NormalFormObstruction<A>>
where
    A: CellAlphabet,
{
    let mut current = start.clone();
    let mut steps = Vec::with_capacity(path.len());
    for step in path {
        let Maybe::Present(cell) = store.get(step.cell)
        else {
            return Err(NormalFormObstruction::UnknownCell { cell: step.cell });
        };
        let Maybe::Present(next) = rewrite_at(cell, &current, &step.at)
        else {
            return Err(NormalFormObstruction::StepDoesNotFire {
                step: Box::new(step.clone()),
            });
        };
        if next == current {
            continue;
        }
        steps.push(DerivationEvent::new(
            step.clone(),
            prim_address(cell, &step.at),
        ));
        current = next;
    }
    Ok(RunSurvivors {
        steps,
        reached: current,
    })
}

/// Run a canonical schedule from `start`, refusing with the kill-signal
/// variant.
///
/// # Specification
/// - ensures: the term reached when every canonical step fires in order.
/// - fails: [`NormalFormObstruction::UnknownCell`] for a stale identifier and
///   [`NormalFormObstruction::ShiftedScheduleDoesNotFire`], the kill signal,
///   for a canonical step carrying no redex.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — reachable only over an adversarial alphabet, since over
///   an honest position order the canonical schedule always fires; the
///   witnesses assert the exact variant, so degrading the kill signal to an
///   ordinary non-firing refusal fails them.
/// - witness: `tests::normal_form::an_alphabet_that_calls_nesting_incomparable_trips_the_kill_signal`
/// - witness: `tests::normal_form::a_non_local_term_algebra_trips_the_kill_signal_at_the_join`
fn run_schedule<A>(
    store: &CellStore<A>,
    start: &A::Cmd,
    schedule: &[CellApp<A>],
) -> Result<A::Cmd, NormalFormObstruction<A>>
where
    A: CellAlphabet,
{
    let mut current = start.clone();
    for step in schedule {
        let Maybe::Present(cell) = store.get(step.cell)
        else {
            return Err(NormalFormObstruction::UnknownCell { cell: step.cell });
        };
        let Maybe::Present(next) = rewrite_at(cell, &current, &step.at)
        else {
            return Err(NormalFormObstruction::ShiftedScheduleDoesNotFire {
                step: Box::new(step.clone()),
            });
        };
        current = next;
    }
    Ok(current)
}

/// A deterministic 128-bit FNV-1a digest over [`core::hash::Hash`] writes.
///
/// The crate needs a content address and has no hashing dependency:
/// [`core::hash::Hash`] is pinned to structural content identity by the
/// [`CellAlphabet`] contract, so streaming it through a fixed-seed hasher turns
/// that guarantee into an orderable key. Every address of the crate is one
/// such digest behind a domain separator of its own.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct ContentHasher
{
    /// The accumulated digest state.
    state: u128,
}

impl ContentHasher
{
    /// A fresh digest state at the FNV-1a offset basis.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            state: CONTENT_BASIS,
        }
    }

    /// The digest accumulated so far, at its full width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest(&self) -> ContentDigest
    {
        ContentDigest(self.state)
    }
}

/// A full-width content digest, which an address type of the crate wraps
/// under its own name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContentDigest(u128);

impl core::hash::Hasher for ContentHasher
{
    /// The digest folded to the width the trait reports.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn finish(&self) -> u64
    {
        let folded = self.state ^ self.state.wrapping_shr(64_u32);
        u64::try_from(folded & u128::from(u64::MAX)).unwrap_or_default()
    }

    /// Mixes `bytes` into the digest, one FNV-1a round per byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write(
        &mut self,
        bytes: &[u8],
    )
    {
        for byte in bytes {
            self.state ^= u128::from(*byte);
            self.state = self.state.wrapping_mul(CONTENT_PRIME);
        }
    }
}

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::Pos;
    use gandr_theory_cell_complexes::PositionStep;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::Sym;
    use gandr_theory_cell_complexes::frame_defining_cell;
    use gandr_theory_coherent_resolutions::OverlapKind;
    use gandr_theory_coherent_resolutions::derive_fused;
    use gandr_theory_coherent_resolutions::enumerate_overlaps;
    use gandr_theory_coherent_resolutions::replay_equivalent;

    use super::*;
    use crate::boundary::EventCount;
    use crate::causal::EventKey;

    /// (add-S): `⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩`.
    ///
    /// # Specification
    /// trivial.
    fn add_s() -> Cell
    {
        let lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        );
        let rhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("m"),
            ConsPat::op(
                "add",
                [ProdPat::meta("n")],
                ConsPat::frame("Succ", ConsPat::meta("alpha")),
            ),
        );
        Cell::new(
            lhs,
            rhs,
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// A reflexive cell `⟨Zero | ⊤⟩ ~> ⟨Zero | ⊤⟩`: the unit step the
    /// normalizer eliminates.
    ///
    /// # Specification
    /// trivial.
    fn reflexive_cell() -> Cell
    {
        let face = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        Cell::new(
            face.clone(),
            face,
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// The cell `id` names in `store`.
    ///
    /// # Specification
    /// - panics: when the store holds no such cell, which is a fixture defect.
    fn stored(
        store: &CellStore,
        id: CellId,
    ) -> &Cell
    {
        let Maybe::Present(cell) = store.get(id)
        else {
            panic!("the fixture names a stored cell");
        };
        cell
    }

    /// The fused-cell store and the tracelet `derive_fused` certifies.
    ///
    /// # Specification
    /// - panics: when the composition is not found or does not fuse, which is a
    ///   fixture defect.
    fn fused_fixture() -> (CellStore, Tracelet)
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let add = store.insert(add_s());
        let composition = enumerate_overlaps(&store)
            .into_iter()
            .find(|candidate| {
                candidate.kind == OverlapKind::Composition
                    && candidate.left == frame
                    && candidate.right == add
            })
            .expect("the composition overlap exists");
        let (_fused, tracelet) =
            derive_fused(&composition, &mut store).expect("the fused cell is derived");
        (store, tracelet)
    }

    #[test]
    fn a_recorded_derivation_normalizes_to_a_replay_receipt()
    {
        let (store, tracelet) = fused_fixture();
        let normal = normalize(
            &store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_a,
        )
        .expect("the two-step derivation replays, so it normalizes");
        assert_eq!(
            tracelet.overlap.peak, normal.peak,
            "the normal form records the boundary it was verified across"
        );
        assert_eq!(tracelet.joins_at, normal.joins_at, "join included");
        assert_eq!(
            2_usize,
            normal.schedule.len(),
            "the two-step path factors into two primitives"
        );
        assert_eq!(
            2_usize,
            normal.primitives.len(),
            "and the two are distinct primitives, so each is graded once"
        );
        for graded in normal.primitives.values() {
            assert_eq!(
                PrimMultiplicity::from(1_u32),
                graded.1,
                "each primitive occurs once"
            );
        }
    }

    #[test]
    fn a_fused_fixture_replays_both_certificate_paths_through_its_critical_path_plan()
    {
        let (store, tracelet) = fused_fixture();
        let witness_a = normalize_certified(
            &store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_a,
        )
        .expect("the generated certificate path_a replays");
        let witness_b = normalize_certified(
            &store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_b,
        )
        .expect("the generated certificate path_b replays");
        assert_eq!(
            witness_a.normal_form().joins_at,
            witness_b.normal_form().joins_at,
            "both certificate paths reach the same join"
        );
        let plan_a = witness_a.replay_plan();
        let plan_b = witness_b.replay_plan();
        // A replay plan is per path, not per boundary: `path_a` fires the two
        // constituent cells and `path_b` the one fused cell, so the two plans
        // schedule different cells. What the two certificate paths share is
        // the join they replay to, and that is what is asserted below.
        assert_ne!(
            plan_a.levels(),
            plan_b.levels(),
            "the fused path and the two-step path are different derivations of one boundary"
        );
        let start = SequentAlphabet::skolemize(&tracelet.overlap.peak);
        let sequential_a = run_schedule(&store, &start, &witness_a.canonical_path())
            .expect("the sequential canonical path_a replay succeeds");
        let sequential_b = run_schedule(&store, &start, &witness_b.canonical_path())
            .expect("the sequential canonical path_b replay succeeds");
        assert_eq!(sequential_a, sequential_b, "both sequential replays agree");
        let Ok(Maybe::Present(planned)) = plan_a.replay_with_fuel(&store, plan_a.critical_path())
        else {
            panic!("the critical-path budget replays the complete plan");
        };
        assert_eq!(
            sequential_a, planned,
            "planned replay equals sequential replay"
        );
        let Ok(Maybe::Present(planned_b)) = plan_b.replay_with_fuel(&store, plan_b.critical_path())
        else {
            panic!("the critical-path budget replays the complete fused plan");
        };
        assert_eq!(
            sequential_b, planned_b,
            "the fused path's planned replay equals its sequential replay"
        );
        let mut on_demand = start;
        for level in 0_usize .. plan_a.levels().len() {
            on_demand = plan_a
                .replay_level(&store, &on_demand, ReplayLevel::from(level))
                .expect("each independent level replays on demand");
        }
        assert_eq!(
            sequential_a, on_demand,
            "on-demand replay equals sequential replay"
        );
        assert_eq!(
            CausalDepth::from(plan_a.levels().len()),
            plan_a.critical_path(),
            "fuel is the number of antichain levels"
        );
        assert!(
            matches!(
                plan_a.replay_level(&store, &on_demand, ReplayLevel::from(plan_a.levels().len())),
                Err(NormalFormObstruction::InvalidReplayLevel { .. })
            ),
            "a level outside the plan is refused as a typed obstruction, not a panic"
        );
        assert!(
            matches!(
                plan_a.replay_with_fuel(&store, CausalDepth::from(0_usize)),
                Ok(Maybe::Absent(replay_fuel::Absent::InsufficientFuel))
            ),
            "serialization work cannot be substituted for critical-path fuel"
        );
    }

    #[test]
    fn the_canonical_path_replays_to_the_recorded_join()
    {
        let (store, tracelet) = fused_fixture();
        let normal = normalize(
            &store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_a,
        )
        .expect("the two-step derivation normalizes");
        let Maybe::Present(path) = normal.canonical_path()
        else {
            panic!("every scheduled address is in the factorization");
        };
        let replayed = Tracelet {
            overlap: tracelet.overlap,
            path_a: path.clone(),
            path_b: path,
            joins_at: tracelet.joins_at,
        };
        assert!(
            bool::from(replayed.replay(&store)),
            "the decompressed canonical schedule is a derivation of the same boundary"
        );
    }

    #[test]
    fn one_derivation_is_nf_equal_to_itself()
    {
        let (store, tracelet) = fused_fixture();
        let normal = normalize(
            &store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_a,
        )
        .expect("the two-step derivation normalizes");
        assert!(
            bool::from(nf_equal(&normal, &normal)),
            "a normal form is its own normal form"
        );
        assert!(
            bool::from(tracelets_nf_equal(&store, &tracelet, &tracelet)),
            "and the certificate-level fast path agrees"
        );
    }

    #[test]
    fn replay_equal_derivations_may_be_nf_distinct()
    {
        // The asymmetry, exhibited rather than disclaimed: `derive_fused`
        // gives one boundary with a two-step `path_a` and a one-step `path_b`,
        // the same transformation by the replay oracle and two different
        // primitive factorizations. A negative from `nf_equal` therefore means
        // nothing about the certificates.
        let (store, tracelet) = fused_fixture();
        let two_step = normalize(
            &store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_a,
        )
        .expect("the two-step derivation normalizes");
        let fused = normalize(
            &store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_b,
        )
        .expect("the single fused step normalizes");
        assert!(
            !bool::from(nf_equal(&two_step, &fused)),
            "the two factorizations differ, so the normal forms do"
        );
        let as_two_step = Tracelet {
            overlap: tracelet.overlap.clone(),
            path_a: tracelet.path_a.clone(),
            path_b: tracelet.path_a.clone(),
            joins_at: tracelet.joins_at.clone(),
        };
        assert!(
            bool::from(replay_equivalent(&tracelet, &as_two_step, &store)),
            "and the replay oracle calls them the same transformation all the same"
        );
    }

    #[test]
    fn nf_equal_certificates_are_replay_equivalent()
    {
        let (store, tracelet) = fused_fixture();
        let twin = tracelet.clone();
        assert!(
            bool::from(tracelets_nf_equal(&store, &tracelet, &twin)),
            "the fast path certifies the pair"
        );
        assert!(
            bool::from(replay_equivalent(&tracelet, &twin, &store)),
            "and the replay oracle confirms it, the implication the fast path owes"
        );
    }

    #[test]
    fn a_unit_step_is_eliminated()
    {
        let mut store = CellStore::new();
        let reflexive = store.insert(reflexive_cell());
        let face = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        let path = alloc::vec![
            CellApp {
                cell: reflexive,
                at: Pos::root(),
            },
            CellApp {
                cell: reflexive,
                at: Pos::root(),
            },
        ];
        let normal =
            normalize(&store, &face, &face, &path).expect("a reflexive path reaches its own peak");
        assert!(
            normal.schedule.is_empty(),
            "both steps left the term unchanged, so unit elimination drops both"
        );
        assert!(
            normal.primitives.is_empty(),
            "and the factorization is the empty product"
        );
    }

    #[test]
    fn an_unknown_cell_identifier_is_refused()
    {
        let (store, tracelet) = fused_fixture();
        let missing = CellId::from(97_usize);
        let path = alloc::vec![CellApp {
            cell: missing,
            at: Pos::root(),
        }];
        let refusal = normalize(&store, &tracelet.overlap.peak, &tracelet.joins_at, &path)
            .expect_err("an unresolvable identifier is refused");
        assert_eq!(
            NormalFormObstruction::UnknownCell { cell: missing },
            refusal,
            "the refusal names the identifier that resolved to nothing"
        );
    }

    #[test]
    fn a_step_that_does_not_fire_is_refused()
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let peak = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        let step = CellApp {
            cell: frame,
            at: Pos::root(),
        };
        let refusal = normalize(&store, &peak, &peak, core::slice::from_ref(&step))
            .expect_err("the frame cell has no redex at this peak");
        assert_eq!(
            NormalFormObstruction::StepDoesNotFire {
                step: Box::new(step)
            },
            refusal,
            "the refusal carries the step that did not fire"
        );
    }

    #[test]
    fn a_path_that_misses_its_join_is_refused()
    {
        let (store, tracelet) = fused_fixture();
        let elsewhere = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        let refusal = normalize(&store, &tracelet.overlap.peak, &elsewhere, &tracelet.path_a)
            .expect_err("the recorded path does not reach this join");
        let NormalFormObstruction::PathMissesTheJoin { reached } = refusal
        else {
            panic!("the join check is what refuses this path");
        };
        assert_eq!(
            SequentAlphabet::skolemize(&tracelet.joins_at),
            *reached,
            "the refusal carries the term the recorded path actually reached"
        );
    }

    #[test]
    fn the_shift_quotient_is_empty_over_the_sequent_alphabet()
    {
        // A sequent command pattern is one cut whose children are a producer
        // and a consumer, so the only command position is the root and two
        // applications are never incomparable. The canonical schedule is
        // therefore the recorded order here, and the shift quotient is
        // exercised on an alphabet whose terms nest commands
        // (`tests/normal_form.rs`). This is a property of the alphabet, not a
        // defect of the quotient.
        let (store, tracelet) = fused_fixture();
        let normal = normalize(
            &store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_a,
        )
        .expect("the two-step derivation normalizes");
        let recorded: Vec<PrimId> = tracelet
            .path_a
            .iter()
            .map(|step| prim_address(stored(&store, step.cell), &step.at))
            .collect();
        assert_eq!(
            recorded, normal.schedule,
            "no transposition is licensed, so the canonical schedule is the recorded one"
        );
        assert_eq!(
            ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
            normal.convexity,
            "and the normal form carries the warrant it was taken under"
        );
    }

    #[test]
    fn the_content_address_is_taken_over_content()
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let add = store.insert(add_s());
        let frame_cell = stored(&store, frame);
        let add_cell = stored(&store, add);
        let root = Pos::root();
        let child = Pos::from_steps([PositionStep::from(0_usize)]);
        assert_eq!(
            prim_address(frame_cell, &root),
            prim_address(frame_cell, &root),
            "the address is a function of the content"
        );
        assert_ne!(
            prim_address(frame_cell, &root),
            prim_address(add_cell, &root),
            "cells with different content take different addresses"
        );
        assert_ne!(
            prim_address(frame_cell, &root),
            prim_address(frame_cell, &child),
            "and so do the same cell at different positions"
        );
        // The address is over content, not over the store index: an
        // independently built store hands the same cell a different id and the
        // same address.
        let mut other = CellStore::new();
        let _padding = other.insert(add_s());
        let elsewhere = other.insert(frame_defining_cell(&Sym::new("Succ")));
        assert_ne!(
            frame, elsewhere,
            "the two stores number the cell differently"
        );
        assert_eq!(
            prim_address(frame_cell, &root),
            prim_address(stored(&other, elsewhere), &root),
            "and the content address is the same all the same"
        );
    }

    #[test]
    fn the_two_address_domains_are_separated_by_type_and_by_digest()
    {
        // A cell address and a primitive address name different things, a cell
        // and a cell together with where it fired, so they are different types
        // and passing one where the other is meant does not compile. That half
        // cannot be asserted at runtime; what can be is that the domain
        // separator makes the digests differ too.
        let cell = frame_defining_cell(&Sym::new("Succ"));
        let PrimId(primitive) = prim_address(&cell, &Pos::root());
        let CellAddress(position_free) = cell_address(&cell);
        assert_ne!(
            primitive, position_free,
            "the domain separators keep the two digests of one cell apart"
        );
    }

    /// The ground peak `⟨Succ(Succ(Zero)) | add(Zero; ⊤)⟩` of the two-step
    /// (add-S) chain.
    ///
    /// # Specification
    /// trivial.
    fn chain_peak() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])])]),
            ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::top()),
        )
    }

    /// Run a recorded path from `start`.
    ///
    /// # Specification
    /// - panics: when a step does not fire, which is a fixture defect.
    fn run_path(
        store: &CellStore,
        start: &CmdPat,
        path: &[CellApp],
    ) -> CmdPat
    {
        run_schedule(store, start, path).expect("every step fires at its recorded position")
    }

    /// Complete a chain fixture around a store that already holds (add-S)
    /// under `add`: the peak, the join the two root steps reach, and the steps.
    ///
    /// # Specification
    /// - panics: when the chain does not fire, which is a fixture defect.
    fn finish_chain(
        store: CellStore,
        add: CellId,
    ) -> (CellStore, CmdPat, CmdPat, [CellApp; 2])
    {
        let peak = chain_peak();
        let steps = [
            CellApp {
                cell: add,
                at: Pos::root(),
            },
            CellApp {
                cell: add,
                at: Pos::root(),
            },
        ];
        let start = SequentAlphabet::skolemize(&peak);
        let joins_at = run_path(&store, &start, &steps);
        (store, peak, joins_at, steps)
    }

    /// The two-step (add-S) chain against a store holding only (add-S), so
    /// the rule takes the first identifier the store hands out.
    ///
    /// # Specification
    /// - panics: when the chain does not fire, which is a fixture defect.
    fn chain_fixture() -> (CellStore, CmdPat, CmdPat, [CellApp; 2])
    {
        let mut store = CellStore::new();
        let add = store.insert(add_s());
        finish_chain(store, add)
    }

    /// The same chain against a store holding an unrelated cell first, so
    /// (add-S) takes a different identifier for the same content.
    ///
    /// Two stores holding one cell under two handles are two presentations of
    /// one rule set, which is what the cross-store comparison is about.
    ///
    /// # Specification
    /// - panics: when the chain does not fire, which is a fixture defect.
    fn chain_fixture_behind_a_decoy() -> (CellStore, CmdPat, CmdPat, [CellApp; 2])
    {
        let mut store = CellStore::new();
        let decoy = store.insert(reflexive_cell());
        let add = store.insert(add_s());
        assert_ne!(
            decoy, add,
            "the two cells are distinct, so the store keeps both"
        );
        finish_chain(store, add)
    }

    /// The keys of `order`'s events, in canonical order.
    ///
    /// # Specification
    /// trivial.
    fn canonical_keys(order: &EventOrder) -> Vec<EventKey>
    {
        order
            .canonical_order()
            .into_iter()
            .filter_map(|index| match order.key(index) {
                | Maybe::Present(key) => Some(key),
                | Maybe::Absent(_) => None,
            })
            .collect()
    }

    #[test]
    fn the_causal_past_digest_reads_the_multiset_and_not_the_order()
    {
        // Arrival-order independence, at the digest: an event's direct
        // predecessors are listed in whichever linear extension was recorded,
        // so a fold that read that order would make the key, and through it
        // the canonical order, a property of the presentation.
        let (store, _peak, _join, steps) = chain_fixture();
        let address = prim_address(stored(&store, steps[0].cell), &Pos::root());
        let left = causal_past_address(address, &[]);
        let right = causal_past_address(address, &[
            causal_past_address(address, &[]),
            CausalPast::default(),
        ]);
        assert_ne!(
            left, right,
            "different predecessor sets give different digests"
        );
        assert_eq!(
            right,
            causal_past_address(address, &[
                CausalPast::default(),
                causal_past_address(address, &[])
            ]),
            "and the same set offered in the other order gives the same digest"
        );
        assert_ne!(
            left,
            causal_past_address(address, &[left]),
            "one address over two different pasts is two digests"
        );
    }

    #[test]
    fn the_event_key_is_taken_over_content_and_never_over_arrival_order()
    {
        // The key digests the resolved cell's content and the position, and a
        // `Cell` holds no store index, only its two faces, its orientation, its
        // provenance and its derived metadata. So two stores that intern one
        // rule under two identifiers give one key.
        let (plain, peak, _join, steps) = chain_fixture();
        let (decoyed, _decoy_peak, _decoy_join, decoy_steps) = chain_fixture_behind_a_decoy();
        assert_ne!(
            steps[0].cell, decoy_steps[0].cell,
            "the same rule carries two identifiers"
        );
        let here = event_order(&plain, &peak, &steps).expect("the chain replays");
        let there = event_order(&decoyed, &peak, &decoy_steps).expect("and so does its twin");
        assert_eq!(
            canonical_keys(&here),
            canonical_keys(&there),
            "the keys are the same, so nothing arrival-ordered or store-local reached them"
        );
    }

    #[test]
    fn a_replay_witness_carries_its_own_boundary_and_order()
    {
        let (store, peak, joins_at, steps) = chain_fixture();
        let witness = normalize_certified(&store, &peak, &joins_at, &steps)
            .expect("the two-step chain replays, so it normalizes");
        assert_eq!(
            &peak,
            witness.peak(),
            "the receipt records the boundary it was verified across"
        );
        assert_eq!(&joins_at, witness.joins_at(), "join included");
        assert_eq!(
            EventCount::from(2_usize),
            witness.event_order().event_count(),
            "both steps moved the term, so both are events"
        );
        assert_eq!(
            witness.normal_form().canonical_path(),
            Maybe::Present(witness.canonical_path()),
            "and the two spellings of the canonical path agree"
        );
    }

    #[test]
    fn a_certified_pair_is_equal_exactly_when_its_normal_forms_are()
    {
        let (store, peak, joins_at, steps) = chain_fixture();
        let left =
            normalize_certified(&store, &peak, &joins_at, &steps).expect("the chain normalizes");
        let right = normalize_certified(&store, &peak, &joins_at, &steps)
            .expect("and normalizes the same way twice");
        assert!(
            bool::from(certified_nf_equal(&left, &right)),
            "one derivation certifies equal to itself"
        );
        let start = SequentAlphabet::skolemize(&peak);
        let prefix = [steps[0].clone()];
        let prefix_join = run_path(&store, &start, &prefix);
        let short = normalize_certified(&store, &peak, &prefix_join, &prefix)
            .expect("the one-step prefix is a derivation of its own");
        assert!(
            !bool::from(certified_nf_equal(&left, &short)),
            "and a derivation reaching a different join does not"
        );
        assert_eq!(
            nf_equal(left.normal_form(), short.normal_form()),
            certified_nf_equal(&left, &short),
            "the certified equality delegates rather than deciding again"
        );
    }

    #[test]
    fn one_derivation_built_in_two_stores_compares_equal_across_them()
    {
        // One derivation, one rule, two stores that number that rule
        // differently. Comparing the handles says the two differ; comparing
        // what the handles resolve to says they are the same, which is the
        // answer replay would give.
        let (plain, peak, joins_at, steps) = chain_fixture();
        let (decoyed, decoy_peak, decoy_join, decoy_steps) = chain_fixture_behind_a_decoy();
        assert_eq!(peak, decoy_peak, "the two fixtures share a peak");
        assert_eq!(joins_at, decoy_join, "and a join");
        let left = normalize(&plain, &peak, &joins_at, &steps).expect("the chain normalizes");
        let right = normalize(&decoyed, &decoy_peak, &decoy_join, &decoy_steps)
            .expect("and so does its twin behind the decoy");
        assert_ne!(
            steps[0].cell, decoy_steps[0].cell,
            "the same rule really does carry two identifiers"
        );
        assert!(
            !bool::from(nf_equal(&left, &right)),
            "the handle-comparing equality separates the two presentations"
        );
        let across = nf_equal_across_stores(&plain, &left, &decoyed, &right)
            .expect("every factor resolves in its own store");
        assert!(
            bool::from(across),
            "and the content-comparing equality identifies them"
        );
    }

    #[test]
    fn across_stores_agrees_with_nf_equal_on_one_store()
    {
        let (store, peak, joins_at, steps) = chain_fixture();
        let left = normalize(&store, &peak, &joins_at, &steps).expect("the chain normalizes");
        let same =
            nf_equal_across_stores(&store, &left, &store, &left).expect("every factor resolves");
        assert_eq!(
            nf_equal(&left, &left),
            same,
            "read against one store the two equalities are the same equality"
        );
        let start = SequentAlphabet::skolemize(&peak);
        let prefix = [steps[0].clone()];
        let prefix_join = run_path(&store, &start, &prefix);
        let short = normalize(&store, &peak, &prefix_join, &prefix).expect("the prefix normalizes");
        let differing =
            nf_equal_across_stores(&store, &left, &store, &short).expect("every factor resolves");
        assert_eq!(
            nf_equal(&left, &short),
            differing,
            "and they agree on the negative direction too"
        );
    }

    #[test]
    fn two_stores_holding_different_cells_at_one_handle_compare_unequal()
    {
        // The cells are resolved and compared. One normal form is read against
        // two stores whose first cell differs, so everything the comparison
        // reads from the normal forms is identical and only the resolved
        // content separates them.
        let (plain, peak, joins_at, steps) = chain_fixture();
        let left = normalize(&plain, &peak, &joins_at, &steps).expect("the chain normalizes");
        let mut swapped = CellStore::new();
        let held = swapped.insert(reflexive_cell());
        assert_eq!(
            steps[0].cell, held,
            "the two stores put different cells under one identifier"
        );
        let across = nf_equal_across_stores(&plain, &left, &swapped, &left)
            .expect("the handle resolves in both stores");
        assert!(
            !bool::from(across),
            "so the comparison answers negative on the content it resolved"
        );
    }

    #[test]
    fn a_factor_naming_an_absent_cell_is_refused_across_stores()
    {
        let (plain, peak, joins_at, steps) = chain_fixture();
        let left = normalize(&plain, &peak, &joins_at, &steps).expect("the chain normalizes");
        let empty = CellStore::new();
        let refusal = nf_equal_across_stores(&plain, &left, &empty, &left);
        assert!(
            matches!(refusal, Err(NormalFormObstruction::UnknownCell { .. })),
            "a factor whose identifier resolves to nothing is refused, not answered"
        );
    }
}
