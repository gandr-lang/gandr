//! The session rules on the judgement's machine: the fork that binds two
//! endpoints, the actions that advance them, the offer whose arms agree on
//! the linear zone, and the fence that keeps an endpoint out of every former
//! that may run its use other than once. The decisions are stated in
//! [`crate::session`].

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::CoreTerm;
use gandr_core_nbe::FreeIndices;
use gandr_core_term::BinderDepth;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::ContextError;
use gandr_core_term::LinearUse;
use gandr_core_term::LinearZone;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::session::ActionKind;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::SessionType;
use gandr_core_term::session::Step as Move;
use gandr_core_term::shift_value_type;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use quenchant_shape::shape::Maybe;

use super::Direction;
use super::Frame;
use super::Goal;
use super::Machine;
use super::Ordinal;
use super::Produced;
use super::Step;
use super::Typing;
use crate::access::AccessDefect;
use crate::context::Atom;
use crate::context::Recording;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::session::Capture;
use crate::session::Endpoint;
use crate::session::ForkSide;
use crate::session::LinearityDefect;
use crate::session::LiveEndpoint;
use crate::session::ProtocolDefect;
use crate::session::session_at;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// Who bound a linear slot: a fork's or a receive's endpoint, a received
/// value, a hold's held value, an access's view, an entry's capability, or an
/// operation clause's continuation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Resident
{
    /// An endpoint a fork bound.
    Endpoint(Endpoint),
    /// A value the hold `at` holds.
    Held
    {
        /// The hold.
        at: ComputationId,
    },
    /// A value the receive `at` bound, opened spent: its reads copy.
    Received
    {
        /// The receive.
        at: ComputationId,
    },
    /// The buffer the receive `at` placed live, opened available: a send
    /// returns it once, and the receive's end refuses it unreturned.
    Buffer
    {
        /// The receive.
        at: ComputationId,
    },
    /// The view the access `at` lends, of a value held at `grade`.
    View
    {
        /// The access.
        at: ComputationId,
        /// The grade the lent value is held at.
        grade: gandr_core_term::memory::HoldGrade,
        /// The held slot's position above the run's base.
        held: usize,
    },
    /// A capability the run's entry holds, to migrate once to `world`.
    Capability
    {
        /// The world it migrates to.
        world: gandr_core_term::world::World,
    },
    /// The continuation the operation clause `clause` receives, which holds an
    /// obligation: a resumption or an abandonment spends it once.
    Continuation
    {
        /// The clause's body.
        clause: ComputationId,
    },
}

/// A linear slot the run bound: who bound it, and the intuitionistic depth
/// its declared type was formed at.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Opened
{
    /// Who bound it.
    pub resident: Resident,
    /// The intuitionistic depth at the binder.
    pub depth: BinderDepth,
}

/// A held slot an access lends: where it stands and the mode it is lent in.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Lent
{
    /// The held slot's position above the run's base.
    pub position: usize,
    /// The mode the access lends it in.
    pub mode: AccessMode<()>,
}

/// A held slot a region keeps a shared view of: frozen against an exclusive
/// access until the region's scope ends.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Keep
{
    /// The held slot's position above the run's base.
    pub position: usize,
    /// The region the view is kept in.
    pub region: RegionDepth,
}

/// An operation clause's continuation that holds an obligation: the level its
/// stack is bound at, the linear slot its end spends and the clause.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Owed
{
    /// The intuitionistic level the stack is bound at.
    pub stack: usize,
    /// The linear slot's position above the run's base.
    pub slot: usize,
    /// The clause's body.
    pub clause: ComputationId,
}

/// The linear state of one run: who bound each linear slot it opened, the
/// held slots its accesses lend, the zones its offers restore and compare,
/// and the free linear indices of the terms it read.
#[derive(Debug)]
pub(super) struct Sessions
{
    /// The linear depth the run began at; slots below it are not the run's.
    pub base: BinderDepth,
    /// One entry per linear slot above `base`, outermost first.
    pub opened: Vec<Opened>,
    /// Each held slot an access lends, with its mode, the innermost access
    /// last.
    pub lent: Vec<Lent>,
    /// Each held slot a region keeps a shared view of, in the order kept.
    pub kept: Vec<Keep>,
    /// How many linear slots above `base` stood open as each region began —
    /// a capability scope's subject, or a hold's scope past its held slot —
    /// outermost first: a slot below a region's mark outlives the region.
    pub regions: Vec<usize>,
    /// How the run's own type reaches a region its definition abstracts, `A at
    /// r` under `@[r : Region]`: where it reaches one, a captor or a child may
    /// name a value kept in a region while no region is open.
    pub abstracted: crate::capability::Reach,
    /// Each capability scope and operation whose clause receives a
    /// continuation holding an obligation, in the order met.
    pub owing: Vec<(ComputationId, gandr_core_term::effect::OperationName)>,
    /// Each open clause's continuation that holds an obligation, innermost
    /// last.
    pub owed: Vec<Owed>,
    /// The level of the owed stack the resumption or abandonment being
    /// judged ends: its one mention that reads it.
    pub ending: Option<usize>,
    /// Each open offer's zone as the offer found it, then as its first arm
    /// left it, innermost offer last.
    zones: Vec<LinearZone>,
    /// The free linear indices of every term asked, each answered once.
    free: FreeIndices,
}

impl Sessions
{
    /// The linear state of a run that begins with `base` linear slots open,
    /// its own type reaching a region its definition abstracts as `abstracted`
    /// says.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn new(
        base: BinderDepth,
        abstracted: crate::capability::Reach,
    ) -> Self
    {
        Self {
            base,
            opened: Vec::new(),
            lent: Vec::new(),
            kept: Vec::new(),
            regions: Vec::new(),
            abstracted,
            owing: Vec::new(),
            owed: Vec::new(),
            ending: None,
            zones: Vec::new(),
            free: FreeIndices::default(),
        }
    }
}

/// How far a run's linear zone, its lendings, its keeps, its regions and its
/// offers' zones stood: what a recovered or refused run falls back to.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Scope
{
    /// The linear depth.
    linear: BinderDepth,
    /// The lendings held.
    lent: usize,
    /// The keeps held.
    kept: usize,
    /// The regions open.
    regions: usize,
    /// The capture records held.
    owing: usize,
    /// The owed continuations held.
    owed: usize,
    /// The offers' zones held.
    zones: usize,
}

/// Where one offer's or one case's zones stand on the run's zone stack: the
/// zone as the former found it at the mark, the zone its arms left so far one
/// above.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct ZoneMark(usize);

/// How a case's arms leave the linear zone: one after another while the run
/// holds no value, or each from the zone the case found and joined after the
/// last while it holds one.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Joining
{
    /// The run holds no value: each arm starts from the zone the one before
    /// it left.
    Threaded,
    /// The run holds a value: each arm starts from the zone at the mark, and
    /// a held value one arm consumed counts as consumed after the case.
    Joined(ZoneMark),
}

/// One linear slot, read: who bound it, its declared type, its remaining
/// use, the depth its type stands at and its position above the run's base.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Resided
{
    /// Who bound it.
    pub resident: Resident,
    /// Its declared type, at `depth`.
    pub state: ValueTypeId,
    /// Its remaining use.
    pub use_state: LinearUse,
    /// The intuitionistic depth `state` stands at.
    pub depth: BinderDepth,
    /// Its position above the run's base.
    pub position: usize,
}

/// One endpoint's slot, read: its endpoint, session type, remaining use and
/// the depth its type stands at.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Slot
{
    /// The endpoint.
    endpoint: Endpoint,
    /// Its session type, at `depth`.
    state: ValueTypeId,
    /// Its remaining use.
    use_state: LinearUse,
    /// The intuitionistic depth `state` stands at.
    depth: BinderDepth,
}

impl Machine<'_, '_>
{
    /// Where the linear zone, the lendings, the keeps, the regions and the
    /// offers' zones stand.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn session_scope(&self) -> Scope
    {
        Scope {
            linear: self.context.depth(Zone::Linear),
            lent: self.sessions.lent.len(),
            kept: self.sessions.kept.len(),
            regions: self.sessions.regions.len(),
            owing: self.sessions.owing.len(),
            owed: self.sessions.owed.len(),
            zones: self.sessions.zones.len(),
        }
    }

    /// Drop every linear slot bound, every lending, keep, region, capture
    /// record and owed continuation made and every offer zone kept since
    /// `scope`, spent or not: the linear half of unwinding a refused or
    /// recovered judgement.
    ///
    /// # Specification
    /// - requires: the zones stand at or above `scope`.
    /// - ensures: they stand at `scope`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal inside a fork leaves the context's linear
    ///   zone as the run found it.
    /// - witness: `judgement::session::tests::a_leftover_endpoint_is_reported_by_name`
    #[spec(ensures: self.context.depth(Zone::Linear) <= scope.linear
        && self.sessions.lent.len() <= scope.lent
        && self.sessions.kept.len() <= scope.kept
        && self.sessions.regions.len() <= scope.regions
        && self.sessions.owing.len() <= scope.owing
        && self.sessions.owed.len() <= scope.owed
        && self.sessions.zones.len() <= scope.zones)]
    pub(super) fn close_sessions(
        &mut self,
        scope: Scope,
    )
    {
        self.context.binders().truncate(Zone::Linear, scope.linear);
        let kept = usize::from(scope.linear).saturating_sub(usize::from(self.sessions.base));
        self.sessions.opened.truncate(kept);
        self.sessions.lent.truncate(scope.lent);
        self.sessions.kept.truncate(scope.kept);
        self.sessions.regions.truncate(scope.regions);
        self.sessions.owing.truncate(scope.owing);
        self.sessions.owed.truncate(scope.owed);
        self.sessions.ending = None;
        self.sessions.zones.truncate(scope.zones);
    }

    /// The endpoints the run bound and still holds, outermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per endpoint's slot above the run's base, with its
    ///   endpoint, session type and remaining use; held values and views are
    ///   left out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a leftover endpoint's failure lists the endpoint left
    ///   and the one the child consumed.
    /// - witness: `judgement::session::tests::a_leftover_endpoint_is_reported_by_name`
    #[spec(ensures: |ret| ret.len() <= self.sessions.opened.len())]
    pub(super) fn live_endpoints(&mut self) -> Vec<LiveEndpoint>
    {
        let base = usize::from(self.sessions.base);
        let opened = &self.sessions.opened;
        self.context
            .binders()
            .linear_slots()
            .skip(base)
            .zip(opened)
            .filter_map(|((state, use_state), opened)| match opened.resident {
                Resident::Endpoint(endpoint) => Some(LiveEndpoint {
                    endpoint,
                    state,
                    use_state,
                }),
                Resident::Received { .. }
                | Resident::Buffer { .. }
                | Resident::Held { .. }
                | Resident::View { .. }
                | Resident::Capability { .. }
                | Resident::Continuation { .. } => None,
            })
            .collect()
    }

    /// The linear slot `index` names, read at `at`, whoever bound it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot's resident, declared type, use, depth and position.
    /// - fails: [`CheckRefusal::Linearity`] naming [`LinearityDefect::Unbound`]
    ///   at `at` for an index past the zone; [`CheckRefusal::MachineInvariant`]
    ///   for a slot the run did not bind.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every action, access and eliminator reads its slot
    ///   here, so the seat exchange, the counter and every refusal by resident
    ///   observe it.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    #[spec(ensures: |ret| match ret {
        | Ok(_) | Err(CheckRefusal::MachineInvariant) => true,
        | Err(CheckRefusal::Linearity { at: refused, defect: LinearityDefect::Unbound { index: unbound } }) => {
            refused == at && unbound == index
        },
        | Err(CheckRefusal::Located { at: refused, defect: crate::worlds::LocatedDefect::Elsewhere { bound } }) => {
            refused == at && bound != self.context.world()
        },
        | Err(_) => false,
    })]
    pub(super) fn resided(
        &mut self,
        at: CoreNode,
        index: DeBruijnIndex,
    ) -> Result<Resided, CheckRefusal>
    {
        let unbound = CheckRefusal::Linearity {
            at,
            defect: LinearityDefect::Unbound { index },
        };
        let binders = self.context.binders();
        let depth = usize::from(binders.depth(Zone::Linear));
        let state = binders
            .declared(Zone::Linear, index)
            .map_err(|_fault| unbound)?;
        let use_state = binders.linear_use(index).map_err(|_fault| unbound)?;
        let used = binders.world();
        let bound = binders
            .located(Zone::Linear, index)
            .map_err(|_fault| unbound)?;
        if bound != used {
            return Err(CheckRefusal::Located {
                at,
                defect: crate::worlds::LocatedDefect::Elsewhere { bound },
            });
        }
        let position = usize::try_from(u32::from(index))
            .ok()
            .and_then(|index| depth.checked_sub(index)?.checked_sub(1))
            .and_then(|position| position.checked_sub(usize::from(self.sessions.base)))
            .ok_or(CheckRefusal::MachineInvariant)?;
        let opened = self
            .sessions
            .opened
            .get(position)
            .ok_or(CheckRefusal::MachineInvariant)?;
        Ok(Resided {
            resident: opened.resident,
            state,
            use_state,
            depth: opened.depth,
            position,
        })
    }

    /// The endpoint's slot `index` names, read at `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot's endpoint, session type, use and depth.
    /// - fails: as [`Self::resided`]; [`CheckRefusal::ShapeMismatch`] wanting
    ///   [`ExpectedShape::Session`] at a term `at` whose slot holds a value or
    ///   a view, and [`CheckRefusal::MachineInvariant`] at a type.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every action reads its endpoint here, so the seat
    ///   exchange and every refusal by endpoint observe it.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    #[spec(ensures: |ret| match ret {
        | Ok(_) | Err(CheckRefusal::MachineInvariant | CheckRefusal::ShapeMismatch { .. }) => true,
        | Err(CheckRefusal::Linearity { at: refused, defect: LinearityDefect::Unbound { index: unbound } }) => {
            refused == at && unbound == index
        },
        | Err(CheckRefusal::Located { at: refused, .. }) => refused == at,
        | Err(_) => false,
    })]
    fn slot(
        &mut self,
        at: CoreNode,
        index: DeBruijnIndex,
    ) -> Result<Slot, CheckRefusal>
    {
        let resided = self.resided(at, index)?;
        match resided.resident {
            Resident::Endpoint(endpoint) => Ok(Slot {
                endpoint,
                state: resided.state,
                use_state: resided.use_state,
                depth: resided.depth,
            }),
            Resident::Received { .. }
            | Resident::Buffer { .. }
            | Resident::Held { .. }
            | Resident::View { .. }
            | Resident::Capability { .. }
            | Resident::Continuation { .. } => match at {
                CoreNode::Term(term) => Err(CheckRefusal::ShapeMismatch {
                    at: term,
                    wanted: ExpectedShape::Session,
                    found: TypeNode::Value(resided.state),
                }),
                CoreNode::Type(_) => Err(CheckRefusal::MachineInvariant),
            },
        }
    }

    /// The available linear slot `index` names, read at the action `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::slot`], its use still available.
    /// - fails: as [`Self::slot`]; [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::Closed`] for a consumed slot.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an action after `close` is refused by name.
    /// - witness: `judgement::session::tests::an_endpoint_used_after_close_is_refused`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|slot| slot.use_state == LinearUse::Available))]
    fn live(
        &mut self,
        at: ComputationId,
        index: DeBruijnIndex,
    ) -> Result<Slot, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        let slot = self.slot(node, index)?;
        match slot.use_state {
            LinearUse::Available => Ok(slot),
            LinearUse::Moved | LinearUse::Consumed => Err(CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::Closed {
                    endpoint: slot.endpoint,
                },
            }),
        }
    }

    /// `ty`, which stands at the intuitionistic depth `depth`, read where the
    /// judgement now stands.
    ///
    /// # Specification
    /// - requires: the judgement stands at or under `depth`.
    /// - ensures: `ty` itself at `depth`; otherwise `ty` shifted past the
    ///   binders opened since.
    /// - fails: [`CheckRefusal::MachineInvariant`] above `depth`.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a receive under the bind of an earlier receive reads
    ///   its payload at the bind's depth.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    /// - witness: `judgement::session::tests::a_type_is_read_shifted_past_the_binders_opened_since_it_was_formed`
    #[spec(
        captures: current = self.context.depth(Zone::Intuitionistic),
        ensures: |ret| (current != depth || ret == Ok(ty))
            && (current >= depth || ret == Err(CheckRefusal::MachineInvariant)),
    )]
    pub(super) fn here(
        &mut self,
        ty: ValueTypeId,
        depth: BinderDepth,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let opened = usize::from(self.context.depth(Zone::Intuitionistic))
            .checked_sub(usize::from(depth))
            .ok_or(CheckRefusal::MachineInvariant)?;
        if opened == 0 {
            return Ok(ty);
        }
        let opened = u32::try_from(opened).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        let arena = self.context.arena_mut();
        Ok(shift_value_type(arena, ty, Binders::from(opened)).settle(arena))
    }

    /// The pure returner of the unit, an action's type.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn unit_returner(&mut self) -> CompTypeId
    {
        let unit = self.context.atom(Atom::Unit).id();
        self.context.arena_mut().comp_type_returner(unit)
    }

    /// The free linear indices of `term`, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the linear indices `term` reads without binding.
    /// - fails: [`CheckRefusal::DanglingNode`] at `term` for a node the arena
    ///   does not hold; [`CheckRefusal::MachineInvariant`] when the walk's
    ///   order breaks.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk naming an endpoint and a fork naming one in
    ///   both halves are refused through it.
    /// - witness: `judgement::session::tests::an_endpoint_captured_by_a_thunk_is_refused`
    #[spec(ensures: |ret| match ret {
        | Ok(ref indices) => indices.is_sorted(),
        | Err(ref refusal) => matches!(*refusal, CheckRefusal::DanglingNode { .. } | CheckRefusal::MachineInvariant),
    })]
    pub(super) fn free_linear(
        &mut self,
        term: CoreTerm,
    ) -> Result<Vec<DeBruijnIndex>, CheckRefusal>
    {
        let node = match term {
            CoreTerm::Value(id) => CoreNode::Term(TermNode::Value(id)),
            CoreTerm::Computation(id) => CoreNode::Term(TermNode::Computation(id)),
        };
        self.sessions
            .free
            .linear(self.context.arena(), term)
            .map(<[DeBruijnIndex]>::to_vec)
            .map_err(|fault| match fault {
                gandr_core_nbe::FreeFault::Dangling => CheckRefusal::DanglingNode { node },
                gandr_core_nbe::FreeFault::MachineInvariant => CheckRefusal::MachineInvariant,
            })
    }

    /// The free linear indices `term` consumes, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the held slots a consume in `term` moves out of without
    ///   binding them.
    /// - fails: as [`Self::free_linear`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold consuming an outer hold is refused through it,
    ///   and a case whose arms consume it checks.
    /// - witness: `judgement::access::tests::a_case_s_arms_each_take_a_hold_from_where_the_case_found_it_1488`
    #[spec(ensures: |ret| match ret {
        | Ok(ref indices) => indices.is_sorted(),
        | Err(ref refusal) => matches!(*refusal, CheckRefusal::DanglingNode { .. } | CheckRefusal::MachineInvariant),
    })]
    fn free_consumed(
        &mut self,
        term: CoreTerm,
    ) -> Result<Vec<DeBruijnIndex>, CheckRefusal>
    {
        let node = match term {
            CoreTerm::Value(id) => CoreNode::Term(TermNode::Value(id)),
            CoreTerm::Computation(id) => CoreNode::Term(TermNode::Computation(id)),
        };
        self.sessions
            .free
            .consumed(self.context.arena(), term)
            .map(<[DeBruijnIndex]>::to_vec)
            .map_err(|fault| match fault {
                gandr_core_nbe::FreeFault::Dangling => CheckRefusal::DanglingNode { node },
                gandr_core_nbe::FreeFault::MachineInvariant => CheckRefusal::MachineInvariant,
            })
    }

    /// Refuse a linear resident named where its use may run other than once:
    /// a thunk, a fixpoint, a branching former, a first-class stack, a
    /// handler, a capability scope or a shift, while the run holds one. A
    /// branch may read a held value: a read copies, and each branch lends it
    /// at most for its own extent. A case's arms are separate paths, so an arm
    /// may consume a held value: each arm starts from the hold as the case
    /// found it, and the case leaves it consumed when any arm consumed it. A
    /// fold's step runs once per element and a lazy product's components in
    /// any number, so neither consumes one. A capability scope's clause
    /// receives the rest of its body as a continuation it may resume twice or
    /// drop, so the body names only residents that owe nothing: a held value,
    /// whose slot stands outside the scope, a received value and a shared
    /// view, each of which a read copies. A thunk or a stack checked at a type
    /// kept in a region may name a shared view whose held slot outlives that
    /// region: the slot is kept, frozen until the region's scope ends. Inside
    /// a capability scope, a thunk or a stack names no variable kept in a
    /// region deeper than the one its own type is kept in. Every former but a
    /// branch names no continuation an operation clause owes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a goal of another former, or any goal while the run holds no
    ///   linear slot, no scope is open and the checked type abstracts no
    ///   region, passes without its free indices read; a kept thunk or stack
    ///   keeps each shared view it names, and nothing else changes.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::Captured`] at the goal's term, with the first
    ///   endpoint it names and what may run it, and
    ///   [`LinearityDefect::ContinuationCaptured`] for an owed continuation it
    ///   names; [`CheckRefusal::Access`] naming [`AccessDefect::Escaped`] for a
    ///   view no region keeps, [`AccessDefect::HeldCaptured`] for a held value
    ///   and for one a fold or a lazy product consumes, and
    ///   [`AccessDefect::KeptEscaped`] for a variable kept deeper than the
    ///   goal; a shift names the innermost resident the run holds, which its
    ///   captured continuation may resume twice.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk naming an endpoint is refused while the same
    ///   action outside one checks; a thunk kept in a scope's region keeps a
    ///   shared view and the same thunk kept in none is refused; a capability
    ///   scope whose body closes an endpoint is refused while one whose body
    ///   reads a held value checks.
    /// - witness: `judgement::session::tests::an_endpoint_captured_by_a_thunk_is_refused`
    /// - witness: `judgement::access::tests::a_view_kept_in_a_region_lives_as_long_as_its_scope`
    /// - witness: `judgement::session::tests::a_scope_names_only_residents_that_owe_nothing_1336`
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    /// - witness: `judgement::access::tests::a_thunk_naming_a_value_kept_at_a_region_binder_is_kept_there_1221`
    /// - witness: `judgement::access::tests::a_case_s_arms_each_take_a_hold_from_where_the_case_found_it_1488`
    #[spec(
        captures: [
            holding = self.context.depth(Zone::Linear) > self.sessions.base,
            scoped = !self.sessions.regions.is_empty(),
            abstracted = self.sessions.abstracted != crate::capability::Reach::Clear,
        ],
        ensures: |ret| holding || scoped || abstracted || ret.is_ok(),
    )]
    pub(super) fn fence(
        &mut self,
        goal: Goal,
    ) -> Result<(), CheckRefusal>
    {
        let holding = self.context.depth(Zone::Linear) > self.sessions.base;
        let abstracted = self.sessions.abstracted != crate::capability::Reach::Clear;
        if !holding && !abstracted && self.sessions.regions.is_empty() {
            return Ok(());
        }
        let (term, node, by) = match goal {
            Goal::Value { term, .. } => {
                let by = match *self.value(term)? {
                    Value::Thunk(_) => Capture::Thunk,
                    Value::Reify(_) => Capture::Stack,
                    Value::Primitive { .. }
                    | Value::PathRefl(_)
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Here(_)
                    | Value::Funext(..)
                    | Value::Equiv(..)
                    | Value::Univalence(..)
                    | Value::Ua { .. }
                    | Value::SessionRelated { .. }
                    | Value::Stay(_)
                    | Value::Then(..)
                    | Value::FlowProduct(..)
                    | Value::Forward(_)
                    | Value::FunctionFlow(..)
                    | Value::Recorded(_)
                    | Value::Dialogue(_)
                    | Value::Web(_)
                    | Value::Returned(_)
                    | Value::Nested(_)
                    | Value::Run(_)
                    | Value::RecordUpdate { .. }
                    | Value::Variable { .. }
                    | Value::Constant(_)
                    | Value::Literal(_)
                    | Value::Tuple(_)
                    | Value::Injection(..)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Ascribe { .. }
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..)
                    | Value::Constructor { .. }
                    | Value::Record(_)
                    | Value::Hole(_)
                    | Value::Mark { .. }
                    | Value::Row(_) => return Ok(()),
                };
                (
                    CoreTerm::Value(term),
                    CoreNode::Term(TermNode::Value(term)),
                    by,
                )
            },
            Goal::Computation { .. } if !holding => return Ok(()),
            Goal::Computation { term, .. } => {
                let by = match *self.computation(term)? {
                    Computation::Fixpoint { .. } => Capture::Recursion,
                    Computation::Case { .. }
                    | Computation::DataCase { .. }
                    | Computation::With(..)
                    | Computation::ListFold { .. }
                    | Computation::ListCase { .. } => Capture::Branch,
                    Computation::Handle { .. } | Computation::Scope { .. } => Capture::Continuation,
                    Computation::Shift(_) => {
                        let node = CoreNode::Term(TermNode::Computation(term));
                        let innermost = self.resided(node, DeBruijnIndex::from(0_u32))?;
                        return captured(node, innermost.resident, Capture::Continuation);
                    },
                    Computation::Primitive { .. }
                    | Computation::Transport(..)
                    | Computation::PathTransport { .. }
                    | Computation::Ride { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::Lambda(_)
                    | Computation::Application(..)
                    | Computation::Return(_)
                    | Computation::Bind(..)
                    | Computation::Ascribe { .. }
                    | Computation::Force(_)
                    | Computation::Decompose(_)
                    | Computation::Split { .. }
                    | Computation::RecordProjection(..)
                    | Computation::TupleProjection(..)
                    | Computation::Hole(_)
                    | Computation::Mark { .. }
                    | Computation::Perform { .. }
                    | Computation::Exercise { .. }
                    | Computation::Resume(..)
                    | Computation::Abandon(_)
                    | Computation::Reset(_)
                    | Computation::Project(..)
                    | Computation::Session(_)
                    | Computation::Memory(_)
                    | Computation::World(_) => return Ok(()),
                };
                (
                    CoreTerm::Computation(term),
                    CoreNode::Term(TermNode::Computation(term)),
                    by,
                )
            },
            Goal::Form(_) | Goal::Stack { .. } => return Ok(()),
        };
        // A branch runs once, and the arms' agreement checks the
        // continuation's slot; every other captor may run it twice or never.
        if by != Capture::Branch {
            self.owed_named(term, node, by)?;
        }
        // A case's arms are separate paths it joins; a fold's step runs once
        // per element, and a lazy product's components may run in any number.
        let joins = if let CoreTerm::Computation(id) = term {
            matches!(
                *self.computation(id)?,
                Computation::Case { .. }
                    | Computation::DataCase { .. }
                    | Computation::ListCase { .. }
            )
        }
        else {
            false
        };
        let scope = match goal {
            Goal::Computation { term, .. } => {
                matches!(*self.computation(term)?, Computation::Scope { .. })
            },
            Goal::Value { .. } | Goal::Form(_) | Goal::Stack { .. } => false,
        };
        let kept = match goal {
            Goal::Value {
                direction: Direction::Check(expected),
                ..
            } if matches!(by, Capture::Thunk | Capture::Stack) => self.kept_in(expected)?,
            Goal::Value { .. } | Goal::Computation { .. } | Goal::Form(_) | Goal::Stack { .. } => {
                Region::Held
            },
        };
        if matches!(by, Capture::Thunk | Capture::Stack)
            && (self.sessions.abstracted != crate::capability::Reach::Clear
                || !self.sessions.regions.is_empty())
        {
            self.contained(term, node, kept)?;
        }
        if !holding {
            return Ok(());
        }
        if by == Capture::Branch && !joins {
            for index in self.free_consumed(term)? {
                if let Resident::Held { .. } = self.resided(node, index)?.resident {
                    return Err(CheckRefusal::Access {
                        at: node,
                        defect: AccessDefect::HeldCaptured { by },
                    });
                }
            }
        }
        for index in self.free_linear(term)? {
            let named = self.resided(node, index)?;
            if let (Region::Scoped(region), Resident::View { at, held, .. }) =
                (kept, named.resident)
                && matches!(
                    *self.computation(at)?,
                    Computation::Memory(MemoryForm::Access {
                        mode: AccessMode::Shared,
                        ..
                    })
                )
                && usize::try_from(u32::from(region))
                    .ok()
                    .and_then(|depth| depth.checked_sub(1))
                    .and_then(|scope| self.sessions.regions.get(scope))
                    .is_some_and(|&mark| held < mark)
            {
                self.sessions.kept.push(Keep {
                    position: held,
                    region,
                });
                continue;
            }
            if scope && self.owing(named.resident)? == Owing::Nothing {
                continue;
            }
            captured(node, named.resident, by)?;
        }
        Ok(())
    }

    /// What `resident` owes that a continuation run twice or never would
    /// break: an endpoint's protocol, a buffer's return, an exclusive view's
    /// resume or abort, a capability's one migration and a clause's
    /// continuation's one end; a held value, a received value and a shared
    /// view, which a read copies, owe nothing.
    ///
    /// # Specification
    /// - requires: a view's access is in the arena.
    /// - ensures: [`Owing::Something`] exactly for an endpoint, a buffer, a
    ///   capability, a continuation and a view of an exclusive access.
    /// - fails: [`CheckRefusal::DanglingNode`] for a view whose access is not
    ///   in the arena.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope naming an endpoint is refused and one reading
    ///   a held value checks.
    /// - witness: `judgement::session::tests::a_scope_names_only_residents_that_owe_nothing_1336`
    #[spec(ensures: |ret| match resident {
        | Resident::Endpoint(_) | Resident::Buffer { .. } | Resident::Capability { .. } | Resident::Continuation { .. } => matches!(ret, Ok(Owing::Something)),
        | Resident::Held { .. } | Resident::Received { .. } => matches!(ret, Ok(Owing::Nothing)),
        | Resident::View { .. } => true,
    })]
    fn owing(
        &self,
        resident: Resident,
    ) -> Result<Owing, CheckRefusal>
    {
        Ok(match resident {
            Resident::Endpoint(_)
            | Resident::Buffer { .. }
            | Resident::Capability { .. }
            | Resident::Continuation { .. } => Owing::Something,
            Resident::Held { .. } | Resident::Received { .. } => Owing::Nothing,
            Resident::View { at, .. } => {
                if matches!(
                    *self.computation(at)?,
                    Computation::Memory(MemoryForm::Access {
                        mode: AccessMode::Shared,
                        ..
                    })
                ) {
                    Owing::Nothing
                }
                else {
                    Owing::Something
                }
            },
        })
    }

    /// The region a value checked at `expected` is kept in: the one
    /// `expected` names at its weak head, or [`Region::Held`] for a type kept
    /// in none.
    ///
    /// # Specification
    /// trivial.
    fn kept_in(
        &mut self,
        expected: ValueTypeId,
    ) -> Result<Region, CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        if let ValueTypeView::Kept { region, .. } = value_type_view(self.context.arena(), head)? {
            return Ok(region);
        }
        Ok(Region::Held)
    }

    /// Refuse the thunk or stack `term` at `node` naming a variable kept in a
    /// region that ends while `kept`, the region its own type is kept in, is
    /// still live: forced past that region's end, the variable would outlive
    /// it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing changes.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::KeptEscaped`]
    ///   at `node` for the first free intuitionistic variable whose type
    ///   reaches a type kept in a region that ends while `kept` is still live,
    ///   any region at all when `kept` is [`Region::Held`];
    ///   [`CheckRefusal::DanglingNode`] and [`CheckRefusal::MachineInvariant`]
    ///   as [`Self::free_linear`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk forcing a kept thunk is refused at a type
    ///   kept in no region and checks at one kept in the same region; a thunk
    ///   forcing a parameter kept at a region its definition abstracts is
    ///   refused at a type kept in no region.
    /// - witness: `judgement::access::tests::a_view_kept_in_a_region_lives_as_long_as_its_scope`
    /// - witness: `capability::tests::a_bound_region_outlives_every_scope_and_no_held_one_1221`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::Access { at, defect }) => at == node && defect == AccessDefect::KeptEscaped,
        | Ok(()) | Err(_) => true,
    })]
    fn contained(
        &mut self,
        term: CoreTerm,
        node: CoreNode,
        kept: Region,
    ) -> Result<(), CheckRefusal>
    {
        let free = self
            .sessions
            .free
            .intuitionistic(self.context.arena(), term)
            .map(<[DeBruijnIndex]>::to_vec)
            .map_err(|fault| match fault {
                gandr_core_nbe::FreeFault::Dangling => CheckRefusal::DanglingNode { node },
                gandr_core_nbe::FreeFault::MachineInvariant => CheckRefusal::MachineInvariant,
            })?;
        for index in free {
            let declared = self
                .context
                .binders()
                .declared(Zone::Intuitionistic, index)
                .map_err(|_fault| CheckRefusal::MachineInvariant)?;
            let reach =
                crate::capability::reaches(self.context.arena(), TypeNode::Value(declared), kept)?;
            if matches!(reach, crate::capability::Reach::Keeps) {
                return Err(CheckRefusal::Access {
                    at: node,
                    defect: AccessDefect::KeptEscaped,
                });
            }
        }
        Ok(())
    }

    /// Refuse the child `term` of the fork `at` naming a variable that lives
    /// in a region: the child runs as a peer no region bounds, so the region
    /// could end while the child still holds the variable. A region the
    /// definition abstracts is the caller's, and ends as soon.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing changes.
    /// - fails: [`CheckRefusal::CapabilityEscaped`] at the fork for the first
    ///   free intuitionistic variable whose type reaches a capability living in
    ///   any region but the held one, and [`CheckRefusal::Access`] naming
    ///   [`AccessDefect::KeptEscaped`] for one whose type reaches a value kept
    ///   in one; [`CheckRefusal::DanglingNode`] and
    ///   [`CheckRefusal::MachineInvariant`] as [`Self::free_linear`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child exercising its scope's capability is refused
    ///   whether or not it still holds its end, and a child exercising a
    ///   capability held for the run checks.
    /// - witness: `judgement::session::tests::a_child_exercises_only_what_outlives_every_region_1334`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::CapabilityEscaped { at: refused, .. }) => refused == TermNode::Computation(at),
        | Err(CheckRefusal::Access { at: refused, defect }) => refused == CoreNode::Term(TermNode::Computation(at)) && defect == AccessDefect::KeptEscaped,
        | Ok(()) | Err(_) => true,
    })]
    fn unbounded(
        &mut self,
        term: CoreTerm,
        at: ComputationId,
    ) -> Result<(), CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        let free = self
            .sessions
            .free
            .intuitionistic(self.context.arena(), term)
            .map(<[DeBruijnIndex]>::to_vec)
            .map_err(|fault| match fault {
                gandr_core_nbe::FreeFault::Dangling => CheckRefusal::DanglingNode { node },
                gandr_core_nbe::FreeFault::MachineInvariant => CheckRefusal::MachineInvariant,
            })?;
        for index in free {
            let declared = self
                .context
                .binders()
                .declared(Zone::Intuitionistic, index)
                .map_err(|_fault| CheckRefusal::MachineInvariant)?;
            match crate::capability::reaches(
                self.context.arena(),
                TypeNode::Value(declared),
                Region::Held,
            )? {
                crate::capability::Reach::Clear => {},
                crate::capability::Reach::Mentions => {
                    return Err(CheckRefusal::CapabilityEscaped {
                        at: TermNode::Computation(at),
                        found: TypeNode::Value(declared),
                    });
                },
                crate::capability::Reach::Keeps => {
                    return Err(CheckRefusal::Access {
                        at: node,
                        defect: AccessDefect::KeptEscaped,
                    });
                },
            }
        }
        Ok(())
    }

    /// End the innermost region, a capability scope's or a hold's: its mark
    /// dropped and every slot kept in it released to an exclusive access.
    ///
    /// # Specification
    /// - requires: the region's body was judged under the innermost mark.
    /// - ensures: one region fewer; every keep in the region that ended or a
    ///   deeper one released.
    /// - fails: [`CheckRefusal::MachineInvariant`] when no region is open.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an exclusive access of a kept slot is refused inside
    ///   the region and checks after its scope ends.
    /// - witness: `judgement::access::tests::a_view_kept_in_a_region_lives_as_long_as_its_scope`
    #[spec(
        captures: open = self.sessions.regions.len(),
        ensures: |ret| ret.is_err() || self.sessions.regions.len().checked_add(1) == Some(open),
    )]
    pub(super) fn close_region(&mut self) -> Result<(), CheckRefusal>
    {
        let ended = u32::try_from(self.sessions.regions.len())
            .map(RegionDepth::from)
            .map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        let _mark = self
            .sessions
            .regions
            .pop()
            .ok_or(CheckRefusal::MachineInvariant)?;
        self.sessions.kept.retain(|keep| keep.region < ended);
        Ok(())
    }

    /// The refusal of a linear variable read as a value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing changes.
    /// - fails: always: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::AsValue`] with the endpoint the index names;
    ///   [`CheckRefusal::UnboundIndex`] for an index past the zone.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an endpoint returned as a value is refused by name.
    /// - witness: `judgement::session::tests::an_endpoint_read_as_a_value_is_refused`
    #[spec(ensures: |ret| ret.is_err())]
    pub(super) fn endpoint_as_value(
        &mut self,
        term: ValueId,
        index: DeBruijnIndex,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Value(term));
        let slot = self.slot(node, index).map_err(|refusal| match refusal {
            CheckRefusal::Linearity {
                defect: LinearityDefect::Unbound { .. },
                ..
            } => CheckRefusal::UnboundIndex {
                at: term,
                zone: Zone::Linear,
                index,
                depth: self.context.depth(Zone::Linear),
            },
            other @ (CheckRefusal::NotADataType(_)
            | CheckRefusal::DataKindNotUniverse(_)
            | CheckRefusal::DataFieldLevel { .. }
            | CheckRefusal::RuleNotPresentable { .. }
            | CheckRefusal::RuleNotRespected { .. }
            | CheckRefusal::NotApart { .. }
            | CheckRefusal::LoopNotRespected { .. }
            | CheckRefusal::LoopUndecided { .. }
            | CheckRefusal::AbstractKindNotUniverse(_)
            | CheckRefusal::RepresentationAboveKind { .. }
            | CheckRefusal::NotAnAbstractType(_)
            | CheckRefusal::AtomTransport { .. }
            | CheckRefusal::SealSiteRepeated(_)
            | CheckRefusal::DataArgumentArity(_)
            | CheckRefusal::UnknownConstructor { .. }
            | CheckRefusal::ConstructorArity(_)
            | CheckRefusal::NonExhaustiveDataCase(_)
            | CheckRefusal::UndecidedCoverage(_)
            | CheckRefusal::AbsentRecordField(_)
            | CheckRefusal::AbsentTupleComponent(_)
            | CheckRefusal::MissingRecordField { .. }
            | CheckRefusal::UnknownOperation { .. }
            | CheckRefusal::HandlerCoverage { .. }
            | CheckRefusal::HandlerUnlawful { .. }
            | CheckRefusal::ShiftWithoutReset { .. }
            | CheckRefusal::DependentStack { .. }
            | CheckRefusal::PathCode(_)
            | CheckRefusal::EndpointMismatch { .. }
            | CheckRefusal::CompoundEndpoint { .. }
            | CheckRefusal::FunextUnsupported { .. }
            | CheckRefusal::PointwiseDistinct { .. }
            | CheckRefusal::EquivUnsupported { .. }
            | CheckRefusal::UncertifiedStratum { .. }
            | CheckRefusal::RoundTripDistinct { .. }
            | CheckRefusal::NotOver { .. }
            | CheckRefusal::UaUncertified { .. }
            | CheckRefusal::UaInequivalent { .. }
            | CheckRefusal::TypeMismatch(_)
            | CheckRefusal::EffectSignatureConflict { .. }
            | CheckRefusal::ShapeMismatch { .. }
            | CheckRefusal::NotSynthesisable { .. }
            | CheckRefusal::UnknownConstant { .. }
            | CheckRefusal::OutOfFragment { .. }
            | CheckRefusal::UnboundIndex { .. }
            | CheckRefusal::BudgetExceeded { .. }
            | CheckRefusal::DanglingNode { .. }
            | CheckRefusal::AdmissionOrder { .. }
            | CheckRefusal::MachineInvariant
            | CheckRefusal::SortMismatch { .. }
            | CheckRefusal::LevelMismatch { .. }
            | CheckRefusal::DependentBind { .. }
            | CheckRefusal::Undecided { .. }
            | CheckRefusal::FamilyArity { .. }
            | CheckRefusal::FamilyArgumentClassifier { .. }
            | CheckRefusal::StaticLambdaArgument { .. }
            | CheckRefusal::StaticClassifierExpected { .. }
            | CheckRefusal::NegativeOccurrence(_)
            | CheckRefusal::NestedOccurrence(_)
            | CheckRefusal::IndexOccurrence(_)
            | CheckRefusal::NonUniformOccurrence(_)
            | CheckRefusal::CrossBlockReference { .. }
            | CheckRefusal::StageNotBelow { .. }
            | CheckRefusal::StagesDisagree { .. }
            | CheckRefusal::SessionMismatch { .. }
            | CheckRefusal::Linearity { .. }
            | CheckRefusal::UnenclosedRun { .. }
            | CheckRefusal::ImplicitUnsolved { .. }
            | CheckRefusal::ModelUnanswered { .. }
            | CheckRefusal::ModelAmbiguous { .. }
            | CheckRefusal::CapabilityForged { .. }
            | CheckRefusal::CapabilityAmplified(_)
            | CheckRefusal::CapabilityOutsideAuthority { .. }
            | CheckRefusal::CapabilityEscaped { .. }
            | CheckRefusal::CapabilityConsumable(_)
            | CheckRefusal::CapabilityUngranted { .. }
            | CheckRefusal::SessionNotEquivalent { .. }
            | CheckRefusal::SessionNotSubtype { .. }
            | CheckRefusal::SessionCodeExpected { .. }
            | CheckRefusal::OpenSessionPayload { .. }
            | CheckRefusal::NonCovariantMotive { .. }
            | CheckRefusal::RideUnsupported { .. }
            | CheckRefusal::RunNotAdmitted { .. }
            | CheckRefusal::DialogueUnmatched { .. }
            | CheckRefusal::DialogueInverted { .. }
            | CheckRefusal::ForwardUnsupported { .. }
            | CheckRefusal::Boundary { .. }
            | CheckRefusal::Access { .. }
            | CheckRefusal::Codata { .. }
            | CheckRefusal::Located { .. }) => other,
        })?;
        Err(CheckRefusal::Linearity {
            at: node,
            defect: LinearityDefect::AsValue {
                endpoint: slot.endpoint,
            },
        })
    }

    /// The rules of the session actions: a send checks its payload, a
    /// receive, a selection and a close synthesise at once, an offer checks
    /// its arms, and a fork forms its protocol.
    ///
    /// # Specification
    /// - requires: `term` is a session action; an offer is judged in checking
    ///   direction only.
    /// - ensures: a send waits on its payload's check against the payload type
    ///   its endpoint's state sends; a receive advances its endpoint and
    ///   synthesises the returner of the payload, a selection advances it to
    ///   the chosen branch and a close consumes it at `end`, both synthesising
    ///   the returner of the unit; an offer checks its first arm with the
    ///   endpoint at that arm's branch; a fork forms its protocol annotation.
    /// - fails: [`CheckRefusal::SessionMismatch`] for an action the state does
    ///   not admit, a label it does not offer, or arms that are not exactly its
    ///   labels; [`CheckRefusal::Linearity`] for an action after close and a
    ///   payload naming its own endpoint or another;
    ///   [`CheckRefusal::NotSynthesisable`] for an offer in synthesis.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat exchange drives every action at both ends,
    ///   and each refusal has its own pathological term.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    /// - witness: `judgement::session::tests::an_operator_holding_the_seat_view_is_refused`
    /// - witness: `judgement::session::tests::an_endpoint_used_twice_in_one_action_is_refused`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::NotSynthesisable { form: crate::refusal::CheckingForm::Offer(offered) }) => {
            offered == term && matches!(direction, Direction::Synthesise)
        },
        | _ => true,
    })]
    pub(super) fn session(
        &mut self,
        term: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Session(ref action) = *self.computation(term)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        match (action, direction) {
            (&SessionAction::Send { endpoint, payload }, _) => self.send(term, endpoint, payload),
            (&SessionAction::Receive { endpoint, body }, _) => {
                self.receive(term, endpoint, body, direction)
            },
            (
                &SessionAction::Select {
                    endpoint,
                    ref label,
                },
                _,
            ) => {
                let label = label.clone();
                self.select(term, endpoint, &label)
            },
            (&SessionAction::Close { endpoint }, _) => self.close_endpoint(term, endpoint),
            (&SessionAction::Offer { .. }, Direction::Check(expected)) => {
                self.offer(term, expected)
            },
            (&SessionAction::Offer { .. }, Direction::Synthesise) => {
                Err(CheckRefusal::NotSynthesisable {
                    form: crate::refusal::CheckingForm::Offer(term),
                })
            },
            (&SessionAction::Fork { protocol, .. }, _) => {
                self.wait(Frame::ForkProtocol {
                    at: term,
                    direction,
                });
                Ok(Step::Descend(Goal::Form(TypeNode::Value(protocol))))
            },
            (&SessionAction::Place { payload, body }, _) => {
                self.place(term, payload, body, direction)
            },
        }
    }

    /// The session type `slot` stands at, when its next step is `observed`;
    /// a typed run keeps that session type, read where the action `at`
    /// stands, as the standing of its endpoint, admitted or not.
    ///
    /// # Specification
    /// - requires: `slot` was read by [`Self::live`]; the action `at` is
    ///   admitted once.
    /// - ensures: the slot's session type, whose step is `observed`.
    /// - fails: [`CheckRefusal::SessionMismatch`] naming the action the state
    ///   admits; [`CheckRefusal::MachineInvariant`] for a slot holding no
    ///   session type.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an operator that holds the seat's end sends where the
    ///   state receives; each action of the seat exchange keeps its endpoint's
    ///   state.
    /// - witness: `judgement::session::tests::an_operator_holding_the_seat_view_is_refused`
    /// - witness: `judgement::session::tests::a_typed_run_keeps_each_endpoint_s_state`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|session| session.step().is_ok_and(|step| step.action() == observed)))]
    fn admitted(
        &mut self,
        at: ComputationId,
        slot: Slot,
        observed: ActionKind,
    ) -> Result<SessionType, CheckRefusal>
    {
        if self.context.recording() == Recording::On {
            let state = self.here(slot.state, slot.depth)?;
            self.context.keep_endpoint(Typing {
                term: TermNode::Computation(at),
                ty: TypeNode::Value(state),
                depth: self.context.depth(Zone::Intuitionistic),
            });
        }
        let session = session_at(self.context, slot.state)?;
        let expected = session
            .step()
            .map_err(|_fault| CheckRefusal::MachineInvariant)?
            .action();
        if expected != observed {
            return Err(CheckRefusal::SessionMismatch {
                at,
                endpoint: slot.endpoint,
                state: slot.state,
                defect: ProtocolDefect::Action { expected, observed },
            });
        }
        Ok(session)
    }

    /// Start a send: delegate an endpoint sent whole, or check the payload,
    /// then advance the endpoint.
    ///
    /// # Specification
    /// - requires: `at` is a send on `endpoint` of `payload`.
    /// - ensures: a payload that is a linear variable naming another endpoint
    ///   is delegated: its slot, read where the send stands, is converted to
    ///   the payload type and consumed, and the endpoint advances; any other
    ///   payload leaves one `SessionSend` frame waiting on its check against
    ///   the payload type, read where the send stands, which is recorded for
    ///   `at`.
    /// - fails: as [`Self::live`] and [`Self::admitted`];
    ///   [`CheckRefusal::Linearity`] naming [`LinearityDefect::UsedTwice`] when
    ///   the payload names the endpoint, and [`LinearityDefect::Closed`] when
    ///   it delegates an endpoint already consumed; the value bridge's refusal
    ///   when the delegated endpoint's session type is not the payload type.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a send over its own endpoint is refused, an endpoint
    ///   sent whole leaves the sender and a later action on it is refused, and
    ///   the seat exchange's sends check.
    /// - witness: `judgement::session::tests::an_endpoint_used_twice_in_one_action_is_refused`
    /// - witness: `judgement::session::tests::a_delegated_endpoint_leaves_its_sender`
    /// - witness: `judgement::session::tests::a_closed_endpoint_is_not_delegated`
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Value { .. }) | Step::Ascend(Produced::CompType(_)))))]
    fn send(
        &mut self,
        at: ComputationId,
        endpoint: DeBruijnIndex,
        payload: ValueId,
    ) -> Result<Step, CheckRefusal>
    {
        let slot = self.live(at, endpoint)?;
        let session = self.admitted(at, slot, ActionKind::Send)?;
        let Ok(Move::Send { payload: ty, next }) = session.step()
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let node = CoreNode::Term(TermNode::Value(payload));
        if self
            .free_linear(CoreTerm::Value(payload))?
            .contains(&endpoint)
        {
            return Err(CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::UsedTwice {
                    endpoint: slot.endpoint,
                },
            });
        }
        let next = self.context.arena_mut().value_type_session(next);
        let expected = self.here(ty, slot.depth)?;
        if self.returned_buffer(at, payload, expected)? == HandedOn::Buffer {
            return self.sent(endpoint, next);
        }
        if let Value::Variable {
            zone: Zone::Linear,
            index,
        } = *self.value(payload)?
        {
            let sent = self.resided(node, index)?;
            if let Resident::Endpoint(delegated) = sent.resident {
                if sent.use_state == LinearUse::Consumed {
                    return Err(CheckRefusal::Linearity {
                        at: node,
                        defect: LinearityDefect::Closed {
                            endpoint: delegated,
                        },
                    });
                }
                let found = self.here(sent.state, sent.depth)?;
                crate::conversion::value_bridge(
                    self.context,
                    payload,
                    found,
                    expected,
                    &mut self.conversions,
                )?;
                // The payload is judged here, not by a descent, so its typing
                // is kept as a checked value's would be.
                if self.context.recording() == Recording::On {
                    self.context.keep_typing(Typing {
                        term: TermNode::Value(payload),
                        ty: TypeNode::Value(expected),
                        depth: self.context.depth(Zone::Intuitionistic),
                    });
                }
                let _delegated = self
                    .context
                    .binders()
                    .occurrence(Zone::Linear, index)
                    .map_err(|_fault| CheckRefusal::MachineInvariant)?;
                return self.sent(endpoint, next);
            }
        }
        self.context.record_payload(at, expected);
        self.wait(Frame::SessionSend { at, endpoint, next });
        Ok(Step::Descend(Goal::Value {
            term: payload,
            direction: Direction::Check(expected),
        }))
    }

    /// Return the buffer `payload` names, where `action` — a send, a
    /// resumption or an exercised operation — hands on a value of `expected`.
    ///
    /// # Specification
    /// - requires: `expected` is read where `action` stands.
    /// - ensures: [`HandedOn::Buffer`] when the payload is a linear variable
    ///   holding a buffer, whose slot, converted to `expected`, is then
    ///   consumed and its typing kept; [`HandedOn::Other`], the slot untouched,
    ///   for any other payload where `expected` is not the buffer at its weak
    ///   head.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::BufferReturnedTwice`] for a buffer already
    ///   returned, and [`LinearityDefect::BufferRead`] at `action` for a buffer
    ///   no slot holds handed where a buffer is expected, which would otherwise
    ///   mint one; the value bridge's refusal when `expected` is not the
    ///   buffer.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an allocated buffer freed once checks and freed twice
    ///   is refused at the second free, and an allocation's reply no placement
    ///   holds is refused where it is freed.
    /// - witness: `judgement::session::tests::an_allocated_buffer_is_returned_once`
    /// - witness: `judgement::session::tests::a_buffer_no_slot_holds_is_never_returned`
    #[spec(
        captures: depth = self.context.depth(Zone::Linear),
        ensures: |ret| self.context.depth(Zone::Linear) == depth,
    )]
    pub(super) fn returned_buffer(
        &mut self,
        action: ComputationId,
        payload: ValueId,
        expected: ValueTypeId,
    ) -> Result<HandedOn, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Value(payload));
        if let Value::Variable {
            zone: Zone::Linear,
            index,
        } = *self.value(payload)?
        {
            let sent = self.resided(node, index)?;
            if let Resident::Buffer { at: site } = sent.resident {
                if sent.use_state == LinearUse::Consumed {
                    return Err(CheckRefusal::Linearity {
                        at: node,
                        defect: LinearityDefect::BufferReturnedTwice { site },
                    });
                }
                let found = self.here(sent.state, sent.depth)?;
                crate::conversion::value_bridge(
                    self.context,
                    payload,
                    found,
                    expected,
                    &mut self.conversions,
                )?;
                if self.context.recording() == Recording::On {
                    self.context.keep_typing(Typing {
                        term: TermNode::Value(payload),
                        ty: TypeNode::Value(expected),
                        depth: self.context.depth(Zone::Intuitionistic),
                    });
                }
                let _returned = self
                    .context
                    .binders()
                    .occurrence(Zone::Linear, index)
                    .map_err(|_fault| CheckRefusal::MachineInvariant)?;
                return Ok(HandedOn::Buffer);
            }
        }
        let head = self.context.whnf_value_type(expected)?;
        if matches!(
            value_type_view(self.context.arena(), head)?,
            ValueTypeView::Buffer
        ) {
            return Err(CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::BufferRead { site: action },
            });
        }
        Ok(HandedOn::Other)
    }

    /// Finish a send whose payload checked: advance the endpoint.
    ///
    /// # Specification
    /// - requires: the payload checked.
    /// - ensures: the endpoint stands at `next`; the send synthesises the
    ///   returner of the unit.
    /// - fails: [`CheckRefusal::MachineInvariant`] when the endpoint is not
    ///   available, which a payload naming no endpoint cannot cause.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's send advances it to the offer that
    ///   follows.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))))]
    pub(super) fn sent(
        &mut self,
        endpoint: DeBruijnIndex,
        next: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let _previous = self
            .context
            .binders()
            .advance(endpoint, next)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        Ok(Step::Ascend(Produced::CompType(self.unit_returner())))
    }

    /// Receive on `endpoint` into the receive's linear binder and judge its
    /// body.
    ///
    /// # Specification
    /// - requires: `at` is a receive on `endpoint` whose body is `body`.
    /// - ensures: the endpoint stands at the continuation; one linear slot
    ///   more, at the payload type read where the receive stands: an endpoint
    ///   the receive binds, available, for a payload that is a session type at
    ///   its weak head, and otherwise a received value opened spent, whose
    ///   reads copy; the type the slot opened at recorded for `at`; one
    ///   `ReceiveBody` frame waits on the body's judgement in the receive's
    ///   direction.
    /// - fails: as [`Self::live`] and [`Self::admitted`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's first receive binds the dispatch, read by
    ///   copy, and a received endpoint is acted on and closed in the body.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    /// - witness: `judgement::session::tests::a_received_endpoint_is_acted_on_and_must_be_closed`
    #[spec(
        captures: before = self.context.depth(Zone::Linear),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(Goal::Computation { .. })))
            && self.context.depth(Zone::Linear) > before
            && self.context.payloads().contains_key(&at)),
    )]
    fn receive(
        &mut self,
        at: ComputationId,
        endpoint: DeBruijnIndex,
        body: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let slot = self.live(at, endpoint)?;
        let session = self.admitted(at, slot, ActionKind::Receive)?;
        let Ok(Move::Receive { payload, next }) = session.step()
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let next = self.context.arena_mut().value_type_session(next);
        let _previous = self
            .context
            .binders()
            .advance(endpoint, next)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        let payload = self.here(payload, slot.depth)?;
        let head = self.context.whnf_value_type(payload)?;
        let view = value_type_view(self.context.arena(), head)?;
        let depth = self.context.depth(Zone::Intuitionistic);
        let endpoint = matches!(view, ValueTypeView::Session(_));
        let buffer = matches!(view, ValueTypeView::Buffer);
        let opened = if endpoint || buffer { head } else { payload };
        self.context.record_payload(at, opened);
        if endpoint {
            self.context.binders().open(Zone::Linear, head);
            self.sessions.opened.push(Opened {
                resident: Resident::Endpoint(Endpoint {
                    fork: at,
                    side: ForkSide::Received,
                }),
                depth,
            });
        }
        else if buffer {
            // A buffer is live: its slot opens available, and only the send
            // that returns it spends it.
            self.context.binders().open(Zone::Linear, head);
            self.sessions.opened.push(Opened {
                resident: Resident::Buffer { at },
                depth,
            });
        }
        else {
            self.context.binders().open(Zone::Linear, payload);
            self.sessions.opened.push(Opened {
                resident: Resident::Received { at },
                depth,
            });
            // A received value owes nothing: its slot opens spent, so a
            // read copies and the body's end finds no residue.
            let _received = self
                .context
                .binders()
                .occurrence(Zone::Linear, DeBruijnIndex::from(0_u32))
                .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        }
        self.wait(Frame::ReceiveBody { at, direction });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction,
        }))
    }

    /// Place the buffer `payload` names live in the placement's linear binder
    /// and judge its body.
    ///
    /// # Specification
    /// - requires: `at` is a placement of `payload` over `body`, the payload
    ///   the intuitionistic binder of the bind the placement stands under.
    /// - ensures: one linear slot more, a buffer opened available at the
    ///   placement; one `ReceiveBody` frame waits on the body's judgement in
    ///   the placement's direction, so the body's end refuses the buffer
    ///   unreturned as a receive's does.
    /// - fails: [`CheckRefusal::MachineInvariant`] for a payload other than an
    ///   intuitionistic variable whose type is the buffer at its weak head,
    ///   which the lowering never builds.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an allocated buffer freed checks, and one the body
    ///   never returns is refused at the placement.
    /// - witness: `judgement::session::tests::an_allocated_buffer_is_returned_once`
    #[spec(
        captures: before = self.context.depth(Zone::Linear),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(Goal::Computation { .. })))
            && self.context.depth(Zone::Linear) > before),
    )]
    fn place(
        &mut self,
        at: ComputationId,
        payload: ValueId,
        body: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        } = *self.value(payload)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let declared = self
            .context
            .binders()
            .occurrence(Zone::Intuitionistic, index)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        let arena = self.context.arena_mut();
        let read = shift_value_type(arena, declared, Binders::past(index)).settle(arena);
        let head = self.context.whnf_value_type(read)?;
        if !matches!(
            value_type_view(self.context.arena(), head)?,
            ValueTypeView::Buffer
        ) {
            return Err(CheckRefusal::MachineInvariant);
        }
        let depth = self.context.depth(Zone::Intuitionistic);
        self.context.binders().open(Zone::Linear, head);
        self.sessions.opened.push(Opened {
            resident: Resident::Buffer { at },
            depth,
        });
        self.wait(Frame::ReceiveBody { at, direction });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction,
        }))
    }

    /// Finish a receive whose body was judged: require a received endpoint
    /// spent, drop the payload's slot and hand the body's result on.
    ///
    /// # Specification
    /// - requires: the body was judged in `direction`.
    /// - ensures: the payload's slot is closed and its entry dropped; the
    ///   receive checked, or synthesised the body's type.
    /// - fails: [`CheckRefusal::Linearity`] naming [`LinearityDefect::Residue`]
    ///   at the receive for a received endpoint left unconsumed;
    ///   [`CheckRefusal::MachineInvariant`] when the innermost slot is not this
    ///   receive's.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a received endpoint the body never closes is refused
    ///   at the receive, and a closed one checks.
    /// - witness: `judgement::session::tests::a_received_endpoint_is_acted_on_and_must_be_closed`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(_))))]
    pub(super) fn received(
        &mut self,
        at: ComputationId,
        direction: Direction<CompTypeId>,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        let innermost = self.resided(node, DeBruijnIndex::from(0_u32))?;
        match innermost.resident {
            Resident::Endpoint(endpoint) if endpoint.fork == at => {
                if innermost.use_state == LinearUse::Available {
                    return Err(CheckRefusal::Linearity {
                        at: node,
                        defect: LinearityDefect::Residue {
                            endpoint,
                            state: innermost.state,
                        },
                    });
                }
            },
            Resident::Received { at: receive } if receive == at => {},
            Resident::Buffer { at: site } if site == at => {
                if innermost.use_state == LinearUse::Available {
                    return Err(CheckRefusal::Linearity {
                        at: node,
                        defect: LinearityDefect::BufferUnreturned { site },
                    });
                }
            },
            Resident::Endpoint(_)
            | Resident::Received { .. }
            | Resident::Buffer { .. }
            | Resident::Held { .. }
            | Resident::View { .. }
            | Resident::Capability { .. }
            | Resident::Continuation { .. } => return Err(CheckRefusal::MachineInvariant),
        }
        let _state = self
            .context
            .binders()
            .close(Zone::Linear)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        let _opened = self.sessions.opened.pop();
        match (direction, produced) {
            (Direction::Check(_), Produced::Checked) => Ok(Step::Ascend(Produced::Checked)),
            (Direction::Synthesise, Produced::CompType(ty)) => {
                Ok(Step::Ascend(Produced::CompType(ty)))
            },
            (Direction::Check(_) | Direction::Synthesise, _) => Err(CheckRefusal::MachineInvariant),
        }
    }

    /// Select `label` on `endpoint`.
    ///
    /// # Specification
    /// - requires: `at` is a selection of `label` on `endpoint`.
    /// - ensures: the endpoint stands at the label's branch; the selection
    ///   synthesises the returner of the unit.
    /// - fails: as [`Self::live`] and [`Self::admitted`];
    ///   [`CheckRefusal::SessionMismatch`] naming [`ProtocolDefect::Label`] for
    ///   a label the state does not offer.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat selects each of its choices once across the
    ///   exchange.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    /// - witness: `judgement::session::tests::a_selection_or_offer_off_the_protocol_s_labels_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))))]
    fn select(
        &mut self,
        at: ComputationId,
        endpoint: DeBruijnIndex,
        label: &FieldLabel,
    ) -> Result<Step, CheckRefusal>
    {
        let slot = self.live(at, endpoint)?;
        let session = self.admitted(at, slot, ActionKind::Select)?;
        let Ok(Move::Select(branches)) = session.step()
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Maybe::Present(next) = branches
            .get(label)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?
        else {
            return Err(CheckRefusal::SessionMismatch {
                at,
                endpoint: slot.endpoint,
                state: slot.state,
                defect: ProtocolDefect::Label,
            });
        };
        let next = self.context.arena_mut().value_type_session(next);
        let _previous = self
            .context
            .binders()
            .advance(endpoint, next)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        Ok(Step::Ascend(Produced::CompType(self.unit_returner())))
    }

    /// Close `endpoint`.
    ///
    /// # Specification
    /// - requires: `at` is a close of `endpoint`.
    /// - ensures: the endpoint is consumed; the close synthesises the returner
    ///   of the unit.
    /// - fails: as [`Self::live`] and [`Self::admitted`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a close before `end` is refused and a close at it
    ///   consumes the endpoint, so a second close is refused as after close.
    /// - witness: `judgement::session::tests::an_endpoint_used_after_close_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))))]
    fn close_endpoint(
        &mut self,
        at: ComputationId,
        endpoint: DeBruijnIndex,
    ) -> Result<Step, CheckRefusal>
    {
        let slot = self.live(at, endpoint)?;
        let _end = self.admitted(at, slot, ActionKind::Close)?;
        let _state = self
            .context
            .binders()
            .occurrence(Zone::Linear, endpoint)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        Ok(Step::Ascend(Produced::CompType(self.unit_returner())))
    }

    /// Start an offer checked against `expected`: its arms must be exactly
    /// the labels its endpoint's state offers; the first arm is checked from
    /// the zone as the offer found it.
    ///
    /// # Specification
    /// - requires: `at` is an offer.
    /// - ensures: the zone as found is kept; the first arm is checked as
    ///   [`Self::arm`] checks it.
    /// - fails: as [`Self::live`] and [`Self::admitted`];
    ///   [`CheckRefusal::SessionMismatch`] naming [`ProtocolDefect::Arms`] for
    ///   arms that are not the state's labels.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the operator's offers check both labels; arms leaving
    ///   different endpoints are refused.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    /// - witness: `judgement::session::tests::offer_arms_leaving_different_endpoints_are_refused`
    /// - witness: `judgement::session::tests::a_selection_or_offer_off_the_protocol_s_labels_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Computation { .. }))))]
    fn offer(
        &mut self,
        at: ComputationId,
        expected: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Session(SessionAction::Offer { endpoint, ref arms }) =
            *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let labels: Vec<FieldLabel> = arms.keys().cloned().collect();
        let slot = self.live(at, endpoint)?;
        let session = self.admitted(at, slot, ActionKind::Offer)?;
        let Ok(Move::Offer(branches)) = session.step()
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if !branches.labels().eq(labels.iter()) {
            return Err(CheckRefusal::SessionMismatch {
                at,
                endpoint: slot.endpoint,
                state: slot.state,
                defect: ProtocolDefect::Arms,
            });
        }
        let zones = ZoneMark(self.sessions.zones.len());
        let found = self.context.binders().linear_zone();
        self.sessions.zones.push(found);
        self.arm(at, Ordinal::FIRST, expected, zones)
    }

    /// Check the offer `at`'s arm at `position` against `expected`, its
    /// endpoint advanced to that arm's branch.
    ///
    /// # Specification
    /// - requires: the zone stands as the offer found it.
    /// - ensures: one `OfferArm` frame waits on the arm's check.
    /// - fails: [`CheckRefusal::MachineInvariant`] for a position past the arms
    ///   or an endpoint not at the offer.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both arms of each offer of the seat exchange are
    ///   checked.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Computation { .. }))))]
    fn arm(
        &mut self,
        at: ComputationId,
        position: Ordinal,
        expected: CompTypeId,
        zones: ZoneMark,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Session(SessionAction::Offer { endpoint, ref arms }) =
            *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let (label, body) = arms
            .iter()
            .nth(position.0)
            .map(|(label, &body)| (label.clone(), body))
            .ok_or(CheckRefusal::MachineInvariant)?;
        let slot = self.live(at, endpoint)?;
        let session = session_at(self.context, slot.state)?;
        let Ok(Move::Offer(branches)) = session.step()
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Ok(Maybe::Present(next)) = branches.get(&label)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let next = self.context.arena_mut().value_type_session(next);
        let _previous = self
            .context
            .binders()
            .advance(endpoint, next)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        self.wait(Frame::OfferArm {
            at,
            arm: position,
            expected,
            zones,
        });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction: Direction::Check(expected),
        }))
    }

    /// Finish the offer `at`'s arm at `position`: keep the zone the first arm
    /// left, require every later arm to leave the same one, and check the
    /// next arm from the zone as the offer found it.
    ///
    /// # Specification
    /// - requires: the arm at `position` checked.
    /// - ensures: the next arm's check is the next goal; after the last arm the
    ///   zone stands as every arm left it and the offer checked.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::ArmsDisagree`] at the arm whose zone differs from
    ///   the first arm's: a slot consumed in one and not the other, or left at
    ///   a session type the other's is not equivalent to.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an arm closing an endpoint the other leaves open is
    ///   refused; the seat exchange's arms agree.
    /// - witness: `judgement::session::tests::offer_arms_leaving_different_endpoints_are_refused`
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(_) | Step::Ascend(Produced::Checked))))]
    pub(super) fn armed(
        &mut self,
        at: ComputationId,
        position: Ordinal,
        expected: CompTypeId,
        zones: ZoneMark,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Session(SessionAction::Offer { ref arms, .. }) = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let count = arms.len();
        let mut bodies = arms.values().copied();
        let first = bodies.next().ok_or(CheckRefusal::MachineInvariant)?;
        let this = arms
            .values()
            .nth(position.0)
            .copied()
            .ok_or(CheckRefusal::MachineInvariant)?;
        let left = self.context.binders().linear_zone();
        if position == Ordinal::FIRST {
            self.sessions.zones.push(left);
        }
        else {
            self.agree(first, this, zones, &left)?;
        }
        let next = position.next()?;
        if next.0 < count {
            let found = self
                .sessions
                .zones
                .get(zones.0)
                .cloned()
                .ok_or(CheckRefusal::MachineInvariant)?;
            self.context.binders().restore_linear(&found);
            return self.arm(at, next, expected, zones);
        }
        self.sessions.zones.truncate(zones.0);
        Ok(Step::Ascend(Produced::Checked))
    }

    /// Require the zone `left` the arm `other` left to agree with the one the
    /// first arm `first` left.
    ///
    /// # Specification
    /// - requires: the first arm's zone is kept above the offer's own.
    /// - ensures: nothing changes when every slot has the same use in both and
    ///   every available slot equivalent session types.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::ArmsDisagree`] with the first slot that differs.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an arm consuming an outer endpoint the first arm left
    ///   is refused.
    /// - witness: `judgement::session::tests::offer_arms_leaving_different_endpoints_are_refused`
    /// - witness: `judgement::session::tests::offer_arms_leaving_an_endpoint_open_agree_on_its_state`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::Linearity { at: refused, defect: LinearityDefect::ArmsDisagree { first: kept, other: differing, .. } }) => {
            refused == CoreNode::Term(TermNode::Computation(other)) && kept == first && differing == other
        },
        | _ => true,
    })]
    fn agree(
        &mut self,
        first: ComputationId,
        other: ComputationId,
        zones: ZoneMark,
        left: &LinearZone,
    ) -> Result<(), CheckRefusal>
    {
        let agreed = self
            .sessions
            .zones
            .get(
                zones
                    .0
                    .checked_add(1)
                    .ok_or(CheckRefusal::MachineInvariant)?,
            )
            .cloned()
            .ok_or(CheckRefusal::MachineInvariant)?;
        if agreed.depth() != left.depth() {
            return Err(CheckRefusal::MachineInvariant);
        }
        let base = usize::from(self.sessions.base);
        let slots: Vec<_> = agreed.slots().zip(left.slots()).collect();
        for (position, ((agreed_type, agreed_use), (left_type, left_use))) in
            slots.into_iter().enumerate()
        {
            let same = agreed_use == left_use
                && (agreed_use == LinearUse::Consumed
                    || agreed_type == left_type
                    || crate::conversion::equivalent(self.context, agreed_type, left_type)?
                        == crate::conversion::Agreement::Convertible);
            if same {
                continue;
            }
            let resident = position
                .checked_sub(base)
                .and_then(|position| self.sessions.opened.get(position))
                .ok_or(CheckRefusal::MachineInvariant)?
                .resident;
            let at = CoreNode::Term(TermNode::Computation(other));
            return Err(match resident {
                Resident::Endpoint(endpoint) => CheckRefusal::Linearity {
                    at,
                    defect: LinearityDefect::ArmsDisagree {
                        endpoint,
                        first,
                        other,
                    },
                },
                // A received value opens spent, so two arms never leave it
                // otherwise.
                Resident::Received { .. } => CheckRefusal::MachineInvariant,
                // One arm returned the buffer and the other kept it.
                Resident::Buffer { at: site } => CheckRefusal::Linearity {
                    at,
                    defect: LinearityDefect::BufferUnreturned { site },
                },
                // Within its hold a held slot's use changes by a consume
                // alone, so one arm consumed it and the other did not.
                Resident::Held { .. } => CheckRefusal::Access {
                    at,
                    defect: AccessDefect::Consumed,
                },
                Resident::View { .. } => CheckRefusal::Access {
                    at,
                    defect: AccessDefect::Unended,
                },
                Resident::Capability { world } => CheckRefusal::Located {
                    at,
                    defect: crate::worlds::LocatedDefect::CapabilityCaptured {
                        world,
                        by: Capture::Branch,
                    },
                },
                // One arm ended the continuation and the other did not.
                Resident::Continuation { clause } => CheckRefusal::Linearity {
                    at,
                    defect: LinearityDefect::ContinuationUnspent { clause },
                },
            });
        }
        Ok(())
    }

    /// Open the arms of a case: while the run holds a value or has placed a
    /// buffer live, keep the zone as the case found it, for each arm to start
    /// from.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Joining::Joined`] at the mark the found zone is kept at
    ///   when a slot the run opened is held or a live buffer;
    ///   [`Joining::Threaded`], nothing kept, otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a case on a list or a sum whose arms consume a held
    ///   value one each checks, and a read after it of a value the first arm or
    ///   the second consumed is refused; a case whose arms each return a live
    ///   buffer checks.
    /// - witness: `judgement::access::tests::a_case_s_arms_each_take_a_hold_from_where_the_case_found_it_1488`
    /// - witness: `judgement::session::tests::a_case_s_arms_each_return_the_placed_buffer_1792`
    #[spec(
        captures: kept = self.sessions.zones.len(),
        ensures: |ret| match ret {
            Joining::Joined(mark) => mark.0 == kept && kept.checked_add(1) == Some(self.sessions.zones.len()),
            Joining::Threaded => self.sessions.zones.len() == kept,
        },
    )]
    pub(super) fn arms_opened(&mut self) -> Joining
    {
        // A held value one arm may consume and another not, and a live buffer
        // every arm returns or none does: each arm starts from it as found.
        if !self.sessions.opened.iter().any(|opened| {
            matches!(
                opened.resident,
                Resident::Held { .. } | Resident::Buffer { .. }
            )
        }) {
            return Joining::Threaded;
        }
        let mark = ZoneMark(self.sessions.zones.len());
        let found = self.context.binders().linear_zone();
        self.sessions.zones.push(found);
        Joining::Joined(mark)
    }

    /// End the arm `arm` of the case whose zones stand at `zones` with another
    /// to come: fold the zone the arm left into the join, and give the next
    /// arm each held slot and live buffer as the case found it and every other
    /// slot as this arm left it.
    ///
    /// # Specification
    /// - requires: the arm `arm` of the case opened at `zones` checked.
    /// - ensures: each held slot and live buffer is at the use the case found
    ///   it at; the join is kept above the found zone.
    /// - fails: as [`Self::arm_folded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::arms_opened`].
    /// - witness: `judgement::access::tests::a_case_s_arms_each_take_a_hold_from_where_the_case_found_it_1488`
    /// - witness: `judgement::session::tests::a_case_s_arms_each_return_the_placed_buffer_1792`
    #[spec(ensures: |ret| ret.is_err() || zones.0.checked_add(2) == Some(self.sessions.zones.len()))]
    pub(super) fn arm_ended(
        &mut self,
        zones: ZoneMark,
        arm: ComputationId,
    ) -> Result<(), CheckRefusal>
    {
        let joined = self.arm_folded(zones, arm)?;
        let found = self
            .sessions
            .zones
            .get(zones.0)
            .ok_or(CheckRefusal::MachineInvariant)?;
        let base = usize::from(self.sessions.base);
        let opened = &self.sessions.opened;
        let next = joined.taking(found, |position, _| {
            usize::from(position)
                .checked_sub(base)
                .and_then(|above| opened.get(above))
                .is_some_and(|slot| {
                    matches!(
                        slot.resident,
                        Resident::Held { .. } | Resident::Buffer { .. }
                    )
                })
        });
        self.context.binders().restore_linear(&next);
        Ok(())
    }

    /// Join the arms of the case whose zones stand at `zones` after its last
    /// arm `arm`: the zone that arm left, each held slot consumed when any arm
    /// consumed it.
    ///
    /// # Specification
    /// - requires: the last arm `arm` of the case opened at `zones` checked.
    /// - ensures: the zone is the join and the case's zones are dropped.
    /// - fails: as [`Self::arm_folded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::arms_opened`].
    /// - witness: `judgement::access::tests::a_case_s_arms_each_take_a_hold_from_where_the_case_found_it_1488`
    /// - witness: `judgement::session::tests::a_case_s_arms_each_return_the_placed_buffer_1792`
    #[spec(ensures: |ret| ret.is_err() || self.sessions.zones.len() == zones.0)]
    pub(super) fn arms_joined(
        &mut self,
        zones: ZoneMark,
        arm: ComputationId,
    ) -> Result<(), CheckRefusal>
    {
        let joined = self.arm_folded(zones, arm)?;
        self.context.binders().restore_linear(&joined);
        self.sessions.zones.truncate(zones.0);
        Ok(())
    }

    /// The zone the arm `arm` just checked left, each held slot taken from the
    /// join of the arms before it where one of them consumed it, kept as the
    /// join above the zone the case found; each live buffer must be left as
    /// the arms before it left it, returned by every arm or by none.
    ///
    /// # Specification
    /// - requires: the arm `arm` of the case opened at `zones` checked.
    /// - ensures: the join is kept one above `zones` and returned.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::BufferUnreturned`] at `arm` for the outermost live
    ///   buffer `arm` returned where the arms before it kept it, or kept where
    ///   they returned it; [`CheckRefusal::MachineInvariant`] when no zone is
    ///   kept at `zones` or the arm left another depth.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::arms_opened`], and an arm keeping a buffer
    ///   another returned is refused at that arm either way round.
    /// - witness: `judgement::access::tests::a_case_s_arms_each_take_a_hold_from_where_the_case_found_it_1488`
    /// - witness: `judgement::session::tests::a_case_s_arms_each_return_the_placed_buffer_1792`
    #[spec(ensures: |ret| match ret.as_ref() {
        | Ok(joined) => zones.0.checked_add(1).and_then(|join| self.sessions.zones.get(join)) == Some(joined),
        | Err(&CheckRefusal::Linearity { at: refused, defect: LinearityDefect::BufferUnreturned { .. } }) => {
            refused == CoreNode::Term(TermNode::Computation(arm))
        },
        | Err(_) => true,
    })]
    fn arm_folded(
        &mut self,
        zones: ZoneMark,
        arm: ComputationId,
    ) -> Result<LinearZone, CheckRefusal>
    {
        let left = self.context.binders().linear_zone();
        let join = zones
            .0
            .checked_add(1)
            .ok_or(CheckRefusal::MachineInvariant)?;
        let found = self
            .sessions
            .zones
            .get(zones.0)
            .ok_or(CheckRefusal::MachineInvariant)?;
        if found.depth() != left.depth() {
            return Err(CheckRefusal::MachineInvariant);
        }
        let base = usize::from(self.sessions.base);
        let opened = &self.sessions.opened;
        let joined = match self.sessions.zones.get(join) {
            Some(earlier) => {
                for (position, ((_, theirs), (_, ours))) in
                    earlier.slots().zip(left.slots()).enumerate()
                {
                    if theirs == ours {
                        continue;
                    }
                    if let Some(Resident::Buffer { at: site }) = position
                        .checked_sub(base)
                        .and_then(|above| opened.get(above))
                        .map(|slot| slot.resident)
                    {
                        return Err(CheckRefusal::Linearity {
                            at: CoreNode::Term(TermNode::Computation(arm)),
                            defect: LinearityDefect::BufferUnreturned { site },
                        });
                    }
                }
                left.taking(earlier, |position, theirs| {
                    theirs != LinearUse::Available
                        && usize::from(position)
                            .checked_sub(base)
                            .and_then(|above| opened.get(above))
                            .is_some_and(|slot| matches!(slot.resident, Resident::Held { .. }))
                })
            },
            None => left,
        };
        self.sessions.zones.truncate(join);
        self.sessions.zones.push(joined.clone());
        Ok(joined)
    }

    /// Judge, at the operation `at` handing on `payload` that `answerer`
    /// answers, the live residents the operation's
    /// continuation ends: the host answers once and captures nothing; a
    /// scope's clause receives the rest of the scope's region as a
    /// continuation, which holding an obligation the clause must end exactly
    /// once, so the capture is recorded for the clause; and an operation
    /// anyone may answer captures every slot the run opened, which is refused.
    /// A received value, which a read copies, passes, and so does the buffer
    /// `payload` names, which the operation hands back whole. An operation an
    /// unwind performs passes: the unwind runs under the empty row, so no
    /// clause answers it, and the row refuses it by name.
    ///
    /// # Specification
    /// - requires: `payload` stands where `at` does.
    /// - ensures: when a scope's clause answers and the continuation captures a
    ///   live resident other than a received value or the buffer `payload` is,
    ///   the scope and the operation are recorded in [`Sessions::owing`];
    ///   nothing else changes.
    /// - fails: as [`captured`] by [`Capture::Continuation`] at `at`, for the
    ///   outermost slot an operation anyone may answer captures whose use is
    ///   still available and whose resident is neither a received value nor the
    ///   buffer `payload` is, and for one a scope captures whose region no
    ///   waiting scope opened; [`CheckRefusal::MachineInvariant`] for a slot
    ///   the binders do not hold; [`CheckRefusal::DanglingNode`] for a payload
    ///   outside the arena.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parent exercising its scope's capability while it
    ///   holds an endpoint opened in the scope has the scope's clause owe the
    ///   continuation, the same exercise after the endpoint closed owes
    ///   nothing, and one exercising a capability held for the run checks with
    ///   the endpoint open.
    /// - witness: `judgement::session::tests::an_operation_a_scope_answers_captures_what_the_scope_opened_1334`
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::MachineInvariant | CheckRefusal::DanglingNode { .. } | CheckRefusal::Linearity { .. } | CheckRefusal::Access { .. } | CheckRefusal::Located { .. })))]
    pub(super) fn region_captured(
        &mut self,
        at: ComputationId,
        answerer: Answerer<'_>,
        payload: ValueId,
    ) -> Result<(), CheckRefusal>
    {
        let mark = match answerer {
            Answerer::Host => return Ok(()),
            // A depth past the open regions reads as the outermost mark.
            Answerer::Scope { depth, .. } => usize::try_from(u32::from(depth))
                .ok()
                .and_then(|depth| depth.checked_sub(1))
                .and_then(|region| self.sessions.regions.get(region))
                .copied()
                .unwrap_or_default(),
            Answerer::Anyone => 0,
        };
        if matches!(self.carrier(None), Some(Frame::AccessUnwind { .. })) {
            return Ok(());
        }
        let node = CoreNode::Term(TermNode::Computation(at));
        let handed = if let Value::Variable {
            zone: Zone::Linear,
            index,
        } = *self.value(payload)?
        {
            Some(index)
        }
        else {
            None
        };
        let opened = self.sessions.opened.len();
        for position in mark .. opened {
            let index = opened
                .checked_sub(position)
                .and_then(|above| above.checked_sub(1))
                .and_then(|index| u32::try_from(index).ok())
                .map(DeBruijnIndex::from)
                .ok_or(CheckRefusal::MachineInvariant)?;
            let use_state = self
                .context
                .binders()
                .linear_use(index)
                .map_err(|_fault| CheckRefusal::MachineInvariant)?;
            if use_state != LinearUse::Available {
                continue;
            }
            let resident = self
                .sessions
                .opened
                .get(position)
                .ok_or(CheckRefusal::MachineInvariant)?
                .resident;
            let returned = handed == Some(index) && matches!(resident, Resident::Buffer { .. });
            if !returned && !matches!(resident, Resident::Received { .. }) {
                if let Answerer::Scope { depth, operation } = answerer
                    && let Some(scope) = self.scope_at(depth)
                {
                    if !self
                        .sessions
                        .owing
                        .iter()
                        .any(|&(owing, ref name)| owing == scope && name == operation)
                    {
                        self.sessions.owing.push((scope, operation.clone()));
                    }
                    return Ok(());
                }
                return captured(node, resident, Capture::Continuation);
            }
        }
        Ok(())
    }

    /// The capability scope whose region stands at `depth`: the waiting scope
    /// subject that region counts, outermost first, among the waiting scope
    /// subjects and hold bodies.
    ///
    /// # Specification
    /// - ensures: the scope when the region at `depth` is a scope's; `None` for
    ///   a hold's region or a depth past the open ones.
    /// - panics: none.
    /// - executable: none — the frames are the machine's private stack, which
    ///   only a judgement drives.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an operation of an inner scope's capability records
    ///   the inner scope, not the outer one.
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    fn scope_at(
        &self,
        depth: RegionDepth,
    ) -> Option<ComputationId>
    {
        let region = usize::try_from(u32::from(depth)).ok()?.checked_sub(1)?;
        let waiting = self
            .frames
            .iter()
            .filter(|waiting| {
                matches!(
                    waiting.frame,
                    Frame::ScopeSubject { .. } | Frame::HoldBody { .. }
                )
            })
            .nth(region)?;
        if let Frame::ScopeSubject { at, .. } = waiting.frame {
            Some(at)
        }
        else {
            None
        }
    }

    /// Open the linear slot the operation clause `clause` owes the
    /// continuation it receives, which the next intuitionistic binder binds
    /// at `stack`: the clause must resume it or abandon it exactly once.
    ///
    /// # Specification
    /// - requires: the clause's payload is bound and its stack is not yet.
    /// - ensures: one linear slot more, held by [`Resident::Continuation`], and
    ///   one [`Owed`] entry at the next intuitionistic level.
    /// - fails: [`CheckRefusal::MachineInvariant`] past the slots a run counts.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clause owing its continuation that resumes it once
    ///   checks, and one that drops it is refused.
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    #[spec(
        captures: [owed = self.sessions.owed.len(), before = self.context.depth(Zone::Linear)],
        ensures: |ret| ret.is_err() || (self.sessions.owed.len() == owed.saturating_add(1) && self.context.depth(Zone::Linear) > before),
    )]
    pub(super) fn owe(
        &mut self,
        clause: ComputationId,
        stack: ValueTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let depth = self.context.depth(Zone::Intuitionistic);
        self.context.binders().open(Zone::Linear, stack);
        self.sessions.opened.push(Opened {
            resident: Resident::Continuation { clause },
            depth,
        });
        let slot = self
            .sessions
            .opened
            .len()
            .checked_sub(1)
            .ok_or(CheckRefusal::MachineInvariant)?;
        self.sessions.owed.push(Owed {
            stack: usize::from(depth),
            slot,
            clause,
        });
        Ok(())
    }

    /// End the operation clause whose body was judged, its payload and stack
    /// still bound: the continuation it owes, if any, must have been ended,
    /// and its slot closes.
    ///
    /// # Specification
    /// - requires: the clause's payload and stack are the innermost
    ///   intuitionistic binders.
    /// - ensures: the clause's [`Owed`] entry and its slot are gone; a clause
    ///   that owes nothing changes nothing.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::ContinuationUnspent`] at the clause's body for a
    ///   continuation neither resumed nor abandoned;
    ///   [`CheckRefusal::MachineInvariant`] when the slot is not the innermost.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clause that drops a continuation holding an
    ///   endpoint is refused, and one that abandons it checks.
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    #[spec(
        captures: owed = self.sessions.owed.len(),
        ensures: |ret| ret.is_err() || self.sessions.owed.len() <= owed,
    )]
    pub(super) fn owed_ended(&mut self) -> Result<(), CheckRefusal>
    {
        let depth = usize::from(self.context.depth(Zone::Intuitionistic));
        let Some(&owed) = self.sessions.owed.last()
        else {
            return Ok(());
        };
        if owed.stack.checked_add(1) != Some(depth) {
            return Ok(());
        }
        if owed.slot.checked_add(1) != Some(self.sessions.opened.len()) {
            return Err(CheckRefusal::MachineInvariant);
        }
        let use_state = self
            .context
            .binders()
            .linear_use(DeBruijnIndex::from(0_u32))
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        if use_state == LinearUse::Available {
            return Err(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Computation(owed.clause)),
                defect: LinearityDefect::ContinuationUnspent {
                    clause: owed.clause,
                },
            });
        }
        let _declared = self
            .context
            .binders()
            .close(Zone::Linear)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        let _opened = self.sessions.opened.pop();
        let _owed = self.sessions.owed.pop();
        Ok(())
    }

    /// The owed continuation the intuitionistic `index` names, read here.
    ///
    /// # Specification
    /// - ensures: the innermost [`Owed`] entry whose stack stands at the level
    ///   `index` names; `None` for a variable no owed stack is.
    /// - panics: none.
    /// - executable: none — the level reads the context's depth, which only a
    ///   judgement drives.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the stack is found from inside a nested binder.
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    fn owed_at(
        &self,
        index: DeBruijnIndex,
    ) -> Option<Owed>
    {
        if self.sessions.owed.is_empty() {
            return None;
        }
        let level = usize::from(self.context.depth(Zone::Intuitionistic))
            .checked_sub(1)?
            .checked_sub(usize::try_from(u32::from(index)).ok()?)?;
        self.sessions
            .owed
            .iter()
            .rev()
            .find(|owed| owed.stack == level)
            .copied()
    }

    /// Spend the owed continuation `stack` names, which the resumption or
    /// abandonment `at` ends, and admit the one read of it that follows.
    ///
    /// # Specification
    /// - ensures: for a stack that is an owed continuation's variable, its slot
    ///   is spent and [`Sessions::ending`] names its level; nothing changes
    ///   otherwise.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::ContinuationUsedTwice`] at `at` for a continuation
    ///   already ended; [`CheckRefusal::DanglingNode`] for a stack outside the
    ///   arena; [`CheckRefusal::MachineInvariant`] for a slot the binders do
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a continuation resumed twice is refused at the second
    ///   resumption.
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    #[spec(ensures: |ret| ret.is_err() || self.sessions.ending.is_none() || !self.sessions.owed.is_empty())]
    pub(super) fn ending(
        &mut self,
        at: ComputationId,
        stack: ValueId,
    ) -> Result<(), CheckRefusal>
    {
        if self.sessions.owed.is_empty() {
            return Ok(());
        }
        let Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        } = *self.value(stack)?
        else {
            return Ok(());
        };
        let Some(owed) = self.owed_at(index)
        else {
            return Ok(());
        };
        let slot = self
            .sessions
            .opened
            .len()
            .checked_sub(owed.slot)
            .and_then(|above| above.checked_sub(1))
            .and_then(|slot| u32::try_from(slot).ok())
            .map(DeBruijnIndex::from)
            .ok_or(CheckRefusal::MachineInvariant)?;
        match self.context.binders().occurrence(Zone::Linear, slot) {
            Ok(_) => {},
            Err(ContextError::LinearSlotConsumed { .. }) => {
                return Err(CheckRefusal::Linearity {
                    at: CoreNode::Term(TermNode::Computation(at)),
                    defect: LinearityDefect::ContinuationUsedTwice {
                        clause: owed.clause,
                    },
                });
            },
            Err(
                ContextError::UnboundIndex { .. }
                | ContextError::LinearSlotUnconsumed { .. }
                | ContextError::NoBinderToClose { .. },
            ) => return Err(CheckRefusal::MachineInvariant),
        }
        self.sessions.ending = Some(owed.stack);
        Ok(())
    }

    /// Admit the read `at` of the intuitionistic `index` only as what the
    /// resumption or abandonment being judged ends, when it names an owed
    /// continuation.
    ///
    /// # Specification
    /// - ensures: [`Sessions::ending`] is cleared when the read is the one it
    ///   admits; nothing changes otherwise.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::ContinuationAsValue`] at `at` for any other read of
    ///   an owed continuation.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clause returning its owed continuation as a value
    ///   is refused.
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::Linearity { defect: LinearityDefect::ContinuationAsValue { .. }, .. })))]
    pub(super) fn mention(
        &mut self,
        at: ValueId,
        index: DeBruijnIndex,
    ) -> Result<(), CheckRefusal>
    {
        let Some(owed) = self.owed_at(index)
        else {
            return Ok(());
        };
        if self.sessions.ending == Some(owed.stack) {
            self.sessions.ending = None;
            return Ok(());
        }
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(at)),
            defect: LinearityDefect::ContinuationAsValue {
                clause: owed.clause,
            },
        })
    }

    /// Refuse `term`, at `node`, naming an owed continuation where `by` may
    /// run its end other than once.
    ///
    /// # Specification
    /// - ensures: nothing changes.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::ContinuationCaptured`] with `by` for the first free
    ///   variable of `term` that is an owed continuation;
    ///   [`CheckRefusal::DanglingNode`] and [`CheckRefusal::MachineInvariant`]
    ///   as [`Self::free_linear`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clause resuming its owed continuation inside a
    ///   thunk is refused, and so is a child forked with it.
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::Linearity { defect: LinearityDefect::ContinuationCaptured { by: captor, .. }, .. }) if captor == by) || matches!(ret, Err(CheckRefusal::DanglingNode { .. } | CheckRefusal::MachineInvariant)))]
    pub(super) fn owed_named(
        &mut self,
        term: CoreTerm,
        node: CoreNode,
        by: Capture,
    ) -> Result<(), CheckRefusal>
    {
        if self.sessions.owed.is_empty() {
            return Ok(());
        }
        let free = self
            .sessions
            .free
            .intuitionistic(self.context.arena(), term)
            .map(<[DeBruijnIndex]>::to_vec)
            .map_err(|fault| match fault {
                gandr_core_nbe::FreeFault::Dangling => CheckRefusal::DanglingNode { node },
                gandr_core_nbe::FreeFault::MachineInvariant => CheckRefusal::MachineInvariant,
            })?;
        for index in free {
            if let Some(owed) = self.owed_at(index) {
                return Err(CheckRefusal::Linearity {
                    at: node,
                    defect: LinearityDefect::ContinuationCaptured {
                        clause: owed.clause,
                        by,
                    },
                });
            }
        }
        Ok(())
    }

    /// Continue a fork whose protocol annotation formed: split the zone, bind
    /// the child's end at the annotation and check the child against the
    /// returner of the unit at the fork's own row, the unknown type's row
    /// empty.
    ///
    /// # Specification
    /// - requires: the annotation formed.
    /// - ensures: one linear slot more, at the annotation's session type; one
    ///   `ForkChild` frame waits on the child's check.
    /// - fails: [`CheckRefusal::ShapeMismatch`] wanting
    ///   [`ExpectedShape::Session`] for an annotation that is no session type
    ///   at its weak head; [`CheckRefusal::Access`] naming
    ///   [`AccessDefect::KeptEscaped`] for a protocol that carries a value kept
    ///   in a region, and [`CheckRefusal::CapabilityEscaped`] for one that
    ///   carries a capability living in one, and the same for a variable the
    ///   child names: the child runs as a peer no region bounds, so a region
    ///   could end while it holds the value; [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::UsedTwice`] for an enclosing endpoint both halves
    ///   name, and [`LinearityDefect::ContinuationCaptured`] by
    ///   [`Capture::Task`] for a continuation an operation clause owes that the
    ///   child names.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat exchange forks at its protocol's alias, and
    ///   an endpoint both halves of an inner fork name is refused; a protocol
    ///   receiving a string checks and one receiving a string kept in a region
    ///   is refused; a child reading through a capability its parent holds for
    ///   the run checks, and one naming its scope's capability is refused.
    /// - witness: `judgement::session::tests::a_child_exercises_only_what_outlives_every_region_1334`
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    /// - witness: `judgement::session::tests::an_endpoint_used_twice_in_one_action_is_refused`
    /// - witness: `judgement::session::tests::an_inner_child_takes_an_outer_endpoint_only_when_its_parent_leaves_it`
    /// - witness: `judgement::session::tests::a_fork_carries_nothing_kept_in_a_region`
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Computation { .. }))))]
    pub(super) fn fork_formed(
        &mut self,
        at: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Session(SessionAction::Fork {
            protocol,
            child,
            parent,
        }) = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let head = self.context.whnf_value_type(protocol)?;
        if !matches!(
            value_type_view(self.context.arena(), head)?,
            ValueTypeView::Session(_)
        ) {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Session,
                found: TypeNode::Value(protocol),
            });
        }
        let node = CoreNode::Term(TermNode::Computation(at));
        // The child runs as a peer no region bounds: a value its protocol
        // carries in a region, or a capability living in one, would outlive
        // the region's end.
        match crate::capability::reaches(self.context.arena(), TypeNode::Value(head), Region::Held)?
        {
            crate::capability::Reach::Clear => {},
            crate::capability::Reach::Mentions => {
                return Err(CheckRefusal::CapabilityEscaped {
                    at: TermNode::Computation(at),
                    found: TypeNode::Value(protocol),
                });
            },
            crate::capability::Reach::Keeps => {
                return Err(CheckRefusal::Access {
                    at: node,
                    defect: AccessDefect::KeptEscaped,
                });
            },
        }
        if self.sessions.abstracted != crate::capability::Reach::Clear
            || !self.sessions.regions.is_empty()
        {
            self.unbounded(CoreTerm::Computation(child), at)?;
        }
        // A child could end the continuation after the clause returned.
        self.owed_named(CoreTerm::Computation(child), node, Capture::Task)?;
        let shared = self.free_linear(CoreTerm::Computation(parent))?;
        let shared: BTreeSet<DeBruijnIndex> = shared.into_iter().collect();
        for index in self.free_linear(CoreTerm::Computation(child))? {
            if u32::from(index) == 0 {
                continue;
            }
            let outer = DeBruijnIndex::from(u32::from(index).saturating_sub(1));
            // A child runs as its own continuation: a held value or a view
            // it names would be shared with the parent. A received value is
            // read by copy and never written, so sharing it is sound.
            let named = self.resided(node, outer)?;
            let Resident::Endpoint(endpoint) = named.resident
            else {
                if !matches!(named.resident, Resident::Received { .. }) {
                    captured(node, named.resident, Capture::Continuation)?;
                }
                continue;
            };
            if !shared.contains(&index) {
                continue;
            }
            return Err(CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::UsedTwice { endpoint },
            });
        }
        let depth = self.context.depth(Zone::Intuitionistic);
        self.context.binders().open(Zone::Linear, head);
        self.sessions.opened.push(Opened {
            resident: Resident::Endpoint(Endpoint {
                fork: at,
                side: ForkSide::Child,
            }),
            depth,
        });
        let row = match direction {
            Direction::Check(expected) => {
                let expected = self.context.whnf_comp_type(expected)?;
                match comp_type_view(self.context.arena(), expected)? {
                    CompTypeView::Returner { effects, .. } => effects.clone(),
                    CompTypeView::Unknown
                    | CompTypeView::With(..)
                    | CompTypeView::Arrow { .. }
                    | CompTypeView::Pi { .. }
                    | CompTypeView::Element { .. }
                    | CompTypeView::Codata { .. } => EffectRow::EMPTY,
                }
            },
            Direction::Synthesise => EffectRow::EMPTY,
        };
        let unit = self.context.atom(Atom::Unit).id();
        let returner = self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(unit, row);
        self.wait(Frame::ForkChild {
            at,
            direction,
            session: head,
        });
        Ok(Step::Descend(Goal::Computation {
            term: child,
            direction: Direction::Check(returner),
        }))
    }

    /// Close the innermost endpoint the run bound, refusing it unless spent,
    /// together with the enclosing endpoints `share` names, one binder out.
    ///
    /// # Specification
    /// - requires: the innermost linear slot is the run's.
    /// - ensures: that slot is closed and its entry dropped.
    /// - fails: [`CheckRefusal::Linearity`] naming [`LinearityDefect::Residue`]
    ///   at the fork with the first endpoint left unconsumed, the innermost
    ///   first.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child that never closes its end is refused, the
    ///   endpoint and its state named.
    /// - witness: `judgement::session::tests::a_leftover_endpoint_is_reported_by_name`
    /// - witness: `judgement::session::tests::an_outer_endpoint_an_inner_child_leaves_open_is_its_residue`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::Linearity { at: refused, defect: LinearityDefect::Residue { .. } }) => {
            refused == CoreNode::Term(TermNode::Computation(at))
        },
        | _ => true,
    })]
    fn spend(
        &mut self,
        at: ComputationId,
        share: &[DeBruijnIndex],
    ) -> Result<(), CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        let named = share.iter().copied().filter(|&index| u32::from(index) != 0);
        for index in core::iter::once(DeBruijnIndex::from(0_u32)).chain(named) {
            let read = self.resided(node, index)?;
            let Resident::Endpoint(endpoint) = read.resident
            else {
                continue;
            };
            if read.use_state == LinearUse::Available {
                return Err(CheckRefusal::Linearity {
                    at: node,
                    defect: LinearityDefect::Residue {
                        endpoint,
                        state: read.state,
                    },
                });
            }
        }
        let _state = self
            .context
            .binders()
            .close(Zone::Linear)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        let _opened = self.sessions.opened.pop();
        Ok(())
    }

    /// Continue a fork whose child checked: require the child's end and its
    /// share of the enclosing ones spent, then bind the parent's end at the
    /// dual and judge the parent in the fork's direction.
    ///
    /// # Specification
    /// - requires: the child checked.
    /// - ensures: the child's slot is closed and the parent's opened at the
    ///   dual of `session`; one `ForkParent` frame waits on the parent.
    /// - fails: as [`Self::spend`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat exchange's operator runs at the dual of the
    ///   seat's end.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Computation { .. }))))]
    pub(super) fn forked(
        &mut self,
        at: ComputationId,
        direction: Direction<CompTypeId>,
        session: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Session(SessionAction::Fork { child, parent, .. }) =
            *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let share = self.free_linear(CoreTerm::Computation(child))?;
        self.spend(at, &share)?;
        let dual = session_at(self.context, session)?.dual();
        let dual = self.context.arena_mut().value_type_session(dual);
        let depth = self.context.depth(Zone::Intuitionistic);
        self.context.binders().open(Zone::Linear, dual);
        self.sessions.opened.push(Opened {
            resident: Resident::Endpoint(Endpoint {
                fork: at,
                side: ForkSide::Parent,
            }),
            depth,
        });
        self.wait(Frame::ForkParent { at, direction });
        Ok(Step::Descend(Goal::Computation {
            term: parent,
            direction,
        }))
    }

    /// Finish a fork whose parent was judged: require the parent's end spent
    /// and hand the parent's result on.
    ///
    /// # Specification
    /// - requires: the parent was judged in `direction`.
    /// - ensures: the parent's slot is closed; the fork checked, or synthesised
    ///   the parent's type.
    /// - fails: as [`Self::spend`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an operator that leaves its end open is refused at
    ///   the fork; the seat exchange's operator closes it on every path.
    /// - witness: `judgement::session::tests::a_leftover_endpoint_is_reported_by_name`
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(_))))]
    pub(super) fn joined(
        &mut self,
        at: ComputationId,
        direction: Direction<CompTypeId>,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        self.spend(at, &[])?;
        match (direction, produced) {
            (Direction::Check(_), Produced::Checked) => Ok(Step::Ascend(Produced::Checked)),
            (Direction::Synthesise, Produced::CompType(ty)) => {
                Ok(Step::Ascend(Produced::CompType(ty)))
            },
            (Direction::Check(_) | Direction::Synthesise, _) => Err(CheckRefusal::MachineInvariant),
        }
    }
}

/// Refuse the resident `resident`, named at `node` by a former that may run
/// its use other than once, as `by` says; a held or received value a branch
/// reads passes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success for a held or received value named by a branch.
/// - fails: [`CheckRefusal::Linearity`] naming [`LinearityDefect::Captured`]
///   for an endpoint and [`LinearityDefect::ContinuationCaptured`] for a
///   clause's continuation; [`CheckRefusal::Access`] naming
///   [`AccessDefect::HeldCaptured`] for a held or received value and
///   [`AccessDefect::Escaped`] for a view, each at `node` with `by`.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a thunk naming an endpoint, a view and a held value is
///   refused by each name, and a branch reading a held value checks.
/// - witness: `judgement::session::tests::an_endpoint_captured_by_a_thunk_is_refused`
/// - witness: `judgement::access::tests::a_view_escaping_its_access_is_refused`
/// - witness: `judgement::session::tests::a_held_value_is_captured_by_a_branch_only`
/// - witness: `judgement::session::tests::a_buffer_capability_or_continuation_capture_is_refused_by_its_name`
#[spec(ensures: |ret| match (resident, ret) {
    | (Resident::Held { .. } | Resident::Received { .. } | Resident::Buffer { .. }, Ok(())) => by == Capture::Branch,
    | (Resident::Endpoint(_) | Resident::View { .. } | Resident::Capability { .. } | Resident::Continuation { .. }, Ok(())) => false,
    | (_, Err(_)) => true,
})]
fn captured(
    node: CoreNode,
    resident: Resident,
    by: Capture,
) -> Result<(), CheckRefusal>
{
    match resident {
        Resident::Endpoint(endpoint) => Err(CheckRefusal::Linearity {
            at: node,
            defect: LinearityDefect::Captured { endpoint, by },
        }),
        // A branch reads a held value by copy, and returns the buffer in each
        // arm or in none, which the case's join checks.
        Resident::Held { .. } | Resident::Received { .. } | Resident::Buffer { .. }
            if by == Capture::Branch =>
        {
            Ok(())
        },
        Resident::Buffer { at: site } => Err(CheckRefusal::Linearity {
            at: node,
            defect: LinearityDefect::BufferRead { site },
        }),
        Resident::Held { .. } | Resident::Received { .. } => Err(CheckRefusal::Access {
            at: node,
            defect: AccessDefect::HeldCaptured { by },
        }),
        Resident::View { .. } => Err(CheckRefusal::Access {
            at: node,
            defect: AccessDefect::Escaped { by },
        }),
        Resident::Capability { world } => Err(CheckRefusal::Located {
            at: node,
            defect: crate::worlds::LocatedDefect::CapabilityCaptured { world, by },
        }),
        Resident::Continuation { clause } => Err(CheckRefusal::Linearity {
            at: node,
            defect: LinearityDefect::ContinuationCaptured { clause, by },
        }),
    }
}

/// What a value handed on whole — by a send, an operation's payload or a
/// resumption — was.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum HandedOn
{
    /// A live buffer, whose slot the hand-off spent.
    Buffer,
    /// Anything else, which the hand-off checks as a value.
    Other,
}

/// Whether a resident owes something a continuation run twice or never would
/// break.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Owing
{
    /// An obligation: a protocol to finish, a buffer to return, an exclusive
    /// view to end, a capability to migrate once or a continuation to end
    /// once.
    Something,
    /// Nothing a read does not copy.
    Nothing,
}

/// Who answers an operation, and so how much of the run its continuation
/// holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Answerer<'operation>
{
    /// The host, through a capability it holds for the run: it answers once.
    Host,
    /// The clause of the capability scope whose region stands at `depth`,
    /// answering `operation`.
    Scope
    {
        /// The region's depth.
        depth: RegionDepth,
        /// The operation answered.
        operation: &'operation gandr_core_term::effect::OperationName,
    },
    /// Whichever handler stands nearest when the operation runs.
    Anyone,
}

#[cfg(test)]
mod tests;
