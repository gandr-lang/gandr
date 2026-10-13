//! The session rules on the judgement's machine: the fork that binds two
//! endpoints, the actions that advance them, the offer whose arms agree on
//! the linear zone, and the fence that keeps an endpoint out of every former
//! that may run its use other than once. The decisions are stated in
//! [`crate::session`].

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::CoreTerm;
use gandr_core_nbe::FreeIndices;
use gandr_core_term::BinderDepth;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::LinearUse;
use gandr_core_term::LinearZone;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::Purity;
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
use crate::context::Atom;
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

/// An endpoint the run bound: which fork and side, and the intuitionistic
/// depth its session type was formed at.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Opened
{
    /// The endpoint.
    endpoint: Endpoint,
    /// The intuitionistic depth at the fork.
    depth: BinderDepth,
}

/// The session state of one run: who bound each linear slot it opened, the
/// zones its offers restore and compare, and the free linear indices of the
/// terms it read.
#[derive(Debug)]
pub(super) struct Sessions
{
    /// The linear depth the run began at; slots below it are not the run's.
    base: BinderDepth,
    /// One entry per linear slot above `base`, outermost first.
    opened: Vec<Opened>,
    /// Each open offer's zone as the offer found it, then as its first arm
    /// left it, innermost offer last.
    zones: Vec<LinearZone>,
    /// The free linear indices of every term asked, each answered once.
    free: FreeIndices,
}

impl Sessions
{
    /// The session state of a run that begins with `base` linear slots open.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn new(base: BinderDepth) -> Self
    {
        Self {
            base,
            opened: Vec::new(),
            zones: Vec::new(),
            free: FreeIndices::default(),
        }
    }
}

/// How far a run's linear zone and its offers' zones stood: what a recovered
/// or refused run falls back to.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Scope
{
    /// The linear depth.
    linear: BinderDepth,
    /// The offers' zones held.
    zones: usize,
}

/// Where one offer's zones stand on the run's zone stack: the zone as the
/// offer found it at the mark, the zone its first arm left one above.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct ZoneMark(usize);

/// One linear slot, read: its endpoint, session type, remaining use and the
/// depth its type stands at.
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
    /// Where the linear zone and the offers' zones stand.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn session_scope(&self) -> Scope
    {
        Scope {
            linear: self.context.depth(Zone::Linear),
            zones: self.sessions.zones.len(),
        }
    }

    /// Drop every endpoint bound and every offer zone kept since `scope`,
    /// spent or not: the session half of unwinding a refused or recovered
    /// judgement.
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
    #[spec(ensures: self.context.depth(Zone::Linear) <= scope.linear && self.sessions.zones.len() <= scope.zones)]
    pub(super) fn close_sessions(
        &mut self,
        scope: Scope,
    )
    {
        self.context.binders().truncate(Zone::Linear, scope.linear);
        let kept = usize::from(scope.linear).saturating_sub(usize::from(self.sessions.base));
        self.sessions.opened.truncate(kept);
        self.sessions.zones.truncate(scope.zones);
    }

    /// The endpoints the run bound and still holds, outermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per linear slot above the run's base, with its
    ///   endpoint, session type and remaining use.
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
            .map(|((state, use_state), opened)| LiveEndpoint {
                endpoint: opened.endpoint,
                state,
                use_state,
            })
            .collect()
    }

    /// The linear slot `index` names, read at `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot's endpoint, session type, use and depth.
    /// - fails: [`CheckRefusal::Linearity`] naming [`LinearityDefect::Unbound`]
    ///   at `at` for an index past the zone; [`CheckRefusal::MachineInvariant`]
    ///   for a slot the run did not bind.
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
        | Ok(_) | Err(CheckRefusal::MachineInvariant) => true,
        | Err(CheckRefusal::Linearity { at: refused, defect: LinearityDefect::Unbound { index: unbound } }) => {
            refused == at && unbound == index
        },
        | Err(_) => false,
    })]
    fn slot(
        &mut self,
        at: CoreNode,
        index: DeBruijnIndex,
    ) -> Result<Slot, CheckRefusal>
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
        let opened = usize::try_from(u32::from(index))
            .ok()
            .and_then(|index| depth.checked_sub(index)?.checked_sub(1))
            .and_then(|position| position.checked_sub(usize::from(self.sessions.base)))
            .and_then(|position| self.sessions.opened.get(position))
            .ok_or(CheckRefusal::MachineInvariant)?;
        Ok(Slot {
            endpoint: opened.endpoint,
            state,
            use_state,
            depth: opened.depth,
        })
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
            | LinearUse::Available => Ok(slot),
            | LinearUse::Consumed => Err(CheckRefusal::Linearity {
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
    #[spec(
        captures: current = self.context.depth(Zone::Intuitionistic),
        ensures: |ret| (current != depth || ret == Ok(ty))
            && (current >= depth || ret == Err(CheckRefusal::MachineInvariant)),
    )]
    fn here(
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
        Ok(shift_value_type(
            self.context.arena_mut(),
            ty,
            Binders::from(opened),
        ))
    }

    /// The pure returner of the unit, an action's type.
    ///
    /// # Specification
    /// trivial.
    fn unit_returner(&mut self) -> CompTypeId
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
    fn free_linear(
        &mut self,
        term: CoreTerm,
    ) -> Result<Vec<DeBruijnIndex>, CheckRefusal>
    {
        let node = match term {
            | CoreTerm::Value(id) => CoreNode::Term(TermNode::Value(id)),
            | CoreTerm::Computation(id) => CoreNode::Term(TermNode::Computation(id)),
        };
        self.sessions
            .free
            .linear(self.context.arena(), term)
            .map(<[DeBruijnIndex]>::to_vec)
            .map_err(|fault| match fault {
                | gandr_core_nbe::FreeFault::Dangling => CheckRefusal::DanglingNode { node },
                | gandr_core_nbe::FreeFault::MachineInvariant => CheckRefusal::MachineInvariant,
            })
    }

    /// Refuse an endpoint named where its use may run other than once: a
    /// thunk, a fixpoint, a branching former, a first-class stack, a handler
    /// or a shift, while the run holds an endpoint.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing changes; a goal of another former, or any goal while
    ///   the run holds no endpoint, passes without its free indices read.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::Captured`] at the goal's term, with the first
    ///   endpoint it names and what may run it; a shift names the innermost
    ///   endpoint the run holds, which its captured continuation may resume
    ///   twice.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk naming an endpoint is refused while the same
    ///   action outside one checks.
    /// - witness: `judgement::session::tests::an_endpoint_captured_by_a_thunk_is_refused`
    #[spec(
        captures: holding = self.context.depth(Zone::Linear) > self.sessions.base,
        ensures: |ret| holding || ret.is_ok(),
    )]
    pub(super) fn fence(
        &mut self,
        goal: Goal,
    ) -> Result<(), CheckRefusal>
    {
        if self.context.depth(Zone::Linear) <= self.sessions.base {
            return Ok(());
        }
        let (term, node, by) = match goal {
            | Goal::Value { term, .. } => {
                let by = match *self.value(term)? {
                    | Value::Thunk(_) => Capture::Thunk,
                    | Value::Reify(_) => Capture::Stack,
                    | _ => return Ok(()),
                };
                (
                    CoreTerm::Value(term),
                    CoreNode::Term(TermNode::Value(term)),
                    by,
                )
            },
            | Goal::Computation { term, .. } => {
                let by = match *self.computation(term)? {
                    | Computation::Fixpoint { .. } => Capture::Recursion,
                    | Computation::Case { .. }
                    | Computation::DataCase { .. }
                    | Computation::With(..)
                    | Computation::ListFold { .. } => Capture::Branch,
                    | Computation::Handle { .. } => Capture::Continuation,
                    | Computation::Shift(_) => {
                        let node = CoreNode::Term(TermNode::Computation(term));
                        let endpoint = self.slot(node, DeBruijnIndex::from(0_u32))?.endpoint;
                        return Err(CheckRefusal::Linearity {
                            at: node,
                            defect: LinearityDefect::Captured {
                                endpoint,
                                by: Capture::Continuation,
                            },
                        });
                    },
                    | _ => return Ok(()),
                };
                (
                    CoreTerm::Computation(term),
                    CoreNode::Term(TermNode::Computation(term)),
                    by,
                )
            },
            | Goal::Form(_) | Goal::Stack { .. } => return Ok(()),
        };
        let Some(&first) = self.free_linear(term)?.first()
        else {
            return Ok(());
        };
        let endpoint = self.slot(node, first)?.endpoint;
        Err(CheckRefusal::Linearity {
            at: node,
            defect: LinearityDefect::Captured { endpoint, by },
        })
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
    /// - witness: `judgement::session::tests::delegation_and_sharing_are_refused_by_name`
    #[spec(ensures: |ret| ret.is_err())]
    pub(super) fn endpoint_as_value(
        &mut self,
        term: ValueId,
        index: DeBruijnIndex,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Value(term));
        let slot = self.slot(node, index).map_err(|refusal| match refusal {
            | CheckRefusal::Linearity {
                defect: LinearityDefect::Unbound { .. },
                ..
            } => CheckRefusal::UnboundIndex {
                at: term,
                zone: Zone::Linear,
                index,
                depth: self.context.depth(Zone::Linear),
            },
            | other => other,
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
    ///   endpoint at that arm's branch; a fork standing at a pure returner
    ///   forms its protocol annotation.
    /// - fails: [`CheckRefusal::SessionMismatch`] for an action the state does
    ///   not admit, a label it does not offer, or arms that are not exactly its
    ///   labels; [`CheckRefusal::Linearity`] for an action after close, a
    ///   payload naming its own endpoint or another, and a fork at an impure
    ///   type; [`CheckRefusal::NotSynthesisable`] for an offer in synthesis.
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
            | (&SessionAction::Send { endpoint, payload }, _) => self.send(term, endpoint, payload),
            | (&SessionAction::Receive { endpoint }, _) => self.receive(term, endpoint),
            | (
                &SessionAction::Select {
                    endpoint,
                    ref label,
                },
                _,
            ) => {
                let label = label.clone();
                self.select(term, endpoint, &label)
            },
            | (&SessionAction::Close { endpoint }, _) => self.close_endpoint(term, endpoint),
            | (&SessionAction::Offer { .. }, Direction::Check(expected)) => {
                self.offer(term, expected)
            },
            | (&SessionAction::Offer { .. }, Direction::Synthesise) => {
                Err(CheckRefusal::NotSynthesisable {
                    form: crate::refusal::CheckingForm::Offer(term),
                })
            },
            | (&SessionAction::Fork { protocol, .. }, _) => {
                if let Direction::Check(expected) = direction {
                    self.pure_fork(term, expected)?;
                }
                self.wait(Frame::ForkProtocol {
                    at: term,
                    direction,
                });
                Ok(Step::Descend(Goal::Form(TypeNode::Value(protocol))))
            },
        }
    }

    /// The session type `slot` stands at, when its next step is `observed`.
    ///
    /// # Specification
    /// - requires: `slot` was read by [`Self::live`].
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
    ///   state receives.
    /// - witness: `judgement::session::tests::an_operator_holding_the_seat_view_is_refused`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|session| session.step().is_ok_and(|step| step.action() == observed)))]
    fn admitted(
        &self,
        at: ComputationId,
        slot: Slot,
        observed: ActionKind,
    ) -> Result<SessionType, CheckRefusal>
    {
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

    /// Start a send: check the payload, then advance the endpoint.
    ///
    /// # Specification
    /// - requires: `at` is a send on `endpoint` of `payload`.
    /// - ensures: one `SessionSend` frame waits on the payload's check against
    ///   the payload type, read where the send stands.
    /// - fails: as [`Self::live`] and [`Self::admitted`];
    ///   [`CheckRefusal::Linearity`] naming [`LinearityDefect::UsedTwice`] when
    ///   the payload names the endpoint and [`LinearityDefect::Delegated`] when
    ///   it names another.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a send over its own endpoint and a send of another
    ///   endpoint are refused, and the seat exchange's sends check.
    /// - witness: `judgement::session::tests::an_endpoint_used_twice_in_one_action_is_refused`
    /// - witness: `judgement::session::tests::delegation_and_sharing_are_refused_by_name`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Value { .. }))))]
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
        let named = self.free_linear(CoreTerm::Value(payload))?;
        if let Some(&other) = named.first() {
            let node = CoreNode::Term(TermNode::Value(payload));
            return Err(CheckRefusal::Linearity {
                at: node,
                defect: if named.contains(&endpoint) {
                    LinearityDefect::UsedTwice {
                        endpoint: slot.endpoint,
                    }
                }
                else {
                    let _named = self.slot(node, other)?;
                    LinearityDefect::Delegated
                },
            });
        }
        let next = self.context.arena_mut().value_type_session(next);
        let expected = self.here(ty, slot.depth)?;
        self.wait(Frame::SessionSend { at, endpoint, next });
        Ok(Step::Descend(Goal::Value {
            term: payload,
            direction: Direction::Check(expected),
        }))
    }

    /// Finish a send whose payload checked: advance the endpoint.
    ///
    /// # Specification
    /// - requires: the payload checked.
    /// - ensures: the endpoint stands at `next`; the send synthesises the
    ///   returner of the unit.
    /// - fails: [`CheckRefusal::MachineInvariant`] when the endpoint is no
    ///   longer available, which a payload naming no endpoint cannot cause.
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

    /// Receive on `endpoint`.
    ///
    /// # Specification
    /// - requires: `at` is a receive on `endpoint`.
    /// - ensures: the endpoint stands at the continuation; the receive
    ///   synthesises the returner of the payload type, read where it stands.
    /// - fails: as [`Self::live`] and [`Self::admitted`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's first receive binds the dispatch.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))))]
    fn receive(
        &mut self,
        at: ComputationId,
        endpoint: DeBruijnIndex,
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
        let returner = self.context.arena_mut().comp_type_returner(payload);
        Ok(Step::Ascend(Produced::CompType(returner)))
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
    ///   or an endpoint no longer at the offer.
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
            let endpoint = position
                .checked_sub(base)
                .and_then(|position| self.sessions.opened.get(position))
                .ok_or(CheckRefusal::MachineInvariant)?
                .endpoint;
            return Err(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Computation(other)),
                defect: LinearityDefect::ArmsDisagree {
                    endpoint,
                    first,
                    other,
                },
            });
        }
        Ok(())
    }

    /// Refuse a fork that stands at `ty` unless `ty` is a pure returner or
    /// the unknown type.
    ///
    /// # Specification
    /// - requires: `ty` is formed.
    /// - ensures: nothing changes.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::Captured`] by [`Capture::Continuation`] with the
    ///   fork's child end: an operation in the fork's scope could be resumed
    ///   twice by a handler.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fork checked against an effectful returner is
    ///   refused while the same fork against the pure one checks.
    /// - witness: `judgement::session::tests::an_endpoint_captured_by_a_thunk_is_refused`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::Linearity { at: refused, defect: LinearityDefect::Captured { endpoint, by } }) => {
            refused == CoreNode::Term(TermNode::Computation(at))
                && endpoint.fork == at
                && by == Capture::Continuation
        },
        | _ => true,
    })]
    fn pure_fork(
        &mut self,
        at: ComputationId,
        ty: CompTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let head = self.context.whnf_comp_type(ty)?;
        let pure = match comp_type_view(self.context.arena(), head)? {
            | CompTypeView::Returner { effects, .. } => effects.purity() == Purity::Pure,
            | CompTypeView::Unknown => true,
            | CompTypeView::With(..)
            | CompTypeView::Arrow { .. }
            | CompTypeView::Pi { .. }
            | CompTypeView::Element { .. } => false,
        };
        if pure {
            return Ok(());
        }
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(at)),
            defect: LinearityDefect::Captured {
                endpoint: Endpoint {
                    fork: at,
                    side: ForkSide::Child,
                },
                by: Capture::Continuation,
            },
        })
    }

    /// Continue a fork whose protocol annotation formed: split the zone, bind
    /// the child's end at the annotation and check the child against the pure
    /// returner of the unit.
    ///
    /// # Specification
    /// - requires: the annotation formed.
    /// - ensures: one linear slot more, at the annotation's session type; one
    ///   `ForkChild` frame waits on the child's check.
    /// - fails: [`CheckRefusal::ShapeMismatch`] wanting
    ///   [`ExpectedShape::Session`] for an annotation that is no session type
    ///   at its weak head; [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::UsedTwice`] for an enclosing endpoint both halves
    ///   name.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat exchange forks at its protocol's alias, and
    ///   an endpoint both halves of an inner fork name is refused.
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    /// - witness: `judgement::session::tests::an_endpoint_used_twice_in_one_action_is_refused`
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
        let shared = self.free_linear(CoreTerm::Computation(parent))?;
        for index in self.free_linear(CoreTerm::Computation(child))? {
            if u32::from(index) == 0 || !shared.contains(&index) {
                continue;
            }
            let outer = DeBruijnIndex::from(u32::from(index).saturating_sub(1));
            let endpoint = self.slot(node, outer)?.endpoint;
            return Err(CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::UsedTwice { endpoint },
            });
        }
        let depth = self.context.depth(Zone::Intuitionistic);
        self.context.binders().open(Zone::Linear, head);
        self.sessions.opened.push(Opened {
            endpoint: Endpoint {
                fork: at,
                side: ForkSide::Child,
            },
            depth,
        });
        let unit = self.unit_returner();
        self.wait(Frame::ForkChild {
            at,
            direction,
            session: head,
        });
        Ok(Step::Descend(Goal::Computation {
            term: child,
            direction: Direction::Check(unit),
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
            let slot = self.slot(node, index)?;
            if slot.use_state == LinearUse::Available {
                return Err(CheckRefusal::Linearity {
                    at: node,
                    defect: LinearityDefect::Residue {
                        endpoint: slot.endpoint,
                        state: slot.state,
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
            endpoint: Endpoint {
                fork: at,
                side: ForkSide::Parent,
            },
            depth,
        });
        self.wait(Frame::ForkParent { at, direction });
        Ok(Step::Descend(Goal::Computation {
            term: parent,
            direction,
        }))
    }

    /// Finish a fork whose parent was judged: require the parent's end spent
    /// and hand the parent's result on, a synthesised type required pure.
    ///
    /// # Specification
    /// - requires: the parent was judged in `direction`.
    /// - ensures: the parent's slot is closed; the fork checked, or synthesised
    ///   the parent's type.
    /// - fails: as [`Self::spend`]; as [`Self::pure_fork`] for a synthesised
    ///   type.
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
            | (Direction::Check(_), Produced::Checked) => Ok(Step::Ascend(Produced::Checked)),
            | (Direction::Synthesise, Produced::CompType(ty)) => {
                self.pure_fork(at, ty)?;
                Ok(Step::Ascend(Produced::CompType(ty)))
            },
            | (Direction::Check(_) | Direction::Synthesise, _) => {
                Err(CheckRefusal::MachineInvariant)
            },
        }
    }

    /// Finish a session type's formation: no payload may be a session type.
    ///
    /// # Specification
    /// - requires: every payload of `at` formed.
    /// - ensures: nothing changes; the session type formed.
    /// - fails: [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::Delegated`] at the first payload that is a session
    ///   type at its weak head.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a protocol sending a session type is refused.
    /// - witness: `judgement::session::tests::delegation_and_sharing_are_refused_by_name`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::Checked))))]
    pub(super) fn session_formed(
        &mut self,
        at: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let payloads: Vec<ValueTypeId> = session_at(self.context, at)?.payloads().to_vec();
        for payload in payloads {
            let head = self.context.whnf_value_type(payload)?;
            if matches!(
                value_type_view(self.context.arena(), head)?,
                ValueTypeView::Session(_)
            ) {
                return Err(CheckRefusal::Linearity {
                    at: CoreNode::Type(TypeNode::Value(payload)),
                    defect: LinearityDefect::Delegated,
                });
            }
        }
        Ok(Step::Ascend(Produced::Checked))
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::sync::Arc;
    use alloc::vec::Vec;

    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::LinearUse;
    use gandr_core_term::Sort;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_core_term::session::ActionKind;
    use gandr_core_term::session::PayloadCount;
    use gandr_core_term::session::PayloadSlot;
    use gandr_core_term::session::Protocol;
    use gandr_core_term::session::ProtocolState;
    use gandr_core_term::session::ProtocolSyntax;
    use gandr_core_term::session::RecursionIndex;
    use gandr_core_term::session::SessionAction;
    use gandr_core_term::session::SessionType;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::StringLiteral;
    use quenchant_shape::shape::Maybe;

    use crate::CheckBudget;
    use crate::CheckRefusal;
    use crate::CheckingContext;
    use crate::CoreNode;
    use crate::Declaration;
    use crate::OriginToken;
    use crate::TermNode;
    use crate::TypeNode;
    use crate::Verdict;
    use crate::body;
    use crate::bridge;
    use crate::check_comp;
    use crate::check_module;
    use crate::form_comp_type;
    use crate::form_value_type;
    use crate::judgement::check_value_with_failure;
    use crate::session::Capture;
    use crate::session::Endpoint;
    use crate::session::ForkSide;
    use crate::session::LinearityDefect;
    use crate::session::ProtocolDefect;

    /// A label or a string as a test spells it.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Spelled(&'static str);

    /// The label `spelled` names.
    ///
    /// # Specification
    /// trivial.
    fn label(Spelled(text): Spelled) -> FieldLabel
    {
        FieldLabel::from(String::from(text))
    }

    /// The session type over `syntax` rooted at its first node, its payloads
    /// `payloads`.
    ///
    /// # Specification
    /// trivial.
    fn session(
        arena: &mut CoreArena,
        syntax: Vec<ProtocolSyntax>,
        payloads: &[ValueTypeId],
    ) -> ValueTypeId
    {
        let protocol = Protocol::new(
            syntax,
            ProtocolState::from(0_usize),
            PayloadCount::from(payloads.len()),
        )
        .unwrap();
        let session = SessionType::new(Arc::new(protocol), Arc::from(payloads)).unwrap();
        arena.value_type_session(session)
    }

    /// The seat's end: `?Dispatch. mu turn. +{ report : !Report. &{ next :
    /// turn, retire : end }, handoff : !Handoff. end }`, every payload a
    /// string.
    ///
    /// # Specification
    /// trivial.
    fn seat_end(arena: &mut CoreArena) -> ValueTypeId
    {
        let string = arena.value_type_base(BaseType::String);
        let state = ProtocolState::from;
        session(
            arena,
            alloc::vec![
                ProtocolSyntax::Receive {
                    payload: PayloadSlot::from(0_usize),
                    next: state(1),
                },
                ProtocolSyntax::Mu(state(2)),
                ProtocolSyntax::Select(BTreeMap::from([
                    (label(Spelled("handoff")), state(6)),
                    (label(Spelled("report")), state(3)),
                ])),
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(1_usize),
                    next: state(4),
                },
                ProtocolSyntax::Offer(BTreeMap::from([
                    (label(Spelled("next")), state(5)),
                    (label(Spelled("retire")), state(7)),
                ])),
                ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(2_usize),
                    next: state(8),
                },
                ProtocolSyntax::End,
                ProtocolSyntax::End,
            ],
            &[string, string, string],
        )
    }

    /// The pure `end` protocol.
    ///
    /// # Specification
    /// trivial.
    fn end(arena: &mut CoreArena) -> ValueTypeId
    {
        session(arena, alloc::vec![ProtocolSyntax::End], &[])
    }

    /// The terms one endpoint's program is built of, the endpoint the
    /// innermost linear binder.
    #[repr(transparent)]
    struct Program<'arena>
    {
        /// The arena.
        arena: &'arena mut CoreArena,
    }

    impl Program<'_>
    {
        /// The endpoint, the innermost linear binder.
        ///
        /// # Specification
        /// trivial.
        fn endpoint() -> DeBruijnIndex
        {
            DeBruijnIndex::from(0_u32)
        }

        /// `x <- action ; rest`.
        ///
        /// # Specification
        /// trivial.
        fn then(
            &mut self,
            action: SessionAction,
            rest: ComputationId,
        ) -> ComputationId
        {
            let action = self.arena.computation_session(action);
            self.arena.computation_bind(action, rest)
        }

        /// The action alone.
        ///
        /// # Specification
        /// trivial.
        fn act(
            &mut self,
            action: SessionAction,
        ) -> ComputationId
        {
            self.arena.computation_session(action)
        }

        /// The string literal `text`.
        ///
        /// # Specification
        /// trivial.
        fn text(
            &mut self,
            Spelled(text): Spelled,
        ) -> ValueId
        {
            self.arena
                .value_literal(Literal::Text(StringLiteral::new(String::from(text))))
        }

        /// `close(c)`.
        ///
        /// # Specification
        /// trivial.
        fn close(&mut self) -> ComputationId
        {
            self.act(SessionAction::Close {
                endpoint: Self::endpoint(),
            })
        }

        /// `select(c, l) ; rest`.
        ///
        /// # Specification
        /// trivial.
        fn select(
            &mut self,
            choice: Spelled,
            rest: ComputationId,
        ) -> ComputationId
        {
            self.then(
                SessionAction::Select {
                    endpoint: Self::endpoint(),
                    label: label(choice),
                },
                rest,
            )
        }

        /// `send(c, text) ; rest`.
        ///
        /// # Specification
        /// trivial.
        fn send(
            &mut self,
            text: Spelled,
            rest: ComputationId,
        ) -> ComputationId
        {
            let payload = self.text(text);
            self.then(
                SessionAction::Send {
                    endpoint: Self::endpoint(),
                    payload,
                },
                rest,
            )
        }

        /// `recv(c) as x ; rest`.
        ///
        /// # Specification
        /// trivial.
        fn receive(
            &mut self,
            rest: ComputationId,
        ) -> ComputationId
        {
            self.then(
                SessionAction::Receive {
                    endpoint: Self::endpoint(),
                },
                rest,
            )
        }

        /// `offer(c) { l => arm, … }`.
        ///
        /// # Specification
        /// trivial.
        fn offer(
            &mut self,
            arms: &[(Spelled, ComputationId)],
        ) -> ComputationId
        {
            self.act(SessionAction::Offer {
                endpoint: Self::endpoint(),
                arms: arms
                    .iter()
                    .map(|&(choice, arm)| (label(choice), arm))
                    .collect(),
            })
        }
    }

    /// The seat's half: receive the dispatch, report, then on `next` hand
    /// off and on `retire` close.
    ///
    /// # Specification
    /// trivial.
    fn seat(arena: &mut CoreArena) -> ComputationId
    {
        let mut program = Program { arena };
        let closed = program.close();
        let notes = program.send(Spelled("notes"), closed);
        let handed = program.select(Spelled("handoff"), notes);
        let retired = program.close();
        let answered = program.offer(&[(Spelled("next"), handed), (Spelled("retire"), retired)]);
        let reported = program.send(Spelled("progress"), answered);
        let chose = program.select(Spelled("report"), reported);
        program.receive(chose)
    }

    /// The operator's half: dispatch, then take each choice the seat makes,
    /// asking for the next report once and retiring the seat the second
    /// time.
    ///
    /// # Specification
    /// trivial.
    fn operator(arena: &mut CoreArena) -> ComputationId
    {
        let mut program = Program { arena };
        let closed = program.close();
        let second_notes = program.receive(closed);
        let closed = program.close();
        let retired = program.select(Spelled("retire"), closed);
        let second_report = program.receive(retired);
        let second = program.offer(&[
            (Spelled("handoff"), second_notes),
            (Spelled("report"), second_report),
        ]);
        let again = program.select(Spelled("next"), second);
        let first_report = program.receive(again);
        let closed = program.close();
        let first_notes = program.receive(closed);
        let first = program.offer(&[
            (Spelled("handoff"), first_notes),
            (Spelled("report"), first_report),
        ]);
        program.send(Spelled("task"), first)
    }

    /// `fork (c : protocol) { child } as d ; parent`.
    ///
    /// # Specification
    /// trivial.
    fn fork(
        arena: &mut CoreArena,
        protocol: ValueTypeId,
        child: ComputationId,
        parent: ComputationId,
    ) -> ComputationId
    {
        arena.computation_session(SessionAction::Fork {
            protocol,
            child,
            parent,
        })
    }

    /// Check `term` against the pure returner of the unit.
    ///
    /// # Specification
    /// trivial.
    fn check_unit(
        arena: &mut CoreArena,
        term: ComputationId,
    ) -> Result<(), CheckRefusal>
    {
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
        let returner = form_comp_type(&mut context, returner)?;
        let checked = check_comp(&mut context, term, returner).map(|_| ());
        assert_eq!(
            context.depth(Zone::Linear),
            gandr_core_term::BinderDepth::default(),
            "a run leaves the linear zone as it found it"
        );
        checked
    }

    /// The child end of `fork`.
    ///
    /// # Specification
    /// trivial.
    const fn child(fork: ComputationId) -> Endpoint
    {
        Endpoint {
            fork,
            side: ForkSide::Child,
        }
    }

    #[test]
    fn the_seat_exchange_checks_at_both_ends()
    {
        let mut arena = CoreArena::new();
        let protocol = seat_end(&mut arena);
        let seat = seat(&mut arena);
        let operator = operator(&mut arena);
        let exchange = fork(&mut arena, protocol, seat, operator);
        assert_eq!(
            check_unit(&mut arena, exchange),
            Ok(()),
            "the seat follows its end and the operator the dual, through both choices"
        );
    }

    #[test]
    fn an_operator_holding_the_seat_view_is_refused()
    {
        let mut arena = CoreArena::new();
        let protocol = seat_end(&mut arena);
        let seat = seat(&mut arena);
        let wrong = Program { arena: &mut arena }.act(SessionAction::Receive {
            endpoint: DeBruijnIndex::from(0_u32),
        });
        let exchange = fork(&mut arena, protocol, seat, wrong);
        let refused = check_unit(&mut arena, exchange);
        assert!(
            matches!(
                refused,
                Err(CheckRefusal::SessionMismatch {
                    at,
                    endpoint: Endpoint { fork, side: ForkSide::Parent },
                    defect: ProtocolDefect::Action { expected: ActionKind::Send, observed: ActionKind::Receive },
                    ..
                }) if at == wrong && fork == exchange
            ),
            "the operator's end sends first, so a receive on it is refused: {refused:?}"
        );
    }

    #[test]
    fn a_leftover_endpoint_is_reported_by_name()
    {
        let mut arena = CoreArena::new();
        let protocol = end(&mut arena);
        let unit = arena.value_unit();
        let idle = arena.computation_return(unit);
        let closed = Program { arena: &mut arena }.close();
        let exchange = fork(&mut arena, protocol, idle, closed);
        let thunk = arena.value_thunk(exchange);
        let unit_type = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit_type);
        let suspended = arena.value_type_thunk(returner);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let suspended = form_value_type(&mut context, suspended).unwrap();
        let failure = check_value_with_failure(&mut context, thunk, suspended).unwrap_err();
        assert_eq!(
            failure.refusal(),
            CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Computation(exchange)),
                defect: LinearityDefect::Residue {
                    endpoint: child(exchange),
                    state: protocol,
                },
            },
            "the child finished with its end unclosed, named with its state"
        );
        assert_eq!(
            failure
                .endpoints()
                .iter()
                .map(|live| (live.endpoint, live.state, live.use_state))
                .collect::<Vec<_>>(),
            [(child(exchange), protocol, LinearUse::Available)],
            "the failure lists every endpoint the run held"
        );
        assert_eq!(
            context.depth(Zone::Linear),
            gandr_core_term::BinderDepth::default(),
            "the refused run leaves no endpoint behind"
        );
    }

    #[test]
    fn an_endpoint_used_after_close_is_refused()
    {
        let mut arena = CoreArena::new();
        let protocol = end(&mut arena);
        let mut program = Program { arena: &mut arena };
        let again = program.close();
        let twice = program.then(
            SessionAction::Close {
                endpoint: DeBruijnIndex::from(0_u32),
            },
            again,
        );
        let closed = program.close();
        let exchange = fork(&mut arena, protocol, twice, closed);
        assert_eq!(
            check_unit(&mut arena, exchange),
            Err(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Computation(again)),
                defect: LinearityDefect::Closed {
                    endpoint: child(exchange),
                },
            }),
            "the second close acts on a consumed endpoint"
        );
    }

    #[test]
    fn an_endpoint_used_twice_in_one_action_is_refused()
    {
        let mut arena = CoreArena::new();
        let string = arena.value_type_base(BaseType::String);
        // !String. end
        let protocol = session(
            &mut arena,
            alloc::vec![
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(0_usize),
                    next: ProtocolState::from(1_usize),
                },
                ProtocolSyntax::End,
            ],
            &[string],
        );
        let itself = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
        let mut program = Program { arena: &mut arena };
        let closed = program.close();
        let send = program.then(
            SessionAction::Send {
                endpoint: DeBruijnIndex::from(0_u32),
                payload: itself,
            },
            closed,
        );
        let received = program.close();
        let parent = program.receive(received);
        let exchange = fork(&mut arena, protocol, send, parent);
        assert_eq!(
            check_unit(&mut arena, exchange),
            Err(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Value(itself)),
                defect: LinearityDefect::UsedTwice {
                    endpoint: child(exchange),
                },
            }),
            "an endpoint sent over itself is used twice in the send"
        );
    }

    #[test]
    fn an_endpoint_captured_by_a_thunk_is_refused()
    {
        let mut arena = CoreArena::new();
        let protocol = end(&mut arena);
        let closed = Program { arena: &mut arena }.close();
        let suspended = arena.value_thunk(closed);
        let forced = arena.computation_force(suspended);
        let parent = Program { arena: &mut arena }.close();
        let exchange = fork(&mut arena, protocol, forced, parent);
        assert_eq!(
            check_unit(&mut arena, exchange),
            Err(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Value(suspended)),
                defect: LinearityDefect::Captured {
                    endpoint: child(exchange),
                    by: Capture::Thunk,
                },
            }),
            "a thunk may be forced any number of times"
        );
        let direct = Program { arena: &mut arena }.close();
        let parent = Program { arena: &mut arena }.close();
        let exchange = fork(&mut arena, protocol, direct, parent);
        assert_eq!(
            check_unit(&mut arena, exchange),
            Ok(()),
            "the same close outside the thunk checks"
        );
    }

    #[test]
    fn offer_arms_leaving_different_endpoints_are_refused()
    {
        let mut arena = CoreArena::new();
        // &{ a : end, b : end }
        let protocol = session(
            &mut arena,
            alloc::vec![
                ProtocolSyntax::Offer(BTreeMap::from([
                    (label(Spelled("a")), ProtocolState::from(1_usize)),
                    (label(Spelled("b")), ProtocolState::from(2_usize)),
                ])),
                ProtocolSyntax::End,
                ProtocolSyntax::End,
            ],
            &[],
        );
        let unit = arena.value_unit();
        let left_open = arena.computation_return(unit);
        let mut program = Program { arena: &mut arena };
        let closed = program.close();
        let offer = program.offer(&[(Spelled("a"), closed), (Spelled("b"), left_open)]);
        let parent_closed = program.close();
        let parent = program.select(Spelled("a"), parent_closed);
        let exchange = fork(&mut arena, protocol, offer, parent);
        assert_eq!(
            check_unit(&mut arena, exchange),
            Err(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Computation(left_open)),
                defect: LinearityDefect::ArmsDisagree {
                    endpoint: child(exchange),
                    first: closed,
                    other: left_open,
                },
            }),
            "one arm closes the endpoint and the other leaves it open"
        );
    }

    #[test]
    fn an_endpoint_at_a_top_level_declaration_is_refused()
    {
        let mut arena = CoreArena::new();
        let protocol = end(&mut arena);
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let suspended = arena.value_type_thunk(returner);
        let declarations = [
            Declaration::new(
                ConstantIndex::from(0_usize),
                Maybe::Present(protocol),
                Maybe::Absent(body::Absent::Hole),
                OriginToken::from(0_usize),
            ),
            Declaration::new(
                ConstantIndex::from(1_usize),
                Maybe::Present(suspended),
                Maybe::Absent(body::Absent::Hole),
                OriginToken::from(1_usize),
            ),
        ];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let report = check_module(&mut context, &declarations);
        let verdicts: Vec<_> = report.judged().iter().map(crate::Judged::verdict).collect();
        assert_eq!(
            verdicts.first(),
            Some(&Verdict::Refused(CheckRefusal::Linearity {
                at: CoreNode::Type(TypeNode::Value(protocol)),
                defect: LinearityDefect::Unrestricted,
            })),
            "an endpoint exists only in the linear zone a fork opens"
        );
        assert!(
            matches!(verdicts.get(1), Some(Verdict::Owed(_))),
            "a declaration at a thunk type is owed as before"
        );
    }

    #[test]
    fn delegation_and_sharing_are_refused_by_name()
    {
        let mut arena = CoreArena::new();
        let ended = end(&mut arena);
        // !end. end
        let delegating = session(
            &mut arena,
            alloc::vec![
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(0_usize),
                    next: ProtocolState::from(1_usize),
                },
                ProtocolSyntax::End,
            ],
            &[ended],
        );
        let child_closed = Program { arena: &mut arena }.close();
        let parent_closed = Program { arena: &mut arena }.close();
        let exchange = fork(&mut arena, delegating, child_closed, parent_closed);
        assert_eq!(
            check_unit(&mut arena, exchange),
            Err(CheckRefusal::Linearity {
                at: CoreNode::Type(TypeNode::Value(ended)),
                defect: LinearityDefect::Delegated,
            }),
            "a protocol that sends a session type delegates"
        );

        let string = arena.value_type_base(BaseType::String);
        // !String. end, whose child sends the parent's end of an inner fork
        let sending = session(
            &mut arena,
            alloc::vec![
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(0_usize),
                    next: ProtocolState::from(1_usize),
                },
                ProtocolSyntax::End,
            ],
            &[string],
        );
        // The payload is the inner fork's parent end, index 0; the send acts
        // on the outer child's end, index 1.
        let outer = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
        let inner_closed = Program { arena: &mut arena }.close();
        let mut program = Program { arena: &mut arena };
        let after_send = program.act(SessionAction::Close {
            endpoint: DeBruijnIndex::from(1_u32),
        });
        let inner_parent = program.then(
            SessionAction::Send {
                endpoint: DeBruijnIndex::from(1_u32),
                payload: outer,
            },
            after_send,
        );
        let inner = fork(&mut arena, ended, inner_closed, inner_parent);
        let received = Program { arena: &mut arena }.close();
        let parent = Program { arena: &mut arena }.receive(received);
        let exchange = fork(&mut arena, sending, inner, parent);
        let refused = check_unit(&mut arena, exchange);
        assert!(
            matches!(
                refused,
                Err(CheckRefusal::Linearity { at: CoreNode::Term(TermNode::Value(at)), defect: LinearityDefect::Delegated })
                    if at == outer
            ),
            "a send whose payload is another endpoint delegates: {refused:?}"
        );

        let itself = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
        let escaped = arena.computation_return(itself);
        let parent = Program { arena: &mut arena }.close();
        let exchange = fork(&mut arena, ended, escaped, parent);
        assert_eq!(
            check_unit(&mut arena, exchange),
            Err(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Value(itself)),
                defect: LinearityDefect::AsValue {
                    endpoint: child(exchange),
                },
            }),
            "an endpoint read as a value would be shared"
        );
    }

    #[test]
    fn readmission_refuses_a_session_typed_declaration_by_name()
    {
        let mut arena = CoreArena::new();
        let protocol = end(&mut arena);
        let quoted = arena.value_quote(protocol);
        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let declarations = [Declaration::new(
            ConstantIndex::from(0_usize),
            Maybe::Present(universe),
            Maybe::Present(quoted),
            OriginToken::from(0_usize),
        )];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let report = check_module(&mut context, &declarations);
        assert!(
            matches!(
                report.judged().first().map(crate::Judged::verdict),
                Some(Verdict::Checked { .. })
            ),
            "a session type is a code the checker forms"
        );
        let readmission = bridge::readmit(&mut arena, &report);
        assert_eq!(
            readmission
                .readmitted()
                .first()
                .map(bridge::Readmitted::outcome),
            Some(&bridge::Outcome::Refused(bridge::Refusal::Session {
                at: CoreNode::Type(TypeNode::Value(protocol)),
            })),
            "the kernel has no channels, so the declaration stays on the checker's side"
        );
        assert_eq!(
            bridge::Refusal::Session {
                at: CoreNode::Type(TypeNode::Value(protocol)),
            }
            .classify(),
            gandr_core_term::FailureClass::Unrepresentable,
            "a session is unrepresentable, not a fault"
        );
    }
}
