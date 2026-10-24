//! The located rules on the judgement's machine: the hold that makes a
//! handle where it stands, the `leta` that opens one at its world, the
//! migration that spends a capability and moves the world register, and the
//! checks every variable, constant and linear resident meets at the world it
//! is read at. The decisions are stated in [`crate::worlds`].

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::LinearUse;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::shift_comp_type;
use gandr_core_term::strengthen_comp_type;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_core_term::world::WorldType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Direction;
use super::Frame;
use super::Goal;
use super::Machine;
use super::Produced;
use super::Step;
use super::session::Opened;
use super::session::Resident;
use crate::context::Recording;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::session::Capture;
use crate::view::ValueTypeView;
use crate::view::value_type_view;
use crate::worlds::Crossed;
use crate::worlds::Crossing;
use crate::worlds::LocatedDefect;
use crate::worlds::WorldMove;
use crate::worlds::crosses;

/// Whether a run opened its entry's capabilities.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Entered
{
    /// No capability was opened: the run is not an entry's outermost one, or
    /// its entry holds none.
    Bare,
    /// The entry's capabilities were opened, one linear slot each.
    Holding,
}

/// The refusal of a located judgement at `at`.
///
/// # Specification
/// trivial.
const fn located(
    at: CoreNode,
    defect: LocatedDefect,
) -> CheckRefusal
{
    CheckRefusal::Located { at, defect }
}

impl Machine<'_, '_>
{
    /// Open the capabilities of the entry under way, when this run is its
    /// outermost: one linear slot per capability, located at the register.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when an entry is under way, the linear zone is empty and the
    ///   entry holds a capability, one available slot per capability, in the
    ///   order named, each at its world's capability type and located at the
    ///   register, and [`Entered::Holding`]; nothing changes otherwise, and
    ///   [`Entered::Bare`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an entry with one capability migrates once and is
    ///   refused a second migration; a body judged at no entry has no
    ///   capability to migrate with.
    /// - witness: `worlds::tests::a_migration_consumes_its_capability_visibly`
    /// - witness: `worlds::tests::a_second_migration_without_a_capability_is_refused`
    #[spec(
        captures: before = usize::from(self.context.depth(Zone::Linear)),
        ensures: |ret| (ret == Entered::Bare) == (usize::from(self.context.depth(Zone::Linear)) == before),
    )]
    pub(super) fn open_entry(&mut self) -> Entered
    {
        if usize::from(self.context.depth(Zone::Linear)) != 0 {
            return Entered::Bare;
        }
        let &Maybe::Present(ref entry) = self.context.worlds().entered()
        else {
            return Entered::Bare;
        };
        let capabilities: Vec<World> = entry.capabilities().to_vec();
        if capabilities.is_empty() {
            return Entered::Bare;
        }
        let depth = self.context.depth(Zone::Intuitionistic);
        for world in capabilities {
            let ty = self
                .context
                .arena_mut()
                .value_type_world(WorldType::Capability(world));
            self.context.binders().open(Zone::Linear, ty);
            self.sessions.opened.push(Opened {
                resident: Resident::Capability { world },
                depth,
            });
        }
        Entered::Holding
    }

    /// The rules of the world forms: a hold makes a handle at the register, a
    /// `leta` opens one, a migration spends a capability and moves the
    /// register.
    ///
    /// # Specification
    /// - requires: `term` is a world form.
    /// - ensures: a hold checked against the returner of a handle at the
    ///   register waits on its value's check against what the handle holds; any
    ///   other hold waits on its value's synthesis; a `leta` waits on its
    ///   handle's synthesis; a migration spends its capability and waits on its
    ///   body at the world it names.
    /// - fails: [`LocatedDefect::Unlocated`] for a hold or a `leta` at the
    ///   host's world; [`LocatedDefect::HoldElsewhere`] for a hold checked
    ///   against a handle at another world; as [`Self::migrate`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each form in each direction, and each refusal by
    ///   name.
    /// - witness: `worlds::tests::a_migration_consumes_its_capability_visibly`
    /// - witness: `worlds::tests::hold_cannot_fabricate_a_remote_value`
    /// - witness: `worlds::tests::a_located_hypothesis_is_usable_only_at_its_world`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(_))))]
    pub(super) fn world(
        &mut self,
        term: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::World(form) = *self.computation(term)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let node = CoreNode::Term(TermNode::Computation(term));
        let register = self.context.binders().world();
        match form {
            WorldForm::Hold { value } => {
                if register == World::Host {
                    return Err(located(node, LocatedDefect::Unlocated));
                }
                if let Direction::Check(expected) = direction {
                    let result = self.returner_expected(term, expected)?;
                    let head = self.context.whnf_value_type(result)?;
                    if let ValueTypeView::World(WorldType::At { inner, world }) =
                        value_type_view(self.context.arena(), head)?
                    {
                        if world != register {
                            return Err(located(node, LocatedDefect::HoldElsewhere {
                                wanted: world,
                            }));
                        }
                        self.wait(Frame::ReturnValue);
                        return Ok(Step::Descend(Goal::Value {
                            term: value,
                            direction: Direction::Check(inner),
                        }));
                    }
                    self.wait(Frame::CompBridge { at: term, expected });
                }
                self.wait(Frame::WorldHold { at: term });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Synthesise,
                }))
            },
            WorldForm::Leta { value, .. } => {
                if register == World::Host {
                    return Err(located(node, LocatedDefect::Unlocated));
                }
                self.wait(Frame::LetaValue {
                    at: term,
                    direction,
                });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Synthesise,
                }))
            },
            WorldForm::Migrate { world, body } => self.migrate(term, world, body, direction),
        }
    }

    /// The handle a hold whose value synthesised `held` makes: `held` at the
    /// register, returned purely.
    ///
    /// # Specification
    /// - requires: a hold standing at the register synthesised `held`.
    /// - ensures: the pure returner of `held at w`, `w` the register.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a report held at the operator's world opens there and
    ///   nowhere else.
    /// - witness: `worlds::tests::a_located_hypothesis_is_usable_only_at_its_world`
    #[spec(ensures: |ret| matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))))]
    pub(super) fn held_here(
        &mut self,
        held: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let world = self.context.binders().world();
        let arena = self.context.arena_mut();
        let handle = arena.value_type_world(WorldType::At { inner: held, world });
        Ok(Step::Ascend(Produced::CompType(
            arena.comp_type_returner(handle),
        )))
    }

    /// Continue a `leta` whose handle synthesised `handle`: open its binder
    /// at the handle's world and judge the body in the `leta`'s direction.
    ///
    /// # Specification
    /// - requires: `at` is a `leta` whose handle synthesised `handle`.
    /// - ensures: one intuitionistic binder more, at what the handle holds and
    ///   located at its world — at the unknown type and the register for an
    ///   unknown handle; one `LetaBody` frame waits on the body.
    /// - fails: [`LocatedDefect::NotAHandle`] for a type of another former;
    ///   [`CheckRefusal::Linearity`] for a handle holding a session type, which
    ///   an unrestricted binder cannot hold.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `leta` at the operator's world opens a report the
    ///   operator may read and the seat may not.
    /// - witness: `worlds::tests::a_located_hypothesis_is_usable_only_at_its_world`
    #[spec(
        captures: before = self.context.depth(Zone::Intuitionistic),
        ensures: |ret| ret.is_err() || self.context.depth(Zone::Intuitionistic) > before,
    )]
    pub(super) fn opened_at(
        &mut self,
        at: ComputationId,
        direction: Direction<CompTypeId>,
        handle: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let WorldForm::Leta { body, .. } = self.world_form(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let head = self.context.whnf_value_type(handle)?;
        let (inner, world) = match value_type_view(self.context.arena(), head)? {
            ValueTypeView::World(WorldType::At { inner, world }) => (inner, world),
            ValueTypeView::Unknown => (head, self.context.binders().world()),
            ValueTypeView::World(WorldType::Capability(_))
            | ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Prefix(_)
            | ValueTypeView::Dialogue(_)
            | ValueTypeView::Web
            | ValueTypeView::Sum(_)
            | ValueTypeView::List(_)
            | ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Character
            | ValueTypeView::Float64
            | ValueTypeView::Fixed(_)
            | ValueTypeView::Unit
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::Product(_)
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Sigma { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Kept { .. }
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Buffer
            | ValueTypeView::Row
            | ValueTypeView::RowTail(_)
            | ValueTypeView::Session(_) => {
                return Err(located(
                    CoreNode::Term(TermNode::Computation(at)),
                    LocatedDefect::NotAHandle { found: handle },
                ));
            },
        };
        crate::session::unrestricted(self.context, inner)?;
        let direction = match direction {
            Direction::Synthesise => Direction::Synthesise,
            Direction::Check(expected) => {
                let arena = self.context.arena_mut();
                Direction::Check(
                    shift_comp_type(arena, expected, Binders::from(1_u32)).settle(arena),
                )
            },
        };
        self.context
            .binders()
            .open_at(Zone::Intuitionistic, inner, world);
        self.wait(Frame::LetaBody { at });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction,
        }))
    }

    /// Finish a `leta` whose body was judged: close its binder and hand the
    /// body's result on, a synthesised type read without the binder.
    ///
    /// # Specification
    /// - requires: the body was judged under the `leta`'s binder.
    /// - ensures: the binder is closed; the `leta` checked, or synthesised the
    ///   body's type strengthened past its binder.
    /// - fails: [`CheckRefusal::DependentBind`] for a synthesised type that
    ///   mentions the binder.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::opened_at`].
    /// - witness: `worlds::tests::a_located_hypothesis_is_usable_only_at_its_world`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(_))))]
    pub(super) fn leta_closed(
        &mut self,
        at: ComputationId,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        match produced {
            Produced::Checked => {
                self.close()?;
                Ok(Step::Ascend(Produced::Checked))
            },
            Produced::CompType(synthesised) => {
                let Maybe::Present(lowered) =
                    strengthen_comp_type(self.context.arena_mut(), synthesised)
                else {
                    return Err(CheckRefusal::DependentBind { at, synthesised });
                };
                let lowered = lowered.settle(self.context.arena_mut());
                self.close()?;
                Ok(Step::Ascend(Produced::CompType(lowered)))
            },
            Produced::ValueType(_) => Err(CheckRefusal::MachineInvariant),
        }
    }

    /// Start the migration `at` to `to`: spend a capability for `to` standing
    /// at the register, move the register and judge `body` there.
    ///
    /// # Specification
    /// - requires: `at` is a migration to `to` of `body`.
    /// - ensures: one capability slot for `to` located at the register, still
    ///   available, is spent; the register is `to`; one `MigrateBody` frame
    ///   waits on the body, holding the world left. A typed run keeps the move
    ///   with the linear zone before and after the spend.
    /// - fails: [`LocatedDefect::UndeclaredWorld`] for a position no world
    ///   declaration holds; [`LocatedDefect::CapabilityCaptured`] under a
    ///   former that may run the migration other than once;
    ///   [`LocatedDefect::CapabilityMissing`] when no such capability is left.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a migration with its capability, a second one
    ///   without, and one under a thunk the entry did not force, each answered
    ///   by name.
    /// - witness: `worlds::tests::a_migration_consumes_its_capability_visibly`
    /// - witness: `worlds::tests::a_second_migration_without_a_capability_is_refused`
    #[spec(ensures: |ret| ret.is_err()
        || (self.context.world() == to && matches!(ret, Ok(Step::Descend(Goal::Computation { .. })))))]
    fn migrate(
        &mut self,
        at: ComputationId,
        to: World,
        body: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        self.context
            .worlds()
            .named(to)
            .map_err(|defect| located(node, defect))?;
        self.uncaptured(node, to)?;
        let register = self.context.binders().world();
        let index = self.capability(node, to, register)?;
        let recording = self.context.recording() == Recording::On;
        let before = recording.then(|| self.context.binders().linear_zone());
        let _spent = self
            .context
            .binders()
            .occurrence(Zone::Linear, index)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        self.context.worlds_mut().spend();
        if let Some(before) = before {
            let after = self.context.binders().linear_zone();
            self.context.keep_move(WorldMove::Migrated {
                at,
                from: register,
                to,
                before,
                after,
            });
        }
        let _left = self.context.binders().relocate(to);
        self.wait(Frame::MigrateBody {
            at,
            from: register,
            direction,
        });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction,
        }))
    }

    /// Finish a migration whose body was judged at the world it moved to: put
    /// the register back at `from` and cross the body's result there.
    ///
    /// # Specification
    /// - requires: the body was judged in `direction` at the register.
    /// - ensures: the register is `from`; the migration checked, or synthesised
    ///   the body's type. A typed run keeps the return.
    /// - fails: [`LocatedDefect::Immobile`] naming [`Crossed::Result`] for a
    ///   result whose type does not cross.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a migration returning a mobile report checks, one
    ///   returning an endpoint and one returning an unmarked abstract payload
    ///   are refused by name.
    /// - witness: `worlds::tests::a_report_crosses_and_an_endpoint_does_not`
    /// - witness: `worlds::tests::an_unmarked_abstract_payload_is_immobile`
    #[spec(ensures: |ret| self.context.world() == from && (ret.is_err() || matches!(ret, Ok(Step::Ascend(_)))))]
    pub(super) fn returned(
        &mut self,
        at: ComputationId,
        from: World,
        direction: Direction<CompTypeId>,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        let _left = self.context.binders().relocate(from);
        let ty = match (direction, produced) {
            (Direction::Check(expected), Produced::Checked) => expected,
            (Direction::Synthesise, Produced::CompType(synthesised)) => synthesised,
            (Direction::Check(_) | Direction::Synthesise, _) => {
                return Err(CheckRefusal::MachineInvariant);
            },
        };
        let result = self.returner_expected(at, ty)?;
        if let Crossing::Stays { former, predicate } = crosses(self.context, result)? {
            return Err(located(node, LocatedDefect::Immobile {
                crossed: Crossed::Result,
                ty: result,
                former,
                predicate,
            }));
        }
        self.context.keep_move(WorldMove::Returned { at, to: from });
        Ok(Step::Ascend(produced))
    }

    /// Refuse a migration to `to` at `at` standing under a former that may run
    /// it other than once: a thunk other than the one the run judges, a
    /// first-class stack, a fixpoint, a branch, a handler or a shift.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing changes.
    /// - fails: [`LocatedDefect::CapabilityCaptured`] naming the innermost such
    ///   former's capture for a pending rule it owns; the run's own goal
    ///   captures nothing, its host forcing it once.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a migration inside a thunk within the entry's own is
    ///   refused, while one directly in the entry's checks.
    /// - witness: `worlds::tests::a_second_migration_without_a_capability_is_refused`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::Located { at: node, defect }) => node == at
            && matches!(defect, LocatedDefect::CapabilityCaptured { world, .. } if world == to),
        | Ok(()) | Err(_) => true,
    })]
    fn uncaptured(
        &self,
        at: CoreNode,
        to: World,
    ) -> Result<(), CheckRefusal>
    {
        let Some(root) = self.frames.first().map(|waiting| waiting.owner)
        else {
            return Ok(());
        };
        for waiting in self.frames.iter().rev() {
            if waiting.owner == root {
                continue;
            }
            let by = match waiting.owner {
                Goal::Value { term, .. } => {
                    let value = self.value(term)?;
                    if matches!(*value, Value::Thunk(_)) {
                        Capture::Thunk
                    }
                    else if matches!(*value, Value::Reify(_)) {
                        Capture::Stack
                    }
                    else {
                        continue;
                    }
                },
                Goal::Computation { term, .. } => {
                    let computation = self.computation(term)?;
                    if matches!(*computation, Computation::Fixpoint { .. }) {
                        Capture::Recursion
                    }
                    else if matches!(
                        *computation,
                        Computation::Case { .. }
                            | Computation::DataCase { .. }
                            | Computation::With(..)
                            | Computation::ListFold { .. }
                            | Computation::ListCase { .. }
                    ) {
                        Capture::Branch
                    }
                    else if matches!(
                        *computation,
                        Computation::Handle { .. }
                            | Computation::Scope { .. }
                            | Computation::Shift(_)
                    ) {
                        Capture::Continuation
                    }
                    else {
                        continue;
                    }
                },
                Goal::Form(_) | Goal::Stack { .. } => continue,
            };
            return Err(located(at, LocatedDefect::CapabilityCaptured {
                world: to,
                by,
            }));
        }
        Ok(())
    }

    /// The index of an available capability for `to` the run holds, located
    /// at `register`, innermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the linear index of such a slot.
    /// - fails: [`LocatedDefect::CapabilityMissing`] at `at` when none is.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first migration finds its capability, the second
    ///   finds it spent.
    /// - witness: `worlds::tests::a_second_migration_without_a_capability_is_refused`
    #[spec(ensures: |ret| match ret {
        | Ok(index) => usize::try_from(u32::from(index))
            .is_ok_and(|index| index < usize::from(self.context.depth(Zone::Linear))),
        | Err(CheckRefusal::Located { at: node, defect }) => node == at
            && defect == (LocatedDefect::CapabilityMissing { world: to }),
        | Err(_) => true,
    })]
    fn capability(
        &mut self,
        at: CoreNode,
        to: World,
        register: World,
    ) -> Result<DeBruijnIndex, CheckRefusal>
    {
        let base = usize::from(self.sessions.base);
        let binders = self.context.binders();
        let depth = usize::from(binders.depth(Zone::Linear));
        let standing: Vec<(LinearUse, World)> = binders
            .linear_slots()
            .map(|(_state, use_state)| use_state)
            .zip(binders.linear_worlds())
            .skip(base)
            .collect();
        let found = self
            .sessions
            .opened
            .iter()
            .zip(standing)
            .enumerate()
            .rev()
            .find_map(|(position, (opened, (use_state, world)))| {
                (opened.resident == (Resident::Capability { world: to })
                    && use_state == LinearUse::Available
                    && world == register)
                    .then_some(position)
            });
        let Some(position) = found
        else {
            return Err(located(at, LocatedDefect::CapabilityMissing { world: to }));
        };
        let index = base
            .checked_add(position)
            .and_then(|outer| depth.checked_sub(outer)?.checked_sub(1))
            .and_then(|index| u32::try_from(index).ok())
            .ok_or(CheckRefusal::MachineInvariant)?;
        Ok(DeBruijnIndex::from(index))
    }

    /// Refuse the intuitionistic variable `index`, read at `term`, when it was
    /// bound at a world other than the register.
    ///
    /// # Specification
    /// - requires: `index` names a binder.
    /// - ensures: nothing changes.
    /// - fails: [`LocatedDefect::Elsewhere`] naming both worlds;
    ///   [`CheckRefusal::MachineInvariant`] for an index past the zone.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a report opened at the operator's world, read there
    ///   and inside a migration to the seat's.
    /// - witness: `worlds::tests::a_located_hypothesis_is_usable_only_at_its_world`
    #[spec(ensures: |ret| match ret {
        | Ok(()) => true,
        | Err(CheckRefusal::Located { defect: LocatedDefect::Elsewhere { bound }, .. }) => {
            bound != self.context.world()
        },
        | Err(refusal) => refusal == CheckRefusal::MachineInvariant,
    })]
    pub(super) fn located_here(
        &mut self,
        term: ValueId,
        index: DeBruijnIndex,
    ) -> Result<(), CheckRefusal>
    {
        let binders = self.context.binders();
        let used = binders.world();
        let bound = binders
            .located(Zone::Intuitionistic, index)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        if bound == used {
            return Ok(());
        }
        Err(located(
            CoreNode::Term(TermNode::Value(term)),
            LocatedDefect::Elsewhere { bound },
        ))
    }

    /// Refuse the constant `constant` of type `ty`, read at `term`, when it is
    /// an entry, or is homed at another world and its type does not cross.
    ///
    /// # Specification
    /// - requires: `ty` is the constant's formed type.
    /// - ensures: nothing changes.
    /// - fails: [`LocatedDefect::EntryNamed`] for a declaration that spent a
    ///   capability; [`LocatedDefect::Immobile`] naming [`Crossed::Constant`]
    ///   for one homed at a declared world other than the register whose type
    ///   does not cross.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's entry named from a later declaration is
    ///   refused; an operator-homed report read inside a migration crosses.
    /// - witness: `worlds::tests::a_second_migration_without_a_capability_is_refused`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::Located { defect: LocatedDefect::EntryNamed { constant: named }, .. }) => {
            named == constant
        },
        | Err(CheckRefusal::Located { at, defect: LocatedDefect::Immobile { crossed, .. } }) => {
            crossed == Crossed::Constant && at == CoreNode::Term(TermNode::Value(term))
        },
        | Ok(()) | Err(_) => true,
    })]
    pub(super) fn located_constant(
        &mut self,
        term: ValueId,
        constant: ConstantIndex,
        ty: ValueTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Value(term));
        let worlds = self.context.worlds();
        worlds
            .nameable(constant)
            .map_err(|defect| located(node, defect))?;
        let home = worlds.home(constant);
        let register = self.context.binders().world();
        if home == World::Host || home == register {
            return Ok(());
        }
        match crosses(self.context, ty)? {
            Crossing::Crosses => Ok(()),
            Crossing::Stays { former, predicate } => Err(located(node, LocatedDefect::Immobile {
                crossed: Crossed::Constant,
                ty,
                former,
                predicate,
            })),
        }
    }

    /// The world form at `at`.
    ///
    /// # Specification
    /// trivial.
    fn world_form(
        &self,
        at: ComputationId,
    ) -> Result<WorldForm, CheckRefusal>
    {
        match *self.computation(at)? {
            Computation::World(form) => Ok(form),
            Computation::Primitive { .. }
            | Computation::Transport(..)
            | Computation::PathTransport { .. }
            | Computation::Ride { .. }
            | Computation::TelescopeTransport { .. }
            | Computation::Lambda(_)
            | Computation::Fixpoint { .. }
            | Computation::Application(..)
            | Computation::Return(_)
            | Computation::Bind(..)
            | Computation::Ascribe { .. }
            | Computation::Force(_)
            | Computation::Decompose(_)
            | Computation::Case { .. }
            | Computation::DataCase { .. }
            | Computation::Split { .. }
            | Computation::RecordProjection(..)
            | Computation::TupleProjection(..)
            | Computation::Hole(_)
            | Computation::Mark { .. }
            | Computation::ListFold { .. }
            | Computation::ListCase { .. }
            | Computation::Perform { .. }
            | Computation::Handle { .. }
            | Computation::Exercise { .. }
            | Computation::Scope { .. }
            | Computation::Resume(..)
            | Computation::Abandon(_)
            | Computation::Reset(_)
            | Computation::Shift(_)
            | Computation::With(..)
            | Computation::Project(..)
            | Computation::Session(_)
            | Computation::Memory(_) => Err(CheckRefusal::MachineInvariant),
        }
    }
}
