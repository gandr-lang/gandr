//! The access rules on the judgement's machine: the hold that binds a held
//! value, the access that lends it to a view, the two eliminators that end
//! the view, a read of either resident, and the naming of an unwind's
//! effect. The decisions are stated in [`crate::access`].

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::LinearUse;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::row::RowInclusion;
use gandr_kernel_term::DeBruijnIndex;

use super::Control;
use super::Direction;
use super::Frame;
use super::Goal;
use super::Machine;
use super::Produced;
use super::Step;
use super::session::Lent;
use super::session::Opened;
use super::session::Resided;
use super::session::Resident;
use crate::access::AccessDefect;
use crate::context::Atom;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::Mismatch;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::session::LinearityDefect;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

impl Machine<'_, '_>
{
    /// The rules of the memory forms: a hold synthesises its value, an
    /// access lends its held slot, or a place of it, in its mode, a resume
    /// checks its value, an abort ends its view at once, a consume moves its
    /// held value out.
    ///
    /// # Specification
    /// - requires: `term` is a memory form.
    /// - ensures: a hold waits on its value's synthesis; an access of the whole
    ///   value opens its view at the held slot's type and waits on its body in
    ///   `direction`; an access at a place whose held slot it may lend waits on
    ///   its index's check against the integer type; a resume waits on its
    ///   value's check against the view's type; an abort spends its view and
    ///   synthesises the returner of the unit; a consume leaves its held slot
    ///   moved out and synthesises the returner of the slot's type.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::NotHeld`] for
    ///   an access of a slot that holds no value, [`AccessDefect::Lent`] for an
    ///   access its slot's lending excludes, [`AccessDefect::NotAView`] for an
    ///   eliminator of a slot that is no view, [`AccessDefect::Spent`] for one
    ///   of a spent view and [`AccessDefect::ReadOnly`] for one of a shared
    ///   view; for a consume, as [`Self::lendable`] at the exclusive mode;
    ///   [`CheckRefusal::Linearity`] naming [`LinearityDefect::Unbound`] for an
    ///   index past the zone.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter drives every form in both directions, and
    ///   each refusal has its own term.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_view_resumed_twice_is_refused`
    /// - witness: `judgement::access::tests::a_held_value_lent_or_misnamed_is_refused`
    /// - witness: `judgement::access::tests::a_shared_view_reads_beside_its_held_value_and_ends_with_its_body`
    /// - witness: `judgement::access::tests::a_place_of_a_held_list_is_lent_at_its_index`
    /// - witness: `judgement::access::tests::a_consume_ends_its_hold_and_answers_the_held_value`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(_) | Step::Ascend(Produced::CompType(_)))))]
    pub(super) fn memory(
        &mut self,
        term: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Memory(ref form) = *self.computation(term)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        match *form {
            MemoryForm::Hold { value, grade, .. } => {
                if grade == HoldGrade::One {
                    self.entered_in_place(value)?;
                }
                self.wait(Frame::HoldValue {
                    at: term,
                    direction,
                });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Synthesise,
                }))
            },
            MemoryForm::Access {
                mode,
                held,
                place: Place::Whole,
                body,
            } => self.access(term, held, mode.mode(), body, direction),
            MemoryForm::Access {
                mode,
                held,
                place: Place::At { index },
                ..
            } => {
                let node = CoreNode::Term(TermNode::Computation(term));
                let _lendable = self.lendable(node, held, mode.mode())?;
                let integer = self.context.atom(Atom::Integer).id();
                self.wait(Frame::AccessIndex {
                    at: term,
                    direction,
                });
                Ok(Step::Descend(Goal::Value {
                    term: index,
                    direction: Direction::Check(integer),
                }))
            },
            MemoryForm::Resume { view, value } => {
                let node = CoreNode::Term(TermNode::Computation(term));
                let lent = self.live_view(node, view)?;
                let expected = self.here(lent.state, lent.depth)?;
                self.wait(Frame::ResumeValue { at: term, view });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Check(expected),
                }))
            },
            MemoryForm::Abort { view } => {
                let node = CoreNode::Term(TermNode::Computation(term));
                let lent = self.live_view(node, view)?;
                if lent.use_state == LinearUse::Moved {
                    return Err(CheckRefusal::Access {
                        at: node,
                        defect: AccessDefect::Moved,
                    });
                }
                self.spend_view(node, view)
            },
            MemoryForm::Consume { held } => {
                let node = CoreNode::Term(TermNode::Computation(term));
                let found = self.lendable(node, held, AccessMode::Exclusive { unwind: () })?;
                let _moved = self
                    .context
                    .binders()
                    .move_out(held)
                    .map_err(|_fault| CheckRefusal::MachineInvariant)?;
                let ty = self.here(found.state, found.depth)?;
                let returner = self.context.arena_mut().comp_type_returner(ty);
                Ok(Step::Ascend(Produced::CompType(returner)))
            },
        }
    }

    /// Refuse an answer that names the innermost region deep, `around` being
    /// the region the answer lands in, the one open around the innermost: the
    /// side condition `ρ ∉ fv(A)` of a region's body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing changes.
    /// - fails: [`CheckRefusal::CapabilityEscaped`] at `at` for an answer whose
    ///   capability lives in a region that ends while `around` is live, and
    ///   [`CheckRefusal::Access`] naming [`AccessDefect::KeptEscaped`] at `at`
    ///   for one whose value is kept there; [`CheckRefusal::DanglingNode`] for
    ///   an answer outside the arena.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold answering a thunk kept in its own region is
    ///   refused, and one answering a value outside it checks.
    /// - witness: `judgement::access::tests::a_view_kept_in_a_hold_lives_as_long_as_the_hold`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::Access { at: refused, defect }) => refused == CoreNode::Term(TermNode::Computation(at))
            && defect == AccessDefect::KeptEscaped,
        | Ok(()) | Err(_) => true,
    })]
    fn answers_outside(
        &self,
        at: ComputationId,
        answer: CompTypeId,
        around: Region,
    ) -> Result<(), CheckRefusal>
    {
        match crate::capability::reaches(
            self.context.arena(),
            TypeNode::Computation(answer),
            around,
        )? {
            crate::capability::Reach::Clear => Ok(()),
            crate::capability::Reach::Mentions => Err(CheckRefusal::CapabilityEscaped {
                at: TermNode::Computation(at),
                found: TypeNode::Computation(answer),
            }),
            crate::capability::Reach::Keeps => Err(CheckRefusal::Access {
                at: CoreNode::Term(TermNode::Computation(at)),
                defect: AccessDefect::KeptEscaped,
            }),
        }
    }

    /// The region the innermost open region stands at.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the number of regions open, as a depth.
    /// - fails: [`CheckRefusal::MachineInvariant`] past the depth a region
    ///   counts.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a view kept at a hold's own depth and at an inner
    ///   hold's depth each stand in the hold that opened it.
    /// - witness: `judgement::access::tests::a_view_kept_in_a_hold_lives_as_long_as_the_hold`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|depth| usize::try_from(u32::from(*depth)).ok() == Some(self.sessions.regions.len())))]
    fn innermost_region(&self) -> Result<RegionDepth, CheckRefusal>
    {
        u32::try_from(self.sessions.regions.len())
            .map(RegionDepth::from)
            .map_err(|_overflow| CheckRefusal::MachineInvariant)
    }

    /// Continue a hold whose value synthesised `held`: open the held slot at
    /// `held`, then the hold's region past it, and judge the scope in the
    /// hold's direction.
    ///
    /// # Specification
    /// - requires: the hold's value synthesised `held`.
    /// - ensures: one linear slot more, at `held`, held by `at`; one region
    ///   more, its mark past the held slot, so a shared view of the held value
    ///   may be kept in the hold's own region; one `HoldBody` frame waits on
    ///   the scope.
    /// - fails: as [`Self::answers_outside`] for a checked answer that names
    ///   the hold's region; [`CheckRefusal::MachineInvariant`] when `at` is no
    ///   hold.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's hold opens its slot at the integer type
    ///   its value synthesised; a view of a held value kept in its own hold's
    ///   region checks, and a hold checked against a type kept there is
    ///   refused.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_view_kept_in_a_hold_lives_as_long_as_the_hold`
    #[spec(
        captures: [before = self.context.depth(Zone::Linear), regions = self.sessions.regions.len()],
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(Goal::Computation { .. })))
            && self.context.depth(Zone::Linear) > before
            && self.sessions.regions.len() == regions.saturating_add(1)),
    )]
    pub(super) fn held(
        &mut self,
        at: ComputationId,
        direction: Direction<CompTypeId>,
        held: gandr_core_term::ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Memory(MemoryForm::Hold { body, .. }) = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if let Direction::Check(expected) = direction {
            let around = Region::Scoped(self.innermost_region()?);
            self.answers_outside(at, expected, around)?;
        }
        let depth = self.context.depth(Zone::Intuitionistic);
        self.context.binders().open(Zone::Linear, held);
        self.sessions.opened.push(Opened {
            resident: Resident::Held { at },
            depth,
        });
        self.sessions.regions.push(self.sessions.opened.len());
        self.wait(Frame::HoldBody { at, direction });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction,
        }))
    }

    /// Finish a hold whose scope was judged: end the hold's region, drop the
    /// held slot and hand the scope's result on, a synthesised type required
    /// outside the hold's region.
    ///
    /// # Specification
    /// - requires: the scope was judged in `direction`, under the hold's
    ///   region.
    /// - ensures: the hold's region ended, every keep in it released; the held
    ///   slot, live or moved out by a consume, is closed and its entry dropped;
    ///   the hold checked, or synthesised the scope's type.
    /// - fails: as [`Self::answers_outside`] for a synthesised type that names
    ///   the hold's region; [`CheckRefusal::MachineInvariant`] when no region
    ///   is open or the innermost slot is not this hold's.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's hold synthesises its scope's type and
    ///   checks against it; an exclusive access after the hold whose region
    ///   kept a view checks.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_view_kept_in_a_hold_lives_as_long_as_the_hold`
    /// - witness: `judgement::access::tests::a_consume_ends_its_hold_and_answers_the_held_value`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(_))))]
    pub(super) fn dropped(
        &mut self,
        at: ComputationId,
        direction: Direction<CompTypeId>,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        let synthesised = match (direction, produced) {
            (Direction::Check(_), Produced::Checked) => None,
            (Direction::Synthesise, Produced::CompType(ty)) => Some(ty),
            (Direction::Check(_) | Direction::Synthesise, _) => {
                return Err(CheckRefusal::MachineInvariant);
            },
        };
        if let Some(ty) = synthesised {
            let around = u32::from(self.innermost_region()?)
                .checked_sub(1)
                .ok_or(CheckRefusal::MachineInvariant)?;
            self.answers_outside(at, ty, Region::Scoped(RegionDepth::from(around)))?;
        }
        self.close_region()?;
        let innermost = self.resided(node, DeBruijnIndex::from(0_u32))?;
        if innermost.resident != (Resident::Held { at }) {
            return Err(CheckRefusal::MachineInvariant);
        }
        // The hold, not the program, spends its slot: a read copies, and a
        // consume moved the value out without spending the slot.
        if innermost.use_state != LinearUse::Consumed {
            let _held = self
                .context
                .binders()
                .occurrence(Zone::Linear, DeBruijnIndex::from(0_u32))
                .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        }
        self.close_resident()?;
        let Some(ty) = synthesised
        else {
            return Ok(Step::Ascend(Produced::Checked));
        };
        Ok(Step::Ascend(Produced::CompType(ty)))
    }

    /// The held slot `held` an access at `node` lends in `mode`, if its
    /// lending admits the access.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot's residence, unchanged.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::NotHeld`] for a
    ///   slot that holds no value, [`AccessDefect::Consumed`] for a held slot a
    ///   consume has moved out, [`AccessDefect::Lent`] for a slot lent
    ///   exclusively, or lent shared to an exclusive access, and
    ///   [`AccessDefect::Kept`] for a slot a region keeps a shared view of, to
    ///   an exclusive access; [`CheckRefusal::Linearity`] naming
    ///   [`LinearityDefect::Unbound`] for an index past the zone.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an access inside another of the same slot and one of
    ///   a view are refused; two shared accesses nest, and an exclusive one
    ///   inside a shared one is refused, of the whole value and at a place; an
    ///   exclusive access of a slot a live region keeps is refused.
    /// - witness: `judgement::access::tests::a_held_value_lent_or_misnamed_is_refused`
    /// - witness: `judgement::access::tests::a_shared_view_reads_beside_its_held_value_and_ends_with_its_body`
    /// - witness: `judgement::access::tests::a_place_of_a_held_list_is_lent_at_its_index`
    /// - witness: `judgement::access::tests::a_view_kept_in_a_region_lives_as_long_as_its_scope`
    /// - witness: `judgement::access::tests::a_consumed_hold_is_read_lent_or_consumed_no_more`
    #[spec(
        captures: lent = self.sessions.lent.len(),
        ensures: |ret| self.sessions.lent.len() == lent && (ret.is_err() || ret.as_ref().is_ok_and(|found| matches!(found.resident, Resident::Held { .. }))),
    )]
    fn lendable(
        &mut self,
        node: CoreNode,
        held: DeBruijnIndex,
        mode: AccessMode<()>,
    ) -> Result<Resided, CheckRefusal>
    {
        let found = self.resided(node, held)?;
        match found.resident {
            Resident::Held { .. } => {},
            Resident::Endpoint(_)
            | Resident::Received { .. }
            | Resident::Buffer { .. }
            | Resident::View { .. }
            | Resident::Capability { .. }
            | Resident::Continuation { .. } => {
                return Err(CheckRefusal::Access {
                    at: node,
                    defect: AccessDefect::NotHeld,
                });
            },
        }
        if found.use_state != LinearUse::Available {
            return Err(CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Consumed,
            });
        }
        // Shared beside shared is the one lending two accesses of a slot share.
        if self.sessions.lent.iter().any(|lent| {
            lent.position == found.position
                && !matches!((lent.mode, mode), (AccessMode::Shared, AccessMode::Shared))
        }) {
            return Err(CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Lent,
            });
        }
        if matches!(mode, AccessMode::Exclusive { .. })
            && self
                .sessions
                .kept
                .iter()
                .any(|keep| keep.position == found.position)
        {
            return Err(CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Kept,
            });
        }
        Ok(found)
    }

    /// Start the access `at` of the whole held slot `held` in `mode`: lend it
    /// and judge the body with the view bound at the held slot's type.
    ///
    /// # Specification
    /// - requires: `at` is an access of `held` in `mode` with body `body`.
    /// - ensures: as [`Self::lend`], the view at the held slot's type read
    ///   where the access stands.
    /// - fails: as [`Self::lendable`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's two accesses lend it in turn; an access
    ///   inside another of the same slot and one of a view are refused; two
    ///   shared accesses nest, and an exclusive one inside a shared one is
    ///   refused.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_held_value_lent_or_misnamed_is_refused`
    /// - witness: `judgement::access::tests::a_shared_view_reads_beside_its_held_value_and_ends_with_its_body`
    #[spec(
        captures: lent = self.sessions.lent.len(),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(Goal::Computation { .. })))
            && self.sessions.lent.len() > lent),
    )]
    fn access(
        &mut self,
        at: ComputationId,
        held: DeBruijnIndex,
        mode: AccessMode<()>,
        body: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        let found = self.lendable(node, held, mode)?;
        let view = self.here(found.state, found.depth)?;
        self.lend(at, &found, mode, view, body, direction)
    }

    /// Continue the access `at` of a place, its index checked: lend the
    /// place, and a linear index with it, and judge the body with the view
    /// bound at the held list's element type.
    ///
    /// # Specification
    /// - requires: `at` is an access at a place, its index checked against the
    ///   integer type.
    /// - ensures: as [`Self::lend`], the view at the element type of the held
    ///   slot's list type, read where the access stands; an index that is a
    ///   linear variable lent shared beside the held slot.
    /// - fails: as [`Self::lendable`]; [`CheckRefusal::Access`] naming
    ///   [`AccessDefect::Unindexed`] for a held slot whose type is no list;
    ///   [`CheckRefusal::MachineInvariant`] when `at` is no access at a place.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held list read at an index, shared and exclusively,
    ///   views its element; a held integer at an index is refused; a held index
    ///   is lent shared for the body.
    /// - witness: `judgement::access::tests::a_place_of_a_held_list_is_lent_at_its_index`
    #[spec(
        captures: lent = self.sessions.lent.len(),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(Goal::Computation { .. })))
            && self.sessions.lent.len() > lent),
    )]
    pub(super) fn placed(
        &mut self,
        at: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Memory(MemoryForm::Access {
            mode,
            held,
            place: Place::At { index },
            body,
        }) = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let node = CoreNode::Term(TermNode::Computation(at));
        let mode = mode.mode();
        let found = self.lendable(node, held, mode)?;
        let list = self.here(found.state, found.depth)?;
        let head = self.context.whnf_value_type(list)?;
        let element = match value_type_view(self.context.arena(), head)? {
            ValueTypeView::List(element) => element,
            ValueTypeView::Unknown => head,
            ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::PathUniverse { .. }
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Prefix(_)
            | ValueTypeView::Dialogue(_)
            | ValueTypeView::Web
            | ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Character
            | ValueTypeView::Float64
            | ValueTypeView::Fixed(_)
            | ValueTypeView::Unit
            | ValueTypeView::Product(_)
            | ValueTypeView::Sigma { .. }
            | ValueTypeView::Sum(_)
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Kept { .. }
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Session(_)
            | ValueTypeView::World(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Buffer => {
                return Err(CheckRefusal::Access {
                    at: node,
                    defect: AccessDefect::Unindexed,
                });
            },
        };
        // A linear index is lent with the place: readable for the body, and
        // spent by nothing until the access ends.
        if let Some(&Value::Variable {
            zone: Zone::Linear,
            index: slot,
        }) = self.context.arena().value(index)
        {
            let resident = self.resided(node, slot)?;
            self.sessions.lent.push(Lent {
                position: resident.position,
                mode: AccessMode::Shared,
            });
        }
        self.lend(at, &found, mode, element, body, direction)
    }

    /// Lend the held slot `found` to the access `at` in `mode`, and descend
    /// into its body with the view bound at `view`, at the grade its hold
    /// holds the value.
    ///
    /// # Specification
    /// - requires: `found` is the held slot `at` lends, its lending checked.
    /// - ensures: the held slot is lent in `mode`; one linear slot more, the
    ///   view, at `view`; one `AccessBody` frame waits on the body.
    /// - fails: [`CheckRefusal::MachineInvariant`] when `found` is no held
    ///   slot.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::access`] and [`Self::placed`].
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_place_of_a_held_list_is_lent_at_its_index`
    /// - witness: `judgement::access::tests::a_value_held_at_grade_one_is_never_copied`
    #[spec(
        captures: lent = self.sessions.lent.len(),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(Goal::Computation { .. }))) && self.sessions.lent.len() > lent),
    )]
    fn lend(
        &mut self,
        at: ComputationId,
        found: &Resided,
        mode: AccessMode<()>,
        view: ValueTypeId,
        body: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let Resident::Held { at: hold } = found.resident
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let grade = self.hold_grade(hold)?;
        self.sessions.lent.push(Lent {
            position: found.position,
            mode,
        });
        let depth = self.context.depth(Zone::Intuitionistic);
        self.context.binders().open(Zone::Linear, view);
        self.sessions.opened.push(Opened {
            resident: Resident::View {
                at,
                grade,
                held: found.position,
            },
            depth,
        });
        self.wait(Frame::AccessBody { at, direction });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction,
        }))
    }

    /// The grade the hold `hold` holds its value at.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the hold's grade.
    /// - fails: [`CheckRefusal::MachineInvariant`] when `hold` is no hold.
    /// - panics: none.
    /// - executable: none — the clause is the projection the body is.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold at grade one is refused where a hold at grade
    ///   `ω` reads, so a grade read wrongly changes a verdict.
    /// - witness: `judgement::access::tests::a_value_held_at_grade_one_is_never_copied`
    fn hold_grade(
        &self,
        hold: ComputationId,
    ) -> Result<HoldGrade, CheckRefusal>
    {
        let Computation::Memory(MemoryForm::Hold { grade, .. }) = *self.computation(hold)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        Ok(grade)
    }

    /// Refuse a hold at grade one whose value `value` was not made in place.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing changes.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::HeldShared`] at
    ///   `value` unless it is a constructor, a literal, a tuple, an injection,
    ///   a record or a list, or an ascription of one: any other value may have
    ///   another holder.
    /// - panics: none.
    /// - executable: none — the clause is the case analysis the body is.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list made in place enters, and the result of a
    ///   bound computation is refused.
    /// - witness: `judgement::access::tests::a_value_held_at_grade_one_is_never_copied`
    fn entered_in_place(
        &self,
        value: ValueId,
    ) -> Result<(), CheckRefusal>
    {
        let mut made = value;
        while let Some(&Value::Ascribe {
            value: ascribed, ..
        }) = self.context.arena().value(made)
        {
            made = ascribed;
        }
        match self.context.arena().value(made) {
            Some(
                &(Value::Constructor { .. }
                | Value::Literal { .. }
                | Value::Tuple { .. }
                | Value::Injection { .. }
                | Value::Record { .. }
                | Value::ListNil
                | Value::ListCons { .. }),
            ) => Ok(()),
            Some(
                &(Value::Primitive { .. }
                | Value::PathRefl { .. }
                | Value::PathProduct { .. }
                | Value::PathEquiv { .. }
                | Value::Here { .. }
                | Value::Funext { .. }
                | Value::Equiv { .. }
                | Value::Univalence { .. }
                | Value::Ua { .. }
                | Value::SessionRelated { .. }
                | Value::Stay { .. }
                | Value::Then { .. }
                | Value::FlowProduct { .. }
                | Value::Forward { .. }
                | Value::FunctionFlow { .. }
                | Value::Recorded { .. }
                | Value::Dialogue { .. }
                | Value::Web { .. }
                | Value::Returned { .. }
                | Value::Nested { .. }
                | Value::Run { .. }
                | Value::RecordUpdate { .. }
                | Value::Variable { .. }
                | Value::Constant { .. }
                | Value::Thunk { .. }
                | Value::Ascribe { .. }
                | Value::Lift { .. }
                | Value::Quote { .. }
                | Value::QuoteComputation { .. }
                | Value::StaticLambda { .. }
                | Value::StaticApplication { .. }
                | Value::Hole { .. }
                | Value::Mark { .. }
                | Value::Reify { .. }),
            )
            | None => Err(CheckRefusal::Access {
                at: CoreNode::Term(TermNode::Value(value)),
                defect: AccessDefect::HeldShared,
            }),
        }
    }

    /// Continue an access whose body was judged. An exclusive access requires
    /// its view spent, closes it, takes back the held slot, and checks the
    /// unwind against the pure returner of the unit; a shared access spends
    /// its view itself, closes it and takes back the held slot. An access at a
    /// linear index takes the index back too.
    ///
    /// # Specification
    /// - requires: the body was judged.
    /// - ensures: the view's slot is closed and the held slot, and a linear
    ///   index, not lent; for an exclusive access, one `AccessUnwind` frame,
    ///   carrying the body's result, waits on the unwind's check; a shared
    ///   access hands the body's result on.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::Unended`] at an
    ///   exclusive access whose view was neither resumed nor aborted;
    ///   [`CheckRefusal::MachineInvariant`] when the innermost slot is not this
    ///   access's view.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body that leaves its exclusive view live is
    ///   refused, the counter's bodies each end theirs, and a shared view needs
    ///   no eliminator.
    /// - witness: `judgement::access::tests::a_view_left_live_is_refused`
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_shared_view_reads_beside_its_held_value_and_ends_with_its_body`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Computation { .. }) | Step::Ascend(_))))]
    pub(super) fn accessed(
        &mut self,
        at: ComputationId,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Memory(MemoryForm::Access { mode, place, .. }) = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let node = CoreNode::Term(TermNode::Computation(at));
        let innermost = self.resided(node, DeBruijnIndex::from(0_u32))?;
        if !matches!(innermost.resident, Resident::View { at: found, .. } if found == at) {
            return Err(CheckRefusal::MachineInvariant);
        }
        match mode {
            AccessMode::Exclusive { .. } if innermost.use_state != LinearUse::Consumed => {
                return Err(CheckRefusal::Access {
                    at: node,
                    defect: AccessDefect::Unended,
                });
            },
            // The access, not the program, ends a shared view: a read copies.
            AccessMode::Shared if innermost.use_state == LinearUse::Available => {
                let _ended = self
                    .context
                    .binders()
                    .occurrence(Zone::Linear, DeBruijnIndex::from(0_u32))
                    .map_err(|_fault| CheckRefusal::MachineInvariant)?;
            },
            AccessMode::Exclusive { .. } | AccessMode::Shared => {},
        }
        self.close_resident()?;
        let _returned = self
            .sessions
            .lent
            .pop()
            .ok_or(CheckRefusal::MachineInvariant)?;
        if let Place::At { index } = place
            && let Some(&Value::Variable {
                zone: Zone::Linear, ..
            }) = self.context.arena().value(index)
        {
            let _index = self
                .sessions
                .lent
                .pop()
                .ok_or(CheckRefusal::MachineInvariant)?;
        }
        match mode {
            AccessMode::Exclusive { unwind } => {
                let unit = self.unit_returner();
                self.wait(Frame::AccessUnwind { at, produced });
                Ok(Step::Descend(Goal::Computation {
                    term: unwind,
                    direction: Direction::Check(unit),
                }))
            },
            AccessMode::Shared => Ok(Step::Ascend(produced)),
        }
    }

    /// Finish a resume whose value checked: spend its view.
    ///
    /// # Specification
    /// - requires: the resume's value checked against the view's type.
    /// - ensures: the view is spent; the resume synthesises the returner of the
    ///   unit.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::Spent`] when
    ///   the value ended the view first.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's resume spends its view, so a second
    ///   resume is refused.
    /// - witness: `judgement::access::tests::a_view_resumed_twice_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))))]
    pub(super) fn resumed(
        &mut self,
        at: ComputationId,
        view: DeBruijnIndex,
    ) -> Result<Step, CheckRefusal>
    {
        self.spend_view(CoreNode::Term(TermNode::Computation(at)), view)
    }

    /// A read of the linear variable `index` at `term`: a held value's, a
    /// received value's or a view's current value, an endpoint's refusal.
    ///
    /// # Specification
    /// - requires: `term` is the variable `index` of the linear zone.
    /// - ensures: a slot held at grade `ω` and not lent exclusively, a received
    ///   value, and a live view of a slot held at grade `ω`, synthesise their
    ///   declared type, read where the variable stands, and nothing is spent;
    ///   an exclusive view of a value held at grade one synthesises it once and
    ///   its value is moved out.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::Lent`] for a
    ///   held slot lent exclusively, [`AccessDefect::Consumed`] for a held slot
    ///   a consume moved out, [`AccessDefect::Spent`] for a spent view, and
    ///   [`AccessDefect::HeldCopied`] for a slot held at grade one, a shared
    ///   view of one, or an exclusive view of one moved already; as
    ///   [`Self::endpoint_as_value`] for an endpoint;
    ///   [`CheckRefusal::UnboundIndex`] for an index past the zone.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter reads its held value after both accesses
    ///   and its view inside the first; a read of a value lent exclusively is
    ///   refused, and one of a value lent shared reads it; a value held at
    ///   grade one is read once through its exclusive view, and every copy of
    ///   it is refused.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_held_value_lent_or_misnamed_is_refused`
    /// - witness: `judgement::access::tests::a_shared_view_reads_beside_its_held_value_and_ends_with_its_body`
    /// - witness: `judgement::access::tests::a_value_held_at_grade_one_is_never_copied`
    /// - witness: `judgement::access::tests::a_consumed_hold_is_read_lent_or_consumed_no_more`
    /// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
    /// - witness: `judgement::session::tests::a_linear_read_of_nothing_or_of_a_buffer_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::ValueType(_)))))]
    pub(super) fn linear_read(
        &mut self,
        term: ValueId,
        index: DeBruijnIndex,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Value(term));
        let read = match self.resided(node, index) {
            Ok(read) => read,
            Err(CheckRefusal::Linearity {
                defect: LinearityDefect::Unbound { .. },
                ..
            }) => {
                return Err(CheckRefusal::UnboundIndex {
                    at: term,
                    zone: Zone::Linear,
                    index,
                    depth: self.context.depth(Zone::Linear),
                });
            },
            Err(other) => return Err(other),
        };
        let defect = match read.resident {
            Resident::Endpoint(_) => return self.endpoint_as_value(term, index),
            Resident::Buffer { at } => {
                return Err(CheckRefusal::Linearity {
                    at: node,
                    defect: LinearityDefect::BufferRead { site: at },
                });
            },
            Resident::Capability { .. } | Resident::Continuation { .. } => AccessDefect::NotHeld,
            Resident::Held { .. }
                if self.sessions.lent.iter().any(|lent| {
                    lent.position == read.position
                        && matches!(lent.mode, AccessMode::Exclusive { .. })
                }) =>
            {
                AccessDefect::Lent
            },
            Resident::View { .. } if read.use_state == LinearUse::Consumed => AccessDefect::Spent,
            Resident::Held { .. } if read.use_state != LinearUse::Available => {
                AccessDefect::Consumed
            },
            Resident::Held { at } => match self.hold_grade(at)? {
                HoldGrade::Many => return self.read_type(&read),
                HoldGrade::One => AccessDefect::HeldCopied,
            },
            Resident::Received { .. }
            | Resident::View {
                grade: HoldGrade::Many,
                ..
            } => return self.read_type(&read),
            Resident::View {
                at,
                grade: HoldGrade::One,
                ..
            } => {
                let Computation::Memory(MemoryForm::Access { mode, .. }) = *self.computation(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                match (mode, read.use_state) {
                    (AccessMode::Exclusive { .. }, LinearUse::Available) => {
                        let _moved = self
                            .context
                            .binders()
                            .move_out(index)
                            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
                        return self.read_type(&read);
                    },
                    (AccessMode::Exclusive { .. }, LinearUse::Moved | LinearUse::Consumed)
                    | (AccessMode::Shared, _) => AccessDefect::HeldCopied,
                }
            },
        };
        Err(CheckRefusal::Access { at: node, defect })
    }

    /// The declared type of the slot `read`, read where the variable stands.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot's declared type, shifted to the current depth.
    /// - fails: as [`Self::here`].
    /// - panics: none.
    /// - executable: none — the clause is the shift the body is.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter reads its held slot and a view, each at
    ///   the integer type where it stands; a read typed at another depth
    ///   mismatches.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_value_held_at_grade_one_is_never_copied`
    fn read_type(
        &mut self,
        read: &Resided,
    ) -> Result<Step, CheckRefusal>
    {
        let ty = self.here(read.state, read.depth)?;
        Ok(Step::Ascend(Produced::ValueType(ty.into())))
    }

    /// The access refusal an effect-row mismatch inside an unwind is: the
    /// computation whose row exceeded the empty one the unwind runs under.
    ///
    /// # Specification
    /// - requires: `refusal` is the refusal of the step `control` names.
    /// - ensures: a computation mismatch whose synthesised row is not within
    ///   its expected one, met where every frame between the step and the
    ///   nearest `AccessUnwind` only carries the unwind's own expected type — a
    ///   bind's or a bridge's — is [`CheckRefusal::Access`] naming
    ///   [`AccessDefect::UnwindEffect`] at the mismatched computation; every
    ///   other refusal is returned unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unwind exercising an operation directly and after
    ///   a bind is renamed; a pure unwind whose value mismatches is not.
    /// - witness: `judgement::access::tests::an_abort_clause_performing_an_effect_is_refused`
    #[spec(ensures: |ret| ret == refusal || matches!((refusal, ret),
        (CheckRefusal::TypeMismatch(Mismatch::Computation { at, .. }),
            CheckRefusal::Access { at: CoreNode::Term(TermNode::Computation(named)), defect: AccessDefect::UnwindEffect }) if at == named))]
    pub(super) fn unwinding(
        &mut self,
        refusal: CheckRefusal,
        control: Control,
    ) -> CheckRefusal
    {
        let CheckRefusal::TypeMismatch(Mismatch::Computation {
            at,
            synthesised,
            expected,
        }) = refusal
        else {
            return refusal;
        };
        let resumed = match control {
            Control::Resuming(waiting) => Some(waiting.frame),
            Control::Starting(_) | Control::Handing => None,
        };
        if !matches!(self.carrier(resumed), Some(Frame::AccessUnwind { .. })) {
            return refusal;
        }
        match self.exceeds(synthesised, expected) {
            Ok(RowInclusion::Excluded) => CheckRefusal::Access {
                at: CoreNode::Term(TermNode::Computation(at)),
                defect: AccessDefect::UnwindEffect,
            },
            Ok(RowInclusion::Included) | Err(_) => refusal,
        }
    }

    /// The innermost frame waiting on the step, `resumed` first, past the
    /// binds and bridges that only carry the step's expected type.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn carrier(
        &self,
        resumed: Option<Frame>,
    ) -> Option<Frame>
    {
        resumed
            .into_iter()
            .chain(self.frames.iter().rev().map(|waiting| waiting.frame))
            .find(|frame| {
                !matches!(
                    frame,
                    Frame::BindBound { .. } | Frame::BindBody { .. } | Frame::CompBridge { .. }
                )
            })
    }

    /// Whether the row of the returner `synthesised` lies within the row of
    /// the returner `expected`.
    ///
    /// # Specification
    /// - requires: both types are formed.
    /// - ensures: [`RowInclusion::Excluded`] exactly when both are returners at
    ///   their weak heads and the first row names an interface the second does
    ///   not grant; [`RowInclusion::Included`] otherwise.
    /// - fails: the weak-head reading's refusal.
    /// - panics: none.
    /// - executable: none — the clause is the weak-head reading the body
    ///   performs against the mutable context; a predicate would rerun it.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an effectful returner against the pure one is
    ///   excluded, and two pure returners of different results are included.
    /// - witness: `judgement::access::tests::an_abort_clause_performing_an_effect_is_refused`
    fn exceeds(
        &mut self,
        synthesised: CompTypeId,
        expected: CompTypeId,
    ) -> Result<RowInclusion, CheckRefusal>
    {
        let found = self.context.whnf_comp_type(synthesised)?;
        let wanted = self.context.whnf_comp_type(expected)?;
        let arena = self.context.arena();
        let (
            CompTypeView::Returner { effects: found, .. },
            CompTypeView::Returner {
                effects: wanted, ..
            },
        ) = (
            comp_type_view(arena, found)?,
            comp_type_view(arena, wanted)?,
        )
        else {
            return Ok(RowInclusion::Included);
        };
        Ok(found.is_subset(wanted, arena))
    }

    /// The live view `index` names, read at `node` by an eliminator.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the view's slot, available or its value moved out, its access
    ///   exclusive.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::NotAView`] for
    ///   a slot no access bound, [`AccessDefect::Spent`] for a spent view and
    ///   [`AccessDefect::ReadOnly`] for a shared view; as [`Self::resided`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an eliminator of a held value, one after a resume and
    ///   one of a shared view are refused by name.
    /// - witness: `judgement::access::tests::a_view_resumed_twice_is_refused`
    /// - witness: `judgement::access::tests::a_held_value_lent_or_misnamed_is_refused`
    /// - witness: `judgement::access::tests::a_shared_view_reads_beside_its_held_value_and_ends_with_its_body`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|read| read.use_state != LinearUse::Consumed))]
    fn live_view(
        &mut self,
        node: CoreNode,
        index: DeBruijnIndex,
    ) -> Result<Resided, CheckRefusal>
    {
        let read = self.resided(node, index)?;
        let defect = match (read.resident, read.use_state) {
            (Resident::View { at, .. }, LinearUse::Available | LinearUse::Moved) => {
                let Computation::Memory(MemoryForm::Access { mode, .. }) = *self.computation(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                match mode {
                    AccessMode::Exclusive { .. } => return Ok(read),
                    AccessMode::Shared => AccessDefect::ReadOnly,
                }
            },
            (Resident::View { .. }, LinearUse::Consumed) => AccessDefect::Spent,
            (
                Resident::Endpoint(_)
                | Resident::Received { .. }
                | Resident::Buffer { .. }
                | Resident::Held { .. }
                | Resident::Capability { .. }
                | Resident::Continuation { .. },
                _,
            ) => AccessDefect::NotAView,
        };
        Err(CheckRefusal::Access { at: node, defect })
    }

    /// Spend the view `index`, read at `node`, and synthesise the returner of
    /// the unit.
    ///
    /// # Specification
    /// - requires: `index` names a view.
    /// - ensures: the view is spent.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::Spent`] for a
    ///   spent view.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an abort spends its view, so a later read is refused.
    /// - witness: `judgement::access::tests::a_view_resumed_twice_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))))]
    fn spend_view(
        &mut self,
        node: CoreNode,
        index: DeBruijnIndex,
    ) -> Result<Step, CheckRefusal>
    {
        match self.context.binders().occurrence(Zone::Linear, index) {
            Ok(_) => Ok(Step::Ascend(Produced::CompType(self.unit_returner()))),
            Err(_) => Err(CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Spent,
            }),
        }
    }

    /// Close the innermost linear slot and drop its entry.
    ///
    /// # Specification
    /// - requires: the innermost linear slot is the run's and spent.
    /// - ensures: one linear slot fewer, one entry fewer.
    /// - fails: [`CheckRefusal::MachineInvariant`] when the slot cannot close.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's hold and accesses each close their own
    ///   slot, leaving the zone as the run found it.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    #[spec(
        captures: before = self.context.depth(Zone::Linear),
        ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Linear)).checked_add(1) == Some(usize::from(before)),
    )]
    fn close_resident(&mut self) -> Result<(), CheckRefusal>
    {
        let _declared = self
            .context
            .binders()
            .close(Zone::Linear)
            .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        let _opened = self
            .sessions
            .opened
            .pop()
            .ok_or(CheckRefusal::MachineInvariant)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests;
