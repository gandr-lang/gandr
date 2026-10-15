//! The access rules on the judgement's machine: the hold that binds a held
//! value, the access that lends it to a view, the two eliminators that end
//! the view, a read of either resident, and the naming of an unwind's
//! effect. The decisions are stated in [`crate::access`].

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::LinearUse;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::effect::Purity;
use gandr_core_term::effect::RowInclusion;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::DeBruijnIndex;

use super::Control;
use super::Direction;
use super::Frame;
use super::Goal;
use super::Machine;
use super::Produced;
use super::Step;
use super::session::Opened;
use super::session::Resided;
use super::session::Resident;
use crate::access::AccessDefect;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::Mismatch;
use crate::refusal::TermNode;
use crate::session::Capture;
use crate::session::LinearityDefect;
use crate::view::CompTypeView;
use crate::view::comp_type_view;

impl Machine<'_, '_>
{
    /// The rules of the memory forms: a hold synthesises its value, an
    /// access lends its held slot, a resume checks its value, an abort ends
    /// its view at once.
    ///
    /// # Specification
    /// - requires: `term` is a memory form.
    /// - ensures: a hold standing at a pure returner waits on its value's
    ///   synthesis; an access opens its view at the held slot's type and waits
    ///   on its body in `direction`; a resume waits on its value's check
    ///   against the view's type; an abort spends its view and synthesises the
    ///   returner of the unit.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::HeldCaptured`]
    ///   for a hold at an impure type, [`AccessDefect::NotHeld`] for an access
    ///   of a slot that holds no value, [`AccessDefect::Lent`] for an access of
    ///   a lent one, [`AccessDefect::NotAView`] for an eliminator of a slot
    ///   that is no view and [`AccessDefect::Spent`] for one of a spent view;
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
            MemoryForm::Hold { value, .. } => {
                if let Direction::Check(expected) = direction {
                    self.pure_hold(term, expected)?;
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
            MemoryForm::Access { held, body, .. } => self.access(term, held, body, direction),
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
                let _lent = self.live_view(node, view)?;
                self.spend_view(node, view)
            },
        }
    }

    /// Refuse a hold that stands at `ty` unless `ty` is a pure returner or the
    /// unknown type.
    ///
    /// # Specification
    /// - requires: `ty` is formed.
    /// - ensures: nothing changes.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::HeldCaptured`]
    ///   by [`Capture::Continuation`] at the hold: an operation in its scope
    ///   could be resumed twice by a handler, running its accesses twice.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold checked against an effectful returner is
    ///   refused while the same hold against the pure one checks.
    /// - witness: `judgement::access::tests::a_held_value_lent_or_misnamed_is_refused`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::Access { at: refused, defect }) => {
            refused == CoreNode::Term(TermNode::Computation(at))
                && defect == AccessDefect::HeldCaptured { by: Capture::Continuation }
        },
        | _ => true,
    })]
    fn pure_hold(
        &mut self,
        at: ComputationId,
        ty: CompTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let head = self.context.whnf_comp_type(ty)?;
        let pure = match comp_type_view(self.context.arena(), head)? {
            CompTypeView::Returner { effects, .. } => effects.purity() == Purity::Pure,
            CompTypeView::Unknown => true,
            CompTypeView::With(..)
            | CompTypeView::Arrow { .. }
            | CompTypeView::Pi { .. }
            | CompTypeView::Element { .. } => false,
        };
        if pure {
            return Ok(());
        }
        Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Computation(at)),
            defect: AccessDefect::HeldCaptured {
                by: Capture::Continuation,
            },
        })
    }

    /// Continue a hold whose value synthesised `held`: open the held slot at
    /// `held` and judge the scope in the hold's direction.
    ///
    /// # Specification
    /// - requires: the hold's value synthesised `held`.
    /// - ensures: one linear slot more, at `held`, held by `at`; one `HoldBody`
    ///   frame waits on the scope.
    /// - fails: [`CheckRefusal::MachineInvariant`] when `at` is no hold.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's hold opens its slot at the integer type
    ///   its value synthesised.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    #[spec(
        captures: before = self.context.depth(Zone::Linear),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(Goal::Computation { .. })))
            && self.context.depth(Zone::Linear) > before),
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
        let depth = self.context.depth(Zone::Intuitionistic);
        self.context.binders().open(Zone::Linear, held);
        self.sessions.opened.push(Opened {
            resident: Resident::Held { at },
            depth,
        });
        self.wait(Frame::HoldBody { at, direction });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction,
        }))
    }

    /// Finish a hold whose scope was judged: drop the held slot and hand the
    /// scope's result on, a synthesised type required pure.
    ///
    /// # Specification
    /// - requires: the scope was judged in `direction`.
    /// - ensures: the held slot is closed and its entry dropped; the hold
    ///   checked, or synthesised the scope's type.
    /// - fails: as [`Self::pure_hold`] for a synthesised type;
    ///   [`CheckRefusal::MachineInvariant`] when the innermost slot is not this
    ///   hold's.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's hold synthesises its scope's type and
    ///   checks against it.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(_))))]
    pub(super) fn dropped(
        &mut self,
        at: ComputationId,
        direction: Direction<CompTypeId>,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        let innermost = self.resided(node, DeBruijnIndex::from(0_u32))?;
        if innermost.resident != (Resident::Held { at }) {
            return Err(CheckRefusal::MachineInvariant);
        }
        // The hold, not the program, spends its slot: a read copies.
        if innermost.use_state == LinearUse::Available {
            let _held = self
                .context
                .binders()
                .occurrence(Zone::Linear, DeBruijnIndex::from(0_u32))
                .map_err(|_fault| CheckRefusal::MachineInvariant)?;
        }
        self.close_resident()?;
        match (direction, produced) {
            (Direction::Check(_), Produced::Checked) => Ok(Step::Ascend(Produced::Checked)),
            (Direction::Synthesise, Produced::CompType(ty)) => {
                self.pure_hold(at, ty)?;
                Ok(Step::Ascend(Produced::CompType(ty)))
            },
            (Direction::Check(_) | Direction::Synthesise, _) => Err(CheckRefusal::MachineInvariant),
        }
    }

    /// Start the access `at` of the held slot `held`: lend it and judge the
    /// body with the view bound at the held slot's type.
    ///
    /// # Specification
    /// - requires: `at` is an access of `held` with body `body`.
    /// - ensures: the held slot is lent; one linear slot more, the view, at the
    ///   held slot's type read where the access stands; one `AccessBody` frame
    ///   waits on the body.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::NotHeld`] for a
    ///   slot that holds no value and [`AccessDefect::Lent`] for a lent one;
    ///   [`CheckRefusal::Linearity`] naming [`LinearityDefect::Unbound`] for an
    ///   index past the zone.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's two accesses lend it in turn; an access
    ///   inside another of the same slot and one of a view are refused.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_held_value_lent_or_misnamed_is_refused`
    #[spec(
        captures: lent = self.sessions.lent.len(),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(Goal::Computation { .. })))
            && self.sessions.lent.len() > lent),
    )]
    fn access(
        &mut self,
        at: ComputationId,
        held: DeBruijnIndex,
        body: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        let found = self.resided(node, held)?;
        match found.resident {
            Resident::Held { .. } => {},
            Resident::Endpoint(_) | Resident::View { .. } => {
                return Err(CheckRefusal::Access {
                    at: node,
                    defect: AccessDefect::NotHeld,
                });
            },
        }
        if self.sessions.lent.contains(&found.position) {
            return Err(CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Lent,
            });
        }
        let view = self.here(found.state, found.depth)?;
        self.sessions.lent.push(found.position);
        let depth = self.context.depth(Zone::Intuitionistic);
        self.context.binders().open(Zone::Linear, view);
        self.sessions.opened.push(Opened {
            resident: Resident::View { at },
            depth,
        });
        self.wait(Frame::AccessBody { at, direction });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction,
        }))
    }

    /// Continue an access whose body was judged: require the view spent,
    /// close it, take back the held slot, and check the unwind against the
    /// pure returner of the unit.
    ///
    /// # Specification
    /// - requires: the body was judged.
    /// - ensures: the view's slot is closed and the held slot no longer lent;
    ///   one `AccessUnwind` frame, carrying the body's result, waits on the
    ///   unwind's check.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::Unended`] at
    ///   the access for a view neither resumed nor aborted;
    ///   [`CheckRefusal::MachineInvariant`] when the innermost slot is not this
    ///   access's view.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body that leaves its view live is refused, and the
    ///   counter's bodies each end theirs.
    /// - witness: `judgement::access::tests::a_view_left_live_is_refused`
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Computation { .. }))))]
    pub(super) fn accessed(
        &mut self,
        at: ComputationId,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Memory(MemoryForm::Access { unwind, .. }) = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let node = CoreNode::Term(TermNode::Computation(at));
        let innermost = self.resided(node, DeBruijnIndex::from(0_u32))?;
        if innermost.resident != (Resident::View { at }) {
            return Err(CheckRefusal::MachineInvariant);
        }
        if innermost.use_state == LinearUse::Available {
            return Err(CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Unended,
            });
        }
        self.close_resident()?;
        let _returned = self
            .sessions
            .lent
            .pop()
            .ok_or(CheckRefusal::MachineInvariant)?;
        let unit = self.unit_returner();
        self.wait(Frame::AccessUnwind { at, produced });
        Ok(Step::Descend(Goal::Computation {
            term: unwind,
            direction: Direction::Check(unit),
        }))
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

    /// A read of the linear variable `index` at `term`: a held value's or a
    /// view's current value, an endpoint's refusal.
    ///
    /// # Specification
    /// - requires: `term` is the variable `index` of the linear zone.
    /// - ensures: a held slot not lent and a live view synthesise their
    ///   declared type, read where the variable stands; nothing is spent.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::Lent`] for a
    ///   lent held slot and [`AccessDefect::Spent`] for a spent view; as
    ///   [`Self::endpoint_as_value`] for an endpoint;
    ///   [`CheckRefusal::UnboundIndex`] for an index past the zone.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter reads its held value after both accesses
    ///   and its view inside the first; a read of a lent value is refused.
    /// - witness: `judgement::access::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    /// - witness: `judgement::access::tests::a_held_value_lent_or_misnamed_is_refused`
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
            Resident::Held { .. } if self.sessions.lent.contains(&read.position) => {
                AccessDefect::Lent
            },
            Resident::View { .. } if read.use_state == LinearUse::Consumed => AccessDefect::Spent,
            Resident::Held { .. } | Resident::View { .. } => {
                let ty = self.here(read.state, read.depth)?;
                return Ok(Step::Ascend(Produced::ValueType(ty)));
            },
        };
        Err(CheckRefusal::Access { at: node, defect })
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
        let innermost = resumed
            .into_iter()
            .chain(self.frames.iter().rev().map(|waiting| waiting.frame))
            .find(|frame| {
                !matches!(
                    frame,
                    Frame::BindBound { .. } | Frame::BindBody { .. } | Frame::CompBridge { .. }
                )
            });
        if !matches!(innermost, Some(Frame::AccessUnwind { .. })) {
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

    /// The live view `index` names, read at `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the view's slot, still available.
    /// - fails: [`CheckRefusal::Access`] naming [`AccessDefect::NotAView`] for
    ///   a slot no access bound and [`AccessDefect::Spent`] for a spent view;
    ///   as [`Self::resided`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an eliminator of a held value and one after a resume
    ///   are refused by name.
    /// - witness: `judgement::access::tests::a_view_resumed_twice_is_refused`
    /// - witness: `judgement::access::tests::a_held_value_lent_or_misnamed_is_refused`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|read| read.use_state == LinearUse::Available))]
    fn live_view(
        &mut self,
        node: CoreNode,
        index: DeBruijnIndex,
    ) -> Result<Resided, CheckRefusal>
    {
        let read = self.resided(node, index)?;
        let defect = match (read.resident, read.use_state) {
            (Resident::View { .. }, LinearUse::Available) => return Ok(read),
            (Resident::View { .. }, LinearUse::Consumed) => AccessDefect::Spent,
            (Resident::Endpoint(_) | Resident::Held { .. }, _) => AccessDefect::NotAView,
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
