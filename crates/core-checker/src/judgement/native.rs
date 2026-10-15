//! Native variable-arity judgments on the explicit frame machine.
//!
//! Records infer exact label sets. Checking admits width and recursive depth
//! subtyping: every expected field must exist and its value must check at the
//! expected classifier. Projection returns the named field's type. Equality
//! stays exact in its labels; assignability is directional. The empty record
//! is the record top, not a top for arbitrary values.

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::SplitMotive;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::instantiate_comp_type;
use gandr_core_term::shift_comp_type_under;
use gandr_kernel_term::Apartness;
use gandr_kernel_term::Component;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Direction;
use super::Frame;
use super::Goal;
use super::Machine;
use super::Produced;
use super::Step;
use super::Waiting;
use crate::CheckRefusal;
use crate::ExpectedShape;
use crate::TermNode;
use crate::TypeNode;
use crate::former;
use crate::respect::Reading;
use crate::respect::obligation;
use crate::respect::root;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

impl Machine<'_, '_>
{
    /// Queue a nominal constructor's formation and field checks.
    ///
    /// # Specification
    /// - requires: `term` is a constructor node.
    /// - ensures: the annotation forms before the declaration-ordered field
    ///   checks; their success synthesizes that same nominal annotation.
    /// - fails: wrong nominal shape, unknown tag, or wrong field arity.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] names the failed constructor premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct heads, arities, tags and field types
    ///   separate the nominal introduction rule.
    /// - witness: `native_formers::native_formers::data_declarations_and_refusals_agree_with_kernel`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Form(TypeNode::Value(_))))))]
    pub(super) fn native_constructor(
        &mut self,
        term: ValueId,
    ) -> Result<Step, CheckRefusal>
    {
        let (datatype, tag, count) = match self.value(term)? {
            &Value::Constructor {
                ref datatype,
                ref tag,
                ref fields,
            } => (*datatype, *tag, fields.len()),
            &Value::Primitive { .. }
            | &Value::PathRefl(_)
            | &Value::PathProduct(..)
            | &Value::PathEquiv { .. }
            | &Value::Here(_)
            | &Value::Funext(..)
            | &Value::Equiv(..)
            | &Value::Ua { .. }
            | &Value::SessionRelated { .. }
            | &Value::Stay(_)
            | &Value::Then(..)
            | &Value::FlowProduct(..)
            | &Value::Forward(_)
            | &Value::FunctionFlow(..)
            | &Value::Recorded(_)
            | &Value::Returned(_)
            | &Value::Nested(_)
            | &Value::Run(_)
            | &Value::Variable { .. }
            | &Value::Constant(_)
            | &Value::Literal(_)
            | &Value::Tuple(_)
            | &Value::Injection(..)
            | &Value::ListNil
            | &Value::ListCons(..)
            | &Value::Thunk(_)
            | &Value::Lift { .. }
            | &Value::Quote(_)
            | &Value::QuoteComputation(_)
            | &Value::StaticLambda(_)
            | &Value::StaticApplication(..)
            | &Value::Record(_)
            | &Value::Hole(_)
            | &Value::Mark { .. }
            | &Value::Reify(_) => return Err(CheckRefusal::MachineInvariant),
        };
        if !matches!(
            self.context.arena().value_type(datatype),
            Some(ValueType::Data { .. })
        ) {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(term),
                wanted: ExpectedShape::Data,
                found: TypeNode::Value(datatype),
            });
        }
        let signature = former::signature(self.context, datatype)?;
        let declared = signature
            .constructors()
            .get(usize::from(tag))
            .ok_or(CheckRefusal::UnknownConstructor { at: term, tag })?;
        if declared.len() != count {
            return Err(CheckRefusal::ConstructorArity(term));
        }
        self.wait(Frame::NativeYield(Produced::ValueType(datatype)));
        for (index, &field_type) in declared.iter().enumerate().rev() {
            let expected = former::instantiate(
                self.context,
                datatype,
                field_type,
                gandr_core_term::BinderDepth::from(signature.parameters().len()),
            )?;
            let field = match self.value(term)? {
                &Value::Constructor { ref fields, .. } => fields
                    .get(index)
                    .copied()
                    .ok_or(CheckRefusal::MachineInvariant)?,
                &Value::Primitive { .. }
                | &Value::PathRefl(_)
                | &Value::PathProduct(..)
                | &Value::PathEquiv { .. }
                | &Value::Here(_)
                | &Value::Funext(..)
                | &Value::Equiv(..)
                | &Value::Ua { .. }
                | &Value::SessionRelated { .. }
                | &Value::Stay(_)
                | &Value::Then(..)
                | &Value::FlowProduct(..)
                | &Value::Forward(_)
                | &Value::FunctionFlow(..)
                | &Value::Recorded(_)
                | &Value::Returned(_)
                | &Value::Nested(_)
                | &Value::Run(_)
                | &Value::Variable { .. }
                | &Value::Constant(_)
                | &Value::Literal(_)
                | &Value::Tuple(_)
                | &Value::Injection(..)
                | &Value::ListNil
                | &Value::ListCons(..)
                | &Value::Thunk(_)
                | &Value::Lift { .. }
                | &Value::Quote(_)
                | &Value::QuoteComputation(_)
                | &Value::StaticLambda(_)
                | &Value::StaticApplication(..)
                | &Value::Record(_)
                | &Value::Hole(_)
                | &Value::Mark { .. }
                | &Value::Reify(_) => return Err(CheckRefusal::MachineInvariant),
            };
            self.wait(Frame::NativeNext(Goal::Value {
                term: field,
                direction: Direction::Check(expected),
            }));
        }
        Ok(Step::Descend(Goal::Form(TypeNode::Value(datatype))))
    }

    /// Check a nominal constructor at a stage: its recursive fields one step
    /// below the stage, its other fields at their declared types.
    ///
    /// # Specification
    /// - requires: `term` is a constructor and `owed` what the stage it is
    ///   checked at owes ([`crate::recursion::constructor_owes`]).
    /// - ensures: the annotation forms before the declaration-ordered field
    ///   checks; a recursive field checks at `owed.fields`, any other at its
    ///   declared type; the constructor checks once they have.
    /// - fails: [`CheckRefusal::TypeMismatch`] for an annotation that does not
    ///   convert with the type the stage refines;
    ///   [`CheckRefusal::StageNotBelow`] for a constructor with no recursive
    ///   field where no hypothesis shows the wanted stage above the first
    ///   ([`crate::recursion::room`]); otherwise as
    ///   [`Self::native_constructor`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] names the failed premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a successor rebuilt two cases deep is admitted at the
    ///   bound, one rebuilt one case deep is refused, and a zero is admitted
    ///   under a successor's field and refused under the zero arm.
    /// - witness: `recursion::tests::a_call_on_a_value_rebuilt_below_the_stage_is_admitted`
    /// - witness: `recursion::tests::a_nullary_argument_needs_a_value_below_the_stage`
    /// - witness: `recursion::tests::a_constructor_of_plain_fields_needs_a_value_below_the_stage`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Form(TypeNode::Value(_))))))]
    pub(super) fn staged_constructor(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
        owed: crate::recursion::Owed,
    ) -> Result<Step, CheckRefusal>
    {
        let &Value::Constructor {
            datatype,
            tag,
            ref fields,
        } = self.value(term)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let count = fields.len();
        if crate::conversion::equivalent(self.context, datatype, owed.base)?
            != crate::conversion::Agreement::Convertible
        {
            return Err(CheckRefusal::TypeMismatch(
                crate::refusal::Mismatch::Value {
                    at: term,
                    synthesised: datatype,
                    expected,
                },
            ));
        }
        let signature = former::signature(self.context, datatype)?;
        let declared = signature
            .constructors()
            .get(usize::from(tag))
            .ok_or(CheckRefusal::UnknownConstructor { at: term, tag })?;
        if declared.len() != count {
            return Err(CheckRefusal::ConstructorArity(term));
        }
        self.wait(Frame::NativeYield(Produced::Checked));
        let mut recursive = 0_usize;
        for (index, &field_type) in declared.iter().enumerate().rev() {
            let declared_type = former::instantiate(
                self.context,
                datatype,
                field_type,
                gandr_core_term::BinderDepth::from(signature.parameters().len()),
            )?;
            let wanted =
                crate::recursion::stage_field(self.context, declared_type, datatype, owed.fields)?;
            if wanted != declared_type {
                // A recursive field stands one step below: the constructor is
                // above it whatever stage the field is at.
                recursive = recursive.saturating_add(1);
            }
            let &Value::Constructor { ref fields, .. } = self.value(term)?
            else {
                return Err(CheckRefusal::MachineInvariant);
            };
            let field = fields
                .get(index)
                .copied()
                .ok_or(CheckRefusal::MachineInvariant)?;
            self.wait(Frame::NativeNext(Goal::Value {
                term: field,
                direction: Direction::Check(wanted),
            }));
        }
        if recursive == 0
            && crate::recursion::room(self.context, owed.wanted)?
                == crate::recursion::Room::Unwitnessed
        {
            return Err(CheckRefusal::StageNotBelow {
                at: term,
                found: gandr_kernel_term::Standing::Top,
                bound: owed.wanted,
            });
        }
        Ok(Step::Descend(Goal::Form(TypeNode::Value(datatype))))
    }

    /// Queue each genuine parameter argument at its instantiated classifier.
    ///
    /// # Specification
    /// - requires: `datatype` is a Data application.
    /// - ensures: every supplied argument checks against its telescope entry.
    /// - fails: absent declaration, wrong arity or malformed internal nodes.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] identifies the failed formation premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dependent arguments separate first-order indices from
    ///   type atoms and expose capture in simultaneous substitution.
    /// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
    #[spec(ensures: |ret| ret.is_err() || ret == Ok(Step::Ascend(Produced::Checked)))]
    pub(super) fn native_data(
        &mut self,
        datatype: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let signature = former::signature(self.context, datatype)?;
        for (index, &parameter) in signature.parameters().iter().enumerate().rev() {
            let expected = former::instantiate(
                self.context,
                datatype,
                parameter,
                gandr_core_term::BinderDepth::from(index),
            )?;
            let argument = match self.context.arena().value_type(datatype) {
                Some(&ValueType::Data { ref arguments, .. }) => arguments
                    .get(index)
                    .copied()
                    .ok_or(CheckRefusal::MachineInvariant)?,
                _ => return Err(CheckRefusal::MachineInvariant),
            };
            self.wait(Frame::NativeNext(Goal::Value {
                term: argument,
                direction: Direction::Check(expected),
            }));
        }
        Ok(Step::Ascend(Produced::Checked))
    }

    /// Synthesize all record field types without making the host stack
    /// recursive.
    ///
    /// # Specification
    /// - requires: `term` is a record literal.
    /// - ensures: starts the first field synthesis, or produces the empty
    ///   record classifier; its continuation pairs exact labels with field
    ///   types in label order, using disjoint result-stack suffixes.
    /// - fails: a malformed internal node or any field's synthesis refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal::MachineInvariant`] for a non-record internal node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested records with unequal fields separate ordering
    ///   and result-stack ownership.
    /// - witness: `native_formers::native_formers::record_width_depth_and_projection`
    #[spec(ensures: |ret| matches!(ret,
        Ok(Step::Descend(Goal::Value { direction: Direction::Synthesise, .. })
            | Step::Ascend(Produced::ValueType(_))) | Err(_)))]
    pub(super) fn native_record(
        &mut self,
        term: ValueId,
    ) -> Result<Step, CheckRefusal>
    {
        let Some(matched_native_node) = self.context.arena().value(term)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Value::Record(ref fields) = *matched_native_node
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let owner = self.owner;
        self.frames.push(Waiting {
            frame: Frame::NativeRecord {
                term,
                base: self.native_types.len(),
            },
            owner,
        });
        for &field in fields.values().rev() {
            self.frames.push(Waiting {
                frame: Frame::NativeCollect,
                owner,
            });
            self.frames.push(Waiting {
                frame: Frame::NativeNext(Goal::Value {
                    term: field,
                    direction: Direction::Synthesise,
                }),
                owner,
            });
        }
        let first = self.frames.pop().ok_or(CheckRefusal::MachineInvariant)?;
        self.resume(first.frame, Produced::Checked)
    }

    /// Check a record literal fieldwise, permitting width and recursive depth.
    ///
    /// Extra fields must still synthesize; a missing required label refuses.
    ///
    /// # Specification
    /// - requires: `term` is a record and `expected` is formed.
    /// - ensures: each required field checks at its declared type, and every
    ///   additional field has a type rather than escaping judgment.
    /// - fails: wrong expected shape or a missing field, then field refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] identifies the failed structural premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — width in both directions, nested depth and a field of
    ///   the wrong type separate record checking from mere label inclusion.
    /// - witness: `native_formers::native_formers::record_width_depth_and_projection`
    #[spec(ensures: |ret| ret.is_err() || ret == Ok(Step::Ascend(Produced::Checked)))]
    pub(super) fn check_native_record(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        let Some(matched_native_node) = self.context.arena().value_type(head)
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(term),
                wanted: ExpectedShape::Record,
                found: TypeNode::Value(expected),
            });
        };
        let ValueType::Record(ref wanted) = *matched_native_node
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(term),
                wanted: ExpectedShape::Record,
                found: TypeNode::Value(expected),
            });
        };
        let Some(matched_native_node) = self.context.arena().value(term)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Value::Record(ref fields) = *matched_native_node
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if !wanted.keys().all(|label| fields.contains_key(label)) {
            return Err(CheckRefusal::MissingRecordField { at: term, expected });
        }
        let owner = self.owner;
        for (label, &field) in fields.iter().rev() {
            let direction = if let Some(&expected) = wanted.get(label) {
                Direction::Check(expected)
            }
            else {
                self.frames.push(Waiting {
                    frame: Frame::NativeDiscard,
                    owner,
                });
                Direction::Synthesise
            };
            self.frames.push(Waiting {
                frame: Frame::NativeNext(Goal::Value {
                    term: field,
                    direction,
                }),
                owner,
            });
        }
        Ok(Step::Ascend(Produced::Checked))
    }

    /// Form a case's motive under exactly one scrutinee binder.
    ///
    /// # Specification
    /// - requires: `term` is a case whose scrutinee synthesized `datatype`.
    /// - ensures: exhaustive coverage before motive checking; branches remain
    ///   ordinary ambient functions and are not given implicit field binders. A
    ///   scrutinee at a stage is read as the type the stage refines, and the
    ///   case opens one stage below it for its recursive fields
    ///   ([`crate::recursion::open_case`]). The root a structural fixpoint
    ///   marked is taken whichever case this is; over a presented type with
    ///   rules the case is read as that fixpoint when it is the marked case,
    ///   and as itself otherwise.
    /// - fails: non-data scrutinee, wrong coverage or absent declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] identifies the failed elimination premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, missing and surplus branches distinguish exact
    ///   coverage; a dependent motive distinguishes its binder's scope; over
    ///   the circle a fixpoint's root case and a bare case are read apart.
    /// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
    /// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
    /// - witness: `native_formers::native_formers::a_case_over_the_circle_takes_its_constructors_and_loops_only`
    #[spec(ensures: |ret| matches!(self.root, Maybe::Absent(root::Absent::Unmarked)) && (ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Form(TypeNode::Computation(_)))))))]
    pub(super) fn native_case(
        &mut self,
        term: ComputationId,
        datatype: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let root = core::mem::replace(&mut self.root, Maybe::Absent(root::Absent::Unmarked));
        let (datatype, opened) = crate::recursion::open_case(self.context, datatype)?;
        // A scrutinee at a looped point's path is split over the words its
        // free cells mint.
        let datatype = self.context.whnf_value_type(datatype)?;
        let datatype = self.context.identified(datatype)?;
        // A case of no branches over a path between two apart terms of a data
        // type owes no branch and no rule.
        if let ValueTypeView::Path {
            carrier,
            left,
            right,
        } = value_type_view(self.context.arena(), datatype)?
            && let &Computation::DataCase {
                motive,
                ref branches,
                ..
            } = self.computation(term)?
            && branches.is_empty()
            && let Maybe::Present(reason) = former::apart(self.context, carrier, (left, right))?
        {
            if reason != Apartness::Apart {
                return Err(CheckRefusal::NotApart { at: term, reason });
            }
            self.wait(Frame::NativeMotive {
                term,
                datatype,
                respect: Maybe::Absent(obligation::Absent::Absurd),
                opened,
            });
            self.context.binders().open(Zone::Intuitionistic, datatype);
            return Ok(Step::Descend(Goal::Form(TypeNode::Computation(motive))));
        }
        if !matches!(
            self.context.arena().value_type(datatype),
            Some(ValueType::Data { .. })
        ) {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(term),
                wanted: ExpectedShape::Data,
                found: TypeNode::Value(datatype),
            });
        }
        let signature = former::signature(self.context, datatype)?;
        let (motive, count) = match self.computation(term)? {
            &Computation::DataCase {
                ref motive,
                ref branches,
                ..
            } => (*motive, branches.len()),
            &Computation::Primitive { .. }
            | &Computation::Transport(..)
            | &Computation::PathTransport { .. }
            | &Computation::Ride { .. }
            | &Computation::TelescopeTransport { .. }
            | &Computation::Lambda(_)
            | &Computation::Fixpoint { .. }
            | &Computation::Application(..)
            | &Computation::Return(_)
            | &Computation::Bind(..)
            | &Computation::Ascribe { .. }
            | &Computation::Force(_)
            | &Computation::Case { .. }
            | &Computation::Split { .. }
            | &Computation::RecordProjection(..)
            | &Computation::TupleProjection(..)
            | &Computation::Hole(_)
            | &Computation::Mark { .. }
            | &Computation::ListFold { .. }
            | &Computation::Perform { .. }
            | &Computation::Handle { .. }
            | &Computation::Exercise { .. }
            | &Computation::Scope { .. }
            | &Computation::Resume(..)
            | &Computation::Reset(_)
            | &Computation::Shift(_)
            | &Computation::With(..)
            | &Computation::Project(..)
            | &Computation::Session(_)
            | &Computation::Memory(_) => return Err(CheckRefusal::MachineInvariant),
        };
        let constructors = signature.constructors().len();
        // A case carries one branch per constructor, and then either no loop
        // arm or one per loop of its sort.
        let looped = crate::loops::loops(self.context, datatype).len();
        if count != constructors && (looped == 0 || constructors.checked_add(looped) != Some(count))
        {
            return Err(CheckRefusal::NonExhaustiveDataCase(term));
        }
        let respect = if signature.presentation().rules().is_empty() {
            Maybe::Absent(obligation::Absent::Free)
        }
        else {
            Maybe::Present(match root {
                Maybe::Present((case, reading)) if case == term => reading,
                Maybe::Present(_) | Maybe::Absent(_) => Reading::Case { datatype },
            })
        };
        self.wait(Frame::NativeMotive {
            term,
            datatype,
            respect,
            opened,
        });
        self.context.binders().open(Zone::Intuitionistic, datatype);
        Ok(Step::Descend(Goal::Form(TypeNode::Computation(motive))))
    }

    /// Check every branch at the motive specialized to its own constructor,
    /// and then, over a presented type, the case's respect for its rules.
    ///
    /// # Specification
    /// - requires: the motive has formed under its one open scrutinee binder.
    /// - ensures: that binder closes before branch functions check; the final
    ///   type substitutes the actual scrutinee into the motive; when the case
    ///   `opened` a stage, each branch binds its recursive fields at it
    ///   ([`crate::recursion::stage_branch`]); with `respect` present the rules
    ///   are decided after every branch has checked and before the type is
    ///   yielded.
    /// - fails: the internal scope guard or telescope instantiation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] preserves the failed scope or branch-type judgment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dependent motives and unequal fields distinguish
    ///   capture, branch order and an incorrectly ambient result type; an
    ///   ill-typed branch of a case over the circle is refused by its own
    ///   mismatch before any rule is decided.
    /// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
    /// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
    #[spec(ensures: |ret| ret.is_err() || ret == Ok(Step::Ascend(Produced::Checked)))]
    pub(super) fn native_branches(
        &mut self,
        term: ComputationId,
        datatype: ValueTypeId,
        respect: Maybe<Reading, obligation::Absent>,
        opened: Maybe<gandr_kernel_term::StageId, crate::recursion::Unstaged>,
    ) -> Result<Step, CheckRefusal>
    {
        self.close()?;
        let (scrutinee, motive, count) = match self.computation(term)? {
            &Computation::DataCase {
                ref scrutinee,
                ref motive,
                ref branches,
            } => (*scrutinee, *motive, branches.len()),
            &Computation::Primitive { .. }
            | &Computation::Transport(..)
            | &Computation::PathTransport { .. }
            | &Computation::Ride { .. }
            | &Computation::TelescopeTransport { .. }
            | &Computation::Lambda(_)
            | &Computation::Fixpoint { .. }
            | &Computation::Application(..)
            | &Computation::Return(_)
            | &Computation::Bind(..)
            | &Computation::Ascribe { .. }
            | &Computation::Force(_)
            | &Computation::Case { .. }
            | &Computation::Split { .. }
            | &Computation::RecordProjection(..)
            | &Computation::TupleProjection(..)
            | &Computation::Hole(_)
            | &Computation::Mark { .. }
            | &Computation::ListFold { .. }
            | &Computation::Perform { .. }
            | &Computation::Handle { .. }
            | &Computation::Exercise { .. }
            | &Computation::Scope { .. }
            | &Computation::Resume(..)
            | &Computation::Reset(_)
            | &Computation::Shift(_)
            | &Computation::With(..)
            | &Computation::Project(..)
            | &Computation::Session(_)
            | &Computation::Memory(_) => return Err(CheckRefusal::MachineInvariant),
        };
        let result =
            gandr_core_term::instantiate_comp_type(self.context.arena_mut(), motive, scrutinee);
        self.wait(Frame::NativeYield(Produced::CompType(result)));
        // A case of no branches over apart endpoints checks no branch, and its
        // scrutinee's path type owes no loop.
        if matches!(respect, Maybe::Absent(obligation::Absent::Absurd)) {
            return Ok(Step::Ascend(Produced::Checked));
        }
        if !crate::loops::loops(self.context, datatype).is_empty() {
            self.wait(Frame::NativeLoops { term, datatype });
        }
        if let Maybe::Present(reading) = respect {
            self.wait(Frame::NativeRespect {
                term,
                datatype,
                reading,
            });
        }
        let constructors = former::signature(self.context, datatype)?;
        let owed = crate::loops::loops(self.context, datatype);
        if count != constructors.constructors().len() {
            for (position, &loop_arm) in owed.iter().enumerate().rev() {
                let expected = crate::loops::arm_type(
                    self.context,
                    term,
                    (datatype, &constructors),
                    loop_arm,
                )?;
                let index = constructors
                    .constructors()
                    .len()
                    .checked_add(position)
                    .ok_or(CheckRefusal::MachineInvariant)?;
                let arm = match self.computation(term)? {
                    &Computation::DataCase { ref branches, .. } => branches
                        .get(index)
                        .copied()
                        .ok_or(CheckRefusal::MachineInvariant)?,
                    &Computation::Primitive { .. }
                    | &Computation::Transport(..)
                    | &Computation::PathTransport { .. }
                    | &Computation::Ride { .. }
                    | &Computation::TelescopeTransport { .. }
                    | &Computation::Lambda(_)
                    | &Computation::Fixpoint { .. }
                    | &Computation::Application(..)
                    | &Computation::Return(_)
                    | &Computation::Bind(..)
                    | &Computation::Ascribe { .. }
                    | &Computation::Force(_)
                    | &Computation::Case { .. }
                    | &Computation::Split { .. }
                    | &Computation::RecordProjection(..)
                    | &Computation::TupleProjection(..)
                    | &Computation::Hole(_)
                    | &Computation::Mark { .. }
                    | &Computation::ListFold { .. }
                    | &Computation::Perform { .. }
                    | &Computation::Handle { .. }
                    | &Computation::Exercise { .. }
                    | &Computation::Scope { .. }
                    | &Computation::Resume(..)
                    | &Computation::Reset(_)
                    | &Computation::Shift(_)
                    | &Computation::With(..)
                    | &Computation::Project(..)
                    | &Computation::Session(_)
                    | &Computation::Memory(_) => return Err(CheckRefusal::MachineInvariant),
                };
                self.wait(Frame::NativeNext(Goal::Computation {
                    term: arm,
                    direction: Direction::Check(expected),
                }));
            }
        }
        for index in (0 .. constructors.constructors().len()).rev() {
            let expected =
                former::branch_type(self.context, datatype, ConstructorTag::from(index), motive)?;
            let expected = match opened {
                Maybe::Present(child) => {
                    let fields = constructors
                        .constructors()
                        .get(index)
                        .map_or(&[][..], alloc::vec::Vec::as_slice);
                    crate::recursion::stage_branch(
                        self.context,
                        datatype,
                        expected,
                        (fields, child),
                    )?
                },
                Maybe::Absent(_plain) => expected,
            };
            let branch = match self.computation(term)? {
                &Computation::DataCase { ref branches, .. } => branches
                    .get(index)
                    .copied()
                    .ok_or(CheckRefusal::MachineInvariant)?,
                &Computation::Primitive { .. }
                | &Computation::Transport(..)
                | &Computation::PathTransport { .. }
                | &Computation::Ride { .. }
                | &Computation::TelescopeTransport { .. }
                | &Computation::Lambda(_)
                | &Computation::Fixpoint { .. }
                | &Computation::Application(..)
                | &Computation::Return(_)
                | &Computation::Bind(..)
                | &Computation::Ascribe { .. }
                | &Computation::Force(_)
                | &Computation::Case { .. }
                | &Computation::Split { .. }
                | &Computation::RecordProjection(..)
                | &Computation::TupleProjection(..)
                | &Computation::Hole(_)
                | &Computation::Mark { .. }
                | &Computation::ListFold { .. }
                | &Computation::Perform { .. }
                | &Computation::Handle { .. }
                | &Computation::Exercise { .. }
                | &Computation::Scope { .. }
                | &Computation::Resume(..)
                | &Computation::Reset(_)
                | &Computation::Shift(_)
                | &Computation::With(..)
                | &Computation::Project(..)
                | &Computation::Session(_)
                | &Computation::Memory(_) => return Err(CheckRefusal::MachineInvariant),
            };
            self.wait(Frame::NativeNext(Goal::Computation {
                term: branch,
                direction: Direction::Check(expected),
            }));
        }
        Ok(Step::Ascend(Produced::Checked))
    }

    /// The case a structural fixpoint opens with, read as the fixpoint
    /// against its type's rules.
    ///
    /// # Specification
    /// - requires: `body` is the body of the fixpoint `fixpoint`, whose
    ///   structural evidence stages its first parameter at `expected`.
    /// - ensures: the case under the body's lambda beside [`Reading::Fold`]
    ///   naming the fixpoint, the domain of `expected`, read as its words where
    ///   it is a path at a looped point, and `expected` itself, when that
    ///   case's scrutinee is the lambda's argument;
    ///   [`root::Absent::NotOverCase`] otherwise.
    /// - fails: as [`crate::context::CheckingContext::identified`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::respect::respected`]: the fold reading
    ///   admits a fixpoint over the circle that a bare reading of its case
    ///   would refuse, and a fold over a path at a looped point respects its
    ///   words' cancellations.
    /// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
    /// - witness: `native_formers::native_formers::a_loop_is_a_word_at_its_path_in_both_checkers`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |root| match *root { Maybe::Present((_, reading)) => matches!(reading, Reading::Fold { fixpoint: marked, .. } if marked == fixpoint), Maybe::Absent(reason) => reason == root::Absent::NotOverCase }))]
    pub(super) fn fold_root(
        &mut self,
        fixpoint: ComputationId,
        expected: gandr_core_term::CompTypeId,
        body: ComputationId,
    ) -> Result<Maybe<(ComputationId, Reading), root::Absent>, CheckRefusal>
    {
        let arena = self.context.arena();
        let not_over_case = Ok(Maybe::Absent(root::Absent::NotOverCase));
        let Some(
            &(gandr_core_term::CompType::Arrow { domain, .. }
            | gandr_core_term::CompType::Pi { domain, .. }),
        ) = arena.comp_type(expected)
        else {
            return not_over_case;
        };
        let Some(&Computation::Lambda(case)) = arena.computation(body)
        else {
            return not_over_case;
        };
        let Some(&Computation::DataCase { scrutinee, .. }) = arena.computation(case)
        else {
            return not_over_case;
        };
        let argument = gandr_core_term::Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        };
        if arena.value(scrutinee) != Some(&argument) {
            return not_over_case;
        }
        Ok(Maybe::Present((case, Reading::Fold {
            fixpoint,
            domain: self.context.identified(domain)?,
            arrow: expected,
        })))
    }

    /// Synthesize the returner of the exact projected field or component.
    ///
    /// # Specification
    /// - requires: `term` is a projection with a synthesized operand type.
    /// - ensures: only an existing label yields its declared field classifier,
    ///   and only a component short of the product's arity yields that
    ///   component's classifier; of a dependent pair, component zero yields the
    ///   first factor and component one the second factor at the first
    ///   component, read as the value the projection of component zero returns.
    /// - fails: a record projection of a non-record, a tuple projection of a
    ///   non-product and non-dependent pair, absent labels and absent
    ///   components refuse separately.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal::ShapeMismatch`], [`CheckRefusal::AbsentRecordField`] or
    /// [`CheckRefusal::AbsentTupleComponent`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal fields and an absent label expose exact
    ///   lookup; each component of a three-component product and the component
    ///   past its last expose positional lookup; both components of a dependent
    ///   pair and the component past them expose the fibre.
    /// - witness: `native_formers::native_formers::record_width_depth_and_projection`
    /// - witness: `native_formers::native_formers::tuple_projection_reads_each_component`
    /// - witness: `judgement::tests::a_projection_of_a_dependent_pair_reads_its_second_factor_at_the_first`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))))]
    pub(super) fn native_projection(
        &mut self,
        term: ComputationId,
        projected: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let head = self.context.whnf_value_type(projected)?;
        let arena = self.context.arena();
        let mismatch = |wanted| CheckRefusal::ShapeMismatch {
            at: TermNode::Computation(term),
            wanted,
            found: TypeNode::Value(projected),
        };
        let part = match (arena.computation(term), arena.value_type(head)) {
            (
                Some(&Computation::RecordProjection(_, ref label)),
                Some(&ValueType::Record(ref fields)),
            ) => fields
                .get(label)
                .copied()
                .ok_or(CheckRefusal::AbsentRecordField(term))?,
            (Some(&Computation::RecordProjection(..)), _) => {
                return Err(mismatch(ExpectedShape::Record));
            },
            (
                Some(&Computation::TupleProjection(_, component)),
                Some(&ValueType::Product(ref parts)),
            ) => parts
                .get(usize::from(component))
                .copied()
                .ok_or(CheckRefusal::AbsentTupleComponent(term))?,
            (
                Some(&Computation::TupleProjection(tuple, component)),
                Some(&ValueType::Sigma { first, second }),
            ) => match usize::from(component) {
                0 => first,
                1 => {
                    let arena = self.context.arena_mut();
                    let at_first =
                        arena.computation_tuple_projection(tuple, Component::from(0_usize));
                    let point = arena.value_returned(at_first);
                    gandr_core_term::instantiate_value_type(arena, second, point)
                },
                _ => return Err(CheckRefusal::AbsentTupleComponent(term)),
            },
            (Some(&Computation::TupleProjection(..)), _) => {
                return Err(mismatch(ExpectedShape::Product));
            },
            _ => return Err(CheckRefusal::MachineInvariant),
        };
        let result = self.context.arena_mut().comp_type_returner(part);
        Ok(Step::Ascend(Produced::CompType(result)))
    }

    /// Open a dependent split's motive binder over the scrutinee's classifier
    /// and form the motive under it.
    ///
    /// # Specification
    /// - requires: `term` is a split with a motive over its scrutinee, and
    ///   `classifier` its scrutinee's synthesised type.
    /// - ensures: one binder of `classifier` is open and the motive's formation
    ///   is the next goal, a frame awaiting it.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at the scrutinee, wanting a
    ///   dependent pair, when the classifier is no dependent pair or the
    ///   unknown type at its weak head, or the split binds other than two
    ///   components; [`CheckRefusal::MachineInvariant`] for any other split.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependent split over a dependent pair forms its
    ///   motive, and over an eager product is a shape mismatch.
    /// - witness: `judgement::tests::a_dependent_split_synthesises_its_motive_at_the_scrutinee`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Form(TypeNode::Computation(_))))))]
    pub(super) fn sigma_split(
        &mut self,
        term: ComputationId,
        classifier: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Split {
            scrutinee,
            arity,
            motive: SplitMotive::Scrutinee(motive),
            ..
        } = *self.computation(term)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let sigma = self.context.whnf_value_type(classifier)?;
        let dependent = matches!(
            value_type_view(self.context.arena(), sigma)?,
            ValueTypeView::Sigma { .. } | ValueTypeView::Unknown
        );
        if !dependent || usize::from(arity) != 2_usize {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(scrutinee),
                wanted: ExpectedShape::Sigma,
                found: TypeNode::Value(classifier),
            });
        }
        self.wait(Frame::SigmaSplitMotive { term, sigma });
        self.context
            .binders()
            .open(Zone::Intuitionistic, classifier);
        Ok(Step::Descend(Goal::Form(TypeNode::Computation(motive))))
    }

    /// Check a dependent split's body under its two components against the
    /// motive at their pair, and synthesise the motive at the scrutinee.
    ///
    /// # Specification
    /// - requires: the motive has formed under its one open scrutinee binder,
    ///   and `sigma` is the scrutinee's classifier at its weak head.
    /// - ensures: the motive binder closes; the first component's binder is
    ///   open over the first factor and the second's over the second factor;
    ///   the body checks against the motive at the pair of the two, and the
    ///   split synthesises the motive at the scrutinee once it has.
    /// - fails: [`CheckRefusal::MachineInvariant`] for any other split or
    ///   classifier, and the scope guard's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body whose type reads the pair checks against the
    ///   motive at it, and the split's type reads the scrutinee.
    /// - witness: `judgement::tests::a_dependent_split_synthesises_its_motive_at_the_scrutinee`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Computation { .. }))))]
    pub(super) fn sigma_split_body(
        &mut self,
        term: ComputationId,
        sigma: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        self.close()?;
        let Computation::Split {
            scrutinee,
            arity,
            motive: SplitMotive::Scrutinee(motive),
            body,
        } = *self.computation(term)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let (first, second) = match value_type_view(self.context.arena(), sigma)? {
            ValueTypeView::Sigma { first, second } => (first, second),
            ValueTypeView::Unknown => (sigma, sigma),
            ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Sum(_)
            | ValueTypeView::List(_)
            | ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Unit
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::Product(_)
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Session(_) => return Err(CheckRefusal::MachineInvariant),
        };
        let arena = self.context.arena_mut();
        let result = instantiate_comp_type(arena, motive, scrutinee);
        let lifted = shift_comp_type_under(arena, motive, Binders::ONE, Binders::from(2_u32));
        let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let inner = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let pair = arena.value_tuple(&[outer, inner]);
        let expected = instantiate_comp_type(arena, lifted, pair);
        self.context.binders().open(Zone::Intuitionistic, first);
        self.context.binders().open(Zone::Intuitionistic, second);
        self.wait(Frame::NativeYield(Produced::CompType(result)));
        self.wait(Frame::SplitBody(arity));
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction: Direction::Check(expected),
        }))
    }
}
