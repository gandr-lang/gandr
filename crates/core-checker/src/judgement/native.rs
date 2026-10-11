//! Native variable-arity judgments on the existing explicit frame machine.

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;

use super::Direction;
use super::Frame;
use super::Goal;
use super::Machine;
use super::Produced;
use super::Step;
use crate::CheckRefusal;
use crate::ExpectedShape;
use crate::TermNode;
use crate::TypeNode;
use crate::former;

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
            | &Value::Constructor {
                ref datatype,
                ref tag,
                ref fields,
            } => (*datatype, *tag, fields.len()),
            | _ => return Err(CheckRefusal::MachineInvariant),
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
        self.frames
            .push(Frame::NativeYield(Produced::ValueType(datatype)));
        for (index, &field_type) in declared.iter().enumerate().rev() {
            let expected = former::instantiate(
                self.context,
                datatype,
                field_type,
                gandr_core_term::BinderDepth::from(signature.parameters().len()),
            )?;
            let field = match self.value(term)? {
                | &Value::Constructor { ref fields, .. } => fields
                    .get(index)
                    .copied()
                    .ok_or(CheckRefusal::MachineInvariant)?,
                | _ => return Err(CheckRefusal::MachineInvariant),
            };
            self.frames.push(Frame::NativeNext(Goal::Value {
                term: field,
                direction: Direction::Check(expected),
            }));
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
                | Some(&ValueType::Data { ref arguments, .. }) => arguments
                    .get(index)
                    .copied()
                    .ok_or(CheckRefusal::MachineInvariant)?,
                | _ => return Err(CheckRefusal::MachineInvariant),
            };
            self.frames.push(Frame::NativeNext(Goal::Value {
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
        self.frames.push(Frame::NativeRecord {
            term,
            base: self.native_types.len(),
        });
        for &field in fields.values().rev() {
            self.frames.push(Frame::NativeCollect);
            self.frames.push(Frame::NativeNext(Goal::Value {
                term: field,
                direction: Direction::Synthesise,
            }));
        }
        let first = self.frames.pop().ok_or(CheckRefusal::MachineInvariant)?;
        self.resume(first, Produced::Checked)
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
        for (label, &field) in fields.iter().rev() {
            let direction = match wanted.get(label) {
                | Some(&expected) => Direction::Check(expected),
                | None => {
                    self.frames.push(Frame::NativeDiscard);
                    Direction::Synthesise
                },
            };
            self.frames.push(Frame::NativeNext(Goal::Value {
                term: field,
                direction,
            }));
        }
        Ok(Step::Ascend(Produced::Checked))
    }

    /// Form a case's motive under exactly one scrutinee binder.
    ///
    /// # Specification
    /// - requires: `term` is a case whose scrutinee synthesized `datatype`.
    /// - ensures: exhaustive coverage before motive checking; branches remain
    ///   ordinary ambient functions and are not given implicit field binders.
    /// - fails: non-data scrutinee, wrong coverage or absent declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] identifies the failed elimination premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, missing and surplus branches distinguish exact
    ///   coverage; a dependent motive distinguishes its binder's scope.
    /// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(Goal::Form(TypeNode::Computation(_))))))]
    pub(super) fn native_case(
        &mut self,
        term: ComputationId,
        datatype: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let datatype = self.context.whnf_value_type(datatype)?;
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
            | &Computation::DataCase {
                ref motive,
                ref branches,
                ..
            } => (*motive, branches.len()),
            | _ => return Err(CheckRefusal::MachineInvariant),
        };
        if count != signature.constructors().len() {
            return Err(CheckRefusal::NonExhaustiveDataCase(term));
        }
        self.frames.push(Frame::NativeMotive { term, datatype });
        self.context.binders().open(Zone::Intuitionistic, datatype);
        Ok(Step::Descend(Goal::Form(TypeNode::Computation(motive))))
    }

    /// Check every branch at the motive specialized to its own constructor.
    ///
    /// # Specification
    /// - requires: the motive has formed under its one open scrutinee binder.
    /// - ensures: that binder closes before branch functions check; the final
    ///   type substitutes the actual scrutinee into the motive.
    /// - fails: the internal scope guard or telescope instantiation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] preserves the failed scope or branch-type judgment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dependent motives and unequal fields distinguish
    ///   capture, branch order and an incorrectly ambient result type.
    /// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
    #[spec(ensures: |ret| ret.is_err() || ret == Ok(Step::Ascend(Produced::Checked)))]
    pub(super) fn native_branches(
        &mut self,
        term: ComputationId,
        datatype: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        self.close()?;
        let (scrutinee, motive, count) = match self.computation(term)? {
            | &Computation::DataCase {
                ref scrutinee,
                ref motive,
                ref branches,
            } => (*scrutinee, *motive, branches.len()),
            | _ => return Err(CheckRefusal::MachineInvariant),
        };
        let result =
            gandr_core_term::instantiate_comp_type(self.context.arena_mut(), motive, scrutinee);
        self.frames
            .push(Frame::NativeYield(Produced::CompType(result)));
        for index in (0 .. count).rev() {
            let expected =
                former::branch_type(self.context, datatype, ConstructorTag::from(index), motive)?;
            let branch = match self.computation(term)? {
                | &Computation::DataCase { ref branches, .. } => branches
                    .get(index)
                    .copied()
                    .ok_or(CheckRefusal::MachineInvariant)?,
                | _ => return Err(CheckRefusal::MachineInvariant),
            };
            self.frames.push(Frame::NativeNext(Goal::Computation {
                term: branch,
                direction: Direction::Check(expected),
            }));
        }
        Ok(Step::Ascend(Produced::Checked))
    }

    /// Synthesize the returner of the exact projected field.
    ///
    /// # Specification
    /// - requires: `term` is a projection with a synthesized operand type.
    /// - ensures: only an existing label yields its declared field classifier.
    /// - fails: non-record operands and absent labels refuse separately.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal::ShapeMismatch`] or [`CheckRefusal::AbsentRecordField`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal fields and an absent label expose exact
    ///   lookup.
    /// - witness: `native_formers::native_formers::record_width_depth_and_projection`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))))]
    pub(super) fn native_projection(
        &mut self,
        term: ComputationId,
        record: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let head = self.context.whnf_value_type(record)?;
        let Some(matched_native_node) = self.context.arena().value_type(head)
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(term),
                wanted: ExpectedShape::Record,
                found: TypeNode::Value(record),
            });
        };
        let ValueType::Record(ref fields) = *matched_native_node
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(term),
                wanted: ExpectedShape::Record,
                found: TypeNode::Value(record),
            });
        };
        let Some(matched_native_node) = self.context.arena().computation(term)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Computation::RecordProjection(_, ref label) = *matched_native_node
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let field = fields
            .get(label)
            .copied()
            .ok_or(CheckRefusal::AbsentRecordField(term))?;
        let result = self.context.arena_mut().comp_type_returner(field);
        Ok(Step::Ascend(Produced::CompType(result)))
    }
}
