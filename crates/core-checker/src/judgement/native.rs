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
use gandr_kernel_term::Component;
use gandr_kernel_term::DeBruijnIndex;

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
        self.wait(Frame::NativeYield(Produced::ValueType(datatype)));
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
            self.wait(Frame::NativeNext(Goal::Value {
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
            let direction = match wanted.get(label) {
                | Some(&expected) => Direction::Check(expected),
                | None => {
                    self.frames.push(Waiting {
                        frame: Frame::NativeDiscard,
                        owner,
                    });
                    Direction::Synthesise
                },
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
    ///   ordinary ambient functions and are not given implicit field binders.
    /// - fails: non-data scrutinee, wrong coverage or absent declaration; a
    ///   case over a presented type with rules refuses
    ///   [`CheckRefusal::RuleNotRespected`] at its first rule, the kernel's
    ///   refusal of the same case.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckRefusal`] identifies the failed elimination premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, missing and surplus branches distinguish exact
    ///   coverage; a dependent motive distinguishes its binder's scope; a case
    ///   over the circle is refused where the same case over a free type
    ///   checks.
    /// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
    /// - witness: `native_formers::native_formers::a_case_over_a_presented_type_is_refused`
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
        // A rule identifies two constructor terms, and a case reads its
        // scrutinee's constructor as it stands, so its arms could tell the two
        // apart. No case is shown to respect the rules yet: each is refused at
        // the first.
        if !signature.presentation().rules().is_empty() {
            return Err(CheckRefusal::RuleNotRespected {
                at: term,
                rule: gandr_kernel_term::RuleIndex::from(0_usize),
            });
        }
        self.wait(Frame::NativeMotive { term, datatype });
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
        self.wait(Frame::NativeYield(Produced::CompType(result)));
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
            self.wait(Frame::NativeNext(Goal::Computation {
                term: branch,
                direction: Direction::Check(expected),
            }));
        }
        Ok(Step::Ascend(Produced::Checked))
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
            | (
                Some(&Computation::RecordProjection(_, ref label)),
                Some(&ValueType::Record(ref fields)),
            ) => fields
                .get(label)
                .copied()
                .ok_or(CheckRefusal::AbsentRecordField(term))?,
            | (Some(&Computation::RecordProjection(..)), _) => {
                return Err(mismatch(ExpectedShape::Record));
            },
            | (
                Some(&Computation::TupleProjection(_, component)),
                Some(&ValueType::Product(ref parts)),
            ) => parts
                .get(usize::from(component))
                .copied()
                .ok_or(CheckRefusal::AbsentTupleComponent(term))?,
            | (
                Some(&Computation::TupleProjection(tuple, component)),
                Some(&ValueType::Sigma { first, second }),
            ) => match usize::from(component) {
                | 0 => first,
                | 1 => {
                    let arena = self.context.arena_mut();
                    let at_first =
                        arena.computation_tuple_projection(tuple, Component::from(0_usize));
                    let point = arena.value_returned(at_first);
                    gandr_core_term::instantiate_value_type(arena, second, point)
                },
                | _ => return Err(CheckRefusal::AbsentTupleComponent(term)),
            },
            | (Some(&Computation::TupleProjection(..)), _) => {
                return Err(mismatch(ExpectedShape::Product));
            },
            | _ => return Err(CheckRefusal::MachineInvariant),
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
            | ValueTypeView::Sigma { first, second } => (first, second),
            | ValueTypeView::Unknown => (sigma, sigma),
            | _ => return Err(CheckRefusal::MachineInvariant),
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
