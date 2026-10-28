//! Native nominal and structural formers at the kernel boundary: data, codata,
//! records, the n-ary tuples, cases, products, sums and lazy products, and the
//! ascriptions, whose children cross in order before the former is assembled.

use anodized::spec;
use gandr_core_term::ValueType;

use super::AnyNode;
use super::Computation;
use super::CoreNode;
use super::Erasure;
use super::Frame;
use super::Image;
use super::Refusal;
use super::Step;
use super::TermArena;
use super::TermNode;
use super::TypeNode;
use super::Value;

impl Erasure<'_, '_>
{
    /// Queue every native child in source order without copying its collection.
    ///
    /// # Specification
    /// - requires: `root` is a native former whose memo entry is not open.
    /// - ensures: the first child is visited before assembly; empty records and
    ///   parameterless nominal types assemble immediately.
    /// - fails: a dangling source node or an internal family mismatch.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — parameterized constructors, dependent cases and
    ///   nested records distinguish missing children and changed order after
    ///   admission.
    /// - witness: `tests::native_formers::dependent_data_parameters_and_case_motives`
    /// - witness: `tests::native_formers::record_width_depth_and_projection`
    #[spec(ensures: |ret| ret.is_err() || !matches!(ret, Ok(Step::Descend(_))) || !self.frames.is_empty())]
    pub(super) fn prepare_native(
        &mut self,
        target: &mut TermArena,
        root: CoreNode,
    ) -> Result<Step, Refusal>
    {
        match root {
            CoreNode::Term(TermNode::Value(at)) => {
                self.memo().values.insert(at, Image::Open);
            },
            CoreNode::Term(TermNode::Computation(at)) => {
                self.memo().computations.insert(at, Image::Open);
            },
            CoreNode::Type(TypeNode::Value(at)) => {
                self.memo().value_types.insert(at, Image::Open);
            },
            CoreNode::Type(TypeNode::Computation(at)) => {
                self.memo().comp_types.insert(at, Image::Open);
            },
        }
        self.frames.push(Frame::NativeBuild(root));
        let value = |at| Frame::NativeNext(CoreNode::Term(TermNode::Value(at)));
        let value_type = |at| Frame::NativeNext(CoreNode::Type(TypeNode::Value(at)));
        let computation = |at| Frame::NativeNext(CoreNode::Term(TermNode::Computation(at)));
        let dangling = Refusal::DanglingNode { node: root };
        match root {
            CoreNode::Term(TermNode::Value(at)) => {
                match *(self.arena.value(at).ok_or(dangling)?) {
                    Value::Constructor {
                        ref datatype,
                        ref fields,
                        ..
                    } => {
                        self.frames.extend(fields.iter().rev().copied().map(value));
                        self.frames.push(value_type(*datatype));
                    },
                    Value::Record(ref fields) => self
                        .frames
                        .extend(fields.values().rev().copied().map(value)),
                    Value::Tuple(ref components) => self
                        .frames
                        .extend(components.iter().rev().copied().map(value)),
                    // The value crosses first, then the type it is ascribed.
                    Value::Ascribe {
                        value: ascribed,
                        ty,
                    } => {
                        self.frames.push(value_type(ty));
                        self.frames.push(value(ascribed));
                    },
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
                    | Value::Injection(..)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Thunk(_)
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..)
                    | Value::Hole(_)
                    | Value::Mark { .. }
                    | Value::Reify(_)
                    | Value::Row(_) => return Err(Refusal::MachineInvariant),
                }
            },
            CoreNode::Term(TermNode::Computation(at)) => {
                match *(self.arena.computation(at).ok_or(dangling)?) {
                    Computation::DataCase {
                        ref scrutinee,
                        ref motive,
                        ref branches,
                        ..
                    } => {
                        self.frames
                            .extend(branches.iter().rev().copied().map(computation));
                        self.frames
                            .push(Frame::NativeNext(CoreNode::Type(TypeNode::Computation(
                                *motive,
                            ))));
                        self.frames.push(value(*scrutinee));
                    },
                    Computation::RecordProjection(ref record, _)
                    | Computation::TupleProjection(ref record, _) => {
                        self.frames.push(value(*record));
                    },
                    Computation::Case {
                        ref scrutinee,
                        ref branches,
                    } => {
                        self.frames
                            .extend(branches.iter().rev().copied().map(computation));
                        self.frames.push(value(*scrutinee));
                    },
                    Computation::With(ref components) => self
                        .frames
                        .extend(components.iter().rev().copied().map(computation)),
                    // The body crosses first, then the type it is ascribed.
                    Computation::Ascribe { body, ty } => {
                        self.frames
                            .push(Frame::NativeNext(CoreNode::Type(TypeNode::Computation(ty))));
                        self.frames.push(computation(body));
                    },
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
                    | Computation::Force(_)
                    | Computation::Decompose(_)
                    | Computation::Split { .. }
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
                    | Computation::Project(..)
                    | Computation::Session(_)
                    | Computation::Memory(_)
                    | Computation::World(_) => return Err(Refusal::MachineInvariant),
                }
            },
            CoreNode::Type(TypeNode::Value(at)) => {
                match *(self.arena.value_type(at).ok_or(dangling)?) {
                    ValueType::Data { ref arguments, .. } => self
                        .frames
                        .extend(arguments.iter().rev().copied().map(value)),
                    ValueType::Record(ref fields) => self
                        .frames
                        .extend(fields.values().rev().copied().map(value_type)),
                    ValueType::Product(ref components) | ValueType::Sum(ref components) => self
                        .frames
                        .extend(components.iter().rev().copied().map(value_type)),
                    ValueType::Session(ref session) => self
                        .frames
                        .extend(session.payloads().iter().rev().copied().map(value_type)),
                    ValueType::PathUniverse(..)
                    | ValueType::Path { .. }
                    | ValueType::Bridge { .. }
                    | ValueType::Flow { .. }
                    | ValueType::Run(_)
                    | ValueType::Prefix(_)
                    | ValueType::Dialogue(_)
                    | ValueType::Web
                    | ValueType::Base(_)
                    | ValueType::Sigma { .. }
                    | ValueType::List(_)
                    | ValueType::Thunk(_)
                    | ValueType::Universe { .. }
                    | ValueType::Lift { .. }
                    | ValueType::Element { .. }
                    | ValueType::Abstract(_)
                    | ValueType::StaticPi { .. }
                    | ValueType::Unknown
                    | ValueType::Stack { .. }
                    | ValueType::Capability { .. }
                    | ValueType::Buffer
                    | ValueType::Staged { .. }
                    | ValueType::Kept { .. }
                    | ValueType::World(_)
                    | ValueType::Row
                    | ValueType::RowTail(_) => return Err(Refusal::MachineInvariant),
                }
            },
            CoreNode::Type(TypeNode::Computation(at)) => {
                match *(self.arena.comp_type(at).ok_or(dangling)?) {
                    gandr_core_term::CompType::Codata { ref arguments, .. } => self
                        .frames
                        .extend(arguments.iter().rev().copied().map(value)),
                    gandr_core_term::CompType::With(ref components) => {
                        self.frames.extend(components.iter().rev().map(|&at| {
                            Frame::NativeNext(CoreNode::Type(TypeNode::Computation(at)))
                        }));
                    },
                    gandr_core_term::CompType::Returner { .. }
                    | gandr_core_term::CompType::Arrow { .. }
                    | gandr_core_term::CompType::Pi { .. }
                    | gandr_core_term::CompType::Element { .. }
                    | gandr_core_term::CompType::Unknown => return Err(Refusal::MachineInvariant),
                }
            },
        }
        match self.frames.pop() {
            Some(Frame::NativeNext(child)) => Ok(Step::Descend(child)),
            Some(Frame::NativeBuild(node)) => self.finish_native(target, node),
            _ => Err(Refusal::MachineInvariant),
        }
    }

    /// Assemble a native node from the memoized images of all its children.
    ///
    /// # Specification
    /// - requires: every child of `root` has crossed in the current mode.
    /// - ensures: the image has the source family, labels, tag and remapped
    ///   nominal identity, and is recorded before it is returned.
    /// - fails: a withheld nominal declaration or an incomplete child image.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — admission after a refused declaration changes kernel
    ///   positions; nominal confusion, lost labels and lost motives are exposed
    ///   by constructor and projection judgments over the exported artifact.
    /// - witness: `tests::native_formers::data_declarations_and_refusals_agree_with_kernel`
    /// - witness: `tests::native_formers::dependent_data_parameters_and_case_motives`
    #[spec(ensures: |ret| match ret {
        Ok(Step::Ascend(AnyNode::Value(image))) => matches!(root,CoreNode::Term(TermNode::Value(at)) if self.reached().values.get(&at) == Some(&Image::Erased(image))),
        Ok(Step::Ascend(AnyNode::Computation(image))) => matches!(root,CoreNode::Term(TermNode::Computation(at)) if self.reached().computations.get(&at) == Some(&Image::Erased(image))),
        Ok(Step::Ascend(AnyNode::ValueType(image))) => matches!(root,CoreNode::Type(TypeNode::Value(at)) if self.reached().value_types.get(&at) == Some(&Image::Erased(image))),
        Ok(Step::Ascend(AnyNode::CompType(image))) => matches!(root,CoreNode::Type(TypeNode::Computation(at)) if self.reached().comp_types.get(&at) == Some(&Image::Erased(image))),
        Err(_) => true,
        _ => false,
    })]
    pub(super) fn finish_native(
        &mut self,
        target: &mut TermArena,
        root: CoreNode,
    ) -> Result<Step, Refusal>
    {
        let memo = self.reached();
        let value = |at| match memo.values.get(&at) {
            Some(&Image::Erased(image)) => Ok(image),
            _ => Err(Refusal::MachineInvariant),
        };
        let value_type = |at| match memo.value_types.get(&at) {
            Some(&Image::Erased(image)) => Ok(image),
            _ => Err(Refusal::MachineInvariant),
        };
        let computation = |at| match memo.computations.get(&at) {
            Some(&Image::Erased(image)) => Ok(image),
            _ => Err(Refusal::MachineInvariant),
        };
        let comp_type = |at| match memo.comp_types.get(&at) {
            Some(&Image::Erased(image)) => Ok(image),
            _ => Err(Refusal::MachineInvariant),
        };
        let dangling = Refusal::DanglingNode { node: root };
        match root {
            CoreNode::Term(TermNode::Value(at)) => {
                let image = match *(self.arena.value(at).ok_or(dangling)?) {
                    Value::Constructor {
                        ref datatype,
                        ref tag,
                        ref fields,
                    } => {
                        let datatype = value_type(*datatype)?;
                        let fields = fields
                            .iter()
                            .copied()
                            .map(value)
                            .collect::<Result<_, _>>()?;
                        target.value_constructor(datatype, *tag, fields)
                    },
                    Value::Record(ref fields) => {
                        let fields = fields
                            .iter()
                            .map(|(label, &field)| value(field).map(|image| (label.clone(), image)))
                            .collect::<Result<_, _>>()?;
                        target.value_record(fields)
                    },
                    Value::Tuple(ref components) => {
                        let components = components.iter().copied().map(value).collect::<Result<
                            alloc::vec::Vec<_>,
                            _,
                        >>(
                        )?;
                        target.value_tuple(&components)
                    },
                    Value::Ascribe {
                        value: ascribed,
                        ty,
                    } => {
                        let returned = target.computation_return(value(ascribed)?);
                        let returner = target.comp_type_returner(value_type(ty)?);
                        let typed = ascription(target, returned, returner);
                        target.value_returned(typed)
                    },
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
                    | Value::Injection(..)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Thunk(_)
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..)
                    | Value::Hole(_)
                    | Value::Mark { .. }
                    | Value::Reify(_)
                    | Value::Row(_) => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_value(at, image))
            },
            CoreNode::Term(TermNode::Computation(at)) => {
                let image = match *(self.arena.computation(at).ok_or(dangling)?) {
                    Computation::DataCase {
                        ref scrutinee,
                        ref motive,
                        ref branches,
                        equations,
                        ..
                    } => {
                        let scrutinee = value(*scrutinee)?;
                        let motive = comp_type(*motive)?;
                        let branches = branches
                            .iter()
                            .copied()
                            .map(computation)
                            .collect::<Result<_, _>>()?;
                        target.computation_data_case_with_equations(
                            scrutinee, motive, branches, equations,
                        )
                    },
                    Computation::RecordProjection(ref record, ref label) => {
                        target.computation_record_projection(value(*record)?, label.clone())
                    },
                    Computation::TupleProjection(ref tuple, component) => {
                        target.computation_tuple_projection(value(*tuple)?, component)
                    },
                    Computation::Case {
                        ref scrutinee,
                        ref branches,
                    } => {
                        let scrutinee = value(*scrutinee)?;
                        let branches = branches.iter().copied().map(computation).collect::<Result<
                            alloc::vec::Vec<_>,
                            _,
                        >>(
                        )?;
                        target.computation_case(scrutinee, &branches)
                    },
                    Computation::With(ref components) => {
                        let components = components
                            .iter()
                            .copied()
                            .map(computation)
                            .collect::<Result<alloc::vec::Vec<_>, _>>()?;
                        target.computation_with(&components)
                    },
                    Computation::Ascribe { body, ty } => {
                        ascription(target, computation(body)?, comp_type(ty)?)
                    },
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
                    | Computation::Force(_)
                    | Computation::Decompose(_)
                    | Computation::Split { .. }
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
                    | Computation::Project(..)
                    | Computation::Session(_)
                    | Computation::Memory(_)
                    | Computation::World(_) => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_computation(at, image))
            },
            CoreNode::Type(TypeNode::Value(at)) => {
                let image = match *(self.arena.value_type(at).ok_or(dangling)?) {
                    ValueType::Data {
                        ref declaration,
                        ref arguments,
                    } => {
                        let crossing = self
                            .crossing
                            .iter()
                            .find(|&&(member, _)| member == *declaration)
                            .map(|&(_, kernel)| kernel)
                            .or_else(|| self.positions.admitted.get(declaration).copied())
                            .or_else(|| {
                                self.positions
                                    .models
                                    .iter()
                                    .find(|model| model.declaration == *declaration)
                                    .map(|model| model.position)
                            });
                        let position = crossing.ok_or(Refusal::WithheldData {
                            at: TypeNode::Value(at),
                            constant: *declaration,
                        })?;
                        let arguments = arguments
                            .iter()
                            .copied()
                            .map(value)
                            .collect::<Result<_, _>>()?;
                        target.value_type_data(position, arguments)
                    },
                    ValueType::Record(ref fields) => {
                        let fields = fields
                            .iter()
                            .map(|(label, &field)| {
                                value_type(field).map(|image| (label.clone(), image))
                            })
                            .collect::<Result<_, _>>()?;
                        target.value_type_record(fields)
                    },
                    ValueType::Product(ref components) => {
                        let components = components
                            .iter()
                            .copied()
                            .map(value_type)
                            .collect::<Result<alloc::vec::Vec<_>, _>>()?;
                        target.value_type_product(&components)
                    },
                    ValueType::Sum(ref summands) => {
                        let summands = summands.iter().copied().map(value_type).collect::<Result<
                            alloc::vec::Vec<_>,
                            _,
                        >>(
                        )?;
                        target.value_type_sum(&summands)
                    },
                    ValueType::Session(ref session) => {
                        let payloads = session
                            .payloads()
                            .iter()
                            .copied()
                            .map(value_type)
                            .collect::<Result<alloc::vec::Vec<_>, _>>()?;
                        let payloads = target.value_type_product(&payloads);
                        target.value_type_session(alloc::sync::Arc::new(graph(session)), payloads)
                    },
                    ValueType::PathUniverse(..)
                    | ValueType::Path { .. }
                    | ValueType::Bridge { .. }
                    | ValueType::Flow { .. }
                    | ValueType::Run(_)
                    | ValueType::Prefix(_)
                    | ValueType::Dialogue(_)
                    | ValueType::Web
                    | ValueType::Base(_)
                    | ValueType::Sigma { .. }
                    | ValueType::List(_)
                    | ValueType::Thunk(_)
                    | ValueType::Universe { .. }
                    | ValueType::Lift { .. }
                    | ValueType::Element { .. }
                    | ValueType::Abstract(_)
                    | ValueType::StaticPi { .. }
                    | ValueType::Unknown
                    | ValueType::Stack { .. }
                    | ValueType::Capability { .. }
                    | ValueType::Buffer
                    | ValueType::Staged { .. }
                    | ValueType::Kept { .. }
                    | ValueType::World(_)
                    | ValueType::Row
                    | ValueType::RowTail(_) => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_value_type(at, image))
            },
            CoreNode::Type(TypeNode::Computation(at)) => {
                let image = match *(self.arena.comp_type(at).ok_or(dangling)?) {
                    gandr_core_term::CompType::Codata {
                        ref declaration,
                        ref arguments,
                    } => {
                        let crossing = self
                            .crossing
                            .iter()
                            .find(|&&(member, _)| member == *declaration)
                            .map(|&(_, kernel)| kernel)
                            .or_else(|| self.positions.admitted.get(declaration).copied());
                        let position = crossing.ok_or(Refusal::WithheldData {
                            at: TypeNode::Computation(at),
                            constant: *declaration,
                        })?;
                        let arguments = arguments
                            .iter()
                            .copied()
                            .map(value)
                            .collect::<Result<_, _>>()?;
                        target.comp_type_codata(position, arguments)
                    },
                    gandr_core_term::CompType::With(ref components) => {
                        let components = components
                            .iter()
                            .copied()
                            .map(comp_type)
                            .collect::<Result<alloc::vec::Vec<_>, _>>()?;
                        target.comp_type_with(&components)
                    },
                    gandr_core_term::CompType::Returner { .. }
                    | gandr_core_term::CompType::Arrow { .. }
                    | gandr_core_term::CompType::Pi { .. }
                    | gandr_core_term::CompType::Element { .. }
                    | gandr_core_term::CompType::Unknown => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_comp_type(at, image))
            },
        }
    }
}

/// The kernel image of the ascription of `body` to `ty`: a typed position the
/// kernel already judges, so the ascription is replayed rather than claimed.
///
/// The kernel has no ascription former; its one computation that both states
/// a type and checks a computation against it is the fold, whose result type
/// is written and whose nil branch checks against its returner. Folding the
/// empty list of units runs the nil branch alone, so the image runs as the
/// body does. A returner `F A` is ascribed by the fold whose nil branch is the
/// body and whose result is `A`; any other type `C` by the fold returning the
/// body suspended, at `U C`, bound and forced. Alternatives were a kernel
/// ascription former, which grows the trusted vocabulary and its wire format
/// for what an existing typed position already judges, and erasing the
/// ascription to its body, which leaves a check-only body in synthesis
/// position for the kernel to refuse and the stated type unreplayed. Reversal:
/// the kernel gains a former of its own once a typed position is wanted that
/// the fold cannot state.
///
/// # Specification
/// - requires: `body` and `ty` are kernel images in `target`.
/// - ensures: for `ty` a returner `F A`, the fold of the empty list of units at
///   result `A` whose nil branch is `body` and whose cons branch returns the
///   folded result; otherwise `x ← fold(nil; return thunk body) : F (U ty);
///   force x`.
/// - provides: the bridge's image of [`Computation::Ascribe`], and under a
///   returned value of [`Value::Ascribe`] at the returner of its type.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an ascribed returner and an ascribed lambda, each by one
///   of the two images, cross and the kernel replays both at the stated type; a
///   check-only body in either image is judged in a checking position, so
///   neither is replayed by erasure.
/// - witness: `bridge::tests::an_ascription_crosses_as_a_typed_position_the_kernel_replays`
#[spec(ensures: |ret| target.computation(ret).is_some())]
fn ascription(
    target: &mut TermArena,
    body: gandr_kernel_term::ComputationId,
    ty: gandr_kernel_term::CompTypeId,
) -> gandr_kernel_term::ComputationId
{
    let element = target.value_type_unit();
    let nil = target.value_list_nil();
    let folded = target.value_variable(gandr_kernel_term::DeBruijnIndex::from(0_u32));
    let on_cons = target.computation_return(folded);
    if let Some(&gandr_kernel_term::CompType::Returner(result)) = target.comp_type(ty) {
        return target.computation_list_fold(element, result, nil, body, on_cons);
    }
    let suspended = target.value_thunk(body);
    let on_nil = target.computation_return(suspended);
    let result = target.value_type_thunk(ty);
    let bound = target.computation_list_fold(element, result, nil, on_nil, on_cons);
    let bound_variable = target.value_variable(gandr_kernel_term::DeBruijnIndex::from(0_u32));
    let forced = target.computation_force(bound_variable);
    target.computation_bind(bound, forced)
}

/// The kernel's session graph of `session`: its protocol node for node at the
/// protocol's root, and the protocol unfolded at the state `session` stands
/// at past it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: at the protocol's root, one kernel node per protocol node at the
///   same position, its payload slots, labels and continuations kept, a
///   recursion variable naming its binder's position, rooted at the root. Past
///   it, the tree reachable from the state, copied with each recursion variable
///   whose binder the copy did not pass through replaced by a fresh copy of
///   that binder, so `S` at a state inside `mu t. B` is `S[t := mu t. B]`,
///   rooted at the copy of the state.
/// - provides: the graph the kernel replays a session statement's pairs over,
///   which the engine computed over the same positions; a statement relates
///   sessions at their roots only.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive seat protocol and its widening cross and the
///   kernel replays the engine's simulation between them; the seat past its
///   root, inside its recursion, forms. A copy that kept the free variable or
///   repeated a node is refused by the kernel's formation.
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
/// - witness: `judgement::session::tests::a_session_code_crosses_re_rooted_at_its_state_1319`
#[spec(ensures: |ret| session.state() != session.protocol().root()
    || (ret.nodes.len() == session.protocol().nodes().len()
        && ret.root.0 == usize::from(session.state())))]
fn graph(session: &gandr_core_term::session::SessionType) -> gandr_kernel_term::session::Graph
{
    use gandr_core_term::session::ProtocolNode;
    use gandr_core_term::session::ProtocolState;
    use gandr_kernel_term::session::Label;
    use gandr_kernel_term::session::Node;
    use gandr_kernel_term::session::PayloadSlot;
    use gandr_kernel_term::session::State;
    let protocol = session.protocol();
    let state = |at: ProtocolState| State(usize::from(at));
    let label =
        |label: &gandr_kernel_term::FieldLabel| Label(alloc::string::String::from(label.as_ref()));
    if session.state() == protocol.root() {
        let nodes = protocol
            .nodes()
            .iter()
            .map(|node| match *node {
                ProtocolNode::Send { payload, next } => {
                    Node::Send(PayloadSlot(usize::from(payload)), state(next))
                },
                ProtocolNode::Receive { payload, next } => {
                    Node::Receive(PayloadSlot(usize::from(payload)), state(next))
                },
                ProtocolNode::Select(ref branches) => Node::Select(
                    branches
                        .iter()
                        .map(|(name, &next)| (label(name), state(next)))
                        .collect(),
                ),
                ProtocolNode::Offer(ref branches) => Node::Offer(
                    branches
                        .iter()
                        .map(|(name, &next)| (label(name), state(next)))
                        .collect(),
                ),
                ProtocolNode::End => Node::End,
                ProtocolNode::Mu(body) => Node::Mu(state(body)),
                ProtocolNode::Recur(binder) => Node::Var(state(binder)),
            })
            .collect();
        return gandr_kernel_term::session::Graph {
            nodes,
            root: state(protocol.root()),
        };
    }
    // Each task copies one protocol state into one kernel slot, under the
    // binders the copy passed through: each a protocol position and its
    // copy's slot.
    let mut nodes = alloc::vec![Node::End];
    let mut tasks = alloc::vec![(
        session.state(),
        0_usize,
        alloc::vec::Vec::<(ProtocolState, usize)>::new()
    )];
    let slot = |nodes: &mut alloc::vec::Vec<Node>| {
        nodes.push(Node::End);
        nodes.len().saturating_sub(1)
    };
    while let Some((at, into, binders)) = tasks.pop() {
        let Some(node) = protocol.nodes().get(usize::from(at))
        else {
            continue;
        };
        let copied = match *node {
            ProtocolNode::Send { payload, next } | ProtocolNode::Receive { payload, next } => {
                let next_slot = slot(&mut nodes);
                tasks.push((next, next_slot, binders));
                if matches!(*node, ProtocolNode::Send { .. }) {
                    Node::Send(PayloadSlot(usize::from(payload)), State(next_slot))
                }
                else {
                    Node::Receive(PayloadSlot(usize::from(payload)), State(next_slot))
                }
            },
            ProtocolNode::Select(ref branches) | ProtocolNode::Offer(ref branches) => {
                let copied = branches
                    .iter()
                    .map(|(name, &next)| {
                        let next_slot = slot(&mut nodes);
                        tasks.push((next, next_slot, binders.clone()));
                        (label(name), State(next_slot))
                    })
                    .collect();
                if matches!(*node, ProtocolNode::Select(_)) {
                    Node::Select(copied)
                }
                else {
                    Node::Offer(copied)
                }
            },
            ProtocolNode::End => Node::End,
            ProtocolNode::Mu(body) => {
                let body_slot = slot(&mut nodes);
                let mut inner = binders;
                inner.push((at, into));
                tasks.push((body, body_slot, inner));
                Node::Mu(State(body_slot))
            },
            ProtocolNode::Recur(binder) => {
                if let Some(&(_, bound)) = binders
                    .iter()
                    .rev()
                    .find(|&&(position, _)| position == binder)
                {
                    Node::Var(State(bound))
                }
                else {
                    // The binder lies above the state: this slot is a fresh
                    // copy of it, which binds the variables inside it.
                    tasks.push((binder, into, binders));
                    continue;
                }
            },
        };
        if let Some(target) = nodes.get_mut(into) {
            *target = copied;
        }
    }
    gandr_kernel_term::session::Graph {
        nodes,
        root: State(0),
    }
}
