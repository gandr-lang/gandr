//! Native nominal and structural formers at the kernel boundary: data, records,
//! and the n-ary tuples, cases, products and sums, whose children cross in
//! order before the former is assembled.

use anodized::spec;
use gandr_core_term::ValueType;

use super::AnyNode;
use super::Block;
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
    /// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
    /// - witness: `native_formers::native_formers::record_width_depth_and_projection`
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
            CoreNode::Type(TypeNode::Computation(_)) => return Err(Refusal::MachineInvariant),
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
                    Value::Primitive { .. }
                    | Value::PathRefl(_)
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Here(_)
                    | Value::Funext(..)
                    | Value::Equiv(..)
                    | Value::Ua { .. }
                    | Value::SessionRelated { .. }
                    | Value::Stay(_)
                    | Value::Then(..)
                    | Value::FlowProduct(..)
                    | Value::Forward(_)
                    | Value::FunctionFlow(..)
                    | Value::Recorded(_)
                    | Value::Returned(_)
                    | Value::Nested(_)
                    | Value::Run(_)
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
                    | Value::Reify(_) => return Err(Refusal::MachineInvariant),
                }
            },
            CoreNode::Term(TermNode::Computation(at)) => {
                match *(self.arena.computation(at).ok_or(dangling)?) {
                    Computation::DataCase {
                        ref scrutinee,
                        ref motive,
                        ref branches,
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
                    | Computation::Split { .. }
                    | Computation::Hole(_)
                    | Computation::Mark { .. }
                    | Computation::ListFold { .. }
                    | Computation::Perform { .. }
                    | Computation::Handle { .. }
                    | Computation::Exercise { .. }
                    | Computation::Scope { .. }
                    | Computation::Resume(..)
                    | Computation::Reset(_)
                    | Computation::Shift(_)
                    | Computation::With(..)
                    | Computation::Project(..)
                    | Computation::Session(_) => return Err(Refusal::MachineInvariant),
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
                    | ValueType::Flow { .. }
                    | ValueType::Run(_)
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
                    | ValueType::Capability { .. } => return Err(Refusal::MachineInvariant),
                }
            },
            CoreNode::Type(TypeNode::Computation(_)) => return Err(Refusal::MachineInvariant),
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
    /// - witness: `native_formers::native_formers::data_declarations_and_refusals_agree_with_kernel`
    /// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
    #[spec(ensures: |ret| match ret {
        Ok(Step::Ascend(AnyNode::Value(image))) => matches!(root,CoreNode::Term(TermNode::Value(at)) if self.reached().values.get(&at) == Some(&Image::Erased(image))),
        Ok(Step::Ascend(AnyNode::Computation(image))) => matches!(root,CoreNode::Term(TermNode::Computation(at)) if self.reached().computations.get(&at) == Some(&Image::Erased(image))),
        Ok(Step::Ascend(AnyNode::ValueType(image))) => matches!(root,CoreNode::Type(TypeNode::Value(at)) if self.reached().value_types.get(&at) == Some(&Image::Erased(image))),
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
                    Value::Primitive { .. }
                    | Value::PathRefl(_)
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Here(_)
                    | Value::Funext(..)
                    | Value::Equiv(..)
                    | Value::Ua { .. }
                    | Value::SessionRelated { .. }
                    | Value::Stay(_)
                    | Value::Then(..)
                    | Value::FlowProduct(..)
                    | Value::Forward(_)
                    | Value::FunctionFlow(..)
                    | Value::Recorded(_)
                    | Value::Returned(_)
                    | Value::Nested(_)
                    | Value::Run(_)
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
                    | Value::Reify(_) => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_value(at, image))
            },
            CoreNode::Term(TermNode::Computation(at)) => {
                let image = match *(self.arena.computation(at).ok_or(dangling)?) {
                    Computation::DataCase {
                        ref scrutinee,
                        ref motive,
                        ref branches,
                    } => {
                        let scrutinee = value(*scrutinee)?;
                        let motive = comp_type(*motive)?;
                        let branches = branches
                            .iter()
                            .copied()
                            .map(computation)
                            .collect::<Result<_, _>>()?;
                        target.computation_data_case(scrutinee, motive, branches)
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
                    | Computation::Split { .. }
                    | Computation::Hole(_)
                    | Computation::Mark { .. }
                    | Computation::ListFold { .. }
                    | Computation::Perform { .. }
                    | Computation::Handle { .. }
                    | Computation::Exercise { .. }
                    | Computation::Scope { .. }
                    | Computation::Resume(..)
                    | Computation::Reset(_)
                    | Computation::Shift(_)
                    | Computation::With(..)
                    | Computation::Project(..)
                    | Computation::Session(_) => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_computation(at, image))
            },
            CoreNode::Type(TypeNode::Value(at)) => {
                let image = match *(self.arena.value_type(at).ok_or(dangling)?) {
                    ValueType::Data {
                        ref declaration,
                        ref arguments,
                    } => {
                        let crossing = match self.block {
                            Block::Open { source, kernel } if source == *declaration => {
                                Some(kernel)
                            },
                            Block::Open { .. } | Block::Closed => {
                                self.positions.admitted.get(declaration).copied()
                            },
                        };
                        let position = crossing.ok_or(Refusal::WithheldData {
                            at,
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
                    | ValueType::Flow { .. }
                    | ValueType::Run(_)
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
                    | ValueType::Capability { .. } => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_value_type(at, image))
            },
            CoreNode::Type(TypeNode::Computation(_)) => Err(Refusal::MachineInvariant),
        }
    }
}

/// The kernel's session graph of `session`'s protocol, node for node, rooted
/// at the protocol's root.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one kernel node per protocol node at the same position, its
///   payload slots, labels and continuations kept, a recursion variable naming
///   its binder's position; the root is the protocol's.
/// - provides: the graph the kernel replays a session statement's pairs over,
///   which the engine computed over the same positions.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive seat protocol and its widening cross and the
///   kernel replays the engine's simulation between them.
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
#[spec(ensures: |ret| ret.nodes.len() == session.protocol().nodes().len()
    && ret.root.0 == usize::from(session.protocol().root()))]
fn graph(session: &gandr_core_term::session::SessionType) -> gandr_kernel_term::session::Graph
{
    use gandr_core_term::session::ProtocolNode;
    use gandr_kernel_term::session::Label;
    use gandr_kernel_term::session::Node;
    use gandr_kernel_term::session::PayloadSlot;
    use gandr_kernel_term::session::State;
    let state = |at: gandr_core_term::session::ProtocolState| State(usize::from(at));
    let labels = |branches: &alloc::collections::BTreeMap<
        gandr_kernel_term::FieldLabel,
        gandr_core_term::session::ProtocolState,
    >| {
        branches
            .iter()
            .map(|(label, &next)| {
                (
                    Label(alloc::string::String::from(label.as_ref())),
                    state(next),
                )
            })
            .collect()
    };
    let nodes = session
        .protocol()
        .nodes()
        .iter()
        .map(|node| match *node {
            ProtocolNode::Send { payload, next } => {
                Node::Send(PayloadSlot(usize::from(payload)), state(next))
            },
            ProtocolNode::Receive { payload, next } => {
                Node::Receive(PayloadSlot(usize::from(payload)), state(next))
            },
            ProtocolNode::Select(ref branches) => Node::Select(labels(branches)),
            ProtocolNode::Offer(ref branches) => Node::Offer(labels(branches)),
            ProtocolNode::End => Node::End,
            ProtocolNode::Mu(body) => Node::Mu(state(body)),
            ProtocolNode::Recur(binder) => Node::Var(state(binder)),
        })
        .collect();
    gandr_kernel_term::session::Graph {
        nodes,
        root: state(session.protocol().root()),
    }
}
