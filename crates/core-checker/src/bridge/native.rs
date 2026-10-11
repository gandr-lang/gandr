//! Native nominal and structural formers at the kernel boundary.

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
            | CoreNode::Term(TermNode::Value(at)) => {
                self.memo().values.insert(at, Image::Open);
            },
            | CoreNode::Term(TermNode::Computation(at)) => {
                self.memo().computations.insert(at, Image::Open);
            },
            | CoreNode::Type(TypeNode::Value(at)) => {
                self.memo().value_types.insert(at, Image::Open);
            },
            | CoreNode::Type(TypeNode::Computation(_)) => return Err(Refusal::MachineInvariant),
        }
        self.frames.push(Frame::NativeBuild(root));
        let value = |at| Frame::NativeNext(CoreNode::Term(TermNode::Value(at)));
        let value_type = |at| Frame::NativeNext(CoreNode::Type(TypeNode::Value(at)));
        let computation = |at| Frame::NativeNext(CoreNode::Term(TermNode::Computation(at)));
        let dangling = Refusal::DanglingNode { node: root };
        match root {
            | CoreNode::Term(TermNode::Value(at)) => {
                match *(self.arena.value(at).ok_or(dangling)?) {
                    | Value::Constructor {
                        ref datatype,
                        ref fields,
                        ..
                    } => {
                        self.frames.extend(fields.iter().rev().copied().map(value));
                        self.frames.push(value_type(*datatype));
                    },
                    | Value::Record(ref fields) => self
                        .frames
                        .extend(fields.values().rev().copied().map(value)),
                    | _ => return Err(Refusal::MachineInvariant),
                }
            },
            | CoreNode::Term(TermNode::Computation(at)) => {
                match *(self.arena.computation(at).ok_or(dangling)?) {
                    | Computation::DataCase {
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
                    | Computation::RecordProjection(ref record, _) => {
                        self.frames.push(value(*record));
                    },
                    | _ => return Err(Refusal::MachineInvariant),
                }
            },
            | CoreNode::Type(TypeNode::Value(at)) => {
                match *(self.arena.value_type(at).ok_or(dangling)?) {
                    | ValueType::Data { ref arguments, .. } => self
                        .frames
                        .extend(arguments.iter().rev().copied().map(value)),
                    | ValueType::Record(ref fields) => self
                        .frames
                        .extend(fields.values().rev().copied().map(value_type)),
                    | _ => return Err(Refusal::MachineInvariant),
                }
            },
            | CoreNode::Type(TypeNode::Computation(_)) => return Err(Refusal::MachineInvariant),
        }
        match self.frames.pop() {
            | Some(Frame::NativeNext(child)) => Ok(Step::Descend(child)),
            | Some(Frame::NativeBuild(node)) => self.finish_native(target, node),
            | _ => Err(Refusal::MachineInvariant),
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
            | Some(&Image::Erased(image)) => Ok(image),
            | _ => Err(Refusal::MachineInvariant),
        };
        let value_type = |at| match memo.value_types.get(&at) {
            | Some(&Image::Erased(image)) => Ok(image),
            | _ => Err(Refusal::MachineInvariant),
        };
        let computation = |at| match memo.computations.get(&at) {
            | Some(&Image::Erased(image)) => Ok(image),
            | _ => Err(Refusal::MachineInvariant),
        };
        let comp_type = |at| match memo.comp_types.get(&at) {
            | Some(&Image::Erased(image)) => Ok(image),
            | _ => Err(Refusal::MachineInvariant),
        };
        let dangling = Refusal::DanglingNode { node: root };
        match root {
            | CoreNode::Term(TermNode::Value(at)) => {
                let image = match *(self.arena.value(at).ok_or(dangling)?) {
                    | Value::Constructor {
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
                    | Value::Record(ref fields) => {
                        let fields = fields
                            .iter()
                            .map(|(label, &field)| value(field).map(|image| (label.clone(), image)))
                            .collect::<Result<_, _>>()?;
                        target.value_record(fields)
                    },
                    | _ => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_value(at, image))
            },
            | CoreNode::Term(TermNode::Computation(at)) => {
                let image = match *(self.arena.computation(at).ok_or(dangling)?) {
                    | Computation::DataCase {
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
                    | Computation::RecordProjection(ref record, ref label) => {
                        target.computation_record_projection(value(*record)?, label.clone())
                    },
                    | _ => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_computation(at, image))
            },
            | CoreNode::Type(TypeNode::Value(at)) => {
                let image = match *(self.arena.value_type(at).ok_or(dangling)?) {
                    | ValueType::Data {
                        ref declaration,
                        ref arguments,
                    } => {
                        let position = self.positions.admitted.get(declaration).copied().ok_or(
                            Refusal::WithheldData {
                                at,
                                constant: *declaration,
                            },
                        )?;
                        let arguments = arguments
                            .iter()
                            .copied()
                            .map(value)
                            .collect::<Result<_, _>>()?;
                        target.value_type_data(position, arguments)
                    },
                    | ValueType::Record(ref fields) => {
                        let fields = fields
                            .iter()
                            .map(|(label, &field)| {
                                value_type(field).map(|image| (label.clone(), image))
                            })
                            .collect::<Result<_, _>>()?;
                        target.value_type_record(fields)
                    },
                    | _ => return Err(Refusal::MachineInvariant),
                };
                Ok(self.erased_value_type(at, image))
            },
            | CoreNode::Type(TypeNode::Computation(_)) => Err(Refusal::MachineInvariant),
        }
    }
}
