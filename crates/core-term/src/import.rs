//! Graph-preserving imports of type annotations into a different core arena.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;

use crate::CompType;
use crate::CompTypeId;
use crate::Computation;
use crate::ComputationId;
use crate::CoreArena;
use crate::SplitMotive;
use crate::Value;
use crate::ValueId;
use crate::ValueType;
use crate::ValueTypeId;

/// An annotation graph contains an unresolved child.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ImportFault;

/// A family-tagged handle in either arena.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Node
{
    /// A value handle.
    Value(ValueId),
    /// A computation handle.
    Computation(ComputationId),
    /// A value-type handle.
    ValueType(ValueTypeId),
    /// A computation-type handle.
    CompType(CompTypeId),
}

/// One owned node whose child handles can be relocated.
#[derive(Debug)]
enum Image
{
    /// A value node.
    Value(Value),
    /// A computation node.
    Computation(Computation),
    /// A value-type node.
    ValueType(ValueType),
    /// A computation-type node.
    CompType(CompType),
}

/// A mutable, family-tagged child handle.
enum Edge<'node>
{
    /// A value child.
    Value(&'node mut ValueId),
    /// A computation child.
    Computation(&'node mut ComputationId),
    /// A value-type child.
    ValueType(&'node mut ValueTypeId),
    /// A computation-type child.
    CompType(&'node mut CompTypeId),
}

impl Edge<'_>
{
    /// Read the child before relocation.
    ///
    /// # Specification
    /// trivial.
    fn node(&self) -> Node
    {
        match *self {
            Self::Value(ref id) => Node::Value(**id),
            Self::Computation(ref id) => Node::Computation(**id),
            Self::ValueType(ref id) => Node::ValueType(**id),
            Self::CompType(ref id) => Node::CompType(**id),
        }
    }

    /// Replace a child with the imported handle of the same family.
    ///
    /// # Specification
    /// - ensures: success replaces this edge by the given handle.
    /// - fails: a different handle family leaves the edge unchanged.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — annotation imports preserve type-to-value-to-type
    ///   edges.
    /// - witness: `import::tests::dependent_annotations_preserve_sharing_across_arenas`
    /// - witness: `import::tests::an_imported_endpoint_maps_every_stack_frame_move_and_clause`
    #[spec(ensures: |ret| ret.is_err() || self.node() == image)]
    fn replace(
        &mut self,
        image: Node,
    ) -> Result<(), ImportFault>
    {
        match (&mut *self, image) {
            (&mut Self::Value(ref mut id), Node::Value(image)) => **id = image,
            (&mut Self::Computation(ref mut id), Node::Computation(image)) => **id = image,
            (&mut Self::ValueType(ref mut id), Node::ValueType(image)) => **id = image,
            (&mut Self::CompType(ref mut id), Node::CompType(image)) => **id = image,
            _ => return Err(ImportFault),
        }
        Ok(())
    }
}

impl Image
{
    /// Borrow all immediate children without a per-node allocation.
    ///
    /// # Specification
    /// trivial.
    fn edges(&mut self) -> [Option<Edge<'_>>; 5]
    {
        use Edge::CompType as CT;
        use Edge::Computation as C;
        use Edge::Value as V;
        use Edge::ValueType as VT;
        match *self {
            Self::Value(Value::Constructor {
                ref mut datatype, ..
            }) => [Some(VT(datatype)), None, None, None, None],
            Self::Computation(Computation::DataCase {
                ref mut scrutinee,
                ref mut motive,
                ..
            }) => [Some(V(scrutinee)), Some(CT(motive)), None, None, None],
            Self::Computation(
                Computation::RecordProjection(ref mut record, _)
                | Computation::TupleProjection(ref mut record, _),
            ) => [Some(V(record)), None, None, None, None],
            Self::Value(Value::Record(_) | Value::Tuple(_) | Value::Recorded(_))
            | Self::ValueType(ValueType::Data { .. } | ValueType::Record(_)) => {
                [None, None, None, None, None]
            },
            Self::Value(
                Value::Variable { .. }
                | Value::Constant(_)
                | Value::Literal(_)
                | Value::ListNil
                | Value::Reify(_)
                | Value::Hole(_),
            )
            | Self::Computation(
                Computation::Hole(_)
                | Computation::Session(_)
                | Computation::Memory(_)
                | Computation::World(_),
            )
            | Self::ValueType(
                ValueType::Base(_)
                | ValueType::Product(_)
                | ValueType::Sum(_)
                | ValueType::Universe { .. }
                | ValueType::Abstract(_)
                | ValueType::Capability { .. }
                | ValueType::Unknown
                | ValueType::Session(_)
                | ValueType::World(_),
            )
            | Self::CompType(CompType::Unknown) => [None, None, None, None, None],
            Self::ValueType(ValueType::Stack {
                input: ref mut first,
                output: ref mut second,
            })
            | Self::CompType(CompType::With(ref mut first, ref mut second)) => {
                [Some(CT(first)), Some(CT(second)), None, None, None]
            },
            Self::Computation(
                Computation::Handle {
                    subject: ref mut first,
                    on_return: ref mut second,
                    ..
                }
                | Computation::Scope {
                    subject: ref mut first,
                    on_return: ref mut second,
                    ..
                }
                | Computation::With(ref mut first, ref mut second)
                | Computation::Bind(ref mut first, ref mut second),
            ) => [Some(C(first)), Some(C(second)), None, None, None],
            Self::Computation(Computation::Ascribe {
                ref mut body,
                ref mut ty,
            }) => [Some(C(body)), Some(CT(ty)), None, None, None],
            Self::Computation(Computation::Split {
                ref mut scrutinee,
                motive: SplitMotive::Scrutinee(ref mut motive),
                ref mut body,
                ..
            }) => [
                Some(V(scrutinee)),
                Some(CT(motive)),
                Some(C(body)),
                None,
                None,
            ],
            Self::Computation(
                Computation::Resume(ref mut stack, ref mut body)
                | Computation::Split {
                    scrutinee: ref mut stack,
                    ref mut body,
                    ..
                },
            ) => [Some(V(stack)), Some(C(body)), None, None, None],
            Self::Value(
                Value::Primitive { ref mut body, .. }
                | Value::Thunk(ref mut body)
                | Value::Returned(ref mut body)
                | Value::Nested(ref mut body)
                | Value::Run(ref mut body),
            )
            | Self::Computation(
                Computation::Lambda(ref mut body)
                | Computation::Fixpoint { ref mut body, .. }
                | Computation::Reset(ref mut body)
                | Computation::Shift(ref mut body)
                | Computation::Project(_, ref mut body)
                | Computation::Mark { ref mut body, .. },
            ) => [Some(C(body)), None, None, None, None],
            Self::Value(
                Value::PathRefl(ref mut body)
                | Value::Here(ref mut body)
                | Value::Stay(ref mut body)
                | Value::Forward(ref mut body)
                | Value::Injection(_, ref mut body)
                | Value::Lift { ref mut body, .. }
                | Value::StaticLambda(ref mut body)
                | Value::Mark { ref mut body, .. },
            )
            | Self::Computation(
                Computation::Return(ref mut body)
                | Computation::Force(ref mut body)
                | Computation::Perform {
                    payload: ref mut body,
                    ..
                },
            )
            | Self::ValueType(
                ValueType::Element {
                    code: ref mut body, ..
                }
                | ValueType::Run(ref mut body),
            )
            | Self::CompType(CompType::Element {
                code: ref mut body, ..
            }) => [Some(V(body)), None, None, None, None],
            Self::Value(
                Value::PathProduct(ref mut first, ref mut second)
                | Value::Funext(ref mut first, ref mut second)
                | Value::Equiv(ref mut first, ref mut second)
                | Value::Then(ref mut first, ref mut second)
                | Value::FlowProduct(ref mut first, ref mut second)
                | Value::FunctionFlow(ref mut first, ref mut second)
                | Value::SessionRelated {
                    source: ref mut first,
                    target: ref mut second,
                    ..
                }
                | Value::Ua {
                    forward: ref mut first,
                    backward: ref mut second,
                    ..
                }
                | Value::ListCons(ref mut first, ref mut second)
                | Value::StaticApplication(ref mut first, ref mut second),
            )
            | Self::Computation(
                Computation::Transport(ref mut first, ref mut second)
                | Computation::Exercise {
                    capability: ref mut first,
                    payload: ref mut second,
                    ..
                },
            )
            | Self::ValueType(ValueType::PathUniverse(ref mut first, ref mut second)) => {
                [Some(V(first)), Some(V(second)), None, None, None]
            },
            Self::Value(Value::PathEquiv {
                ref mut path_type,
                ref mut forward,
                ref mut backward,
                ..
            }) => [
                Some(VT(path_type)),
                Some(V(forward)),
                Some(V(backward)),
                None,
                None,
            ],
            Self::Computation(
                Computation::PathTransport {
                    ref mut motive,
                    ref mut path,
                    ref mut value,
                }
                | Computation::Ride {
                    ref mut motive,
                    flow: ref mut path,
                    ref mut value,
                },
            ) => [Some(VT(motive)), Some(V(path)), Some(V(value)), None, None],
            Self::Computation(Computation::TelescopeTransport {
                ref mut motive,
                ref mut path,
                ref mut start,
                ref mut over,
                ref mut value,
            }) => [
                Some(CT(motive)),
                Some(V(path)),
                Some(V(start)),
                Some(V(over)),
                Some(V(value)),
            ],
            Self::ValueType(
                ValueType::Path {
                    ref mut carrier,
                    ref mut left,
                    ref mut right,
                }
                | ValueType::Flow {
                    ref mut carrier,
                    source: ref mut left,
                    target: ref mut right,
                },
            ) => [Some(VT(carrier)), Some(V(left)), Some(V(right)), None, None],
            Self::Value(Value::Quote(ref mut ty))
            | Self::ValueType(
                ValueType::List(ref mut ty)
                | ValueType::Lift {
                    inner: ref mut ty, ..
                }
                | ValueType::Staged {
                    base: ref mut ty, ..
                },
            )
            | Self::CompType(CompType::Returner {
                result: ref mut ty, ..
            }) => [Some(VT(ty)), None, None, None, None],
            Self::Value(Value::QuoteComputation(ref mut ty))
            | Self::ValueType(ValueType::Thunk(ref mut ty)) => {
                [Some(CT(ty)), None, None, None, None]
            },
            Self::Computation(Computation::Primitive {
                ref mut arguments, ..
            }) => match *arguments {
                crate::primitive::Arguments::Unary(ref mut value) => {
                    [Some(V(value)), None, None, None, None]
                },
                crate::primitive::Arguments::Binary([ref mut first, ref mut second]) => {
                    [Some(V(first)), Some(V(second)), None, None, None]
                },
            },
            Self::Computation(Computation::Application(ref mut head, ref mut argument)) => {
                [Some(C(head)), Some(V(argument)), None, None, None]
            },
            Self::Computation(Computation::Case {
                ref mut scrutinee, ..
            }) => [Some(V(scrutinee)), None, None, None, None],
            Self::Computation(Computation::ListFold {
                ref mut element,
                ref mut result,
                ref mut list,
                ref mut on_nil,
                ref mut on_cons,
            }) => [
                Some(VT(element)),
                Some(VT(result)),
                Some(V(list)),
                Some(C(on_nil)),
                Some(C(on_cons)),
            ],
            Self::ValueType(
                ValueType::StaticPi {
                    domain: ref mut first,
                    codomain: ref mut second,
                }
                | ValueType::Sigma {
                    ref mut first,
                    ref mut second,
                },
            ) => [Some(VT(first)), Some(VT(second)), None, None, None],
            Self::CompType(
                CompType::Arrow {
                    ref mut domain,
                    ref mut codomain,
                }
                | CompType::Pi {
                    ref mut domain,
                    ref mut codomain,
                },
            ) => [Some(VT(domain)), Some(CT(codomain)), None, None, None],
        }
    }
}

/// One iterative postorder step.
#[derive(Debug)]
enum Task
{
    /// Import a node unless it already has an image.
    Open(Node),
    /// Relocate a node after its children have images.
    Close(Node, Image),
}

/// Imports reachable annotations, preserving sharing between successive roots.
///
/// No source handle escapes into the destination. Binder indices, constants,
/// literal payloads and replay evidence are preserved; only arena ids change.
/// Source and destination must therefore use the same declaration and binder
/// context. Dropping this importer or either arena is independent of term
/// depth.
#[derive(Debug)]
pub struct TypeImporter<'source, 'target>
{
    /// The source annotation arena.
    source: &'source CoreArena,
    /// The receiving annotation arena.
    target: &'target mut CoreArena,
    /// Imported nodes, shared by every requested root.
    images: BTreeMap<Node, Node>,
    /// The explicit postorder stack.
    pending: Vec<Task>,
}

impl<'source, 'target> TypeImporter<'source, 'target>
{
    /// Start an import session between distinct arenas.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn new(
        source: &'source CoreArena,
        target: &'target mut CoreArena,
    ) -> Self
    {
        Self {
            source,
            target,
            images: BTreeMap::new(),
            pending: Vec::new(),
        }
    }

    /// The image of the source computation type `source`, when an import of
    /// this session copied it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the target node the importer relocated `source` to; none when
    ///   no root imported so far reaches it.
    /// - provides: a side table keyed by source nodes, such as the names a
    ///   lowering keeps beside its dependent arrows, carried to the target.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependent arrow inside an imported annotation
    ///   answers its relocated node, and one no import reached answers none.
    /// - witness: `import::tests::an_imported_arrow_answers_its_image`
    #[spec(ensures: |ret| ret.is_none_or(|image| self.target.comp_type(image).is_some()))]
    #[inline]
    #[must_use]
    pub fn comp_type_image(
        &self,
        source: CompTypeId,
    ) -> Option<CompTypeId>
    {
        match self.images.get(&Node::CompType(source)) {
            Some(&Node::CompType(image)) => Some(image),
            Some(&(Node::Value(_) | Node::Computation(_) | Node::ValueType(_))) | None => None,
        }
    }

    /// The image of the source value type `source`, when an import of this
    /// session copied it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the target node the importer relocated `source` to; none when
    ///   no root imported so far reaches it.
    /// - provides: a side table keyed by source value types, such as the
    ///   relation a lowering records for a type written as one, carried to the
    ///   target.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an imported root and a value type inside it answer
    ///   their relocated nodes, and one no import reached answers none.
    /// - witness: `import::tests::an_imported_arrow_answers_its_image`
    #[spec(ensures: |ret| ret.is_none_or(|image| self.target.value_type(image).is_some()))]
    #[inline]
    #[must_use]
    pub fn value_type_image(
        &self,
        source: ValueTypeId,
    ) -> Option<ValueTypeId>
    {
        match self.images.get(&Node::ValueType(source)) {
            Some(&Node::ValueType(image)) => Some(image),
            Some(&(Node::Value(_) | Node::Computation(_) | Node::CompType(_))) | None => None,
        }
    }

    /// Copy a reachable value-type graph, retaining previous imported nodes.
    ///
    /// # Specification
    /// - requires: the same binder and declaration context in both arenas.
    /// - ensures: success returns a target-owned type with the source graph's
    ///   syntax and sharing; unrelated source nodes are not copied.
    /// - fails: an unresolved source edge or an inconsistent family image.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ImportFault` for an unresolved source edge. Already imported
    /// children remain reusable after a refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shared dependent annotation imported into a
    ///   nonempty arena must preserve its variable and must not retain source
    ///   handles.
    /// - witness: `import::tests::dependent_annotations_preserve_sharing_across_arenas`
    /// - witness: `import::tests::an_imported_endpoint_maps_every_stack_frame_move_and_clause`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|id| self.target.value_type(id).is_some()))]
    #[inline]
    pub fn value_type(
        &mut self,
        root: ValueTypeId,
    ) -> Result<ValueTypeId, ImportFault>
    {
        self.pending.clear();
        self.pending.push(Task::Open(Node::ValueType(root)));
        while let Some(task) = self.pending.pop() {
            match task {
                Task::Open(node) => {
                    if self.images.contains_key(&node) {
                        continue;
                    }
                    let mut image = match node {
                        Node::Value(id) => self.source.value(id).cloned().map(Image::Value),
                        Node::Computation(id) => {
                            self.source.computation(id).cloned().map(Image::Computation)
                        },
                        Node::ValueType(id) => {
                            self.source.value_type(id).cloned().map(Image::ValueType)
                        },
                        Node::CompType(id) => {
                            self.source.comp_type(id).cloned().map(Image::CompType)
                        },
                    }
                    .ok_or(ImportFault)?;
                    let children = image.edges().map(|edge| edge.map(|edge| edge.node()));
                    self.pending.push(Task::Close(node, image));
                    if let Node::CompType(id) = node
                        && let Some(ty) = self.source.comp_type(id)
                        && let CompType::Returner { ref effects, .. } = *ty
                    {
                        self.pending.extend(
                            effects
                                .types()
                                .rev()
                                .map(|ty| Task::Open(Node::ValueType(ty))),
                        );
                    }
                    match node {
                        Node::Value(id) => {
                            let value = self.source.value(id).ok_or(ImportFault)?;
                            match *value {
                                Value::Constructor { ref fields, .. } => self.pending.extend(
                                    fields
                                        .iter()
                                        .rev()
                                        .map(|&value| Task::Open(Node::Value(value))),
                                ),
                                Value::Record(ref fields) => self.pending.extend(
                                    fields
                                        .values()
                                        .rev()
                                        .map(|&value| Task::Open(Node::Value(value))),
                                ),
                                Value::Tuple(ref components) => self.pending.extend(
                                    components
                                        .iter()
                                        .rev()
                                        .map(|&value| Task::Open(Node::Value(value))),
                                ),
                                Value::Recorded(ref moves) => {
                                    self.pending.extend(moves.iter().rev().filter_map(
                                        |movement| match movement.payload() {
                                            quenchant_shape::shape::Maybe::Present(value) => {
                                                Some(Task::Open(Node::Value(value)))
                                            },
                                            quenchant_shape::shape::Maybe::Absent(_) => None,
                                        },
                                    ));
                                },
                                Value::Reify(ref frames) => {
                                    self.pending.extend(frames.iter().rev().filter_map(|frame| {
                                        match *frame {
                                            crate::control::StackFrame::Apply(value) => {
                                                Some(Task::Open(Node::Value(value)))
                                            },
                                            crate::control::StackFrame::Bind(body) => {
                                                Some(Task::Open(Node::Computation(body)))
                                            },
                                            crate::control::StackFrame::Project(_) => None,
                                        }
                                    }));
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
                                | Value::Mark { .. } => {},
                            }
                        },
                        Node::Computation(id) => {
                            let computation = self.source.computation(id).ok_or(ImportFault)?;
                            match *computation {
                                Computation::Case { ref branches, .. } => {
                                    self.pending.extend(
                                        branches
                                            .iter()
                                            .rev()
                                            .map(|&body| Task::Open(Node::Computation(body))),
                                    );
                                },
                                Computation::DataCase { ref branches, .. } => {
                                    self.pending.extend(
                                        branches
                                            .iter()
                                            .rev()
                                            .map(|&body| Task::Open(Node::Computation(body))),
                                    );
                                },
                                Computation::Perform { ref signature, .. }
                                | Computation::Exercise { ref signature, .. } => {
                                    self.pending.extend(
                                        signature
                                            .types()
                                            .rev()
                                            .map(|ty| Task::Open(Node::ValueType(ty))),
                                    );
                                },
                                Computation::Handle {
                                    ref signature,
                                    ref clauses,
                                    ..
                                }
                                | Computation::Scope {
                                    ref signature,
                                    ref clauses,
                                    ..
                                } => {
                                    self.pending.extend(
                                        signature
                                            .types()
                                            .rev()
                                            .map(|ty| Task::Open(Node::ValueType(ty))),
                                    );
                                    self.pending.extend(
                                        clauses.iter().rev().map(|clause| {
                                            Task::Open(Node::Computation(clause.body))
                                        }),
                                    );
                                },
                                Computation::Session(ref action) => {
                                    self.pending.extend(
                                        action
                                            .value_types()
                                            .map(|ty| Task::Open(Node::ValueType(ty)))
                                            .chain(
                                                action
                                                    .values()
                                                    .map(|value| Task::Open(Node::Value(value))),
                                            )
                                            .chain(
                                                action.computations().map(|body| {
                                                    Task::Open(Node::Computation(body))
                                                }),
                                            ),
                                    );
                                },
                                Computation::Memory(ref form) => {
                                    self.pending.extend(
                                        form.values()
                                            .map(|value| Task::Open(Node::Value(value)))
                                            .chain(
                                                form.computations().map(|body| {
                                                    Task::Open(Node::Computation(body))
                                                }),
                                            ),
                                    );
                                },
                                Computation::World(ref form) => {
                                    self.pending.extend(
                                        form.values()
                                            .map(|value| Task::Open(Node::Value(value)))
                                            .chain(
                                                form.computations().map(|body| {
                                                    Task::Open(Node::Computation(body))
                                                }),
                                            ),
                                    );
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
                                | Computation::Ascribe { .. }
                                | Computation::Force(_)
                                | Computation::Split { .. }
                                | Computation::RecordProjection(..)
                                | Computation::TupleProjection(..)
                                | Computation::Hole(_)
                                | Computation::Mark { .. }
                                | Computation::ListFold { .. }
                                | Computation::Resume(..)
                                | Computation::Reset(_)
                                | Computation::Shift(_)
                                | Computation::With(..)
                                | Computation::Project(..) => {},
                            }
                        },
                        Node::ValueType(id) => {
                            let ty = self.source.value_type(id).ok_or(ImportFault)?;
                            match *ty {
                                ValueType::Data { ref arguments, .. } => self.pending.extend(
                                    arguments
                                        .iter()
                                        .rev()
                                        .map(|&value| Task::Open(Node::Value(value))),
                                ),
                                ValueType::Record(ref fields) => self.pending.extend(
                                    fields
                                        .values()
                                        .rev()
                                        .map(|&ty| Task::Open(Node::ValueType(ty))),
                                ),
                                ValueType::Product(ref components)
                                | ValueType::Sum(ref components) => self.pending.extend(
                                    components
                                        .iter()
                                        .rev()
                                        .map(|&ty| Task::Open(Node::ValueType(ty))),
                                ),
                                ValueType::Session(ref session) => self.pending.extend(
                                    session
                                        .payloads()
                                        .iter()
                                        .rev()
                                        .map(|&ty| Task::Open(Node::ValueType(ty))),
                                ),
                                ValueType::World(ref ty) => self
                                    .pending
                                    .extend(ty.types().map(|ty| Task::Open(Node::ValueType(ty)))),
                                ValueType::Capability { ref authority, .. } => {
                                    self.pending.extend(
                                        authority
                                            .types()
                                            .rev()
                                            .map(|ty| Task::Open(Node::ValueType(ty))),
                                    );
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
                                | ValueType::Staged { .. }
                                | ValueType::StaticPi { .. }
                                | ValueType::Unknown
                                | ValueType::Stack { .. } => {},
                            }
                        },
                        Node::CompType(_) => {},
                    }
                    self.pending
                        .extend(children.into_iter().flatten().rev().map(Task::Open));
                },
                Task::Close(node, mut image) => {
                    for mut edge in image.edges().into_iter().flatten() {
                        let image = *self.images.get(&edge.node()).ok_or(ImportFault)?;
                        edge.replace(image)?;
                    }
                    if let Image::CompType(CompType::Returner {
                        ref mut effects, ..
                    }) = image
                    {
                        *effects =
                            effects.try_map_types(crate::effect::TypeOrder::Forward, |ty| {
                                match self.images.get(&Node::ValueType(ty)) {
                                    Some(&Node::ValueType(image)) => Ok(image),
                                    _ => Err(ImportFault),
                                }
                            })?;
                    }
                    let map_type = |ty| match self.images.get(&Node::ValueType(ty)) {
                        Some(&Node::ValueType(mapped)) => Ok(mapped),
                        _ => Err(ImportFault),
                    };
                    let map_value = |value| match self.images.get(&Node::Value(value)) {
                        Some(&Node::Value(mapped)) => Ok(mapped),
                        _ => Err(ImportFault),
                    };
                    let map_computation = |body| match self.images.get(&Node::Computation(body)) {
                        Some(&Node::Computation(mapped)) => Ok(mapped),
                        _ => Err(ImportFault),
                    };
                    match image {
                        Image::Value(Value::Constructor { ref mut fields, .. })
                        | Image::ValueType(ValueType::Data {
                            arguments: ref mut fields,
                            ..
                        }) => {
                            for value in fields {
                                *value = map_value(*value)?;
                            }
                        },
                        Image::Value(Value::Record(ref mut fields)) => {
                            for value in fields.values_mut() {
                                *value = map_value(*value)?;
                            }
                        },
                        Image::Value(Value::Tuple(ref mut components)) => {
                            for value in components.iter_mut() {
                                *value = map_value(*value)?;
                            }
                        },
                        Image::ValueType(ValueType::Record(ref mut fields)) => {
                            for ty in fields.values_mut() {
                                *ty = map_type(*ty)?;
                            }
                        },
                        Image::ValueType(
                            ValueType::Product(ref mut components)
                            | ValueType::Sum(ref mut components),
                        ) => {
                            for ty in components.iter_mut() {
                                *ty = map_type(*ty)?;
                            }
                        },
                        Image::Computation(Computation::DataCase {
                            ref mut branches, ..
                        }) => {
                            for body in branches {
                                *body = map_computation(*body)?;
                            }
                        },
                        Image::Computation(Computation::Case {
                            ref mut branches, ..
                        }) => {
                            for body in branches.iter_mut() {
                                *body = map_computation(*body)?;
                            }
                        },
                        Image::Value(Value::Reify(ref mut frames)) => {
                            for index in 0 .. frames.len() {
                                let original = *frames.get(index).ok_or(ImportFault)?;
                                let mapped = match original {
                                    crate::control::StackFrame::Apply(value) => {
                                        match self.images.get(&Node::Value(value)) {
                                            Some(&Node::Value(mapped)) => {
                                                crate::control::StackFrame::Apply(mapped)
                                            },
                                            _ => return Err(ImportFault),
                                        }
                                    },
                                    crate::control::StackFrame::Bind(body) => {
                                        match self.images.get(&Node::Computation(body)) {
                                            Some(&Node::Computation(mapped)) => {
                                                crate::control::StackFrame::Bind(mapped)
                                            },
                                            _ => return Err(ImportFault),
                                        }
                                    },
                                    crate::control::StackFrame::Project(side) => {
                                        crate::control::StackFrame::Project(side)
                                    },
                                };
                                if mapped != original {
                                    *alloc::sync::Arc::make_mut(frames)
                                        .get_mut(index)
                                        .ok_or(ImportFault)? = mapped;
                                }
                            }
                        },
                        Image::Value(Value::Recorded(ref mut moves)) => {
                            for index in 0 .. moves.len() {
                                let original = moves.get(index).ok_or(ImportFault)?;
                                let quenchant_shape::shape::Maybe::Present(payload) =
                                    original.payload()
                                else {
                                    continue;
                                };
                                let mapped = map_value(payload)?;
                                if mapped != payload {
                                    let moved = original.carrying(mapped);
                                    *alloc::sync::Arc::make_mut(moves)
                                        .get_mut(index)
                                        .ok_or(ImportFault)? = moved;
                                }
                            }
                        },
                        Image::Computation(
                            Computation::Perform {
                                ref mut signature, ..
                            }
                            | Computation::Exercise {
                                ref mut signature, ..
                            },
                        ) => {
                            *signature = signature
                                .try_map_types(crate::effect::TypeOrder::Forward, map_type)?;
                        },
                        Image::Computation(
                            Computation::Handle {
                                ref mut signature,
                                ref mut clauses,
                                ..
                            }
                            | Computation::Scope {
                                ref mut signature,
                                ref mut clauses,
                                ..
                            },
                        ) => {
                            *signature = signature
                                .try_map_types(crate::effect::TypeOrder::Forward, map_type)?;
                            for index in 0 .. clauses.len() {
                                let body = clauses.get(index).ok_or(ImportFault)?.body;
                                let Some(&Node::Computation(mapped)) =
                                    self.images.get(&Node::Computation(body))
                                else {
                                    return Err(ImportFault);
                                };
                                if mapped != body {
                                    alloc::sync::Arc::make_mut(clauses)
                                        .get_mut(index)
                                        .ok_or(ImportFault)?
                                        .body = mapped;
                                }
                            }
                        },
                        Image::Computation(Computation::Session(ref mut action)) => {
                            *action = action.try_map(
                                crate::session::ChildOrder::Forward,
                                &mut (),
                                |&mut (), value| map_value(value),
                                |&mut (), body| map_computation(body),
                                |&mut (), ty| map_type(ty),
                            )?;
                        },
                        Image::Computation(Computation::Memory(ref mut form)) => {
                            *form = form.try_map(
                                crate::session::ChildOrder::Forward,
                                &mut (),
                                |&mut (), value| map_value(value),
                                |&mut (), body| map_computation(body),
                            )?;
                        },
                        Image::Computation(Computation::World(ref mut form)) => {
                            *form = form.try_map(
                                crate::session::ChildOrder::Forward,
                                &mut (),
                                |&mut (), value| map_value(value),
                                |&mut (), body| map_computation(body),
                            )?;
                        },
                        Image::ValueType(ValueType::Session(ref mut session)) => {
                            *session = session
                                .try_map_payloads(crate::session::ChildOrder::Forward, map_type)?;
                        },
                        Image::ValueType(ValueType::World(ref mut ty)) => {
                            *ty = ty.try_map(map_type)?;
                        },
                        Image::ValueType(ValueType::Capability {
                            ref mut authority, ..
                        }) => {
                            *authority = authority
                                .try_map_types(crate::effect::TypeOrder::Forward, map_type)?;
                        },
                        Image::Value(_)
                        | Image::Computation(_)
                        | Image::ValueType(_)
                        | Image::CompType(_) => {},
                    }
                    let copied = match image {
                        Image::Value(value) => Node::Value(self.target.alloc_value(value)),
                        Image::Computation(comp) => {
                            Node::Computation(self.target.alloc_computation(comp))
                        },
                        Image::ValueType(ty) => Node::ValueType(self.target.alloc_value_type(ty)),
                        Image::CompType(ty) => Node::CompType(self.target.alloc_comp_type(ty)),
                    };
                    let _previous = self.images.insert(node, copied);
                },
            }
        }
        match self.images.get(&Node::ValueType(root)) {
            Some(&Node::ValueType(image)) => Ok(image),
            _ => Err(ImportFault),
        }
    }
}

#[cfg(test)]
mod tests;
