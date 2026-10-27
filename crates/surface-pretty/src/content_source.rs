//! A checkpoint's content table as the printer's source.
//!
//! The incremental checker hands a checked item's signature and a synthesised
//! item's type back as [`ContentNode`] tables. A [`ContentSource`] reads such
//! a table as a [`Source`], naming a constant or an abstract type by its item
//! key, so [`present_type`](crate::present_type) lays it out in the one
//! spelling every face shows, writing `?` wherever a node has no surface
//! spelling.

use anodized::spec;
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::NodeIndex;
use gandr_core_incremental::Reference;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::session::SessionAction;
use quenchant_shape::shape::Maybe;

use crate::Constructors;
use crate::FamilyKey;
use crate::Name;
use crate::Source;
use crate::former::Arity;
use crate::former::Component;
use crate::former::Former;
use crate::former::Unreadable;

/// A checkpoint's content table, read by the presentation printer, its
/// constructors named from a table.
#[derive(Clone, Copy, Debug)]
pub struct ContentSource<'nodes>
{
    /// The table.
    nodes: &'nodes [ContentNode],
    /// The constructors' names, by family.
    constructors: Option<&'nodes Constructors<'nodes>>,
}

impl<'nodes> From<&'nodes [ContentNode]> for ContentSource<'nodes>
{
    /// The source reading `nodes`, naming no constructor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nodes: &'nodes [ContentNode]) -> Self
    {
        Self {
            nodes,
            constructors: None,
        }
    }
}

impl<'nodes> ContentSource<'nodes>
{
    /// This source, naming constructors from `constructors`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn naming(
        self,
        constructors: &'nodes Constructors<'nodes>,
    ) -> Self
    {
        Self {
            constructors: Some(constructors),
            ..self
        }
    }
}

/// The name `reference` carries.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the item key's text when the reference names an item whose key is
///   UTF-8; none for an unoccupied position and for a key that is not text.
/// - provides: the constant, abstract-type and family readings.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an abstract type by its key, a key spelled with `?`, and
///   an unoccupied position are each asserted at their exact spelling.
/// - witness: `content_source::tests::value_ty_covers_every_reachable_former`
/// - witness: `content_source::tests::fidelity_tracks_unsupported_nodes_not_user_punctuation`
#[spec(ensures: |ret| match *reference {
    Reference::Unoccupied => ret.is_none(),
    Reference::Item { ref key, .. } => ret == core::str::from_utf8(key.as_ref()).ok().map(Name::from),
})]
fn key(reference: &Reference) -> Option<Name<'_>>
{
    match *reference {
        Reference::Item { ref key, .. } => core::str::from_utf8(key.as_ref()).ok().map(Name::from),
        Reference::Unoccupied => None,
    }
}

impl Source for ContentSource<'_>
{
    type Node = NodeIndex;

    /// The content node at `node`, as the printer reads it.
    ///
    /// # Specification
    /// - requires: nothing; any index is admissible.
    /// - ensures: each core former read as its [`Former`], over the same
    ///   indices; a family by its key, a constructor by the name the
    ///   constructor table gives its family's tag; the honest set's members — a
    ///   hole, a mark, the unknown type, a lift — as unreadable, an unresolved
    ///   node and an index past the table as dangling, and a name the table
    ///   cannot spell as unnamed.
    /// - provides: the printer's input over checkpoint tables.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every value-type and computation-type former the
    ///   fragment writes, a former over the wrong polarity, an unresolved node,
    ///   a dangling index and a cycle are each asserted at their exact
    ///   spelling.
    /// - witness: `content_source::tests::value_ty_covers_every_reachable_former`
    /// - witness: `content_source::tests::comp_ty_covers_every_reachable_former`
    /// - witness: `content_source::tests::ty_dispatches_on_polarity`
    /// - witness: `content_source::tests::a_malformed_table_spells_unknown`
    /// - witness: `content_source::tests::an_empty_tuple_or_record_reads_as_the_unit_and_a_full_one_by_its_arity`
    #[spec(ensures: |ret| match (self.nodes.get(usize::from(node)), ret) {
        (None, Former::Unreadable(reason)) => reason == Unreadable::Dangling,
        (None, _) => false,
        (Some(content), Former::Unreadable(reason)) => match *content {
            ContentNode::Unresolved(_) => reason == Unreadable::Dangling,
            ContentNode::Hole(_) | ContentNode::ComputationHole(_) => reason == Unreadable::Hole,
            ContentNode::ValueMark { .. } | ContentNode::ComputationMark { .. } => reason == Unreadable::Mark,
            ContentNode::UnknownType | ContentNode::UnknownComputationType => reason == Unreadable::UnknownType,
            ContentNode::ValueLift { .. } | ContentNode::TypeLift { .. } => reason == Unreadable::Lift,
            ContentNode::Constant(ref reference) | ContentNode::Abstract(ref reference) => reason == Unreadable::Unnamed && key(reference).is_none(),
            ContentNode::BufferType | ContentNode::RowKind | ContentNode::RowTail(_) | ContentNode::RowValue(_) | ContentNode::WebType | ContentNode::DialogueType(_) | ContentNode::Dialogue(_) | ContentNode::Web(_) | ContentNode::Decompose(_) | ContentNode::Univalence(..) | ContentNode::ListCase { .. } | ContentNode::Abandon(_) | ContentNode::RecordUpdate(..) |
            ContentNode::Data { .. } | ContentNode::RecordType(_) | ContentNode::Constructor { .. } | ContentNode::Record(_) | ContentNode::DataCase { .. } | ContentNode::RecordProjection(..) | ContentNode::TupleProjection(..) | ContentNode::Reify(_) | ContentNode::Stack { .. } | ContentNode::WithType(..) | ContentNode::Perform { .. } | ContentNode::Handle { .. } | ContentNode::Exercise { .. } | ContentNode::Scope { .. } | ContentNode::Capability { .. } | ContentNode::Resume(..) | ContentNode::Split(..) | ContentNode::DependentSplit { .. } | ContentNode::Reset(_) | ContentNode::Shift(_) | ContentNode::With(..) | ContentNode::Ascribe { .. } | ContentNode::ValueAscribe { .. } | ContentNode::Project(..) | ContentNode::PrimitiveValue(_) | ContentNode::Primitive(..) | ContentNode::PathUniverse(..) | ContentNode::PathRefl(_) | ContentNode::PathProduct(..) | ContentNode::Funext(..) | ContentNode::Equiv(..) | ContentNode::Ua { .. } | ContentNode::PathEquiv { .. } | ContentNode::Transport(..) | ContentNode::PathType { .. } | ContentNode::Here(_) | ContentNode::Returned(_) | ContentNode::Nested(_) | ContentNode::Run(_) | ContentNode::ElementTransport { .. } | ContentNode::TelescopeTransport { .. } | ContentNode::SessionRelated { .. } | ContentNode::Stay(_) | ContentNode::Then(..) | ContentNode::Forward(_) | ContentNode::FunctionFlow(..) | ContentNode::FlowProduct(..) | ContentNode::Recorded(_) | ContentNode::Ride { .. } | ContentNode::FlowType { .. } | ContentNode::RunType(_) | ContentNode::PrefixType(_) | ContentNode::Variable { .. } | ContentNode::Literal(_) | ContentNode::Tuple(_) | ContentNode::ListNil | ContentNode::ListCons(..) | ContentNode::Injection(..) | ContentNode::Thunk(_) | ContentNode::Quote(_) | ContentNode::QuoteComputation(_) | ContentNode::StaticLambda(_) | ContentNode::StaticApplication(..) | ContentNode::Lambda(_) | ContentNode::Application(..) | ContentNode::Return(_) | ContentNode::Bind(..) | ContentNode::Force(_) | ContentNode::Case { .. } | ContentNode::Fixpoint { .. } | ContentNode::ListFold { .. } | ContentNode::Session(_) | ContentNode::Memory(_) | ContentNode::Base(_) | ContentNode::Product(_) | ContentNode::Sum(_) | ContentNode::List(_) | ContentNode::KeptType { .. } | ContentNode::ThunkType(_) | ContentNode::Universe { .. } | ContentNode::Element { .. } | ContentNode::StaticPi { .. } | ContentNode::Sigma { .. } | ContentNode::SessionType(_) | ContentNode::Returner { .. } | ContentNode::Arrow { .. } | ContentNode::Pi { .. } | ContentNode::ComputationElement { .. } => false,
        },
        (Some(&(ContentNode::Constant(ref reference) | ContentNode::Abstract(ref reference))), Former::Constant(name) | Former::Abstract(name)) => key(reference) == Some(name),
        (Some(content), Former::Data { name, .. }) =>
            matches!(*content, ContentNode::Data { ref declaration, .. } if key(declaration) == name),
        (Some(_), _) => true,
    })]
    #[inline]
    fn read(
        &self,
        node: NodeIndex,
    ) -> Former<'_, NodeIndex>
    {
        let Some(content) = self.nodes.get(usize::from(node))
        else {
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "an index past the table names no node: a malformed source, with no \
                              term to spell"
                )
            )]
            return Former::Unreadable(Unreadable::Dangling);
        };
        #[cfg_attr(
            dylint_lib = "quenchant_dylints",
            expect(
                answer_totality,
                reason = "a reference the table holds no key for: a malformed naming table, with \
                          no name to write"
            )
        )]
        let unnamed = Former::Unreadable(Unreadable::Unnamed);
        match *content {
            ContentNode::Reify(_) => Former::Reify,
            ContentNode::Stack { input, output } => Former::Stack(input, output),
            ContentNode::WithType(ref components) => Former::With(Arity::from(components.len())),
            ContentNode::PrimitiveValue(primitive) => {
                Former::Constant(Name::from(<&'static str>::from(primitive.name())))
            },
            ContentNode::Data {
                ref declaration,
                ref arguments,
            } => Former::Data {
                name: key(declaration),
                arity: Arity::from(arguments.len()),
            },
            ContentNode::Constructor {
                datatype,
                tag,
                ref fields,
            } => {
                let family = self
                    .nodes
                    .get(usize::from(datatype))
                    .and_then(|family| match *family {
                        ContentNode::Data {
                            ref declaration, ..
                        } => key(declaration),
                        ContentNode::RecordType(_)
                        | ContentNode::Constructor { .. }
                        | ContentNode::Record(_)
                        | ContentNode::DataCase { .. }
                        | ContentNode::RecordProjection(..)
                        | ContentNode::TupleProjection(..)
                        | ContentNode::Reify(_)
                        | ContentNode::Stack { .. }
                        | ContentNode::WithType(..)
                        | ContentNode::Perform { .. }
                        | ContentNode::Handle { .. }
                        | ContentNode::Exercise { .. }
                        | ContentNode::Scope { .. }
                        | ContentNode::Capability { .. }
                        | ContentNode::Resume(..)
                        | ContentNode::Abandon(_)
                        | ContentNode::Split(..)
                        | ContentNode::DependentSplit { .. }
                        | ContentNode::Reset(_)
                        | ContentNode::Shift(_)
                        | ContentNode::With(..)
                        | ContentNode::Ascribe { .. }
                        | ContentNode::ValueAscribe { .. }
                        | ContentNode::Project(..)
                        | ContentNode::PrimitiveValue(_)
                        | ContentNode::Primitive(..)
                        | ContentNode::PathUniverse(..)
                        | ContentNode::PathRefl(_)
                        | ContentNode::PathProduct(..)
                        | ContentNode::Funext(..)
                        | ContentNode::Equiv(..)
                        | ContentNode::Univalence(..)
                        | ContentNode::Ua { .. }
                        | ContentNode::PathEquiv { .. }
                        | ContentNode::Transport(..)
                        | ContentNode::PathType { .. }
                        | ContentNode::Here(_)
                        | ContentNode::Returned(_)
                        | ContentNode::Nested(_)
                        | ContentNode::Run(_)
                        | ContentNode::RecordUpdate(..)
                        | ContentNode::ElementTransport { .. }
                        | ContentNode::TelescopeTransport { .. }
                        | ContentNode::SessionRelated { .. }
                        | ContentNode::Stay(_)
                        | ContentNode::Then(..)
                        | ContentNode::Forward(_)
                        | ContentNode::FunctionFlow(..)
                        | ContentNode::FlowProduct(..)
                        | ContentNode::Recorded(_)
                        | ContentNode::Dialogue(_)
                        | ContentNode::Web(_)
                        | ContentNode::Decompose(_)
                        | ContentNode::Ride { .. }
                        | ContentNode::FlowType { .. }
                        | ContentNode::RunType(_)
                        | ContentNode::PrefixType(_)
                        | ContentNode::DialogueType(_)
                        | ContentNode::WebType
                        | ContentNode::Variable { .. }
                        | ContentNode::Constant(_)
                        | ContentNode::Literal(_)
                        | ContentNode::Tuple(_)
                        | ContentNode::ListNil
                        | ContentNode::ListCons(..)
                        | ContentNode::Injection(..)
                        | ContentNode::Thunk(_)
                        | ContentNode::ValueLift { .. }
                        | ContentNode::Quote(_)
                        | ContentNode::QuoteComputation(_)
                        | ContentNode::StaticLambda(_)
                        | ContentNode::StaticApplication(..)
                        | ContentNode::Hole(_)
                        | ContentNode::ValueMark { .. }
                        | ContentNode::Lambda(_)
                        | ContentNode::Application(..)
                        | ContentNode::Return(_)
                        | ContentNode::Bind(..)
                        | ContentNode::Force(_)
                        | ContentNode::Case { .. }
                        | ContentNode::ComputationHole(_)
                        | ContentNode::ComputationMark { .. }
                        | ContentNode::Fixpoint { .. }
                        | ContentNode::ListFold { .. }
                        | ContentNode::ListCase { .. }
                        | ContentNode::Session(_)
                        | ContentNode::Memory(_)
                        | ContentNode::Base(_)
                        | ContentNode::BufferType
                        | ContentNode::RowKind
                        | ContentNode::RowTail(_)
                        | ContentNode::RowValue(_)
                        | ContentNode::Product(_)
                        | ContentNode::Sum(_)
                        | ContentNode::List(_)
                        | ContentNode::KeptType { .. }
                        | ContentNode::ThunkType(_)
                        | ContentNode::Universe { .. }
                        | ContentNode::TypeLift { .. }
                        | ContentNode::Element { .. }
                        | ContentNode::StaticPi { .. }
                        | ContentNode::Sigma { .. }
                        | ContentNode::SessionType(_)
                        | ContentNode::Abstract(_)
                        | ContentNode::UnknownType
                        | ContentNode::Returner { .. }
                        | ContentNode::Arrow { .. }
                        | ContentNode::Pi { .. }
                        | ContentNode::ComputationElement { .. }
                        | ContentNode::UnknownComputationType
                        | ContentNode::Unresolved(_) => None,
                    })
                    .zip(self.constructors);
                Former::Constructor {
                    name: family.and_then(|(family, constructors)| {
                        constructors
                            .constructor(
                                FamilyKey::Named(family),
                                Component::from(usize::from(tag)),
                            )
                            .map(|(name, _)| name)
                    }),
                    arity: Arity::from(fields.len()),
                    placement: family.map_or(
                        crate::Placement::Applied,
                        |(family, constructors)| {
                            constructors
                                .placement(FamilyKey::Named(family), Arity::from(fields.len()))
                        },
                    ),
                    classifier: matches!(
                        self.nodes.get(usize::from(datatype)),
                        Some(ContentNode::Data { arguments, .. }) if !arguments.is_empty()
                    )
                    .then_some(datatype),
                }
            },
            ContentNode::DataCase {
                scrutinee,
                motive,
                ref branches,
                equations,
                ..
            } => Former::DataCase {
                scrutinee,
                motive,
                arity: Arity::from(branches.len()),
                equations: Arity::from(usize::from(equations)),
            },
            ContentNode::RecordProjection(record, ref label) => {
                Former::RecordProjection(record, Name::from(label.as_ref()))
            },
            ContentNode::TupleProjection(tuple, component) => {
                Former::TupleProjection(tuple, Component::from(usize::from(component)))
            },
            ContentNode::Primitive(primitive, ref arguments) => Former::Primitive {
                name: Name::from(<&'static str>::from(primitive.name())),
                arity: Arity::from(arguments.len()),
            },
            ContentNode::Perform {
                ref signature,
                ref operation,
                payload,
            } => Former::Perform {
                interface: Name::from(signature.name().as_ref()),
                operation: Name::from(operation.as_ref()),
                payload,
            },
            ContentNode::Handle {
                subject,
                on_return,
                ref clauses,
                ..
            } => Former::Handle {
                subject,
                on_return,
                clauses: Arity::from(clauses.len()),
            },
            ContentNode::Exercise {
                capability,
                ref operation,
                payload,
                ..
            } => Former::Exercise {
                capability,
                operation: Name::from(operation.as_ref()),
                payload,
            },
            ContentNode::Scope {
                ref signature,
                subject,
                on_return,
                ref clauses,
            } => Former::Scope {
                interface: Name::from(signature.name().as_ref()),
                subject,
                on_return,
                clauses: Arity::from(clauses.len()),
                sorts: &[],
                answered: None,
            },
            ContentNode::Resume(stack, resumed) => Former::Resume(stack, resumed),
            ContentNode::Abandon(stack) => Former::Abandon(stack),
            ContentNode::Split(scrutinee, arity, body)
            | ContentNode::DependentSplit {
                scrutinee,
                arity,
                body,
                ..
            } => Former::Split {
                scrutinee,
                arity: Arity::from(usize::from(arity)),
                body,
            },
            ContentNode::Reset(body) => Former::Reset(body),
            ContentNode::Shift(body) => Former::Shift(body),
            ContentNode::With(ref components) => Former::Lazy(Arity::from(components.len())),
            ContentNode::Ascribe { body, ty } => Former::Ascription { body, ty },
            ContentNode::ValueAscribe { value, ty } => Former::Annotated { value, ty },
            ContentNode::Project(component, observed) => {
                Former::Project(Component::from(usize::from(component)), observed)
            },
            ContentNode::Transport(path, transported) => Former::Transport(path, transported),
            ContentNode::ElementTransport {
                motive,
                path,
                value,
            } => Former::PathTransport {
                motive,
                path,
                value,
            },
            ContentNode::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value,
            } => Former::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value,
            },
            ContentNode::ListFold {
                list,
                on_nil,
                on_cons,
                ..
            } => Former::ListFold {
                list,
                nil: on_nil,
                cons: on_cons,
            },
            ContentNode::ListCase {
                list,
                on_nil,
                on_cons,
            } => Former::ListCase {
                list,
                nil: on_nil,
                cons: on_cons,
            },
            ContentNode::Case {
                scrutinee,
                ref branches,
            } => Former::Case {
                scrutinee,
                arity: Arity::from(branches.len()),
            },
            ContentNode::Session(ref action) => match *action {
                SessionAction::Send { endpoint, payload } => Former::Send { endpoint, payload },
                SessionAction::Receive { endpoint, body } => Former::Receive { endpoint, body },
                SessionAction::Select {
                    endpoint,
                    ref label,
                } => Former::Select {
                    endpoint,
                    label: Name::from(label.as_ref()),
                },
                SessionAction::Offer { endpoint, ref arms } => Former::Offer {
                    endpoint,
                    arms: Arity::from(arms.len()),
                },
                SessionAction::Close { endpoint } => Former::Close(endpoint),
                SessionAction::Fork {
                    protocol,
                    child,
                    parent,
                } => Former::Fork {
                    protocol,
                    child,
                    parent,
                },
                SessionAction::Place { payload, body } => Former::Place { payload, body },
            },
            ContentNode::Memory(ref form) => match *form {
                MemoryForm::Hold { value, body, grade } => Former::Hold { value, body, grade },
                MemoryForm::Access {
                    mode,
                    held,
                    place,
                    body,
                } => Former::Access {
                    held,
                    place,
                    body,
                    mode,
                },
                MemoryForm::Resume { view, value } => Former::ResumeView { view, value },
                MemoryForm::Abort { view } => Former::AbortView(view),
                MemoryForm::Consume { held } => Former::ConsumeHeld(held),
            },
            ContentNode::Fixpoint { body, .. } => Former::Fixpoint(body),
            ContentNode::Ride {
                motive,
                flow,
                value,
            } => Former::Ride {
                motive,
                flow,
                value,
            },
            ContentNode::Lambda(body) => Former::Lambda(body),
            ContentNode::Application(function, argument) => Former::Application(function, argument),
            ContentNode::Return(value) => Former::Return(value),
            ContentNode::Bind(bound, rest) => Former::Bind(bound, rest),
            ContentNode::Force(thunk) => Former::Force(thunk),
            ContentNode::Decompose(dialogue) => Former::Decompose(dialogue),
            ContentNode::PathUniverse(source, target) => Former::PathUniverse(source, target),
            ContentNode::Funext(left, right) => Former::Funext(left, right),
            ContentNode::Equiv(forward, backward) => Former::Equiv(forward, backward),
            ContentNode::Univalence(record, _) => Former::Univalence(record),
            ContentNode::SessionRelated {
                relation,
                source,
                target,
                payloads,
            } => Former::SessionRelated(
                relation,
                source,
                target,
                match self.nodes.get(usize::from(payloads)) {
                    Some(&ContentNode::Tuple(ref components)) if components.is_empty() => None,
                    _ => Some(payloads),
                },
            ),
            ContentNode::Stay(point) => Former::Stay(point),
            ContentNode::Then(first, second) => Former::Then(first, second),
            ContentNode::FlowProduct(first, second) => Former::FlowProduct(first, second),
            ContentNode::Forward(translator) => Former::Forward(translator),
            ContentNode::FunctionFlow(domain, codomain) => Former::FunctionFlow(domain, codomain),
            ContentNode::RunType(code) => Former::RunType(code),
            ContentNode::PrefixType(code) => Former::PrefixType(code),
            ContentNode::DialogueType(code) => Former::DialogueType(code),
            ContentNode::WebType => Former::WebType,
            ContentNode::Ua {
                stratum,
                ref sides,
                forward,
                backward,
            } => Former::Ua {
                stratum,
                source: Name::from(sides.source.name.as_ref()),
                target: Name::from(sides.target.name.as_ref()),
                forward,
                backward,
            },
            ContentNode::PathRefl(code) => Former::PathRefl(code),
            ContentNode::Here(point) => Former::Here(point),
            ContentNode::PathProduct(first, second) => Former::PathProduct(first, second),
            ContentNode::PathEquiv {
                forward, backward, ..
            } => Former::PathEquiv(forward, backward),
            ContentNode::PathType {
                carrier,
                left,
                right,
            } => Former::Path {
                carrier,
                left,
                right,
            },
            ContentNode::Returned(body) => Former::Returned(body),
            ContentNode::Variable { zone, index } => Former::Variable { zone, index },
            ContentNode::Constant(ref reference) => {
                key(reference).map_or(unnamed, Former::Constant)
            },
            ContentNode::ListNil => Former::ListNil,
            ContentNode::ListCons(head, tail) => Former::ListCons(head, tail),
            ContentNode::Literal(ref literal) => Former::Literal(literal),
            ContentNode::Tuple(ref components) if components.is_empty() => Former::Unit,
            ContentNode::Tuple(ref components) => Former::Tuple(Arity::from(components.len())),
            ContentNode::Injection(summand, body) => {
                Former::Injection(Component::from(usize::from(summand)), body)
            },
            ContentNode::Thunk(body) => Former::Thunk(body),
            ContentNode::Nested(body) => Former::Nested(body),
            ContentNode::Run(body) => Former::Run(body),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a universe lift: the core's explicit cumulativity, which the \
                              surface grammar has no syntax for"
                )
            )]
            ContentNode::ValueLift { .. } | ContentNode::TypeLift { .. } => {
                Former::Unreadable(Unreadable::Lift)
            },
            ContentNode::Quote(quoted) => Former::Quote(quoted),
            ContentNode::QuoteComputation(quoted) => Former::QuoteComputation(quoted),
            ContentNode::RowValue(ref row) => Former::Row {
                effects: row,
                tail: row.tail(),
            },
            ContentNode::Base(base) => Former::BaseType(base),
            ContentNode::BufferType => Former::BufferType,
            ContentNode::RowKind => Former::RowType,
            ContentNode::RecordType(ref fields) if fields.is_empty() => {
                Former::Product(Arity::from(0_usize))
            },
            ContentNode::Record(ref fields) if fields.is_empty() => Former::Unit,
            ContentNode::RecordType(ref fields) => Former::RecordType(Arity::from(fields.len())),
            ContentNode::Record(ref fields) => Former::Record(Arity::from(fields.len())),
            ContentNode::RecordUpdate(base, overlay) => {
                let written = if let Some(&ContentNode::Record(ref fields)) =
                    self.nodes.get(usize::from(overlay))
                {
                    fields.len()
                }
                else {
                    0_usize
                };
                Former::RecordUpdate(base, Arity::from(written))
            },
            ContentNode::Product(ref parts) => Former::Product(Arity::from(parts.len())),
            ContentNode::Sum(ref parts) => Former::Sum(Arity::from(parts.len())),
            ContentNode::List(element) => Former::List(element),
            ContentNode::KeptType { value, region } => Former::Kept {
                inner: value,
                region,
            },
            ContentNode::ThunkType(body) => Former::ThunkType(body),
            ContentNode::Universe { sort, ref level } => Former::Universe { sort, level },
            // A row's tail reads as the row term it stands for, as a decode
            // reads as its code.
            ContentNode::Element { code, .. } | ContentNode::RowTail(code) => Former::Element(code),
            ContentNode::Abstract(ref reference) => {
                key(reference).map_or(unnamed, Former::Abstract)
            },
            ContentNode::Returner {
                result,
                ref effects,
            } => {
                if effects.purity() == gandr_core_term::effect::Purity::Pure {
                    Former::Returner(result)
                }
                else {
                    Former::EffectfulReturner {
                        result,
                        effects,
                        tail: effects.tail(),
                    }
                }
            },
            ContentNode::Arrow { domain, codomain } => Former::Arrow { domain, codomain },
            ContentNode::Pi { domain, codomain } => Former::Pi { domain, codomain },
            ContentNode::ComputationElement { code, .. } => Former::ComputationElement(code),
            ContentNode::StaticLambda(body) => Former::StaticLambda(body),
            ContentNode::StaticApplication(operator, argument) => {
                Former::StaticApplication(operator, argument)
            },
            ContentNode::StaticPi { domain, codomain } => Former::StaticPi { domain, codomain },
            ContentNode::Sigma { first, second } => Former::Sigma { first, second },
            ContentNode::SessionType(ref session) => Former::Session {
                protocol: session.protocol(),
                state: session.state(),
                payloads: Arity::from(session.payloads().len()),
            },
            ContentNode::Capability {
                ref authority,
                grade,
                region,
            } => Former::Capability {
                authority,
                grade,
                region,
            },
            ContentNode::FlowType {
                carrier,
                source,
                target,
            } => Former::Flow {
                carrier,
                left: source,
                right: target,
            },
            ContentNode::Recorded(ref moves) => Former::Recorded {
                moves,
                payloads: Arity::from(
                    moves
                        .iter()
                        .filter(|step| matches!(step.payload(), Maybe::Present(_)))
                        .count(),
                ),
            },
            ContentNode::Dialogue(ref moves) => Former::Dialogue {
                moves,
                payloads: Arity::from(
                    moves
                        .iter()
                        .filter(|turn| matches!(turn.movement.payload(), Maybe::Present(_)))
                        .count(),
                ),
            },
            ContentNode::Web(ref pieces) => Former::Web(pieces),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "an unresolved node names no term: a malformed table, with nothing to \
                              spell"
                )
            )]
            ContentNode::Unresolved(_) => Former::Unreadable(Unreadable::Dangling),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a hole, a term the author has not written: the walk writes it as \
                              the grammar's hole `?`"
                )
            )]
            ContentNode::Hole(_) | ContentNode::ComputationHole(_) => {
                Former::Unreadable(Unreadable::Hole)
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a mark, a term the elaborator could not type: the grammar has no \
                              spelling for a mark"
                )
            )]
            ContentNode::ValueMark { .. } | ContentNode::ComputationMark { .. } => {
                Former::Unreadable(Unreadable::Mark)
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the unknown type a hole or a mark synthesises: the walk writes it as \
                              the grammar's `unknown_type` where a type is read"
                )
            )]
            ContentNode::UnknownType | ContentNode::UnknownComputationType => {
                Former::Unreadable(Unreadable::UnknownType)
            },
        }
    }

    /// The index of component `index` of the n-ary former at `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the index at `index` among a product's, a sum's, a tuple's or
    ///   a lazy product's components, a record's or a record type's fields and
    ///   the fields a record update writes in label order, a session type's
    ///   payloads in slot order, a family's arguments, a constructor's fields,
    ///   a primitive's arguments, a case's or a data case's branches, a
    ///   handler's clauses, an offer's arms or a recorded run's payloads in
    ///   move order; none past them, for another node, or past the table.
    /// - provides: the printer's reading of an n-ary former.
    /// - fails: never.
    /// - panics: none.
    /// - intension: a record's field is reached by counting through its
    ///   label-ordered map, linear in the fields before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the table fixture's products and sums of arity zero
    ///   to three, its tuples of arity one to three and its record type of two
    ///   fields read every component in order and nothing past them; a base
    ///   type reads none.
    /// - witness: `content_source::tests::value_ty_covers_every_reachable_former`
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    #[spec(ensures: |ret| ret.is_none() || self.nodes.get(usize::from(node)).is_some())]
    #[inline]
    fn component(
        &self,
        node: NodeIndex,
        index: Component,
    ) -> Option<NodeIndex>
    {
        let at = usize::from(index);
        match *self.nodes.get(usize::from(node))? {
            ContentNode::Product(ref parts)
            | ContentNode::Sum(ref parts)
            | ContentNode::Tuple(ref parts)
            | ContentNode::WithType(ref parts)
            | ContentNode::With(ref parts)
            | ContentNode::Data {
                arguments: ref parts,
                ..
            }
            | ContentNode::Constructor {
                fields: ref parts, ..
            }
            | ContentNode::DataCase {
                branches: ref parts,
                ..
            }
            | ContentNode::Case {
                branches: ref parts,
                ..
            } => parts.get(at).copied(),
            ContentNode::Primitive(_, ref arguments) => arguments.get(at).copied(),
            ContentNode::RecordType(ref fields) | ContentNode::Record(ref fields) => {
                fields.values().nth(at).copied()
            },
            ContentNode::RecordUpdate(_, overlay) => {
                if let ContentNode::Record(ref fields) = *self.nodes.get(usize::from(overlay))? {
                    fields.values().nth(at).copied()
                }
                else {
                    None
                }
            },
            ContentNode::SessionType(ref session) => session.payloads().get(at).copied(),
            ContentNode::Handle { ref clauses, .. } | ContentNode::Scope { ref clauses, .. } => {
                clauses.get(at).map(|clause| clause.body)
            },
            ContentNode::Session(SessionAction::Offer { ref arms, .. }) => {
                arms.values().nth(at).copied()
            },
            ContentNode::Recorded(ref moves) => moves
                .iter()
                .filter_map(|step| match step.payload() {
                    Maybe::Present(payload) => Some(payload),
                    Maybe::Absent(_) => None,
                })
                .nth(at),
            ContentNode::Dialogue(ref moves) => moves
                .iter()
                .filter_map(|turn| match turn.movement.payload() {
                    Maybe::Present(payload) => Some(payload),
                    Maybe::Absent(_) => None,
                })
                .nth(at),
            ContentNode::Web(_)
            | ContentNode::Decompose(_)
            | ContentNode::DialogueType(_)
            | ContentNode::WebType
            | ContentNode::RecordProjection(..)
            | ContentNode::TupleProjection(..)
            | ContentNode::Reify(_)
            | ContentNode::Stack { .. }
            | ContentNode::Perform { .. }
            | ContentNode::Exercise { .. }
            | ContentNode::Capability { .. }
            | ContentNode::Resume(..)
            | ContentNode::Abandon(_)
            | ContentNode::Split(..)
            | ContentNode::DependentSplit { .. }
            | ContentNode::Reset(_)
            | ContentNode::Shift(_)
            | ContentNode::Ascribe { .. }
            | ContentNode::ValueAscribe { .. }
            | ContentNode::Project(..)
            | ContentNode::PrimitiveValue(_)
            | ContentNode::PathUniverse(..)
            | ContentNode::PathRefl(_)
            | ContentNode::PathProduct(..)
            | ContentNode::Funext(..)
            | ContentNode::Equiv(..)
            | ContentNode::Univalence(..)
            | ContentNode::Ua { .. }
            | ContentNode::PathEquiv { .. }
            | ContentNode::Transport(..)
            | ContentNode::PathType { .. }
            | ContentNode::Here(_)
            | ContentNode::Returned(_)
            | ContentNode::Nested(_)
            | ContentNode::Run(_)
            | ContentNode::ElementTransport { .. }
            | ContentNode::TelescopeTransport { .. }
            | ContentNode::SessionRelated { .. }
            | ContentNode::Stay(_)
            | ContentNode::Then(..)
            | ContentNode::Forward(_)
            | ContentNode::FunctionFlow(..)
            | ContentNode::FlowProduct(..)
            | ContentNode::Ride { .. }
            | ContentNode::FlowType { .. }
            | ContentNode::RunType(_)
            | ContentNode::PrefixType(_)
            | ContentNode::Variable { .. }
            | ContentNode::Constant(_)
            | ContentNode::Literal(_)
            | ContentNode::ListNil
            | ContentNode::ListCons(..)
            | ContentNode::Injection(..)
            | ContentNode::Thunk(_)
            | ContentNode::ValueLift { .. }
            | ContentNode::Quote(_)
            | ContentNode::QuoteComputation(_)
            | ContentNode::StaticLambda(_)
            | ContentNode::StaticApplication(..)
            | ContentNode::Hole(_)
            | ContentNode::ValueMark { .. }
            | ContentNode::Lambda(_)
            | ContentNode::Application(..)
            | ContentNode::Return(_)
            | ContentNode::Bind(..)
            | ContentNode::Force(_)
            | ContentNode::ComputationHole(_)
            | ContentNode::ComputationMark { .. }
            | ContentNode::Fixpoint { .. }
            | ContentNode::ListFold { .. }
            | ContentNode::ListCase { .. }
            | ContentNode::Session(_)
            | ContentNode::Memory(_)
            | ContentNode::Base(_)
            | ContentNode::BufferType
            | ContentNode::RowKind
            | ContentNode::RowTail(_)
            | ContentNode::RowValue(_)
            | ContentNode::List(_)
            | ContentNode::KeptType { .. }
            | ContentNode::ThunkType(_)
            | ContentNode::Universe { .. }
            | ContentNode::TypeLift { .. }
            | ContentNode::Element { .. }
            | ContentNode::StaticPi { .. }
            | ContentNode::Sigma { .. }
            | ContentNode::Abstract(_)
            | ContentNode::UnknownType
            | ContentNode::Returner { .. }
            | ContentNode::Arrow { .. }
            | ContentNode::Pi { .. }
            | ContentNode::ComputationElement { .. }
            | ContentNode::UnknownComputationType
            | ContentNode::Unresolved(_) => None,
        }
    }

    /// The label of entry `index` of the record, the record update, the record
    /// type, the handler or the offer at `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the label at `index` among a record's or a record type's
    ///   fields, the fields a record update writes and an offer's arms, in
    ///   label order, and the operation a handler's clause answers; none past
    ///   them, for another node, or past the table.
    /// - provides: the printer's reading of a record's labels.
    /// - fails: never.
    /// - panics: none.
    /// - intension: as [`Self::component`], linear in the fields before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the table fixture's record type of two fields spells
    ///   each field under its own label, in label order.
    /// - witness: `content_source::tests::value_ty_covers_every_reachable_former`
    #[spec(ensures: |ret| ret.is_none() || self.nodes.get(usize::from(node)).is_some())]
    #[inline]
    fn label(
        &self,
        node: NodeIndex,
        index: Component,
    ) -> Option<Name<'_>>
    {
        let at = usize::from(index);
        let label: &str = match *self.nodes.get(usize::from(node))? {
            ContentNode::RecordType(ref fields) | ContentNode::Record(ref fields) => {
                fields.keys().nth(at).map(AsRef::as_ref)
            },
            ContentNode::RecordUpdate(_, overlay) => {
                if let ContentNode::Record(ref fields) = *self.nodes.get(usize::from(overlay))? {
                    fields.keys().nth(at).map(AsRef::as_ref)
                }
                else {
                    None
                }
            },
            ContentNode::Handle { ref clauses, .. } | ContentNode::Scope { ref clauses, .. } => {
                clauses.get(at).map(|clause| clause.operation.as_ref())
            },
            ContentNode::Session(SessionAction::Offer { ref arms, .. }) => {
                arms.keys().nth(at).map(AsRef::as_ref)
            },
            ContentNode::Data { .. }
            | ContentNode::Constructor { .. }
            | ContentNode::DataCase { .. }
            | ContentNode::RecordProjection(..)
            | ContentNode::TupleProjection(..)
            | ContentNode::Reify(_)
            | ContentNode::Stack { .. }
            | ContentNode::WithType(..)
            | ContentNode::Perform { .. }
            | ContentNode::Exercise { .. }
            | ContentNode::Capability { .. }
            | ContentNode::Resume(..)
            | ContentNode::Abandon(_)
            | ContentNode::Split(..)
            | ContentNode::DependentSplit { .. }
            | ContentNode::Reset(_)
            | ContentNode::Shift(_)
            | ContentNode::With(..)
            | ContentNode::Ascribe { .. }
            | ContentNode::ValueAscribe { .. }
            | ContentNode::Project(..)
            | ContentNode::PrimitiveValue(_)
            | ContentNode::Primitive(..)
            | ContentNode::PathUniverse(..)
            | ContentNode::PathRefl(_)
            | ContentNode::PathProduct(..)
            | ContentNode::Funext(..)
            | ContentNode::Equiv(..)
            | ContentNode::Univalence(..)
            | ContentNode::Ua { .. }
            | ContentNode::PathEquiv { .. }
            | ContentNode::Transport(..)
            | ContentNode::PathType { .. }
            | ContentNode::Here(_)
            | ContentNode::Returned(_)
            | ContentNode::Nested(_)
            | ContentNode::Run(_)
            | ContentNode::ElementTransport { .. }
            | ContentNode::TelescopeTransport { .. }
            | ContentNode::SessionRelated { .. }
            | ContentNode::Stay(_)
            | ContentNode::Then(..)
            | ContentNode::Forward(_)
            | ContentNode::FunctionFlow(..)
            | ContentNode::FlowProduct(..)
            | ContentNode::Recorded(_)
            | ContentNode::Dialogue(_)
            | ContentNode::Web(_)
            | ContentNode::Decompose(_)
            | ContentNode::Ride { .. }
            | ContentNode::FlowType { .. }
            | ContentNode::RunType(_)
            | ContentNode::PrefixType(_)
            | ContentNode::DialogueType(_)
            | ContentNode::WebType
            | ContentNode::Variable { .. }
            | ContentNode::Constant(_)
            | ContentNode::Literal(_)
            | ContentNode::Tuple(_)
            | ContentNode::ListNil
            | ContentNode::ListCons(..)
            | ContentNode::Injection(..)
            | ContentNode::Thunk(_)
            | ContentNode::ValueLift { .. }
            | ContentNode::Quote(_)
            | ContentNode::QuoteComputation(_)
            | ContentNode::StaticLambda(_)
            | ContentNode::StaticApplication(..)
            | ContentNode::Hole(_)
            | ContentNode::ValueMark { .. }
            | ContentNode::Lambda(_)
            | ContentNode::Application(..)
            | ContentNode::Return(_)
            | ContentNode::Bind(..)
            | ContentNode::Force(_)
            | ContentNode::Case { .. }
            | ContentNode::ComputationHole(_)
            | ContentNode::ComputationMark { .. }
            | ContentNode::Fixpoint { .. }
            | ContentNode::ListFold { .. }
            | ContentNode::ListCase { .. }
            | ContentNode::Session(_)
            | ContentNode::Memory(_)
            | ContentNode::Base(_)
            | ContentNode::BufferType
            | ContentNode::RowKind
            | ContentNode::RowTail(_)
            | ContentNode::RowValue(_)
            | ContentNode::Product(_)
            | ContentNode::Sum(_)
            | ContentNode::List(_)
            | ContentNode::KeptType { .. }
            | ContentNode::ThunkType(_)
            | ContentNode::Universe { .. }
            | ContentNode::TypeLift { .. }
            | ContentNode::Element { .. }
            | ContentNode::StaticPi { .. }
            | ContentNode::Sigma { .. }
            | ContentNode::SessionType(_)
            | ContentNode::Abstract(_)
            | ContentNode::UnknownType
            | ContentNode::Returner { .. }
            | ContentNode::Arrow { .. }
            | ContentNode::Pi { .. }
            | ContentNode::ComputationElement { .. }
            | ContentNode::UnknownComputationType
            | ContentNode::Unresolved(_) => None,
        }?;
        Some(Name::from(label))
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::format;
    use alloc::string::String;
    use alloc::string::ToString as _;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_incremental::ContentNode;
    use gandr_core_incremental::ItemKey;
    use gandr_core_incremental::NodeIndex;
    use gandr_core_incremental::Occurrence;
    use gandr_core_incremental::Reference;
    use gandr_core_incremental::Sort;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::FieldLabel;

    use super::ContentSource;
    use crate::Fidelity;
    use crate::PageWidth;
    use crate::Presentation;
    use crate::PresentationError;
    use crate::present_type;

    /// The type at `root` of `nodes`, laid out at a hundred columns.
    ///
    /// # Specification
    /// trivial.
    fn spell(
        nodes: &[ContentNode],
        root: NodeIndex,
    ) -> Result<Presentation, PresentationError>
    {
        present_type(
            &ContentSource::from(nodes),
            root,
            PageWidth::from(100_u32),
            crate::Form::Explicit.into(),
        )
    }

    /// The first eight node indices.
    ///
    /// # Specification
    /// trivial.
    fn indices() -> [NodeIndex; 8]
    {
        [0, 1, 2, 3, 4, 5, 6, 7].map(NodeIndex::from)
    }

    /// The abstract type keyed `key`.
    ///
    /// # Specification
    /// trivial.
    fn key(key: ItemKey) -> ContentNode
    {
        ContentNode::Abstract(Reference::Item {
            key,
            occurrence: Occurrence::from(0),
        })
    }

    /// The text and fidelity of the table's spelling from its first node.
    ///
    /// # Specification
    /// - requires: the table fits the presentation layout budget.
    /// - ensures: the text and fidelity of its root type; an absent root is an
    ///   approximate question mark.
    /// - provides: the type-spelling oracle read by the rendering witnesses.
    /// - fails: never.
    /// - panics: if the presentation engine rejects the layout.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every printable type former, wrong polarities and
    ///   malformed tables are distinguished by exact text and fidelity.
    /// - witness: `content_source::tests::value_ty_covers_every_reachable_former`
    /// - witness: `content_source::tests::a_malformed_table_spells_unknown`
    #[spec(ensures: |ret| !ret.0.is_empty()
        && (!nodes.is_empty() || (ret.0 == "?" && ret.1 == Fidelity::Approximate)))]
    fn spelled(nodes: &[ContentNode]) -> (String, Fidelity)
    {
        let spelling = spell(nodes, NodeIndex::from(0)).expect("a transcript type lays out");
        (spelling.to_string(), spelling.fidelity())
    }

    /// The faithful spelling `text`.
    ///
    /// # Specification
    /// trivial.
    fn faithful(text: String) -> (String, Fidelity)
    {
        (text, Fidelity::Faithful)
    }

    /// The approximate spelling `text`.
    ///
    /// # Specification
    /// trivial.
    fn approximate(text: String) -> (String, Fidelity)
    {
        (text, Fidelity::Approximate)
    }

    /// Every value type the fragment writes spells exactly, nested formers
    /// parenthesized.
    #[test]
    fn value_ty_covers_every_reachable_former()
    {
        let [_, n1, n2, n3, n4, ..] = indices();
        let integer = ContentNode::Base(BaseType::Integer);
        assert_eq!(
            spelled(core::slice::from_ref(&integer)),
            faithful("Integer".into())
        );
        assert_eq!(
            spelled(&[ContentNode::Base(BaseType::String)]),
            faithful("String".into())
        );
        assert_eq!(
            spelled(&[ContentNode::Product(Vec::new())]),
            faithful("Unit".into())
        );
        assert_eq!(
            spelled(&[key(ItemKey::from("Shape"))]),
            faithful("Shape".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::ThunkType(n1),
                ContentNode::Returner {
                    result: n2,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                integer.clone(),
            ]),
            faithful("+U (-F Integer)".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::ThunkType(n1),
                ContentNode::Arrow {
                    domain: n2,
                    codomain: n3,
                },
                integer,
                ContentNode::Returner {
                    result: n2,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
            ]),
            faithful("+U (Integer -> -F Integer)".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::PathUniverse(n1, n2),
                ContentNode::Quote(n3),
                ContentNode::Quote(n4),
                ContentNode::Product(Vec::new()),
                ContentNode::Base(BaseType::Integer),
            ]),
            approximate("Path_U(Unit, Integer)".into())
        );
        // One 3-ary product, the nested product one of its components; the
        // empty sum; the sum of two units; the 1-ary product; and a record
        // type, its fields in label order whatever order they were given in.
        assert_eq!(
            spelled(&[
                ContentNode::Product(Vec::from([n1, n2, n3])),
                ContentNode::Base(BaseType::Integer),
                ContentNode::Product(Vec::from([n1, n1])),
                ContentNode::Sum(Vec::new()),
            ]),
            faithful("#{Integer, #{Integer, Integer}, Void}".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Sum(Vec::from([n1, n1])),
                ContentNode::Product(Vec::new()),
            ]),
            faithful("Bool".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Product(Vec::from([n1])),
                ContentNode::Base(BaseType::Integer),
            ]),
            faithful("#{Integer}".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::RecordType(BTreeMap::from([
                    (FieldLabel::from(String::from("v")), n2),
                    (FieldLabel::from(String::from("n")), n1),
                ])),
                ContentNode::Base(BaseType::Integer),
                ContentNode::Base(BaseType::String),
            ]),
            faithful("#{n : Integer, v : String}".into())
        );
        // The empty record type is the unit type; a family spells applied to
        // its arguments, a path type over its carrier and endpoints.
        assert_eq!(
            spelled(&[ContentNode::RecordType(BTreeMap::new())]),
            faithful("Unit".into())
        );
        let item = |key: &str| Reference::Item {
            key: ItemKey::from(key),
            occurrence: Occurrence::from(0),
        };
        assert_eq!(
            spelled(&[
                ContentNode::PathType {
                    carrier: n1,
                    left: n2,
                    right: n3,
                },
                ContentNode::Data {
                    declaration: item("List"),
                    arguments: Vec::from([n4]),
                },
                ContentNode::Constant(item("nil")),
                ContentNode::Constant(item("empty")),
                ContentNode::Quote(NodeIndex::from(5)),
                ContentNode::Base(BaseType::Integer),
            ]),
            faithful("Path(List(Integer), nil, empty)".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Sum(Vec::from([n1, n4])),
                ContentNode::Base(BaseType::Integer),
            ]),
            approximate("+{Integer, ?}".into())
        );
    }

    /// Every computation type the fragment writes spells exactly: the arrow
    /// right associative, a thunk domain bare, a returner's thunk argument
    /// parenthesized.
    #[test]
    fn comp_ty_covers_every_reachable_former()
    {
        let [_, n1, n2, n3, n4, n5, ..] = indices();
        let integer = ContentNode::Base(BaseType::Integer);
        assert_eq!(
            spelled(&[
                ContentNode::Returner {
                    result: n1,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                integer.clone()
            ]),
            faithful("-F Integer".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Returner {
                    result: n1,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                ContentNode::ThunkType(n2),
                ContentNode::Returner {
                    result: n3,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                ContentNode::Product(Vec::new()),
            ]),
            faithful("-F (+U (-F Unit))".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Arrow {
                    domain: n1,
                    codomain: n2,
                },
                integer.clone(),
                ContentNode::Arrow {
                    domain: n3,
                    codomain: n4,
                },
                ContentNode::Base(BaseType::String),
                ContentNode::Returner {
                    result: n5,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                ContentNode::Product(Vec::new()),
            ]),
            faithful("Integer -> String -> -F Unit".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Arrow {
                    domain: n1,
                    codomain: n3,
                },
                ContentNode::ThunkType(n3),
                integer,
                ContentNode::Returner {
                    result: n2,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
            ]),
            faithful("+U (-F Integer) -> -F Integer".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::WithType(alloc::vec![n1, n2]),
                ContentNode::Returner {
                    result: n3,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                ContentNode::Arrow {
                    domain: n3,
                    codomain: n1,
                },
                ContentNode::Base(BaseType::Integer),
            ]),
            faithful("&{-F Integer, Integer -> -F Integer}".into())
        );
    }

    /// A former reads its argument at the polarity it takes: `+U` over a value
    /// type, `-F` over a computation type, an arrow from a computation type,
    /// and a term at the root each spell approximately, at exactly the
    /// misplaced node.
    #[test]
    fn ty_dispatches_on_polarity()
    {
        let [_, n1, n2, ..] = indices();
        let integer = ContentNode::Base(BaseType::Integer);
        assert_eq!(
            spelled(&[ContentNode::ThunkType(n1), integer.clone()]),
            approximate("+U ?".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Returner {
                    result: n1,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                ContentNode::Returner {
                    result: n2,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                integer.clone(),
            ]),
            approximate("-F ?".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Arrow {
                    domain: n1,
                    codomain: n1,
                },
                ContentNode::Returner {
                    result: n2,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                integer,
            ]),
            approximate("? -> -F Integer".into())
        );
        assert_eq!(
            spelled(&[ContentNode::Tuple(Vec::new())]),
            approximate("?".into())
        );
    }

    /// Fidelity follows the nodes the surface cannot write, not the characters
    /// a name happens to hold: a name spelled with `?` stays faithful, while an
    /// unoccupied position, the numeric atom and an unresolved type are each
    /// approximate.
    #[test]
    fn fidelity_tracks_unsupported_nodes_not_user_punctuation()
    {
        let [_, n1, n2, ..] = indices();
        assert_eq!(
            spelled(&[key(ItemKey::from("Maybe?"))]),
            faithful("Maybe?".into())
        );
        let integer = ContentNode::Base(BaseType::Integer);
        for unsupported in [
            ContentNode::Abstract(Reference::Unoccupied),
            ContentNode::Base(BaseType::Numeric),
            ContentNode::Unresolved(Sort::ValueType),
        ] {
            assert_eq!(
                spelled(&[unsupported.clone(), integer.clone()]),
                approximate("?".into()),
                "{unsupported:?} has no surface spelling"
            );
        }
        assert_eq!(
            spelled(&[
                ContentNode::ThunkType(n1),
                ContentNode::Returner {
                    result: n2,
                    effects: gandr_core_term::effect::EffectRow::EMPTY
                },
                ContentNode::Base(BaseType::Numeric),
            ]),
            approximate("+U (-F ?)".into())
        );
    }

    /// A spelling displays as the surface text, never as the table's debug
    /// image, and its text view agrees with its display.
    #[test]
    fn types_render_without_debug()
    {
        let [n0, n1, n2, n3, n4, ..] = indices();
        let nodes = [
            ContentNode::ThunkType(n1),
            ContentNode::Arrow {
                domain: n2,
                codomain: n3,
            },
            ContentNode::Base(BaseType::String),
            ContentNode::Returner {
                result: n4,
                effects: gandr_core_term::effect::EffectRow::EMPTY,
            },
            ContentNode::Product(Vec::new()),
        ];
        let spelling = spell(&nodes, n0).expect("a transcript type lays out");
        assert_eq!(spelling.to_string(), "+U (String -> -F Unit)");
        assert_eq!(AsRef::<str>::as_ref(&spelling), "+U (String -> -F Unit)");
        let debug = format!("{nodes:?}");
        assert!(
            debug.contains("ThunkType") && !spelling.to_string().contains("ThunkType"),
            "the display is not the debug image: {debug}"
        );
    }

    /// A dangling index, an empty table and a cycle each spell approximately
    /// rather than panicking or looping.
    #[test]
    fn a_malformed_table_spells_unknown()
    {
        let [n0, n1, .., n7] = indices();
        assert_eq!(
            spelled(&[ContentNode::ThunkType(n7)]),
            approximate("+U ?".into())
        );
        assert_eq!(spelled(&[]), approximate("?".into()));
        let cycle: Vec<ContentNode> = Vec::from([ContentNode::ThunkType(n1), ContentNode::Arrow {
            domain: n0,
            codomain: n1,
        }]);
        assert_eq!(spelled(&cycle), approximate("?".into()));
    }

    /// An empty tuple and an empty record read as the unit; a tuple or record
    /// with members reads as itself over its arity.
    #[test]
    fn an_empty_tuple_or_record_reads_as_the_unit_and_a_full_one_by_its_arity()
    {
        use crate::Arity;
        use crate::Former;
        use crate::Source as _;

        let [n0, n1, n2, n3, ..] = indices();
        let nodes = [
            ContentNode::Tuple(Vec::new()),
            ContentNode::Tuple(Vec::from([n0, n0])),
            ContentNode::Record(BTreeMap::new()),
            ContentNode::Record(BTreeMap::from([(FieldLabel::from(String::from("x")), n0)])),
        ];
        let source = ContentSource::from(&nodes[..]);
        assert!(matches!(source.read(n0), Former::Unit), "the empty tuple");
        assert!(
            matches!(source.read(n1), Former::Tuple(arity) if arity == Arity::from(2_usize)),
            "a pair"
        );
        assert!(matches!(source.read(n2), Former::Unit), "the empty record");
        assert!(
            matches!(source.read(n3), Former::Record(arity) if arity == Arity::from(1_usize)),
            "a record of one field"
        );
    }
}
