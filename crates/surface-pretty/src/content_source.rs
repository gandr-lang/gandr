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

use crate::Name;
use crate::Source;
use crate::former::Arity;
use crate::former::Component;
use crate::former::Former;

/// A checkpoint's content table, read by the presentation printer.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct ContentSource<'nodes>(&'nodes [ContentNode]);

impl<'nodes> From<&'nodes [ContentNode]> for ContentSource<'nodes>
{
    /// The source reading `nodes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nodes: &'nodes [ContentNode]) -> Self
    {
        Self(nodes)
    }
}

/// The name `reference` carries, wrapped as `wrap` says.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `wrap` over the item key's text when the reference names an item
///   whose key is UTF-8; [`Former::Unreadable`] for an unoccupied position and
///   for a key that is not text.
/// - provides: the constant and abstract-type readings.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an abstract type by its key, a key spelled with `?`, and
///   an unoccupied position are each asserted at their exact spelling.
/// - witness: `content_source::tests::value_ty_covers_every_reachable_former`
/// - witness: `content_source::tests::fidelity_tracks_unsupported_nodes_not_user_punctuation`
#[spec(ensures: |ret| match *reference {
    Reference::Unoccupied => matches!(ret, Former::Unreadable),
    Reference::Item { ref key, .. } => core::str::from_utf8(key.as_ref()).is_ok()
        || matches!(ret, Former::Unreadable),
})]
fn named<'nodes>(
    reference: &'nodes Reference,
    wrap: fn(Name<'nodes>) -> Former<'nodes, NodeIndex>,
) -> Former<'nodes, NodeIndex>
{
    match *reference {
        | Reference::Item { ref key, .. } => match core::str::from_utf8(key.as_ref()) {
            | Ok(name) => wrap(Name::from(name)),
            | Err(_) => Former::Unreadable,
        },
        | Reference::Unoccupied => Former::Unreadable,
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
    ///   indices; every computation former as [`Former::Computation`]; an
    ///   unresolved node, a hole, a mark, the unknown type, and an index past
    ///   the table, as [`Former::Unreadable`].
    /// Native data and record syntax is outside this source adapter's fragment.
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
    #[spec(ensures: |ret| match (self.0.get(usize::from(node)), ret) {
        (Some(&ContentNode::PrimitiveValue(primitive)), Former::Constant(name)) => name.as_ref() == primitive.name().as_ref(),
        (Some(&ContentNode::Data { .. } | &ContentNode::RecordType(_) |
&ContentNode::Constructor { .. } | &ContentNode::Record(_) |
&ContentNode::Unresolved(_) | &ContentNode::Hole(_) | &ContentNode::ValueMark { .. } |
&ContentNode::ComputationHole(_) | &ContentNode::ComputationMark { .. } |
&ContentNode::UnknownType | &ContentNode::UnknownComputationType) | None, Former::Unreadable) |
(Some(&ContentNode::Reify(_)), Former::Reify) |
(Some(&ContentNode::DataCase { .. } | &ContentNode::RecordProjection(..) |
&ContentNode::Primitive(..) | &ContentNode::Transport(..) |
&ContentNode::Lambda(_) | &ContentNode::Application(..) |
&ContentNode::Perform { .. } | &ContentNode::Handle { .. } | &ContentNode::Resume(..) | &ContentNode::Reset(_) | &ContentNode::Shift(_) | &ContentNode::With(..) | &ContentNode::Project(..) | &ContentNode::ListFold { .. } |
&ContentNode::Return(_) | &ContentNode::Bind(..) | &ContentNode::Force(_) |
&ContentNode::Case { .. } | &ContentNode::Fixpoint { .. }), Former::Computation) |
(Some(&ContentNode::ListNil), Former::ListNil) |
(Some(&ContentNode::Thunk(_)), Former::Thunk) |
(Some(&ContentNode::ValueLift { .. }), Former::ValueLift) |
(Some(&ContentNode::TypeLift { .. }), Former::TypeLift) => true,
        (Some(&ContentNode::Stack { input: a, output: b }), Former::Stack(c, d))
        | (Some(&ContentNode::WithType(a, b)), Former::With(c, d)) | (Some(&ContentNode::PathUniverse(a, b)), Former::PathUniverse(c, d))
        | (Some(&ContentNode::PathProduct(a, b)), Former::PathProduct(c, d))
        | (Some(&ContentNode::PathEquiv { forward: a, backward: b, .. }), Former::PathEquiv(c, d))
        | (Some(&ContentNode::ListCons(a, b)), Former::ListCons(c, d))
        | (Some(&ContentNode::StaticApplication(a, b)), Former::StaticApplication(c, d))
        | (Some(&ContentNode::Arrow { domain: a, codomain: b }), Former::Arrow { domain: c, codomain: d })
        | (Some(&ContentNode::Pi { domain: a, codomain: b }), Former::Pi { domain: c, codomain: d })
        | (Some(&ContentNode::StaticPi { domain: a, codomain: b }), Former::StaticPi { domain: c, codomain: d }) => a == c && b == d,
        (Some(&ContentNode::Variable { zone, index }), Former::Variable { zone: actual_zone, index: actual_index }) =>
            zone == actual_zone && index == actual_index,
        (Some(&ContentNode::Constant(Reference::Item { ref key, .. })), Former::Constant(name))
        | (Some(&ContentNode::Abstract(Reference::Item { ref key, .. })), Former::Abstract(name)) =>
            name.as_ref().as_bytes() == key.as_ref(),
        (Some(content), Former::Literal(actual)) =>
            matches!(*content, ContentNode::Literal(ref literal) if literal == actual),
        (Some(&ContentNode::Injection(summand, body)), Former::Injection(actual_side, actual_body)) =>
            summand == actual_side.into() && body == actual_body,
        (Some(&ContentNode::Injection(summand, _)), Former::Unreadable) => usize::from(summand) > 1,
        (Some(held), Former::Unit) => matches!(*held, ContentNode::Tuple(ref components) if components.is_empty()),
        (Some(held), Former::Tuple(arity)) => matches!(*held, ContentNode::Tuple(ref components) if !components.is_empty() && components.len() == usize::from(arity)),
        (Some(&ContentNode::PathRefl(a)), Former::PathRefl(b))
        | (Some(&ContentNode::Quote(a)), Former::Quote(b))
        | (Some(&ContentNode::QuoteComputation(a)), Former::QuoteComputation(b))
        | (Some(&ContentNode::List(a)), Former::List(b))
        | (Some(&ContentNode::ThunkType(a)), Former::ThunkType(b))
        | (Some(&ContentNode::Element { code: a, .. }), Former::Element(b))
        | (Some(&ContentNode::ComputationElement { code: a, .. }), Former::ComputationElement(b))
        | (Some(&ContentNode::StaticLambda(a)), Former::StaticLambda(b)) => a == b,
        (Some(&ContentNode::Returner { result, ref effects }), Former::Returner(actual)) => result == actual && effects.signatures().len() == 0,
        (Some(&ContentNode::Returner { result, ref effects }), Former::EffectfulReturner { result: actual, .. }) => result == actual && effects.signatures().len() != 0,
        (Some(&ContentNode::Base(a)), Former::BaseType(b)) => a == b,
        (Some(&ContentNode::Product(ref parts)), Former::Product(arity)) | (Some(&ContentNode::Sum(ref parts)), Former::Sum(arity)) =>
            parts.len() != 1 && usize::from(arity) == parts.len(),
        (Some(&ContentNode::Product(ref parts) | &ContentNode::Sum(ref parts)), Former::Unreadable) => parts.len() == 1,
        (Some(&ContentNode::Universe { sort, ref level }), Former::Universe { sort: actual_sort, level: actual_level }) =>
            sort == actual_sort && level == actual_level,

        (Some(&ContentNode::Constant(ref reference) | &ContentNode::Abstract(ref reference)), Former::Unreadable) =>
            match *reference {
                Reference::Unoccupied => true,
                Reference::Item { ref key, .. } => core::str::from_utf8(key.as_ref()).is_err(),
            },
        _ => false,
    })]
    #[inline]
    fn read(
        &self,
        node: NodeIndex,
    ) -> Former<'_, NodeIndex>
    {
        let Some(content) = self.0.get(usize::from(node))
        else {
            return Former::Unreadable;
        };
        match *content {
            | ContentNode::DataCase { .. } | ContentNode::RecordProjection(..) => {
                Former::Computation
            },
            | ContentNode::Reify(_) => Former::Reify,
            | ContentNode::Stack { input, output } => Former::Stack(input, output),
            | ContentNode::WithType(first, second) => Former::With(first, second),
            | ContentNode::PrimitiveValue(primitive) => {
                Former::Constant(Name::from(<&'static str>::from(primitive.name())))
            },
            | ContentNode::Primitive(..)
            | ContentNode::Perform { .. }
            | ContentNode::Handle { .. }
            | ContentNode::Resume(..)
            | ContentNode::Reset(_)
            | ContentNode::Shift(_)
            | ContentNode::With(..)
            | ContentNode::Project(..)
            | ContentNode::Transport(..)
            | ContentNode::Lambda(_)
            | ContentNode::Application(..)
            | ContentNode::Return(_)
            | ContentNode::Bind(..)
            | ContentNode::Force(_)
            | ContentNode::ListFold { .. }
            | ContentNode::Case { .. }
            | ContentNode::Fixpoint { .. } => Former::Computation,
            | ContentNode::PathUniverse(source, target) => Former::PathUniverse(source, target),
            | ContentNode::PathRefl(code) => Former::PathRefl(code),
            | ContentNode::PathProduct(first, second) => Former::PathProduct(first, second),
            | ContentNode::PathEquiv {
                forward, backward, ..
            } => Former::PathEquiv(forward, backward),
            | ContentNode::Variable { zone, index } => Former::Variable { zone, index },
            | ContentNode::Constant(ref reference) => named(reference, Former::Constant),
            | ContentNode::ListNil => Former::ListNil,
            | ContentNode::ListCons(head, tail) => Former::ListCons(head, tail),
            | ContentNode::Literal(ref literal) => Former::Literal(literal),
            | ContentNode::Tuple(ref components) if components.is_empty() => Former::Unit,
            | ContentNode::Tuple(ref components) => Former::Tuple(Arity::from(components.len())),
            | ContentNode::Injection(summand, body) => {
                match gandr_kernel_term::Side::try_from(summand) {
                    | Ok(side) => Former::Injection(side, body),
                    // An injection past the second summand has no spelling yet.
                    | Err(_) => Former::Unreadable,
                }
            },
            | ContentNode::Thunk(_) => Former::Thunk,
            | ContentNode::ValueLift { .. } => Former::ValueLift,
            | ContentNode::Quote(quoted) => Former::Quote(quoted),
            | ContentNode::QuoteComputation(quoted) => Former::QuoteComputation(quoted),
            | ContentNode::Base(base) => Former::BaseType(base),
            // The 1-ary product and sum have no spelling yet.
            | ContentNode::Product(ref parts) | ContentNode::Sum(ref parts) if parts.len() == 1 => {
                Former::Unreadable
            },
            | ContentNode::Product(ref parts) => Former::Product(Arity::from(parts.len())),
            | ContentNode::Sum(ref parts) => Former::Sum(Arity::from(parts.len())),
            | ContentNode::List(element) => Former::List(element),
            | ContentNode::ThunkType(body) => Former::ThunkType(body),
            | ContentNode::Universe { sort, ref level } => Former::Universe { sort, level },
            | ContentNode::TypeLift { .. } => Former::TypeLift,
            | ContentNode::Element { code, .. } => Former::Element(code),
            | ContentNode::Abstract(ref reference) => named(reference, Former::Abstract),
            | ContentNode::Returner {
                result,
                ref effects,
            } => {
                if effects.signatures().len() == 0 {
                    Former::Returner(result)
                }
                else {
                    Former::EffectfulReturner { result, effects }
                }
            },
            | ContentNode::Arrow { domain, codomain } => Former::Arrow { domain, codomain },
            | ContentNode::Pi { domain, codomain } => Former::Pi { domain, codomain },
            | ContentNode::ComputationElement { code, .. } => Former::ComputationElement(code),
            | ContentNode::StaticLambda(body) => Former::StaticLambda(body),
            | ContentNode::StaticApplication(operator, argument) => {
                Former::StaticApplication(operator, argument)
            },
            | ContentNode::StaticPi { domain, codomain } => Former::StaticPi { domain, codomain },
            | ContentNode::Data { .. }
            | ContentNode::RecordType(_)
            | ContentNode::Constructor { .. }
            | ContentNode::Record(_)
            | ContentNode::Unresolved(_)
            | ContentNode::Hole(_)
            | ContentNode::ValueMark { .. }
            | ContentNode::ComputationHole(_)
            | ContentNode::ComputationMark { .. }
            | ContentNode::UnknownType
            | ContentNode::UnknownComputationType => Former::Unreadable,
        }
    }

    /// The index of component `index` of the product, the sum or the tuple at
    /// `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the index at `index` among a product's, a sum's or a tuple's
    ///   components; none past them, for another node, or past the table.
    /// - provides: the printer's reading of an n-ary product, sum or tuple.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the table fixture's products and sums of arity zero,
    ///   two and three, and its tuples of arity one to three, read every
    ///   component in order and nothing past them; a base type reads none.
    /// - witness: `content_source::tests::value_ty_covers_every_reachable_former`
    #[spec(ensures: |ret| ret == match self.0.get(usize::from(node)) {
        | Some(&(ContentNode::Product(ref parts) | ContentNode::Sum(ref parts) | ContentNode::Tuple(ref parts))) => parts.get(usize::from(index)).copied(),
        | _ => None,
    })]
    #[inline]
    fn component(
        &self,
        node: NodeIndex,
        index: Component,
    ) -> Option<NodeIndex>
    {
        match *self.0.get(usize::from(node))? {
            | ContentNode::Product(ref parts)
            | ContentNode::Sum(ref parts)
            | ContentNode::Tuple(ref parts) => parts.get(usize::from(index)).copied(),
            | _ => None,
        }
    }
}

#[cfg(test)]
mod tests
{
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
        present_type(&ContentSource::from(nodes), root, PageWidth::from(100_u32))
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
    fn named(key: ItemKey) -> ContentNode
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
            spelled(&[named(ItemKey::from("Shape"))]),
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
        // One 3-ary chain, its nested product parenthesized; the empty sum;
        // the sum of two units; and the 1-ary product, which has no spelling.
        assert_eq!(
            spelled(&[
                ContentNode::Product(Vec::from([n1, n2, n3])),
                ContentNode::Base(BaseType::Integer),
                ContentNode::Product(Vec::from([n1, n1])),
                ContentNode::Sum(Vec::new()),
            ]),
            faithful("Integer * (Integer * Integer) * Void".into())
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
            approximate("?".into())
        );
        // A component the table does not hold spells `?`.
        assert_eq!(
            spelled(&[
                ContentNode::Sum(Vec::from([n1, n4])),
                ContentNode::Base(BaseType::Integer),
            ]),
            approximate("Integer + ?".into())
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
            spelled(&[named(ItemKey::from("Maybe?"))]),
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
}
