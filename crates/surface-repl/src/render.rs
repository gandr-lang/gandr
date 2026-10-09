//! A type's content table, laid out by the presentation printer.
//!
//! The incremental checker hands a checked item's signature and a synthesised
//! item's type back as [`ContentNode`] tables. A [`ContentTable`] reads such a
//! table as the printer's [`Source`], naming a constant or an abstract type by
//! its item key, and [`spell`] lays the type out at the transcript's width in
//! the one spelling every face shows — `Integer`, `+U C`, `-F A`, `A -> C`,
//! `(x : A) -> C`, `Type[+, l]` — writing `?` wherever a node has no surface
//! spelling.

use gandr_core_incremental::ContentNode;
use gandr_core_incremental::NodeIndex;
use gandr_core_incremental::Reference;
use gandr_surface_pretty::Former;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::PresentationError;
use gandr_surface_pretty::Source;
use gandr_surface_pretty::present_type;

/// The page width a transcript line lays a type out at.
///
/// A transcript is a function of its input alone, so the width is fixed
/// rather than read off a terminal; a type wider than the page breaks onto
/// continuation lines, which the batch writer indents under the line's mark.
const TRANSCRIPT_WIDTH: u32 = 100;

/// A checkpoint's content table, read by the presentation printer.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct ContentTable<'nodes>(&'nodes [ContentNode]);

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
/// - witness: `render::tests::value_ty_covers_every_reachable_former`
/// - witness: `render::tests::fidelity_tracks_unsupported_nodes_not_user_punctuation`
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

impl Source for ContentTable<'_>
{
    type Node = NodeIndex;

    /// The content node at `node`, as the printer reads it.
    ///
    /// # Specification
    /// - requires: nothing; any index is admissible.
    /// - ensures: each core former read as its [`Former`], over the same
    ///   indices; every computation former as [`Former::Computation`]; an
    ///   unresolved node, and an index past the table, as
    ///   [`Former::Unreadable`].
    /// - provides: the printer's input over checkpoint tables.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every value-type and computation-type former the
    ///   fragment writes, a former over the wrong polarity, an unresolved node,
    ///   a dangling index and a cycle are each asserted at their exact
    ///   spelling; L2 — the type of every declaration of the strict corpus
    ///   spells as its source wrote it.
    /// - witness: `render::tests::value_ty_covers_every_reachable_former`
    /// - witness: `render::tests::comp_ty_covers_every_reachable_former`
    /// - witness: `render::tests::ty_dispatches_on_polarity`
    /// - witness: `render::tests::a_malformed_table_spells_unknown`
    /// - witness: `loop::tests::corpus_types_spell_as_their_source_writes_them`
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
            | ContentNode::Variable { zone, index } => Former::Variable { zone, index },
            | ContentNode::Constant(ref reference) => named(reference, Former::Constant),
            | ContentNode::Unit => Former::Unit,
            | ContentNode::Literal(ref literal) => Former::Literal(literal),
            | ContentNode::Pair(first, second) => Former::Pair(first, second),
            | ContentNode::Injection(side, body) => Former::Injection(side, body),
            | ContentNode::Thunk(_) => Former::Thunk,
            | ContentNode::ValueLift { .. } => Former::ValueLift,
            | ContentNode::Quote(quoted) => Former::Quote(quoted),
            | ContentNode::QuoteComputation(quoted) => Former::QuoteComputation(quoted),
            | ContentNode::Lambda(_)
            | ContentNode::Application(..)
            | ContentNode::Return(_)
            | ContentNode::Bind(..)
            | ContentNode::Force(_)
            | ContentNode::Case { .. } => Former::Computation,
            | ContentNode::Base(base) => Former::BaseType(base),
            | ContentNode::UnitType => Former::UnitType,
            | ContentNode::Product(first, second) => Former::Product(first, second),
            | ContentNode::Sum(first, second) => Former::Sum(first, second),
            | ContentNode::ThunkType(body) => Former::ThunkType(body),
            | ContentNode::Universe { sort, ref level } => Former::Universe { sort, level },
            | ContentNode::TypeLift { .. } => Former::TypeLift,
            | ContentNode::Element { code, .. } => Former::Element(code),
            | ContentNode::Abstract(ref reference) => named(reference, Former::Abstract),
            | ContentNode::Returner(result) => Former::Returner(result),
            | ContentNode::Arrow { domain, codomain } => Former::Arrow { domain, codomain },
            | ContentNode::Pi { domain, codomain } => Former::Pi { domain, codomain },
            | ContentNode::ComputationElement { code, .. } => Former::ComputationElement(code),
            | ContentNode::StaticLambda(_)
            | ContentNode::StaticApplication(..)
            | ContentNode::StaticPi { .. }
            | ContentNode::Unresolved(_) => Former::Unreadable,
        }
    }
}

/// The type at `root` of `nodes`, laid out at the transcript's width.
///
/// # Specification
/// - requires: nothing; any table and index are admissible.
/// - ensures: the printer's presentation of the root as a type, at
///   [`TRANSCRIPT_WIDTH`] columns: every former the surface writes in its one
///   spelling, and every node it cannot — the numeric atom, a lift, an
///   unresolved node, an unoccupied position, a term, an index past the table,
///   a former over an argument of the wrong polarity — written `?`, the
///   presentation then approximate. A table that would take more than the
///   printer's visit budget, which only a malformed one does, spells `?`.
/// - provides: the one spelling a transcript line names a type by.
/// - fails: a layout ceiling the printer reaches, which no table of a size a
///   transcript holds reaches.
/// - panics: none.
///
/// # Errors
/// The printer's [`PresentationError`].
///
/// # Adequacy
/// - hypothesis: L3 — every value-type and computation-type former of the
///   fragment, nested, is asserted at its exact spelling; a former over the
///   wrong polarity, an unsupported node, a dangling index and a cycle are each
///   asserted approximate; L2 — the type of every declaration of the strict
///   corpus spells as its source wrote it.
/// - witness: `render::tests::value_ty_covers_every_reachable_former`
/// - witness: `render::tests::comp_ty_covers_every_reachable_former`
/// - witness: `render::tests::ty_dispatches_on_polarity`
/// - witness: `render::tests::fidelity_tracks_unsupported_nodes_not_user_punctuation`
/// - witness: `render::tests::types_render_without_debug`
/// - witness: `render::tests::a_malformed_table_spells_unknown`
/// - witness: `loop::tests::corpus_types_spell_as_their_source_writes_them`
#[inline]
pub fn spell(
    nodes: &[ContentNode],
    root: NodeIndex,
) -> Result<Presentation, PresentationError>
{
    present_type(
        &ContentTable(nodes),
        root,
        PageWidth::from(TRANSCRIPT_WIDTH),
    )
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::string::ToString as _;
    use alloc::vec::Vec;

    use gandr_core_incremental::ContentNode;
    use gandr_core_incremental::ItemKey;
    use gandr_core_incremental::NodeIndex;
    use gandr_core_incremental::Occurrence;
    use gandr_core_incremental::Reference;
    use gandr_core_incremental::Sort;
    use gandr_kernel_term::BaseType;
    use gandr_surface_diagnostics::RenderStyle;
    use gandr_surface_pretty::Fidelity;
    use gandr_surface_render_remote::OutKind;
    use gandr_surface_syntax::SourceText;

    use super::spell;
    use crate::LoopEvent;
    use crate::SessionLoop;

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
    /// trivial.
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
        let [_, n1, n2, n3, ..] = indices();
        let integer = ContentNode::Base(BaseType::Integer);
        assert_eq!(
            spelled(core::slice::from_ref(&integer)),
            faithful("Integer".into())
        );
        assert_eq!(
            spelled(&[ContentNode::Base(BaseType::String)]),
            faithful("String".into())
        );
        assert_eq!(spelled(&[ContentNode::UnitType]), faithful("Unit".into()));
        assert_eq!(
            spelled(&[named(ItemKey::from("Shape"))]),
            faithful("Shape".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::ThunkType(n1),
                ContentNode::Returner(n2),
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
                ContentNode::Returner(n2),
            ]),
            faithful("+U (Integer -> -F Integer)".into())
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
            spelled(&[ContentNode::Returner(n1), integer.clone()]),
            faithful("-F Integer".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Returner(n1),
                ContentNode::ThunkType(n2),
                ContentNode::Returner(n3),
                ContentNode::UnitType,
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
                ContentNode::Returner(n5),
                ContentNode::UnitType,
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
                ContentNode::Returner(n2),
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
                ContentNode::Returner(n1),
                ContentNode::Returner(n2),
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
                ContentNode::Returner(n2),
                integer,
            ]),
            approximate("? -> -F Integer".into())
        );
        assert_eq!(spelled(&[ContentNode::Unit]), approximate("?".into()));
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
                ContentNode::Returner(n2),
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
            ContentNode::Returner(n4),
            ContentNode::UnitType,
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

    /// Each class of run the fragment writes reaches the transcript as the
    /// line of its own kind, spelled as `gandr run` prints it.
    #[test]
    fn eval_renders_each_outcome_class()
    {
        let mut repl = SessionLoop::new(RenderStyle::Plain).expect("the loop starts");
        let mut last = |line: &str| match repl
            .offer(SourceText::from(line))
            .expect("the session does not fault")
        {
            | LoopEvent::Block(block) => block.lines.last().cloned(),
            | other => panic!("`{line}` answers a block, not {other:?}"),
        };
        assert_eq!(
            last("def answer = 42 ;"),
            Some((OutKind::Value, String::from("42"))),
            "a produced value renders in the structural notation"
        );
        assert_eq!(
            last(r#"def text = "line\n\t\"\\tail" ;"#),
            Some((OutKind::Value, String::from(r#""line\n\t\"\\tail""#))),
            "string values stay one escaped transcript line"
        );
        assert_eq!(
            last(
                "def identity : +U (Integer -> -F Integer) ; def identity = thunk { fn (x) { ret x } } ;"
            ),
            Some((OutKind::Value, String::from("<fun>"))),
            "a function terminal renders opaquely"
        );
        let _goal = last("def later : Integer ;");
        assert_eq!(
            last("def copy : Integer ; def copy = later ;"),
            Some((
                OutKind::Blame,
                String::from("blame: `later` is owed its body")
            )),
            "a run reaching a goal renders its blame"
        );
        assert_eq!(
            last("def small : Type ; def small = Integer ;"),
            Some((
                OutKind::Stuck,
                String::from(
                    "unrunnable: `small` is a code, which the machine carries no image of"
                )
            )),
            "a run that never reaches the machine renders as a note"
        );
    }
}
