//! A type's content table, laid out at the transcript's width.
//!
//! The incremental checker hands a checked item's signature and a synthesised
//! item's type back as [`ContentNode`] tables. [`spell`] lays one out through
//! the printer's [`ContentSource`] at the transcript's width, in the one
//! spelling every face shows — `Integer`, `+U C`, `-F A`, `A -> C`,
//! `(x : A) -> C`, `Type[+, l]` — writing `?` wherever a node has no surface
//! spelling.

use anodized::spec;
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::NodeIndex;
use gandr_surface_pretty::ContentSource;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::PresentationError;
use gandr_surface_pretty::present_type;

/// The page width a transcript line lays a type out at.
///
/// A transcript is a function of its input alone, so the width is fixed
/// rather than read off a terminal; a type wider than the page breaks onto
/// continuation lines, which the batch writer indents under the line's mark.
pub const TRANSCRIPT_WIDTH: u32 = 100;

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
/// - hypothesis: L2 — one-line signatures in three selected strict corpus
///   sources retain their written type spelling at the transcript's width; the
///   former-by-former spellings are witnessed where [`ContentSource`] is.
/// - witness: `loop::tests::corpus_types_spell_as_their_source_writes_them`
#[spec(ensures: |ret| match nodes.get(usize::from(root)) {
    None | Some(&ContentNode::Unresolved(_)) => ret.as_ref().is_ok_and(|shown|
        shown.as_ref() == "?" && shown.fidelity() == gandr_surface_pretty::Fidelity::Approximate),
    Some(&ContentNode::UnitType) => ret.as_ref().is_ok_and(|shown|
        shown.as_ref() == "Unit" && shown.fidelity() == gandr_surface_pretty::Fidelity::Faithful),
    Some(_) => ret.is_err() || ret.as_ref().is_ok_and(|shown| !AsRef::<str>::as_ref(shown).is_empty()),
})]
#[inline]
pub fn spell(
    nodes: &[ContentNode],
    root: NodeIndex,
) -> Result<Presentation, PresentationError>
{
    present_type(
        &ContentSource::from(nodes),
        root,
        PageWidth::from(TRANSCRIPT_WIDTH),
    )
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use gandr_surface_diagnostics::RenderStyle;
    use gandr_surface_render_remote::OutKind;
    use gandr_surface_syntax::SourceText;

    use crate::LoopEvent;
    use crate::SessionLoop;

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
                "def identity : +U (Integer -> -F Integer) ; def identity = thunk { fn (x) { return x } } ;"
            ),
            Some((OutKind::Value, String::from("<fun>"))),
            "a function terminal renders opaquely"
        );
        let _goal = last("def later : Integer ;");
        assert!(matches!(
            last("def copy : Integer ; def copy = later ;"),
            Some((OutKind::Blame, _))
        ));
        assert!(matches!(
            last("def small : Type ; def small = Integer ;"),
            Some((OutKind::Stuck, _))
        ));
    }
}
