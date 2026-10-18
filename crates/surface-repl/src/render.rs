//! A type's content table, laid out at the transcript's width.
//!
//! The incremental checker hands a checked item's signature and a synthesised
//! item's type back as [`ContentNode`] tables. [`spell`] lays one out through
//! the printer's [`ContentSource`] at the transcript's width, in the sugared
//! form every face a person reads takes — `Integer`, `A => B`, `-F A`, `A ->
//! C`, `A * B`, `(x : A) -> C`, `Type[+, l]` — writing `?` wherever a node has
//! no surface spelling.
//!
//! # Types are spelled from the checkpoints
//!
//! A type line names its type through the session's `type_of` at the
//! transcript's width, the one spelling every transcript line uses: the
//! incremental checker's checkpoint holds a checked or owed item's signature,
//! and a synthesised item's type, as content tables, and `spell` lays a table
//! out through the presentation printer's `ContentSource`,
//! `gandr-surface-pretty`'s reading of a content table, in its sugared form —
//! `Integer`, `String`, `Unit`, `(A, B) => C` for `+U (A -> B -> -F C)`, `+U
//! C` otherwise, `-F A`, `A -> C` right associative, `A * B`, `A + B`, `C &
//! D`, `(x : A) -> C` with generated binder names, `Type`, `Type[-]`,
//! `Type[+, l]`, a decode as the code it reads, a constant or an abstract type
//! by its item key. A node the surface cannot write — the numeric atom, a lift,
//! an unoccupied position, an unresolved node, a term — is written `?`, and the
//! presentation is marked approximate, by the nodes it met rather than by the
//! characters of a name. The printer keeps its own stack and a visit budget, so
//! a malformed table spells `?` rather than looping. Over the strict corpus's
//! `values`, `functions` and `classifier/universes` sources every signature
//! spells as its source wrote it, its thunked arrows read as the alias. The
//! table's reading and the checkpoint lookup live in the printer and the
//! session rather than here so the language server's hover spells a type in
//! the same words.
//!
//! Nonempty effect rows, Stack and With classifiers have diagnostic notation
//! marked approximate, not parseable source. Stack literals display as opaque
//! stack values rather than fabricated frames; computation forms remain
//! computations. Empty effect rows retain the ordinary pure-returner spelling.
//!
//! The page is 100 columns, fixed rather than read off a terminal, so a
//! transcript stays a function of its input. It bounds the type, not the `name
//! :` before it, and a type wider than the page breaks onto continuation lines,
//! which `rows` lays out as later rows of the type line. The choice reverses
//! when a face lays types out at its own width: the terminal face once it reads
//! the terminal's.
//!
//! Types come from checker checkpoints rather than surface-built stand-ins or
//! `Debug` images. The shared printer handles universes and dependent arrows as
//! well as ordinary arrows and polarity bridges.
//!
//! # Native universe-path presentation
//!
//! The checkpoint adapter passes native `Path_U` endpoints, reflexivity codes,
//! forward/backward maps and product paths to `surface-pretty` in constructor
//! order. Its native notation, `gandr-surface-pretty`'s, is approximate, not a
//! new expression the REPL can parse. A transport computation is not presented
//! as a value or a certificate verdict.
//!
//! **Choice.** Reuse the same source interface and fidelity result as ordinary
//! core presentation, rather than render stored evidence with `Debug` or run it
//! while printing. **Reversal.** Parsed path syntax and a certified run-stage
//! image are prerequisites for an interactive introduction or elimination;
//! merely storing a classifier is not enough.

use anodized::spec;
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::NodeIndex;
use gandr_surface_pretty::ContentSource;
use gandr_surface_pretty::Form;
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
/// - ensures: the printer's presentation of the root as a type, in the sugared
///   form at [`TRANSCRIPT_WIDTH`] columns: every former the surface writes in
///   its sugar where the shape admits one and else in its one spelling, and
///   every node it cannot — the numeric atom, a lift, an unresolved node, an
///   unoccupied position, a term, an index past the table, a former over an
///   argument of the wrong polarity — written `?`, the presentation then
///   approximate. A table that would take more than the printer's visit budget,
///   which only a malformed one does, spells `?`.
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
/// - witness: `tests::repl_loop::corpus_types_spell_as_their_source_writes_them`
#[spec(ensures: |ret| match nodes.get(usize::from(root)) {
    None | Some(&ContentNode::Unresolved(_)) => ret.as_ref().is_ok_and(|shown|
        shown.as_ref() == "?" && shown.fidelity() == gandr_surface_pretty::Fidelity::Approximate),
    Some(held) if matches!(*held, ContentNode::Product(ref parts) if parts.is_empty()) => ret.as_ref().is_ok_and(|shown|
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
        Form::Sugared,
    )
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use gandr_surface_render_remote::OutKind;
    use gandr_surface_render_terminal::RenderStyle;
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
            LoopEvent::Block(block) => block.lines.last().cloned(),
            other @ (LoopEvent::Continue | LoopEvent::Quit) => {
                panic!("`{line}` answers a block, not {other:?}")
            },
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
            Some((OutKind::Value, String::from("fn (a) { a }"))),
            "a function terminal renders as its `fn`"
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
