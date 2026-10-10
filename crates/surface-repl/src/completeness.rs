//! The completeness gate: a buffer is submitted once the parser expects no
//! further token.

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_parser::CompletionStatus;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::Molder;
use gandr_surface_parser::label;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

/// Whether `buffer` is parse-complete under `grammar`: whether the parser,
/// having read it, expects no further token.
///
/// # Specification
/// - requires: nothing; any text is admissible.
/// - ensures: complete exactly when molding `buffer`'s tokens through the
///   parser's push machine leaves no form open and no operand owed at the end
///   of input. A hole `?` is a complete term, so a buffer holding one is
///   submitted and typed; complete is not clean, so a buffer whose parse needs
///   a repair inside it can still be complete.
/// - provides: the gate the loop submits on.
/// - fails: never.
/// - panics: none.
/// - intension: one labelling and one molding pass over `buffer`; no tree is
///   committed.
///
/// # Adequacy
/// - hypothesis: L3 — the gate's two sides: an open form and a declaration
///   without its terminator wait; a bare atom, a hole, a terminated declaration
///   and the empty buffer submit. The executable clause guards that empty
///   boundary; it does not repeat the labeling and molding passes.
/// - witness: `loop::tests::an_open_form_is_incomplete`
/// - witness: `loop::tests::a_bare_atom_is_complete`
/// - witness: `loop::tests::a_hole_is_complete`
/// - witness: `loop::tests::a_declaration_waits_for_its_terminator`
/// - witness: `loop::tests::an_empty_buffer_is_complete`
#[spec(ensures: |ret| !<&str>::from(buffer).is_empty() || bool::from(ret))]
#[inline]
#[must_use]
pub fn completeness(
    grammar: &Pbg,
    buffer: SourceText<'_>,
) -> CompletionStatus
{
    let mut molder = Molder::new(grammar);
    let mut state = MeldState::new(grammar);
    let tokens = label(SourceFragment::from(<&str>::from(buffer)));
    molder.mold_stream(&mut state, &tokens, buffer);
    state.expected().is_complete()
}
