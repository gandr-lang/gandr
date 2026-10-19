//! The completeness gate: a buffer is submitted once the parser expects no
//! further token.
//!
//! # Completeness is the parser's
//!
//! A buffer is submitted when the parser's push machine, having molded its
//! tokens, expects nothing more. Complete is not clean: a repaired buffer can
//! be complete and is submitted with its diagnostics. Empty fresh input is
//! ignored. Offered text may contain pasted line breaks, which are preserved;
//! meta-commands dispatch only without a pending buffer. EOF submits a pending
//! buffer regardless of completeness. An interrupt discards pending text
//! without forgetting accepted declarations.

use anodized::spec;
use gandr_surface_grammar::LabelText;
use gandr_surface_grammar::Pbg;
use gandr_surface_parser::CompletionStatus;
use gandr_surface_parser::DeclarationStart;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::Molder;
use gandr_surface_parser::TokenText;
use gandr_surface_parser::candidate_labels;
use gandr_surface_parser::declaration_head;
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
/// - witness: `tests::repl_loop::an_open_form_is_incomplete`
/// - witness: `tests::repl_loop::a_bare_atom_is_complete`
/// - witness: `tests::repl_loop::a_hole_is_complete`
/// - witness: `tests::repl_loop::a_declaration_waits_for_its_terminator`
/// - witness: `tests::repl_loop::an_empty_buffer_is_complete`
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

/// Whether `buffer`'s first significant token opens a declaration: whether the
/// parser's own declaration-head predicate accepts any mold the token's fresh
/// candidates carry.
///
/// # Specification
/// - requires: nothing; any text is admissible.
/// - ensures: true exactly when the buffer's first non-space token has a
///   candidate label whose fresh molds include one the parser's
///   declaration-head predicate accepts; false for an empty buffer and for a
///   buffer whose first token is no declaration head.
/// - provides: the gate that reads a complete buffer as an expression or a type
///   rather than as declarations.
/// - fails: never.
/// - panics: none.
/// - intension: one labelling pass over `buffer` and one scan of the first
///   token's fresh candidates; no tree is committed.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration head and a bare atom differ at the first
///   token's fresh candidates.
/// - witness: `tests::repl_loop::an_expression_is_read_as_a_probe`
#[spec(ensures: |ret| !bool::from(ret) || !<&str>::from(buffer).is_empty())]
#[inline]
#[must_use]
pub fn first_token_is_declaration(
    grammar: &Pbg,
    buffer: SourceText<'_>,
) -> DeclarationStart
{
    let source = SourceFragment::from(<&str>::from(buffer));
    let tokens = label(source);
    let Some(token) = tokens
        .iter()
        .find(|token| !matches!(token.lexeme, Lexeme::Space))
    else {
        return DeclarationStart::from(false);
    };
    let slice = token.text(&source);
    let text = TokenText::from(AsRef::<str>::as_ref(&slice));
    DeclarationStart::from(candidate_labels(token.lexeme, text).iter().any(|&label| {
        grammar
            .tile_label(LabelText(<&str>::from(label)))
            .is_some_and(|label| {
                grammar
                    .fresh_candidates(label)
                    .iter()
                    .any(|&mold| bool::from(declaration_head(grammar, mold)))
            })
    }))
}
