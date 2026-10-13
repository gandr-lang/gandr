//! The diagnostics model: what one step of the dispatcher's walk reports — each
//! refusal, unsettled declaration, goal, shadowing warning, lint finding and
//! ledger line — as a [`Diagnostic`] every face projects, and the builders
//! that make it.
//!
//! # The model holds the diagnostic; a face only projects it
//!
//! [`diagnose`] builds a [`Diagnostic`] from what the producers recorded: the
//! refusal, the declaration's settlement, the lowering's origin table, the
//! [`Spellings`] the composition made while the arena was at hand, and the
//! [`Failure`] the checking machine kept when it refused a body. The
//! diagnostic owns its message and its stable key, its typed detail, its
//! annotations with their roles and exact byte spans, the contexts its refusal
//! stood inside with the binders each opened, the hypotheses in scope, the
//! note, the offending expression and the excerpt of source lines it covers.
//! `gandr-surface-render-terminal` lays it out as a snippet;
//! `gandr-surface-lsp` publishes it as an editor diagnostic, its primary
//! annotation the range and every other annotation and located context related
//! information. Neither reads a producer's type.
//!
//! **Choice.** This crate, renamed in place from the terminal renderer it was,
//! is the model and its builders; the renderer moved to its own crate beside
//! it. **Alternative.** A new `surface-report` crate holding the model beside
//! the renderer left under this name, which keeps the old name on the
//! terminal's projection and gives the model a name no face had depended on.
//! It lost because every consumer of this crate already read the model's
//! facts — class, span, label, note — through it, and the name says what it
//! holds. **Reversal.** If a second model is ever needed beside this one, a
//! face-neutral `surface-report` takes the shared part and this crate keeps
//! the builders.
//!
//! # Every span is the producer's
//!
//! A lowering refusal and a corpus refusal carry their spans. A checker refusal
//! names core nodes; the origin table maps each node the lowering minted back
//! to the syntax it came from, and a binder's name to where it was written. A
//! node the table records nothing for leaves its annotation out, and a
//! diagnostic with no primary annotation claims no span. Each span is checked
//! against the source's text before it is kept: a span outside the text, or
//! one splitting a character, is unlocated, never clamped. Nothing searches the
//! text for a plausible locus, and nothing widens an absent one to the whole
//! declaration: a guessed locus misleads where an honest absence only fails to
//! help.
//!
//! # The failure is the checker's own
//!
//! A checker refusal is built from the [`Failure`] the checking machine kept
//! when it refused: the rules it stood inside, outermost first, each with the
//! node whose judgement pushed it, how that node was judged and the binders it
//! opened, and the hypotheses in scope. The machine keeps them on the one run
//! that refused, so a diagnostic never re-runs the checker to explain a
//! refusal. The `frame` module reads each rule as a sentence and folds the
//! rules at one span into one context.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in the module that owns it.
//!
//! # Example
//!
//! ```
//! use gandr_surface_diagnostics::Severity;
//! use gandr_surface_diagnostics::Subject;
//! use gandr_surface_diagnostics::diagnose;
//! use gandr_surface_lowering::LoweringRefusal;
//! use gandr_surface_syntax::ByteOffset;
//! use gandr_surface_syntax::ByteSpan;
//! use gandr_surface_syntax::SourceText;
//! use quenchant_shape::shape::Maybe;
//!
//! let text = SourceText::from("def broken = missing ;\n");
//! let span = ByteSpan::new(ByteOffset::from(13_usize), ByteOffset::from(20_usize))?;
//! let diagnostic = diagnose(
//!     std::path::Path::new("broken.gandr"),
//!     text,
//!     Subject::Source(LoweringRefusal::UnresolvedName {
//!         span,
//!         name: "missing".into(),
//!     }),
//! );
//! assert_eq!(diagnostic.severity, Severity::Error);
//! assert_eq!(diagnostic.span, Maybe::Present(span));
//! assert_eq!(diagnostic.annotations[0].locus.line, 1_usize);
//! # Ok::<(), Box<dyn core::error::Error>>(())
//! ```
//!
//! # Specification discipline
//!
//! Nontrivial items carry executable predicates and bounded `# Adequacy`
//! claims. The nontrivial `Display` methods state an exemption:
//! `fmt::Formatter` exposes neither its output buffer nor an independent
//! destination-failure observer. The finite witnesses include UTF-8 splits and
//! end-of-file spans; invalid primary and context loci retain their distinct
//! absence reasons.
//!
//! [`Failure`]: gandr_core_checker::Failure

extern crate alloc;

mod culprit;
mod frame;
mod lint;
mod locus;
mod message;
mod model;
mod report;
mod spelled;
mod verbosity;

pub use crate::culprit::Culprit;
pub use crate::frame::Sentence;
pub use crate::frame::sentence;
pub use crate::lint::Lint;
pub use crate::locus::Label;
pub use crate::model::AnnotationKind;
pub use crate::model::Binding;
pub use crate::model::Compared;
pub use crate::model::Detail;
pub use crate::model::Diagnostic;
pub use crate::model::DiagnosticAnnotation;
pub use crate::model::DiagnosticContext;
pub use crate::model::DiagnosticDetail;
pub use crate::model::Excerpt;
pub use crate::model::Fix;
pub use crate::model::Identifier;
pub use crate::model::Judged;
pub use crate::model::Locus;
pub use crate::model::Message;
pub use crate::model::MessageKey;
pub use crate::model::Severity;
pub use crate::model::binding;
pub use crate::model::context_locus;
pub use crate::model::expression;
pub use crate::model::fix;
pub use crate::model::located;
pub use crate::model::producer;
pub use crate::report::Class;
pub use crate::report::PATHLESS;
pub use crate::report::Subject;
pub use crate::report::Unsettlement;
pub use crate::report::diagnose;
pub use crate::report::report_identifier;
pub use crate::report::report_note;
pub use crate::report::report_span;
pub use crate::spelled::Failures;
pub use crate::spelled::Families;
pub use crate::spelled::Spellings;
pub use crate::spelled::constant_names;
pub use crate::spelled::kept;
pub use crate::spelled::spelling;
pub use crate::verbosity::Verbosity;
