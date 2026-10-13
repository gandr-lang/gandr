//! Lays a diagnostic out for a terminal: the snippet `gandr check` and
//! `gandr test` print, the transcript the session writes, and the plain text
//! the tests compare.
//!
//! # A projection of the model
//!
//! [`render()`] reads one `gandr_surface_diagnostics::Diagnostic` and writes
//! it: its severity, identifier and message on the first line, its excerpt
//! with each annotation and each located context marked at its bytes, each
//! unlocated context and its note as notes, and the details its
//! `Verbosity` adds. It reads no producer's type and composes nothing: what
//! a diagnostic says is decided once, in the model, and every face shows the
//! same facts. The alternative was the renderer reading the step and the
//! producers' refusals itself, as it did before the model existed, which let
//! the terminal and the editor disagree about a refusal's loci and causes.
//! Reversal: a layout that needs a fact the model does not hold adds it to
//! the model, never a second reading here.
//!
//! # The backend stays behind the API
//!
//! `annotate-snippets` lays the snippet out. None of its types crosses this
//! crate's API: a consumer reads [`RenderStyle`], [`TerminalCapability`] and
//! [`Rendered`]. This crate is the only one in the workspace that depends on
//! it.
//!
//! The snippet layout is
//! [`annotate-snippets`](https://docs.rs/annotate-snippets/0.12.16) 0.12.16,
//! maintained by the Rust project and used by rustc and cargo, with default
//! features off. It adds three crates to the graph — `annotate-snippets`,
//! `anstyle`, which `clap` already brings, and `unicode-width` — and builds
//! without `std`, so a rendering is a `String` and nothing else.
//!
//! | Candidate | Why it lost |
//! | --------- | ----------- |
//! | [`codespan-reporting`](https://docs.rs/codespan-reporting/0.13.1) 0.13.1 | the closest second: two crates, but colour goes through `termcolor` or a hand-written style writer, and its file database answers lookups fallibly where the diagnostic already holds its excerpt |
//! | [`ariadne`](https://docs.rs/ariadne/0.6.0) 0.6.0 | one maintainer, its GitHub repository archived on a move to another host, and `yansi` always linked |
//! | [`miette`](https://docs.rs/miette/7.6.0) 7.6.0 | the graphical handler needs `fancy-base`, about thirty crates including `syn`, and reports must implement its `Diagnostic` trait |
//!
//! The choice reverses on a security advisory or an unmaintained notice against
//! `annotate-snippets`, on the Rust project ceasing to use it, or on a release
//! that drops plain rendering or the `std`-free build; `codespan-reporting` is
//! next.
//!
//! # Example
//!
//! ```
//! use gandr_surface_diagnostics::Subject;
//! use gandr_surface_diagnostics::Verbosity;
//! use gandr_surface_diagnostics::diagnose;
//! use gandr_surface_render_terminal::RenderStyle;
//! use gandr_surface_render_terminal::render;
//! use gandr_surface_syntax::SourceText;
//!
//! let diagnostic = diagnose(
//!     std::path::Path::new("ledger.gandr"),
//!     SourceText::from(""),
//!     Subject::Ledger {
//!         line: "unsettled: a pending source",
//!         at: quenchant_shape::shape::Maybe::Absent(
//!             gandr_surface_diagnostics::report_span::Absent::Standing,
//!         ),
//!     },
//! );
//! assert_eq!(
//!     render(&diagnostic, RenderStyle::Plain, Verbosity::User).as_ref(),
//!     "ledger.gandr: unsettled: a pending source"
//! );
//! ```
//!
//! # Specification discipline
//!
//! Nontrivial items carry executable predicates and bounded `# Adequacy`
//! claims. The rendering goldens are layout examples, not exhaustive backend
//! coverage.

extern crate alloc;

mod render;
mod style;

pub use crate::render::render;
pub use crate::style::RenderStyle;
pub use crate::style::Rendered;
pub use crate::style::TerminalCapability;
