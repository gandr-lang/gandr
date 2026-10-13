//! Renders what one step of the dispatcher's walk prints: each refusal, each
//! unsettled declaration and each goal as a source snippet with its span, what
//! the span is and its message, and each ledger line a verb prints beside them.
//!
//! # The one input is the step
//!
//! [`entries`] reads a [`Step`] whole, under the verb its walk runs. A
//! declaration and the refusal it produced are one [`DeclarationReport`], so a
//! refusal the walk carries cannot miss the renderer: a face that read
//! refusals from a list kept beside the declarations could lose one recorded
//! only with its declaration.
//!
//! `entries` reads the whole `Step` under its verb. A declaration and the
//! refusal it produced are one `DeclarationReport`, so every refusal the walk
//! carries reaches the renderer with its declaration; a face reading refusals
//! from a list kept beside the declarations could drop one. The step carries
//! the three things rendering needs and the composition already had: the
//! source's text, borrowed; the lowering's origin table, moved out of the
//! lowered module once checking is done; and the spellings of the types its
//! checker refusals compare, made while the arena was at hand.
//!
//! Passing text separately while exposing the composed module would split one
//! fact across calls that must agree. The choice reverses if a consumer needs
//! to render a source it never walked; such a consumer needs a constructor
//! taking text and origins together.
//!
//! # Every span is the producer's
//!
//! A lowering refusal and a corpus refusal carry their spans; a checker
//! refusal names core nodes, which the lowering's origin table, carried in the
//! step, maps back to the syntax that produced them. A node the table holds
//! nothing for leaves its locus absent: a report with no primary locus names
//! its source's path and claims no span. Nothing here searches the text for a
//! plausible one.
//!
//! A lowering refusal and a corpus refusal carry their spans. A checker refusal
//! names core nodes; the origin table maps each node the lowering minted back
//! to the syntax it came from. A node the table records nothing for leaves its
//! locus absent, and a report with no primary locus names its source's path and
//! quotes no line. Each span is checked against the step's text before it is
//! laid out: a span outside the text, or one splitting a character, is
//! unlocated, never clamped. Nothing searches the text for a plausible locus,
//! and nothing widens an absent one to the whole declaration: a guessed locus
//! misleads where an honest absence only fails to help.
//!
//! # The backend stays behind the API
//!
//! `annotate-snippets` lays the snippet out. None of its types crosses this
//! crate's API: a consumer reads [`Report`], [`Class`], [`RenderStyle`],
//! [`Verbosity`] and [`Rendered`].
//!
//! The snippet layout is
//! [`annotate-snippets`](https://docs.rs/annotate-snippets/0.12.16) 0.12.16,
//! maintained by the Rust project and used by rustc and cargo, with default
//! features off. It adds three crates to the graph — `annotate-snippets`,
//! `anstyle`, which `clap` already brings, and `unicode-width` — and builds
//! without `std`, so a rendering is a `String` and nothing else. None of its
//! types crosses this crate's API.
//!
//! | Candidate | Why it lost |
//! | --------- | ----------- |
//! | [`codespan-reporting`](https://docs.rs/codespan-reporting/0.13.1) 0.13.1 | the closest second: two crates, but colour goes through `termcolor` or a hand-written style writer, and its file database answers lookups fallibly where the step already holds the text |
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
//! use gandr_surface_diagnostics::RenderStyle;
//! use gandr_surface_diagnostics::Verbosity;
//! use gandr_surface_diagnostics::entries;
//! use gandr_surface_dispatcher::Goals;
//! use gandr_surface_dispatcher::Verb;
//! use gandr_surface_dispatcher::Walk;
//! use quenchant_shape::shape::Maybe;
//!
//! let directory =
//!     std::env::temp_dir().join(format!("gandr-diagnostics-doc-{}", std::process::id()));
//! std::fs::create_dir_all(&directory)?;
//! let path = directory.join("broken.gandr");
//! std::fs::write(&path, "def answer = 42 ;\ndef broken = missing ;\n")?;
//!
//! let verb = Verb::Check(Goals::Gated);
//! let mut walk = Walk::new(vec![path]);
//! let mut printed = Vec::new();
//! while let Maybe::Present(step) = walk.step() {
//!     for entry in entries(&step, verb) {
//!         printed.push(
//!             entry
//!                 .render(RenderStyle::Plain, Verbosity::User)
//!                 .to_string(),
//!         );
//!     }
//! }
//! std::fs::remove_dir_all(&directory)?;
//! assert_eq!(printed.len(), 1, "one unsettled declaration, one report");
//! # Ok::<(), Box<dyn core::error::Error>>(())
//! ```
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in the module that owns it.
//!
//! [`Step`]: gandr_surface_dispatcher::Step
//! [`DeclarationReport`]: gandr_surface_corpus::DeclarationReport
//!
//! # Specification discipline
//!
//! Nontrivial items carry executable predicates and bounded `# Adequacy`
//! claims. Borrowed identity checks avoid copying or scanning source text.
//! Enforcing tests exercise span validity and causal labels alongside iterator
//! progress and numeric payload roles. The nontrivial `Display` methods state
//! an exemption: `fmt::Formatter` exposes neither its output buffer nor an
//! independent destination-failure observer.
//!
//! The finite witnesses include UTF-8 splits and end-of-file spans. Invalid
//! primary and context loci retain their distinct absence reasons; no span is
//! clamped. The rendering goldens are layout examples, not exhaustive backend
//! coverage. Each item's Rustdoc states its domain and links its own-crate
//! witnesses.

mod culprit;
mod entry;
mod locus;
mod message;
mod report;
mod style;

pub use crate::culprit::Culprit;
pub use crate::entry::Entries;
pub use crate::entry::Entry;
pub use crate::entry::Line;
pub use crate::entry::entries;
pub use crate::locus::Annotation;
pub use crate::locus::Comparison;
pub use crate::locus::Judging;
pub use crate::locus::Label;
pub use crate::locus::PrimaryLabel;
pub use crate::locus::Reason;
pub use crate::locus::report_context;
pub use crate::report::Class;
pub use crate::report::Detail;
pub use crate::report::Message;
pub use crate::report::Note;
pub use crate::report::Report;
pub use crate::report::Title;
pub use crate::report::Unsettlement;
pub use crate::report::report_identifier;
pub use crate::report::report_note;
pub use crate::report::report_span;
pub use crate::style::RenderStyle;
pub use crate::style::Rendered;
pub use crate::style::TerminalCapability;
pub use crate::style::Verbosity;
