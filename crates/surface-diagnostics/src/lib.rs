//! Renders what one step of the dispatcher's walk prints: each refusal, each
//! unsettled declaration and each goal as a source snippet with its span, its
//! class and its message, and each ledger line a verb prints beside them.
//!
//! # The one input is the step
//!
//! [`entries`] reads a [`Step`] whole, under the verb its walk runs. A
//! declaration and the refusal it produced are one [`DeclarationReport`], so a
//! refusal the walk carries cannot miss the renderer: a face that read
//! refusals from a list kept beside the declarations could lose one recorded
//! only with its declaration.
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
//! # The backend stays behind the API
//!
//! `annotate-snippets` lays the snippet out. None of its types crosses this
//! crate's API: a consumer reads [`Report`], [`Class`], [`RenderStyle`] and
//! [`Rendered`].
//!
//! # Example
//!
//! ```
//! use gandr_surface_diagnostics::Entry;
//! use gandr_surface_diagnostics::RenderStyle;
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
//!         match entry {
//!             | Entry::Report(report) => {
//!                 printed.push(report.render(RenderStyle::Plain).to_string())
//!             },
//!             | Entry::Line(line) => printed.push(line.to_string()),
//!         }
//!     }
//! }
//! std::fs::remove_dir_all(&directory)?;
//! assert_eq!(printed.len(), 1, "one unsettled declaration, one report");
//! assert!(
//!     printed[0].starts_with("error[UnresolvedName]: no declaration or binder answers `missing`"),
//!     "{}",
//!     printed[0]
//! );
//! # Ok::<(), Box<dyn core::error::Error>>(())
//! ```
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.
//!
//! [`Step`]: gandr_surface_dispatcher::Step
//! [`DeclarationReport`]: gandr_surface_corpus::DeclarationReport

mod entry;
mod locus;
mod report;
mod style;

pub use crate::entry::Entries;
pub use crate::entry::Entry;
pub use crate::entry::Line;
pub use crate::entry::entries;
pub use crate::report::Class;
pub use crate::report::Report;
pub use crate::report::Unsettlement;
pub use crate::report::report_span;
pub use crate::style::RenderStyle;
pub use crate::style::Rendered;
pub use crate::style::TerminalCapability;
