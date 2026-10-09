//! **The renderer seam**: the plain data a pipeline hands a renderer, and the
//! versioned frame that carries it across a process boundary.
//!
//! The crate parses, lowers, types and marks nothing, and names no other
//! crate of the workspace, so a language server, a terminal face or an agent
//! links it without linking the checker. Three modules:
//!
//! - `present`: highlight and mark spans over validated byte ranges, diagnostic
//!   and goal cards, transcript blocks, and the projection from a byte offset
//!   to a zero-based row and column: a character column for an editor widget, a
//!   UTF-16 column over a line index for a language server.
//! - `diagnostic`: the registry of stable diagnostic codes, each with its
//!   localizable message template, and the typed message arguments.
//! - `wire`: the render-bus [`RenderFrame`] — a document-scoped or
//!   connection-scoped [`FrameBody`] under the wire schema version
//!   [`WIRE_SCHEMA_VERSION`].
//!
//! # `serde`
//!
//! The default-off `serde` feature derives the serde wire image of every type
//! here. Decoding validates: a byte range whose end lies before its start, a
//! frame at another schema version, and a frame whose routing keys disagree
//! with its body are refused, so a decoded value holds every invariant a
//! constructed one does.
//!
//! # Example
//!
//! ```
//! use gandr_surface_render_remote::ByteOffset;
//! use gandr_surface_render_remote::ByteRange;
//! use gandr_surface_render_remote::DocId;
//! use gandr_surface_render_remote::DocVersion;
//! use gandr_surface_render_remote::DocumentUri;
//! use gandr_surface_render_remote::FrameScope;
//! use gandr_surface_render_remote::HlRole;
//! use gandr_surface_render_remote::HlSpan;
//! use gandr_surface_render_remote::Pos;
//! use gandr_surface_render_remote::PositionColumn;
//! use gandr_surface_render_remote::PositionRow;
//! use gandr_surface_render_remote::RenderFrame;
//! use gandr_surface_render_remote::ReportView;
//! use gandr_surface_render_remote::SourceText;
//! use gandr_surface_render_remote::pos_of_byte;
//!
//! let source = "def x = 1 ;\ndef y = x ;";
//! let keyword = HlSpan {
//!     range: ByteRange::new(ByteOffset::from(12_usize), ByteOffset::from(15_usize))?,
//!     role: HlRole::Keyword,
//! };
//! assert_eq!(
//!     pos_of_byte(SourceText::from(source), keyword.range.start())?,
//!     Pos {
//!         row: PositionRow::from(1_usize),
//!         col: PositionColumn::from(0_usize),
//!     },
//!     "the second line's keyword opens the second row"
//! );
//!
//! let document = DocId {
//!     uri: DocumentUri::from(String::from("file:///example.gandr")),
//!     version: DocVersion::from(3_i32),
//! };
//! let frame = RenderFrame::frame(document.clone(), ReportView {
//!     highlights: vec![keyword],
//!     ..ReportView::default()
//! });
//! assert_eq!(
//!     frame.scope(),
//!     &FrameScope::Document(document),
//!     "a report frame is routed to its document"
//! );
//! # Ok::<(), Box<dyn core::error::Error>>(())
//! ```
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

#![no_std]

extern crate alloc;

mod diagnostic;
mod present;
mod wire;

pub use crate::diagnostic::DIAGNOSTIC_CODES;
pub use crate::diagnostic::DiagnosticCode;
pub use crate::diagnostic::DiagnosticMessage;
pub use crate::diagnostic::DiagnosticTemplate;
pub use crate::diagnostic::UnknownDiagnosticCode;
pub use crate::present::ByteOffset;
pub use crate::present::ByteRange;
pub use crate::present::DiagCard;
pub use crate::present::GoalCard;
pub use crate::present::HlRole;
pub use crate::present::HlSpan;
pub use crate::present::InvertedRange;
pub use crate::present::LineIndex;
pub use crate::present::MarkKind;
pub use crate::present::MarkSpan;
pub use crate::present::OutKind;
pub use crate::present::Pos;
pub use crate::present::PosOfByteError;
pub use crate::present::PositionColumn;
pub use crate::present::PositionRow;
pub use crate::present::SourceText;
pub use crate::present::TranscriptBlock;
pub use crate::present::Utf16Column;
pub use crate::present::Utf16Pos;
pub use crate::present::byte_of_pos;
pub use crate::present::pos_of_byte;
pub use crate::wire::DocId;
pub use crate::wire::DocVersion;
pub use crate::wire::DocumentUri;
pub use crate::wire::FrameBody;
pub use crate::wire::FrameScope;
pub use crate::wire::RenderFrame;
pub use crate::wire::ReportView;
pub use crate::wire::WIRE_SCHEMA_VERSION;
pub use crate::wire::WireSchemaVersion;
