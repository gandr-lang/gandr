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
//! `serde` is off by default. It enables serde with `alloc`, for the owned
//! strings and vectors and the tagged enums' buffered content, and `derive`.
//! JSON (`serde_json`, `alloc` only) is a development dependency: the codec
//! witnesses round-trip through it, and the crate chooses no format for a
//! transport. The crate also names itself as a development dependency with
//! `serde` on, so every test build carries the codec and the workspace suite
//! runs the witnesses the serde impls cite; the default library build stays
//! without it.
//!
//! An in-process renderer pays for no serialization machinery. The alternatives
//! were serde always on, which compiles the derive stack into every renderer,
//! and a hand-written codec, which owns a format serde already provides through
//! its data model. The choice reverses on a high-risk advisory or an
//! unmaintained mark against serde, or on a transport whose format serde cannot
//! carry.
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
//! reverse it, is in the module that owns it.
//!
//! # Readers
//!
//! Each form here has a reader that lands with it or next:
//!
//! | Form | Reader |
//! | ---- | ------ |
//! | `HlRole`, `HlSpan`, `ByteOffset`, `ByteRange` | the mold highlighter in `gandr-surface-grammar`, which classifies each tile by its mold; then the language server's semantic tokens, the read-evaluate loop's echo and the terminal face's paint |
//! | `DiagCard`, `DiagnosticCode`, `DiagnosticMessage` | the read-evaluate loop's parse-repair cards under `W0012`; the session report that maps refusals onto codes, and the language server's diagnostics once they carry that report's codes |
//! | `TranscriptBlock`, `OutKind` | the read-evaluate loop's transcript encoder and the terminal face that draws it |
//! | `SourceText`, `Pos`, `pos_of_byte`, `byte_of_pos` | a renderer that addresses rows and columns: the terminal face's cursor, the language server's ranges |
//! | `LineIndex`, `Utf16Pos`, `Utf16Column` | the language server's diagnostic ranges, related locations and semantic tokens |
//! | `MarkSpan`, `RenderFrame`, `ReportView` | the engine hub's render-bus face in `gandr-surface-lsp`, which writes a report per publication, and the side view in `gandr-surface-tui`, which reads it |
//! | `GoalCard` | a renderer in another process, once goals carry spelled types |
//!
//! # A leaf beside the pipeline
//!
//! The crate depends on no workspace crate. A renderer that links it links
//! strings, ranges and enums, never the parser, the checker or their
//! dependencies, and nothing the pipeline adds can make a renderer re-implement
//! typing: if a renderer needs information this vocabulary cannot carry, the
//! fix is a field here filled by the pipeline, so every renderer gains it at
//! once. `ByteOffset` is therefore this crate's own, not the concrete syntax
//! tree's; a producer converts at its edge.
//!
//! The alternatives were reusing the syntax tree's offset and span, which ties
//! every renderer to the tree crate and its digest and specification
//! dependencies, and a vocabulary per renderer, which forks the moment two
//! renderers paint one report. The choice reverses only if a renderer genuinely
//! needs the tree itself, which would make it a pipeline stage rather than a
//! renderer.
//!
//! # Forms this crate does not carry
//!
//! Each form below is left out because no reader is scheduled for it; each
//! arrives with the reader named beside it, and not before, because a form
//! nothing reads is an untested promise.
//!
//! | Form | Arrives with |
//! | ---- | ------------ |
//! | a node-keyed delta body, its patch form and the capability that advertises it | an incremental delta engine that produces patches, together with a renderer that applies them; until then every report is a whole `Frame` |
//! | obligation cards and their severity-ordered classes, and the capability that advertises them | the same delta engine's reader; until then a parser's recovery obligation can reach a renderer as a `DiagCard` under `W0012` |
//! | a capability advertisement on `Hello` | the first capability a server can back; a flag with no machinery behind it would advertise a channel no server fills |
//! | the typing machine's projection: the derivation forest, the control register, the frame-stack summary and the machine digest | an inspection face that paints the typing machine; the forest arrives as an arena of nodes addressed by id, never as nodes that own their children |
//! | attribute cards | an attribute inspection face |
//! | the type under a cursor and completion candidates | the language server's hover and completion over goals, once hole goals and the checker's spellings carry them |
//! | a preview frame of the buffer before submission | a terminal face that previews a buffer before it is submitted |
//!
//! # References
//!
//! - Eric Zhao, Raef Maroof, Anand Dukkipati, Andrew Blinn, Zhiyi Pan, and
//!   Cyrus Omar. "Total Type Error Localization and Recovery with Holes."
//!   _Proceedings of the ACM on Programming Languages_ 8, POPL (January 2024).
//!   `doi:10.1145/3632910` — marks: an error located at the term it concerns,
//!   and an empty hole tinted rather than reported, which `MarkSpan` and
//!   `MarkKind` carry.
//! - Kohei Honda, Vasco T. Vasconcelos, and Makoto Kubo. "Language Primitives
//!   and Type Discipline for Structured Communication-Based Programming." In
//!   _Programming Languages and Systems (ESOP 1998)_, Lecture Notes in Computer
//!   Science 1381, pages 122–138, 1998. `doi:10.1007/BFb0053567` — the binary
//!   session the frame's message set is the projection of.
//! - Simon J. Gay and Malcolm Hole. "Subtyping for Session Types in the Pi
//!   Calculus." _Acta Informatica_ 42, 2–3 (2005), pages 191–225.
//!   `doi:10.1007/s00236-005-0177-z` — the subtyping under which a typed
//!   endpoint can later carry the same messages.
//! - Microsoft. "Language Server Protocol Specification 3.17." <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/>
//!   — the document URI and version a frame is routed by, and the position
//!   encoding a language server converts a character column into.

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
