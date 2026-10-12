//! The read-evaluate loop over the interactive session.
//!
//! A [`SessionLoop`] takes lines. A line opening with `:` while no buffer is
//! waiting is a meta-command; any other line joins the buffer, and once the
//! parser expects no further token — [`completeness()`] — the buffer is
//! submitted to the session as the next chunk of one growing revision.
//!
//! # A chunk is kept only when nothing in it was refused
//!
//! The session judges each revision whole, exactly as `gandr check --goals`
//! judges a strict source. The loop owns the accepted text and submits it with
//! the new chunk after it; the chunk joins the accepted text only when the
//! revision drew no refusal, so the accepted text never carries one and a
//! refused chunk leaves the next submission where the last accepted one was.
//!
//! The session judges whole revisions and keeps no text, so the loop owns the
//! accepted text and submits it with each new chunk after it: a later line sees
//! every declaration kept before it. A chunk is kept when its revision drew no
//! refusal — no refusal, no unsettled declaration, no refusal of the revision
//! as a whole — and is otherwise dropped, the accepted text and the
//! declarations' standings unchanged. The encoder reports a declaration when
//! the chunk introduced it, or when its outcome differs from the accepted
//! revision's, which is how a definition settling an earlier signature is seen.
//!
//! Keeping every chunk would repeat a refused declaration at each later
//! submission or require age filtering. Dropping it keeps accepted text clean.
//! Reports count lines and columns from the first accepted line: `:load`
//! submits one chunk whose reports address the session, not the file. The
//! choice reverses when lowering accepts earlier declarations as a seed,
//! allowing reports to address each chunk alone.
//!
//! # The transcript is the renderer seam's
//!
//! [`encode_submission`] turns what a chunk changed into a
//! [`TranscriptBlock`](gandr_surface_render_remote::TranscriptBlock): a type
//! line per checked declaration, laid out by the presentation printer through
//! [`spell`], a goal line per owed one, the diagnostics renderer's report per
//! refusal, and a card per parse repair ([`repair_cards`]). The encoder is a
//! library function, so every face draws the same blocks.
//!
//! A block's `rows` layout contains the echo followed by result lines,
//! retaining kinds, leads, text and byte offsets. The first row takes the
//! kind's mark; subsequent nonempty rows take its indentation, and empty rows
//! take no indentation. Type and diagnostic rows have no mark. CRLF terminators
//! are stripped; a lone carriage return is retained. `write_block` writes this
//! layout without flushing; faces flush on normal or faulted endings, but not
//! after write errors. A flush error takes precedence over the ending being
//! returned.
//!
//! # Two faces, one layout
//!
//! [`run_batch`] reads any line source and writes a plain transcript,
//! deterministically; [`run_interactive`] reads a terminal through a line
//! editor. Both drive the same loop. A block's [`rows()`] are its one layout:
//! [`write_block`] prints them, and a full-screen face paints the same rows.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in the module that owns it.
//!
//! # A verb of the driver
//!
//! The loop is reached as `gandr repl`, beside `check`, `test`, `lsp` and
//! `tui`; bare `gandr` keeps its status report. Making bare `gandr` the loop or
//! treating a file path as a verb would change the driver specification. The
//! choice reverses if bare `gandr` is designated the loop.
//!
//! # Specification evidence
//!
//! The crate has 45 tests. Predicates observe branch decisions, empty-state
//! boundaries, byte ranges, preserved payloads and transcript kinds; a type's
//! absence reasons are the session's and witnessed there. They do not parse,
//! print, evaluate or clone a whole session a second time. The corpus spelling
//! witness covers one-line signatures in three selected strict sources, not
//! every corpus file or arbitrary syntax. Diagnostic prose is not a golden
//! interface.
//!
//! | Boundary | Witness |
//! | -------- | ------- |
//! | Empty, incomplete and complete input | `loop::tests::an_empty_buffer_is_complete`, `loop::tests::a_declaration_waits_for_its_terminator` |
//! | Pasted lines, ignored blank input, interruption and retained declarations | `loop::tests::multiline_and_interrupted_buffers_preserve_accepted_declarations` |
//! | Unicode literal coverage and scalar boundaries | `highlight::tests::unicode_literals_keep_their_byte_boundaries` |
//! | Old, crossing and zero-width repairs; distinguishable repair classes | `remote::tests::repair_boundaries_preserve_locations_and_distinct_classes` |
//! | Every output kind, UTF-8 byte offsets, empty rows, CRLF and lone carriage returns | `loop::tests::row_kinds_and_unicode_boundaries_keep_their_meaning` |
//! | Empty transcript performs no write or flush | `loop::tests::empty_transcripts_do_not_touch_the_writer` |
//! | Partial-write refusal, skipped flush and flush-error precedence | `loop::tests::write_and_flush_failures_keep_their_kind` |
//! | End and failed reads leave later events unread and flush once | `loop::tests::terminal_endings_stop_reads_and_flush_once` |
//!
//! The terminal adapter additionally needs a pseudo-terminal smoke: fresh and
//! continuing prompts, a completed definition, an interrupted buffer, a
//! definition referring to accepted text, and EOF with a pending buffer.
//! Scripted tests observe the same state transitions but cannot establish
//! terminal-device behavior.
//!
//! Five items have explicit executable exemptions. Their boundary witnesses
//! observe behavior that the signature cannot inspect without consuming it or
//! adding an observer:
//!
//! | Item | Why no runtime predicate |
//! | ---- | ------------------------ |
//! | `rows::line_rows` | The opaque one-shot iterator has no row observer or clone; consuming it would change the caller's rows. |
//! | `rows::rows` | The same opaque iterator boundary prevents observing rows before returning them. |
//! | `LineSource::read` | An abstract source exposes no history observer; the caller's stopping obligation is not a return-value property. |
//! | `interactive::drive` | Arbitrary sources can return any fault kind; generic writers expose neither transcript nor flush state. |
//! | `interactive::converse` | The same generic source and writer prevent observing the transcript and read sequence. |
//!
//! Single-pass iterators and generic I/O remain the API instead of adding
//! collection, cloning or observer traits solely for assertions. Reconsider an
//! exemption if its API gains a non-consuming semantic observer. All predicates
//! and witnesses run in the enforcing lane; executable checks are a bounded
//! part of the specification, not proof of the whole protocol.
//!
//! # References
//!
//! - David Moon, Andrew Blinn, Thomas J. Porter and Cyrus Omar. "Syntactic
//!   Completions with Material Obligations." _Proceedings of the ACM on
//!   Programming Languages_ 9, OOPSLA2 (2025).
//!   <https://doi.org/10.1145/3763182>, arXiv:2508.16848 — the expected set the
//!   gate reads, and the obligation classes a repair card names.
//! - The rustyline contributors. `rustyline` 18.0.1. <https://docs.rs/rustyline/18.0.1/rustyline/>
//!   — the line editor of the terminal face.

extern crate alloc;

mod batch;
mod completeness;
mod encode;
mod highlight;
mod interactive;
mod live_match;
mod meta;
mod remote;
mod render;
mod rows;
mod session_loop;

pub use gandr_surface_parser::CompletionStatus;

pub use crate::batch::Ended;
pub use crate::batch::Fault;
pub use crate::batch::run_batch;
pub use crate::batch::write_block;
pub use crate::completeness::completeness;
pub use crate::encode::Disposition;
pub use crate::encode::Echo;
pub use crate::encode::Encoded;
pub use crate::encode::Offer;
pub use crate::encode::Standings;
pub use crate::encode::Subject;
pub use crate::encode::encode_submission;
pub use crate::highlight::SpanOrder;
pub use crate::highlight::highlight_source;
pub use crate::highlight::span_order;
pub use crate::interactive::LineSource;
pub use crate::interactive::Read;
pub use crate::interactive::drive;
pub use crate::interactive::run_interactive;
pub use crate::live_match::encode_match;
pub use crate::remote::repair_cards;
pub use crate::render::spell;
pub use crate::rows::Lead;
pub use crate::rows::Mark;
pub use crate::rows::Row;
pub use crate::rows::rows;
pub use crate::session_loop::Faulted;
pub use crate::session_loop::LoopError;
pub use crate::session_loop::LoopEvent;
pub use crate::session_loop::Prompt;
pub use crate::session_loop::SessionLoop;
pub use crate::session_loop::finished;
