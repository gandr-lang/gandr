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
//! # The transcript is the renderer seam's
//!
//! [`encode_submission`] turns what a chunk changed into a
//! [`TranscriptBlock`](gandr_surface_render_remote::TranscriptBlock): a type
//! line per checked declaration in [`spell`]'s one spelling, a goal line per
//! owed one, the diagnostics renderer's report per refusal, and a card per
//! parse repair ([`repair_cards`]). The encoder is a library function, so every
//! face draws the same blocks.
//!
//! # Two faces, one layout
//!
//! [`run_batch`] reads any line source and writes a plain transcript,
//! deterministically; [`run_interactive`] reads a terminal through a line
//! editor. Both drive the same loop. A block's [`rows()`] are its one layout:
//! [`write_block`] prints them, and a full-screen face paints the same rows.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

extern crate alloc;

mod batch;
mod completeness;
mod encode;
mod highlight;
mod interactive;
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
pub use crate::encode::spelled;
pub use crate::highlight::SpanOrder;
pub use crate::highlight::highlight_source;
pub use crate::highlight::span_order;
pub use crate::interactive::LineSource;
pub use crate::interactive::Read;
pub use crate::interactive::drive;
pub use crate::interactive::run_interactive;
pub use crate::remote::repair_cards;
pub use crate::render::Fidelity;
pub use crate::render::Spelling;
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
