//! The terminal face over the read-evaluate loop.
//!
//! An [`App`] holds one `gandr-surface-repl` loop, the line being edited, the
//! lines the loop holds for the parser, and every transcript block the loop
//! answered. [`draw`] paints it full-screen: the transcript pane lays each
//! block out as the loop's rows, the same rows the plain transcript prints,
//! and styles them through [`style_of`], total over the highlight roles, and
//! [`style_of_kind`], total over the line kinds; the input pane holds the
//! waiting lines and the line; a status line says what the keys do.
//!
//! # One loop, three ways to drive it
//!
//! [`drive`] is the event loop: draw, read an [`Input`], apply it. [`run()`]
//! drives it over the terminal's keys in raw mode on the alternate screen;
//! [`run_smoke`] drives it once on a headless backend and prints
//! [`SMOKE_NOTE`]; a test drives it over scripted keys. The face parses,
//! lowers, types and marks nothing: every line goes to the loop, and every
//! block it paints is the loop's.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

extern crate alloc;

mod app;
mod run;
mod theme;
mod view;

pub use crate::app::App;
pub use crate::app::Handled;
pub use crate::app::Key;
pub use crate::run::Input;
pub use crate::run::InputSource;
pub use crate::run::SMOKE_NOTE;
pub use crate::run::drive;
pub use crate::run::run;
pub use crate::run::run_smoke;
pub use crate::theme::style_of;
pub use crate::theme::style_of_kind;
pub use crate::view::draw;
