//! Editor sessions driven one keystroke at a time.
//!
//! A buffer models the editor: its text, its cursor, the closers and the
//! indentation it inserts for the writer, and the edit each keystroke sends.
//! A typist reaches a target text through the keystrokes a person makes. Each
//! keystroke is synchronised with the server — through `serve` itself for a
//! single editor, in process over a shared workspace for two — and checked
//! before the next: the server answers every change before it reads the next
//! message, so the session runs in lockstep and every intermediate text is a
//! case. The oracle is a fresh connection opening the same text whole.

extern crate alloc;

/// The cases, in a `cfg(test)` module so the crate's lint wall reads them as
/// test code rather than as shipping code.
#[cfg(test)]
mod editor
{
    mod buffer;
    mod client;
    mod editing;
    mod scenarios;
    mod shapes;
    mod typist;
}
