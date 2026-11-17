//! Sampled call stacks, read from `perf script -F ip,sym,srcline --inline`.
//!
//! Each sample is a run of frames, innermost first, ended by a blank line. A
//! frame line starts with a tab and holds the address and the symbol; the line
//! after it, indented by two spaces, holds the frame's source location as
//! `file:line`, suffixed ` (inlined)` for an inlined frame. Workspace files
//! are named relative to the workspace root; `??:0` marks a frame without
//! line information.

use std::io::BufRead;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::error::CostError;
use crate::region::Line;

/// A frame's symbol: a function name, or a generic instance of one.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Symbol(String);

impl From<&str> for Symbol
{
    /// Adopts `name` as a frame's symbol.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(name.to_owned())
    }
}

/// Whether a frame runs a specified function's body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Body
{
    /// The frame is anodized's `eval_once`, through which an instrumented
    /// function calls its own body.
    Entered,
    /// Any other frame.
    Elsewhere,
}

impl Symbol
{
    /// Whether this frame is the call into a specified function's body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Body::Entered`] exactly for anodized's `eval_once`, named
    ///   in full or as an inlined `eval_once<…>` instance.
    /// - provides: the frame that separates a function's body from its checks;
    ///   anodized spans the call into the body with the attribute, so the
    ///   caller's line alone cannot tell them apart.
    /// - panics: none.
    /// - executable: none — the two names are the definition; a predicate could
    ///   only repeat them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the full and the inlined `eval_once` names and the
    ///   `eval` a clause runs through; matching `eval` as well, or missing the
    ///   inlined form, changes the charged region.
    /// - witness: `ledger::tests::a_body_under_its_attribute_line_is_not_a_check`
    #[inline]
    #[must_use]
    pub fn body(&self) -> Body
    {
        if self.0.contains("anodized::__::eval_once") || self.0.starts_with("eval_once<") {
            Body::Entered
        }
        else {
            Body::Elsewhere
        }
    }
}

/// Where a frame was executing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Location
{
    /// The source file, resolved against the workspace root.
    pub file: PathBuf,
    /// The line.
    pub line: Line,
}

quenchant_shape::reason_enum! {
    /// Why a frame has no source location.
    pub mod position {
        /// The reason a frame's location is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// perf printed no location line for the frame.
            NotPrinted,
            /// The location is `??:0`, a line `0`, or not `file:line`.
            Unknown,
        }
    }
}

/// One frame of a sampled stack.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Frame
{
    /// The function the frame runs.
    pub symbol: Symbol,
    /// Where it was executing.
    pub location: Maybe<Location, position::Absent>,
}

quenchant_shape::reason_enum! {
    /// Why no further sample was read.
    pub mod exhausted {
        /// The reason a read returned no sample.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The script ended.
            EndOfScript,
        }
    }
}

/// A reader of `perf script` output, one sample at a time.
///
/// # Specification
/// - provides: samples in the order perf printed them, without holding the
///   whole script in memory.
#[derive(Debug)]
pub struct Stacks<R>
{
    /// The script.
    lines: R,
    /// The directory relative locations are resolved against.
    root: PathBuf,
    /// The line being read.
    buffer: String,
}

impl<R: BufRead> Stacks<R>
{
    /// Reads `lines`, resolving relative locations against `root`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn new(
        lines: R,
        root: &Path,
    ) -> Self
    {
        Self {
            lines,
            root: root.to_path_buf(),
            buffer: String::new(),
        }
    }

    /// The next sample's frames, innermost first.
    ///
    /// # Specification
    /// - requires: nothing — any text is admissible input.
    /// - ensures: the frames up to the next blank line or the end of the
    ///   script; a sample without frames is skipped.
    /// - provides: [`exhausted::Absent::EndOfScript`] once no frame remains.
    /// - fails: [`CostError::Io`] when the script cannot be read.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CostError::Io`] — reading the script failed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two samples, one ending without a trailing blank
    ///   line, with inlined, unknown, absolute and relative locations and a
    ///   frame with none; a merged sample, a lost frame or a misresolved path
    ///   changes the asserted stacks.
    /// - witness: `stack::tests::a_script_reads_as_its_samples`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |sample| match *sample {
        Maybe::Present(ref frames) => !frames.is_empty(),
        Maybe::Absent(_) => true,
    }))]
    #[inline]
    pub fn next_sample(&mut self) -> Result<Maybe<Vec<Frame>, exhausted::Absent>, CostError>
    {
        let mut frames: Vec<Frame> = Vec::new();
        loop {
            self.buffer.clear();
            let read = self
                .lines
                .read_line(&mut self.buffer)
                .map_err(|error| CostError::Io {
                    path: PathBuf::from("perf script"),
                    message: error.to_string(),
                })?;
            let line = self.buffer.trim_end_matches(['\n', '\r']);
            if read == 0 || line.is_empty() {
                if !frames.is_empty() {
                    return Ok(Maybe::Present(frames));
                }
                if read == 0 {
                    return Ok(Maybe::Absent(exhausted::Absent::EndOfScript));
                }
            }
            else if let Some(frame) = line.strip_prefix('\t') {
                let symbol = frame
                    .trim_start()
                    .split_once(' ')
                    .map_or("", |(_, symbol)| symbol);
                frames.push(Frame {
                    symbol: Symbol::from(symbol),
                    location: Maybe::Absent(position::Absent::NotPrinted),
                });
            }
            else if let Some(text) = line.strip_prefix("  ")
                && let Some(frame) = frames.last_mut()
            {
                let text = text.trim();
                let text = text.strip_suffix(" (inlined)").unwrap_or(text);
                frame.location = match text.rsplit_once(':') {
                    Some((file, line)) if file != "??" => match line.parse::<usize>() {
                        Ok(line) if line > 0 => Maybe::Present(Location {
                            file: self.root.join(file),
                            line: Line::from(line),
                        }),
                        Ok(_) | Err(_) => Maybe::Absent(position::Absent::Unknown),
                    },
                    Some(_) | None => Maybe::Absent(position::Absent::Unknown),
                };
            }
        }
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use quenchant_shape::shape::Maybe;

    use super::Frame;
    use super::Location;
    use super::Stacks;
    use super::Symbol;
    use super::exhausted;
    use super::position;
    use crate::region::Line;

    #[test]
    fn a_script_reads_as_its_samples()
    {
        let script = "\n\
            \t    55e6d1247fd3 {closure#0}<core::iter::find::check>\n  \
            /rust/library/core/src/iter/traits/iterator.rs:2967 (inlined)\n\
            \t    55e6d1247fd3 successors\n  \
            crates/surface-grammar/src/mold.rs:1123 (inlined)\n\
            \t    55e6d1247fd3 {closure#0}\n  \
            ??:0 (inlined)\n\
            \t    55e6d123fcb2 [unknown]\n\
            \n\
            \n\
            \t    55e6d124c74e <gandr::Molder>::push_form_successors\n  \
            crates/surface-parser/src/mold.rs:0\n";
        let mut stacks = Stacks::new(script.as_bytes(), Path::new("/ws"));
        let at = |file: &str, line| {
            Maybe::Present(Location {
                file: Path::new(file).to_path_buf(),
                line: Line::from(line),
            })
        };
        assert_eq!(
            stacks.next_sample().unwrap(),
            Maybe::Present(vec![
                Frame {
                    symbol: Symbol::from("{closure#0}<core::iter::find::check>"),
                    location: at("/rust/library/core/src/iter/traits/iterator.rs", 2967),
                },
                Frame {
                    symbol: Symbol::from("successors"),
                    location: at("/ws/crates/surface-grammar/src/mold.rs", 1123),
                },
                Frame {
                    symbol: Symbol::from("{closure#0}"),
                    location: Maybe::Absent(position::Absent::Unknown),
                },
                Frame {
                    symbol: Symbol::from("[unknown]"),
                    location: Maybe::Absent(position::Absent::NotPrinted),
                },
            ]),
            "an absolute path kept, a relative one resolved, `??:0` and a missing line absent"
        );
        assert_eq!(
            stacks.next_sample().unwrap(),
            Maybe::Present(vec![Frame {
                symbol: Symbol::from("<gandr::Molder>::push_form_successors"),
                location: Maybe::Absent(position::Absent::Unknown),
            }]),
            "the empty sample between skipped; line 0 is no location; no trailing blank line"
        );
        assert_eq!(
            stacks.next_sample().unwrap(),
            Maybe::Absent(exhausted::Absent::EndOfScript),
            "the end"
        );
    }
}
