//! How a report is laid out for its destination, and the text it becomes.
//!
//! # Plain unless asked
//!
//! [`RenderStyle::Plain`] is the default: deterministic text with no escape
//! sequence, the form a test compares and a pipe receives. Styled output is
//! the caller's explicit choice, and [`RenderStyle::for_terminal`] makes it
//! only for a destination that is a terminal.

use core::fmt;

/// Whether an output destination is a terminal capable of styled rendering.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TerminalCapability
{
    /// Captured, redirected or otherwise non-terminal output.
    #[default]
    NonTerminal,
    /// An interactive terminal.
    Terminal,
}

impl From<bool> for TerminalCapability
{
    /// The capability `is_terminal` answers, as `std::io::IsTerminal`
    /// reports it for a destination.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_terminal: bool) -> Self
    {
        if is_terminal {
            Self::Terminal
        }
        else {
            Self::NonTerminal
        }
    }
}

/// How a report is laid out: plain text, or styled for a terminal.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RenderStyle
{
    /// Deterministic text with no terminal escape sequence.
    #[default]
    Plain,
    /// The snippet backend's styled terminal presentation, coloured with ANSI
    /// escape sequences.
    Styled,
}

impl RenderStyle
{
    /// The style a destination of `capability` takes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`RenderStyle::Styled`] exactly for
    ///   [`TerminalCapability::Terminal`], [`RenderStyle::Plain`] otherwise.
    /// - provides: the one place a face turns what it knows of its output into
    ///   a style, so no face colours a pipe.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two capabilities, both enumerated with the exact
    ///   style asserted, each reached through the `bool` conversion a face
    ///   holds.
    /// - witness: `diagnostics::diagnostics::render_style_follows_terminal_capability`
    #[inline]
    #[must_use]
    pub const fn for_terminal(capability: TerminalCapability) -> Self
    {
        match capability {
            | TerminalCapability::NonTerminal => Self::Plain,
            | TerminalCapability::Terminal => Self::Styled,
        }
    }
}

/// The text one report renders as: lines without a final terminator.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Rendered(String);

impl From<String> for Rendered
{
    /// Adopt `text` as a rendering.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for Rendered
{
    /// Borrow the rendered text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for Rendered
{
    /// Writes the rendered text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}
