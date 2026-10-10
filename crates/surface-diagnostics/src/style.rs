//! How a report is laid out for its destination, and the text it becomes.
//!
//! # Plain unless asked
//!
//! [`RenderStyle::Plain`] adds no terminal styling. Styled output is the
//! caller's explicit choice, and [`RenderStyle::for_terminal`] selects it for
//! a terminal. Literal controls in caller-provided paths are preserved; style
//! selection does not sanitize that content.

use core::fmt;

use anodized::spec;

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
    /// - requires: nothing.
    /// - ensures: true denotes a terminal; false denotes a non-terminal.
    /// - provides: a capability from the caller's terminal observation.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both boolean inputs reach an exact style observation
    ///   through the capability. A reversed or constant mapping changes one
    ///   result; operating-system detection is outside this conversion.
    /// - witness: `diagnostics::diagnostics::render_style_follows_terminal_capability`
    #[spec(ensures: |ret| matches!(ret, Self::Terminal) == is_terminal)]
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
    /// Text without added terminal styling; caller path controls remain
    /// literal.
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
    /// - hypothesis: L3 — the two capabilities exhaust the typed domain,
    ///   observed through their exact styles. Reversed or constant selection
    ///   changes a result; backend rendering is a separate decision surface.
    /// - witness: `diagnostics::diagnostics::render_style_follows_terminal_capability`
    #[spec(ensures: |ret| matches!((capability, ret),
        (TerminalCapability::NonTerminal, Self::Plain)
            | (TerminalCapability::Terminal, Self::Styled)
    ))]
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

/// Owned presentation text. [`crate::Report::render`] adds no framing
/// terminator; literal path content can include one. Adopting a string
/// preserves its bytes unchanged.
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
