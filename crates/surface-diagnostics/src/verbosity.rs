//! How much of a diagnostic a face shows.

/// How much of a diagnostic a face shows.
///
/// Every level shows the same diagnostic: a level chooses what to show, never
/// what the diagnostic holds.
///
/// | Level | Adds |
/// | ----- | ---- |
/// | `User`, the default | the message, the labels, the contexts and the note |
/// | `Detailed` | `class:` the class, `detail:` the producer's own wording where it differs from the message, `expression:` the primary span's source text when it is one line, `hypotheses:` the names and types in scope where it was refused |
/// | `Debug` | `spans:` the byte span of every locus, `rules:` each context's rule by its stable name, `refusal:` the producer's refusal and failure as their implementers print them, core ids included |
/// | `Json` | instead of the rendering, one line of JSON: [`crate::Diagnostic::json`] |
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Verbosity
{
    /// The message, the labels, the contexts and the note.
    #[default]
    User,
    /// Adds the class, the producer's own wording, the source text of the
    /// primary span and the hypotheses in scope.
    Detailed,
    /// Adds the byte span of every locus, each context's rule and the
    /// producer's refusal and failure as their implementers print them.
    Debug,
    /// The whole diagnostic as one line of JSON, for tools and agents; a
    /// style adds nothing to it.
    Json,
}
