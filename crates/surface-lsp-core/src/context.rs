//! What a handler of a navigation request asks the workspace for: the copy
//! of a document that a connection is answered from, its text, its reading
//! and what its hovers read.
//!
//! The workspace holds its copies in the server, above this crate. A handler
//! below the server names the copy through this trait, and the server
//! implements it. Each handler is generic over the trait, so each call
//! resolves when the server compiles, with no indirection at run time.

use gandr_surface_syntax::SourceText;

use crate::hover::Hovering;
use crate::peer::Peer;
use crate::protocol::DocumentUri;
use crate::reading::Reading;

/// The workspace, as a handler of a navigation request reads it.
pub trait Context
{
    /// One copy of a document.
    type Held<'context>: Held
    where
        Self: 'context;

    /// The copy of the document at `uri` that `peer` is answered from: its
    /// own, or the latest when it holds none. None when no connection holds
    /// the document.
    ///
    /// # Specification
    /// trivial.
    fn view<'context>(
        &'context self,
        uri: &'context DocumentUri,
        peer: Peer,
    ) -> Option<Self::Held<'context>>;
}

/// One copy of a document, as a handler of a navigation request reads it.
pub trait Held
{
    /// The text of the copy.
    ///
    /// # Specification
    /// trivial.
    fn source(&self) -> SourceText<'_>;

    /// The reading of the text, made now when no reader made it since the
    /// text last changed.
    ///
    /// # Specification
    /// trivial.
    fn reading(&self) -> &Reading;

    /// What the hovers of the text read, made now when no hover made it
    /// since the text or its closure last changed. None when the session of
    /// the copy did not build.
    ///
    /// # Specification
    /// trivial.
    fn hovering(&self) -> Option<&Hovering>;
}
