//! What a handler of a navigation request asks the workspace for: the copy
//! of a document that a connection is answered from, its text, its reading
//! and what its hovers read.
//!
//! The workspace holds its copies in the server, above this crate. A handler
//! below the server carries the workspace and a copy by address, as an
//! [`Erased`], and asks for each part through a function that the server
//! defines and the linker binds. So each ask is a direct call, with no
//! generic and no trait object.

use core::marker::PhantomData;
use core::ptr::NonNull;

use crate::peer::Peer;
use crate::protocol::DocumentUri;

/// The address of a value that the server holds, which a crate below the
/// server carries without its type, for `'held`.
#[derive(Clone, Copy, Debug)]
pub struct Erased<'held>(NonNull<()>, PhantomData<&'held ()>);

impl Erased<'_>
{
    /// The address `address`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(address: NonNull<()>) -> Self
    {
        Self(address, PhantomData)
    }

    /// The address.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn address(self) -> NonNull<()>
    {
        self.0
    }
}

/// One copy of a document, as a handler of a navigation request reads it:
/// the workspace and the copy by address, the URI of the document and the
/// connection that the copy answers.
#[derive(Clone, Copy, Debug)]
pub struct Viewed<'context>
{
    /// The workspace that holds the copy.
    pub workspace: Erased<'context>,
    /// The copy.
    pub document: Erased<'context>,
    /// The URI of the document.
    pub uri: &'context DocumentUri,
    /// The connection that the copy answers.
    pub peer: Peer,
}
