//! The inbox of a paced loop: what its reader and its watches hand it.
//!
//! A connection's loop reads its client's frames on one thread and meets them
//! in order on another. A watch of the files on disk, and another connection
//! over the same workspace, hand the loop what changed through the same
//! channel. [`Inbox`] holds both ends of that channel, [`Changes`] is the
//! handle that a watch keeps, and [`Read`] is one thing handed over.
//! [`Unread`] says whether an input holds bytes past the frame that the reader
//! took ([`Behind`]), so the frames of one write are handed over together.

use alloc::vec::Vec;
use std::path::PathBuf;
use std::sync::mpsc;

use crate::rpc::Classified;
use crate::transport::TransportFault;

/// What the reading thread, or a watch beside it, hands the loop.
#[derive(Debug)]
pub enum Read
{
    /// A message, classified, and whether the input held bytes past it.
    Message(Classified, Behind),
    /// Files changed on disk.
    Changed(Vec<PathBuf>),
    /// Files another connection's editor changed.
    Edited(Vec<PathBuf>),
    /// A checked fill of a document the loop's connection holds was kept.
    Proposed,
    /// An admission the loop's connection started ended.
    Admitted,
    /// The first view of the trace layer subscribed.
    Traced,
    /// The stream closed at a frame boundary.
    Closed,
    /// The stream failed.
    Fault(TransportFault),
}

/// Whether an input holds bytes past the last message the reader took: the
/// start of a frame the client wrote with it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Behind(pub bool);

/// An input that says whether it holds bytes it read and did not hand out.
pub trait Unread
{
    /// Whether bytes the input read are still to be handed out.
    ///
    /// # Specification
    /// trivial.
    fn unread(&self) -> Behind;
}

impl<Inner: ?Sized> Unread for std::io::BufReader<Inner>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn unread(&self) -> Behind
    {
        Behind(!self.buffer().is_empty())
    }
}

/// Where a paced loop takes what it meets: its reader's messages and a
/// watch's changes.
#[derive(Debug)]
pub struct Inbox
{
    /// The sending end, for the reader and each watch.
    sending: mpsc::Sender<Read>,
    /// The receiving end, the loop's.
    receiving: mpsc::Receiver<Read>,
}

impl Default for Inbox
{
    /// An empty inbox.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        let (sending, receiving) = mpsc::channel();
        Self { sending, receiving }
    }
}

impl Inbox
{
    /// A handle a watch hands this inbox's loop the files it saw change by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn changes(&self) -> Changes
    {
        Changes(self.sending.clone())
    }

    /// The two ends of the inbox: the sending end, for the reader and each
    /// watch, and the receiving end, for the loop.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn ends(self) -> (mpsc::Sender<Read>, mpsc::Receiver<Read>)
    {
        (self.sending, self.receiving)
    }
}

/// A handle a watch, or another connection, hands a paced loop the files it
/// saw change by.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct Changes(mpsc::Sender<Read>);

impl Changes
{
    /// Hand the loop `paths`, changed on disk; nothing once the loop ended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn hand(
        &self,
        paths: Vec<PathBuf>,
    )
    {
        let _sent = self.0.send(Read::Changed(paths));
    }

    /// Hand the loop `paths`, changed in another connection's editor;
    /// nothing once the loop ended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn edited(
        &self,
        paths: Vec<PathBuf>,
    )
    {
        let _sent = self.0.send(Read::Edited(paths));
    }

    /// Tell the loop another connection kept a checked fill of a document its
    /// connection holds; nothing once the loop ended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn proposed(&self)
    {
        let _sent = self.0.send(Read::Proposed);
    }

    /// Tell the loop an admission its connection started ended; nothing once
    /// the loop ended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn admitted(&self)
    {
        let _sent = self.0.send(Read::Admitted);
    }

    /// Tell the loop that the first view of the trace layer subscribed;
    /// nothing once the loop ended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn traced(&self)
    {
        let _sent = self.0.send(Read::Traced);
    }
}

#[cfg(test)]
pub mod tests
{
    use alloc::vec::Vec;
    use std::path::PathBuf;

    use super::Inbox;
    use super::Read;

    /// The files a watch handed `inbox`'s loop, one list per handing, in the
    /// order they came.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn handed(inbox: &Inbox) -> Vec<Vec<PathBuf>>
    {
        inbox
            .receiving
            .try_iter()
            .filter_map(|read| match read {
                Read::Changed(paths) => Some(paths),
                Read::Message(..)
                | Read::Edited(_)
                | Read::Proposed
                | Read::Admitted
                | Read::Traced
                | Read::Closed
                | Read::Fault(_) => None,
            })
            .collect()
    }
}
