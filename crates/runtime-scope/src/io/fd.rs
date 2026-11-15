//! The operations of the scope on a descriptor and on time: a read, a
//! write, a write linked to its file's sync, a timer and a cancel.

use ::core::marker::PhantomData;
use ::core::pin::Pin;
use ::core::task::Context;
use ::core::task::Poll;
use ::core::task::ready;

use crate::adapter::Adapter;
use crate::adapter::Native;
use crate::completion::Completion;
use crate::completion::Count;
use crate::error::RuntimeError;
use crate::io::buf::Buf;
use crate::op::Descriptor;
use crate::op::Lent;
use crate::op::Op;
use crate::op::Ticket;
use crate::op::Timeout;
use crate::scope::Scope;

impl<'tsk, 'env: 'tsk, A> Scope<'tsk, 'env, A>
where
    A: Adapter,
{
    /// A read of at most the length of `buf` from `fd` into `buf`, a buffer
    /// lent for the scope's life; the completion gives back the bytes read.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn read<'fd, F>(
        &'tsk self,
        fd: &'fd F,
        mut buf: Buf<'tsk>,
    ) -> OpRead<'tsk, 'env, 'fd, A>
    where
        Descriptor: for<'f> From<&'f F>,
    {
        let rsp = self.request(Op::Read {
            fd: Descriptor::from(fd),
            into: Lent::of(&mut buf),
        });
        OpRead {
            rsp,
            buf: Some(buf),
            phd: PhantomData,
        }
    }

    /// A write of `buf`, a buffer lent for the scope's life, to `fd`; the
    /// completion gives the count of bytes written.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn write<'fd, F>(
        &'tsk self,
        fd: &'fd F,
        mut buf: Buf<'tsk>,
    ) -> OpWrite<'tsk, 'env, 'fd, A>
    where
        Descriptor: for<'f> From<&'f F>,
    {
        let rsp = self.request(Op::Write {
            fd: Descriptor::from(fd),
            from: Lent::of(&mut buf),
        });
        OpWrite {
            rsp,
            phd: PhantomData,
        }
    }

    /// A write of `buf` to the file `fd`, linked to the file's sync: the
    /// sync starts once the write completes, and the pair completes once,
    /// with the count of bytes written or the first refusal.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn write_sync<'fd, F>(
        &'tsk self,
        fd: &'fd F,
        mut buf: Buf<'tsk>,
    ) -> OpWrite<'tsk, 'env, 'fd, A>
    where
        Descriptor: for<'f> From<&'f F>,
    {
        let rsp = self.request(Op::WriteSync {
            fd: Descriptor::from(fd),
            from: Lent::of(&mut buf),
        });
        OpWrite {
            rsp,
            phd: PhantomData,
        }
    }

    /// A timer that completes once `after`, a span lent for the scope's
    /// life, passes.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn timer(
        &'tsk self,
        after: &'tsk Timeout,
    ) -> OpTimer<'tsk, 'env, A>
    {
        let rsp = self.request(Op::Timer { after });
        OpTimer {
            rsp,
            phd: PhantomData,
        }
    }

    /// A cancel of the operation that `target` names. The cancel completes,
    /// and the operation completes too, with the kernel's cancelled refusal
    /// when the cancel caught it.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn cancel(
        &'tsk self,
        target: Ticket,
    ) -> OpCancel<'tsk, 'env, A>
    {
        let rsp = self.request(Op::Cancel { target });
        OpCancel {
            rsp,
            phd: PhantomData,
        }
    }
}

/// A read into a buffer that the scope's caller lends for the scope's life;
/// the completion gives back the bytes read.
#[non_exhaustive]
pub struct OpRead<'tsk, 'env, 'fd, A = Native>
where
    A: Adapter,
{
    /// The completion of the read.
    rsp: Completion<'tsk>,
    /// The buffer, until the completion gives it back.
    buf: Option<Buf<'tsk>>,
    /// The borrows of the scope and of the descriptor, which the operation
    /// holds until its completion.
    phd: PhantomData<(&'tsk Scope<'tsk, 'env, A>, &'fd ())>,
}

impl<A> OpRead<'_, '_, '_, A>
where
    A: Adapter,
{
    /// The ticket of the read while the kernel holds it: what a cancel names.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ticket(&self) -> Option<Ticket>
    {
        self.rsp.ticket()
    }
}

impl<'tsk, A> Future for OpRead<'tsk, '_, '_, A>
where
    A: Adapter,
{
    type Output = Result<Buf<'tsk>, RuntimeError>;

    /// The bytes read, once the kernel completes the read.
    ///
    /// # Specification
    ///
    /// - provides: the buffer's prefix that the kernel wrote.
    /// - fails: the kernel's error when it refuses the read, `Read` when the
    ///   read already gave the buffer back, `Overrun` when the kernel's count
    ///   passes the buffer, and the completion's refusal.
    /// - panics: none.
    /// - executable: none — the bytes are the descriptor's, and the call holds
    ///   nothing to check them against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a pipe's read gives back the bytes that its write
    ///   wrote.
    /// - witness: `io::fd::test::echo`
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let cqe = ready!(Pin::new(&mut this.rsp).poll(cx))?;
        let buf = this.buf.take().ok_or(RuntimeError::Read)?;
        let count = cqe.count()?;
        Poll::Ready(buf.prefix(count).ok_or(RuntimeError::Overrun))
    }
}

/// A write of a buffer that the scope's caller lends for the scope's life,
/// alone or linked to its file's sync; the completion gives the count of
/// bytes written.
#[non_exhaustive]
pub struct OpWrite<'tsk, 'env, 'fd, A = Native>
where
    A: Adapter,
{
    /// The completion of the write, or of the pair.
    rsp: Completion<'tsk>,
    /// The borrows of the scope and of the descriptor, which the operation
    /// holds until its completion.
    phd: PhantomData<(&'tsk Scope<'tsk, 'env, A>, &'fd ())>,
}

impl<A> Future for OpWrite<'_, '_, '_, A>
where
    A: Adapter,
{
    type Output = Result<Count, RuntimeError>;

    /// The count of bytes written, once the kernel completes the write, or
    /// the write and its sync.
    ///
    /// # Specification
    ///
    /// - provides: the count of bytes written.
    /// - fails: the kernel's error when it refuses the write or the sync, and
    ///   the completion's refusal.
    /// - panics: none.
    /// - executable: none — the count is the kernel's.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a pipe's write of four bytes counts four, and a
    ///   pair's count follows its sync.
    /// - witness: `io::fd::test::echo`
    /// - witness: `io::fd::test::write_sync`
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let cqe = ready!(Pin::new(&mut this.rsp).poll(cx))?;
        Poll::Ready(cqe.count())
    }
}

/// A timer of a span that the scope's caller lends for the scope's life.
#[non_exhaustive]
pub struct OpTimer<'tsk, 'env, A = Native>
where
    A: Adapter,
{
    /// The completion of the timer.
    rsp: Completion<'tsk>,
    /// The borrow of the scope.
    phd: PhantomData<&'tsk Scope<'tsk, 'env, A>>,
}

impl<A> OpTimer<'_, '_, A>
where
    A: Adapter,
{
    /// The ticket of the timer while the kernel holds it: what a cancel
    /// names.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ticket(&self) -> Option<Ticket>
    {
        self.rsp.ticket()
    }
}

impl<A> Future for OpTimer<'_, '_, A>
where
    A: Adapter,
{
    type Output = Result<(), RuntimeError>;

    /// The timer's end, once its span passes.
    ///
    /// # Specification
    ///
    /// - ensures: on `Ok`, the span passed.
    /// - fails: the kernel's error when it refuses the timer or a cancel ends
    ///   it, and the completion's refusal.
    /// - panics: none.
    /// - executable: none — the time is the kernel's clock.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a timer of one tick completes after its span.
    /// - witness: `io::fd::test::timer`
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let cqe = ready!(Pin::new(&mut this.rsp).poll(cx))?;
        Poll::Ready(cqe.done())
    }
}

/// A cancel of an operation in flight.
#[non_exhaustive]
pub struct OpCancel<'tsk, 'env, A = Native>
where
    A: Adapter,
{
    /// The completion of the cancel.
    rsp: Completion<'tsk>,
    /// The borrow of the scope.
    phd: PhantomData<&'tsk Scope<'tsk, 'env, A>>,
}

impl<A> Future for OpCancel<'_, '_, A>
where
    A: Adapter,
{
    type Output = Result<(), RuntimeError>;

    /// The cancel's outcome, once the kernel completes it.
    ///
    /// # Specification
    ///
    /// - ensures: on `Ok`, the cancel caught its operation, whose own
    ///   completion follows with the kernel's cancelled refusal.
    /// - fails: the kernel's error when the operation was not found or was past
    ///   the point of a cancel, and the completion's refusal.
    /// - panics: none.
    /// - executable: none — the operation's state is the kernel's.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a cancel of a pending read completes, and so does the
    ///   read, with the cancelled refusal.
    /// - witness: `io::fd::test::cancel`
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output>
    {
        let this = self.get_mut();
        let cqe = ready!(Pin::new(&mut this.rsp).poll(cx))?;
        Poll::Ready(cqe.done())
    }
}

/// The tests of the descriptor and time operations, on the target's
/// adapter: the ring on Linux.
#[cfg(test)]
pub(crate) mod test
{
    use ::assert_fs::prelude::PathChild as _;
    use ::core::time::Duration;
    use ::rustix::io::Errno;
    use ::std::io::Read as _;
    use ::std::io::Write as _;
    use ::std::time::Instant;

    use super::*;

    /// A pipe's write of four bytes counts four, and the pipe's read gives
    /// them back.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a queue of the kernel, which Miri cannot run"
    )]
    fn echo()
    {
        let (reader, writer) = ::std::io::pipe().unwrap();
        let mut sent = *b"ping";
        let mut got = [0_u8; 8];
        let (wrote, echoed) = crate::test::harness::runtime::new()
            .run(async |scope| -> Result<(Count, Vec<u8>), RuntimeError> {
                let wrote = scope.write(&writer, Buf::from(sent.as_mut_slice())).await?;
                let read = scope.read(&reader, Buf::from(got.as_mut_slice())).await?;
                Ok((wrote, read.to_vec()))
            })
            .unwrap()
            .unwrap();
        assert_eq!(usize::from(wrote), 4);
        assert_eq!(echoed.as_slice(), b"ping".as_slice());
    }

    /// A scope that ends with a read in flight cancels it before the run
    /// returns. So the bytes that the writer writes after the run stay in
    /// the pipe, and the buffer keeps its zeros.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a queue of the kernel, which Miri cannot run"
    )]
    fn read_in_flight()
    {
        let (mut reader, mut writer) = ::std::io::pipe().unwrap();
        let mut got = [0_u8; 8];
        crate::test::harness::runtime::new()
            .run(async |scope| {
                let read = scope.read(&reader, Buf::from(got.as_mut_slice()));
                drop(read);
            })
            .unwrap();
        writer.write_all(b"late").unwrap();
        let mut late = [0_u8; 4];
        reader.read_exact(&mut late).unwrap();
        assert_eq!(&late, b"late");
        assert_eq!(got, [0_u8; 8]);
    }

    /// A timer of one millisecond completes with no refusal, no sooner than
    /// its span.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a queue of the kernel, which Miri cannot run"
    )]
    fn timer()
    {
        let span = Duration::from_millis(1);
        let after = Timeout::from(span);
        let waited = crate::test::harness::runtime::new()
            .run(async |scope| -> Result<Duration, RuntimeError> {
                let start = Instant::now();
                scope.timer(&after).await?;
                Ok(start.elapsed())
            })
            .unwrap()
            .unwrap();
        assert!(
            waited >= span,
            "the timer completes after its span, not at {waited:?}"
        );
    }

    /// A scope that ends with a timer of a minute in flight cancels it, so
    /// the run returns long before the minute.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a queue of the kernel, which Miri cannot run"
    )]
    fn timer_in_flight()
    {
        let span = Duration::from_secs(60);
        let after = Timeout::from(span);
        let start = Instant::now();
        crate::test::harness::runtime::new()
            .run(async |scope| {
                let timer = scope.timer(&after);
                drop(timer);
            })
            .unwrap();
        let ran = start.elapsed();
        assert!(
            ran < span,
            "the scope's end cancels the timer, but the run took {ran:?}"
        );
    }

    /// A cancel of a read that waits on an empty pipe completes, and the
    /// read completes with the kernel's cancelled refusal.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a queue of the kernel, which Miri cannot run"
    )]
    fn cancel()
    {
        let (reader, _writer) = ::std::io::pipe().unwrap();
        let mut got = [0_u8; 8];
        let read = crate::test::harness::runtime::new()
            .run(
                async |scope| -> Result<Option<RuntimeError>, RuntimeError> {
                    let read = scope.read(&reader, Buf::from(got.as_mut_slice()));
                    let ticket = read.ticket().unwrap();
                    scope.cancel(ticket).await?;
                    Ok(read.await.err())
                },
            )
            .unwrap()
            .unwrap();
        assert_eq!(read, Some(RuntimeError::Kernel(Errno::CANCELED)));
    }

    /// A write linked to its file's sync counts its four bytes once both
    /// complete, and the file holds them.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a queue of the kernel, which Miri cannot run"
    )]
    fn write_sync()
    {
        let temp = ::assert_fs::TempDir::new().unwrap();
        let path = temp.child("file");
        let file = ::std::fs::File::create(&path).unwrap();
        let mut sent = *b"data";
        let wrote = crate::test::harness::runtime::new()
            .run(async |scope| {
                scope
                    .write_sync(&file, Buf::from(sent.as_mut_slice()))
                    .await
            })
            .unwrap()
            .unwrap();
        assert_eq!(usize::from(wrote), 4);
        assert_eq!(
            ::std::fs::read(&path).unwrap().as_slice(),
            b"data".as_slice()
        );
    }

    /// A scope that ends with a linked pair in flight cancels both of its
    /// entries: the pipe is full, so the pair's write waits. The run
    /// returns, and the pipe holds only the bytes that filled it.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a queue of the kernel, which Miri cannot run"
    )]
    fn write_sync_in_flight()
    {
        let (mut reader, mut writer) = ::std::io::pipe().unwrap();
        let capacity = ::rustix::pipe::fcntl_getpipe_size(&writer).unwrap();
        writer.write_all(&vec![0_u8; capacity]).unwrap();
        let mut sent = *b"late";
        crate::test::harness::runtime::new()
            .run(async |scope| {
                let pair = scope.write_sync(&writer, Buf::from(sent.as_mut_slice()));
                drop(pair);
            })
            .unwrap();
        drop(writer);
        let mut held = Vec::new();
        reader.read_to_end(&mut held).unwrap();
        assert_eq!(held, vec![0_u8; capacity]);
    }
}
