#![expect(clippy::missing_safety_doc, reason = "WIP")]

pub type BufResult<T, B> = (::std::io::Result<T>, B);

pub unsafe trait IoBuf: Unpin + 'static
{
    fn read_ptr(&self) -> *const u8;

    fn bytes_init(&self) -> usize;

    // #[inline]
    // fn slice(self, range: impl ops::RangeBounds<usize>) -> Slice<Self>
    // where
    //     Self: Sized,
    // {
    //     let (begin, end) = parse_range(range, self.bytes_init());
    //     Slice::new(self, begin, end)
    // }

    // #[inline]
    // unsafe fn slice_unchecked(self, range: impl ops::RangeBounds<usize>) ->
    // Slice<Self> where
    //     Self: Sized,
    // {
    //     let (begin, end) = parse_range(range, self.bytes_init());
    //     Slice::new_unchecked(self, begin, end)
    // }
}

pub unsafe trait IoVecBuf: Unpin + 'static
{
    fn read_iovec_ptr(&self) -> *const libc::iovec;

    fn read_iovec_len(&self) -> usize;
}

pub unsafe trait IoBufMut: Unpin + 'static
{
    fn write_ptr(&mut self) -> *mut u8;

    fn bytes_total(&mut self) -> usize;

    unsafe fn set_init(
        &mut self,
        pos: usize,
    );

    // #[inline]
    // fn slice_mut(mut self, range: impl ::core::ops::RangeBounds<usize>) ->
    // SliceMut<Self> where
    //     Self: Sized,
    //     Self: IoBuf,
    // {
    //     let (begin, end) = parse_range(range, self.bytes_total());
    //     SliceMut::new(self, begin, end)
    // }

    // #[inline]
    // unsafe fn slice_mut_unchecked(mut self, range: impl
    // ops::RangeBounds<usize>) -> SliceMut<Self> where
    //     Self: Sized,
    // {
    //     let (begin, end) = parse_range(range, self.bytes_total());
    //     SliceMut::new_unchecked(self, begin, end)
    // }
}

pub unsafe trait IoVecBufMut: Unpin + 'static
{
    fn write_iovec_ptr(&mut self) -> *mut ::libc::iovec;

    fn write_iovec_len(&mut self) -> usize;

    unsafe fn set_init(
        &mut self,
        pos: usize,
    );
}
