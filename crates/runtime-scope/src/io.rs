pub mod socket;

use crate::buf::BufResult;
use crate::buf::IoBuf;
use crate::buf::IoBufMut;
use crate::buf::IoVecBuf;
use crate::buf::IoVecBufMut;

macro_rules! reader_trait {
    ($future:ident, $n_ty:ty, $f:ident) => {
        /// Read number in async way.
        fn $f(&mut self) -> impl Future<Output = std::io::Result<$n_ty>>;
    };
}

// macro_rules! reader_be_impl {
//     ($future:ident, $n_ty:ty, $f:ident) => {
//         async fn $f(&mut self) -> std::io::Result<$n_ty> {
//             let (res, buf) = self
//                 .read_exact(std::boxed::Box::new([0;
// std::mem::size_of::<$n_ty>()]))                 .await;
//             res?;
//             use crate::utils::box_into_inner::IntoInner;
//             Ok(<$n_ty>::from_be_bytes(Box::consume(buf)))
//         }
//     };
// }

// macro_rules! reader_le_impl {
//     ($future:ident, $n_ty:ty, $f:ident) => {
//         async fn $f(&mut self) -> std::io::Result<$n_ty> {
//             let (res, buf) = self
//                 .read_exact(std::boxed::Box::new([0;
// std::mem::size_of::<$n_ty>()]))                 .await;
//             res?;
//             use crate::utils::box_into_inner::IntoInner;
//             Ok(<$n_ty>::from_le_bytes(Box::consume(buf)))
//         }
//     };
// }

pub trait AsyncBufRead: AsyncReadRent
{
    fn fill_buf(&mut self) -> impl Future<Output = std::io::Result<&[u8]>>;
    fn consume(
        &mut self,
        amt: usize,
    );
}

pub trait AsyncBufReadExt
{
    fn read_until<'buf>(
        &'buf mut self,
        byte: u8,
        buf: &'buf mut Vec<u8>,
    ) -> impl Future<Output = ::std::io::Result<usize>>;

    fn read_line<'buf>(
        &'buf mut self,
        buf: &'buf mut String,
    ) -> impl Future<Output = ::std::io::Result<usize>>;
}

pub trait AsyncReadRent
{
    fn read<T>(
        &mut self,
        buf: T,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBufMut;
    fn readv<T>(
        &mut self,
        buf: T,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoVecBufMut;
}

pub trait AsyncReadRentAt
{
    fn read_at<T>(
        &mut self,
        buf: T,
        pos: usize,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBufMut;
}

pub trait AsyncReadRentExt
{
    fn read_exact<T>(
        &mut self,
        buf: T,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBufMut + 'static;

    fn read_vectored_exact<T>(
        &mut self,
        buf: T,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoVecBufMut + 'static;

    reader_trait!(ReadU8Future, u8, read_u8);
    reader_trait!(ReadU16Future, u16, read_u16);
    reader_trait!(ReadU32Future, u32, read_u32);
    reader_trait!(ReadU64Future, u64, read_u64);
    reader_trait!(ReadU128Future, u16, read_u128);
    reader_trait!(ReadI8Future, i8, read_i8);
    reader_trait!(ReadI16Future, i16, read_i16);
    reader_trait!(ReadI32Future, i32, read_i32);
    reader_trait!(ReadI64Future, i64, read_i64);
    reader_trait!(ReadI128Future, i128, read_i128);
    reader_trait!(ReadF32Future, f32, read_f32);
    reader_trait!(ReadF64Future, f64, read_f64);

    reader_trait!(ReadU8LEFuture, u8, read_u8_le);
    reader_trait!(ReadU16LEFuture, u16, read_u16_le);
    reader_trait!(ReadU32LEFuture, u32, read_u32_le);
    reader_trait!(ReadU64LEFuture, u64, read_u64_le);
    reader_trait!(ReadU128LEFuture, u128, read_u128_le);
    reader_trait!(ReadI8LEFuture, i8, read_i8_le);
    reader_trait!(ReadI16LEFuture, i16, read_i16_le);
    reader_trait!(ReadI32LEFuture, i32, read_i32_le);
    reader_trait!(ReadI64LEFuture, i64, read_i64_le);
    reader_trait!(ReadI128LEFuture, i128, read_i128_le);
    reader_trait!(ReadF32LEFuture, f32, read_f32_le);
    reader_trait!(ReadF64LEFuture, f64, read_f64_le);
}

pub trait AsyncWriteRent
{
    fn write<T>(
        &mut self,
        buf: T,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBuf;

    fn writev<T>(
        &mut self,
        buf_vec: T,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoVecBuf;

    fn flush(&mut self) -> impl Future<Output = std::io::Result<()>>;

    fn shutdown(&mut self) -> impl Future<Output = std::io::Result<()>>;
}

pub trait AsyncWriteRentAt
{
    fn write_at<T>(
        &self,
        buf: T,
        pos: usize,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBufMut;
}

pub trait AsyncWriteRentExt
{
    fn write_all<T>(
        &mut self,
        buf: T,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBuf + 'static;

    fn write_vectored_all<T>(
        &mut self,
        buf: T,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoVecBuf + 'static;
}

pub trait CancelableAsyncReadRent: AsyncReadRent
{
    fn cancelable_read<T>(
        &mut self,
        buf: T,
        c: CancelHandle,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBufMut;

    fn cancelable_readv<T>(
        &mut self,
        buf: T,
        c: CancelHandle,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoVecBufMut;
}

pub trait CancelableAsyncReadRentExt
{
    fn cancelable_read_exact<T>(
        &mut self,
        buf: T,
        c: CancelHandle,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBufMut + 'static;

    fn cancelable_read_vectored_exact<T>(
        &mut self,
        buf: T,
        c: CancelHandle,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoVecBufMut + 'static;

    reader_trait!(ReadU8Future, u8, cancelable_read_u8);
    reader_trait!(ReadU16Future, u16, cancelable_read_u16);
    reader_trait!(ReadU32Future, u32, cancelable_read_u32);
    reader_trait!(ReadU64Future, u64, cancelable_read_u64);
    reader_trait!(ReadU128Future, u128, cancelable_read_u128);
    reader_trait!(ReadI8Future, i8, cancelable_read_i8);
    reader_trait!(ReadI16Future, i16, cancelable_read_i16);
    reader_trait!(ReadI32Future, i32, cancelable_read_i32);
    reader_trait!(ReadI64Future, i64, cancelable_read_i64);
    reader_trait!(ReadI128Future, i128, cancelable_read_i128);
    reader_trait!(ReadF32Future, f32, cancelable_read_f32);
    reader_trait!(ReadF64Future, f64, cancelable_read_f64);

    reader_trait!(ReadU8LEFuture, u8, cancelable_read_u8_le);
    reader_trait!(ReadU16LEFuture, u16, cancelable_read_u16_le);
    reader_trait!(ReadU32LEFuture, u32, cancelable_read_u32_le);
    reader_trait!(ReadU64LEFuture, u64, cancelable_read_u64_le);
    reader_trait!(ReadU128LEFuture, u128, cancelable_read_u128_le);
    reader_trait!(ReadI8LEFuture, i8, cancelable_read_i8_le);
    reader_trait!(ReadI16LEFuture, i16, cancelable_read_i16_le);
    reader_trait!(ReadI32LEFuture, i32, cancelable_read_i32_le);
    reader_trait!(ReadI64LEFuture, i64, cancelable_read_i64_le);
    reader_trait!(ReadI128LEFuture, i128, cancelable_read_i128_le);
    reader_trait!(ReadF32LEFuture, f32, cancelable_read_f32_le);
    reader_trait!(ReadF64LEFuture, f64, cancelable_read_f64_le);
}

pub trait CancelableAsyncWriteRent: AsyncWriteRent
{
    fn cancelable_write<T>(
        &mut self,
        buf: T,
        c: CancelHandle,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBuf;

    fn cancelable_writev<T>(
        &mut self,
        buf_vec: T,
        c: CancelHandle,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoVecBuf;

    fn cancelable_flush(
        &mut self,
        c: CancelHandle,
    ) -> impl Future<Output = std::io::Result<()>>;

    fn cancelable_shutdown(
        &mut self,
        c: CancelHandle,
    ) -> impl Future<Output = std::io::Result<()>>;
}

pub trait CancelableAsyncWriteRentExt
{
    fn write_all<T>(
        &mut self,
        buf: T,
        c: CancelHandle,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoBuf + 'static;

    fn write_vectored_all<T>(
        &mut self,
        buf: T,
        c: CancelHandle,
    ) -> impl Future<Output = BufResult<usize, T>>
    where
        T: IoVecBuf + 'static;
}

#[non_exhaustive]
pub struct CancelHandle;
