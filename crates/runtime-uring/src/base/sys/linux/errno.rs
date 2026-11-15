//! The error number that the kernel answers.

/// An error number that the kernel answers, in its encoded form: the number
/// negated in 16 bits, as an answer from -4095 to -1 holds it in its low
/// bits.
#[derive(Eq, PartialEq, Hash, Copy, Clone)]
#[cfg_attr(feature = "debug", derive(Debug))]
#[repr(transparent)]
pub struct Errno(u16);

impl Errno
{
    /// The error number whose encoded form is `encoded`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub const fn from_encoded(encoded: u16) -> Self
    {
        Self(encoded)
    }

    /// Whether the answer `val` names an error: an answer from -4095 to -1.
    ///
    /// # Specification
    ///
    /// trivial.
    pub const fn contains(val: isize) -> bool
    {
        -4095 <= val && val < 0
    }

    /// The error number, as the standard library's errors take it.
    ///
    /// # Specification
    ///
    /// trivial.
    #[expect(
        clippy::as_conversions,
        reason = "a const fn cannot call `i32::from`, and a u16 widens into an i32 whole"
    )]
    pub const fn into_raw_os_error(self) -> i32
    {
        self.0.wrapping_neg() as i32
    }

    // pub(crate) const fn from_raw_os_error(raw: i32) -> Self {
    //     Self::from_errno(raw as u32)
    // }

    // pub(crate) const fn from_errno(raw: u32) -> Self {
    //     let encoded = raw.wrapping_neg() as u16;
    //     assert!(encoded >= 0xF001);
    //     Self(encoded)
    // }
}

impl From<Errno> for ::std::io::Error
{
    /// The standard library's error of the error number `value`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(value: Errno) -> Self
    {
        let code = value.into_raw_os_error();
        Self::from_raw_os_error(code)
    }
}
