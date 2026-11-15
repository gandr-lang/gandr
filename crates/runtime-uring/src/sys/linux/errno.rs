#[derive(Eq, PartialEq, Hash, Copy, Clone)]
#[cfg_attr(feature = "debug", derive(Debug))]
#[repr(transparent)]
pub struct Errno(pub(crate) u16);

impl Errno {
    pub(crate) const fn contains(val: isize) -> bool {
        -4095 <= val && val < 0
    }

    #[expect(clippy::as_conversions, reason = "const")]
    pub(crate) const fn into_raw_os_error(self) -> i32 {
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

impl From<Errno> for ::std::io::Error {
    fn from(value: Errno) -> Self {
        let code = value.into_raw_os_error();
        Self::from_raw_os_error(code)
    }
}
