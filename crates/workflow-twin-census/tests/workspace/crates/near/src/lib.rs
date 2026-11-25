//! A crate that the emitter of the fixture depends on: one public function
//! in the export fragment, and its test.

/// Two times `value`, with a wrap.
pub fn twice(value: u64) -> u64
{
    value.wrapping_mul(2)
}

#[cfg(test)]
mod tests
{
    #[test]
    fn twice_doubles()
    {
        assert_eq!(super::twice(3), 6);
    }
}
