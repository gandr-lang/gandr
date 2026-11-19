//! One function for each refusal that a crate can cause: a generic one, a
//! private one, one that the build copies into each caller, and one whose
//! argument is an array.

#[inline(never)]
pub fn generic<T: Copy>(value: T) -> T
{
    value
}

#[inline(never)]
fn private(value: u64) -> u64
{
    value.rotate_left(1)
}

pub fn inlined(value: u64) -> u64
{
    value ^ 3
}

#[inline(never)]
pub fn calls_private(value: u64) -> u64
{
    private(value)
}

#[inline(never)]
pub fn array(bytes: [u8; 4]) -> u8
{
    bytes[0] ^ bytes[3]
}
