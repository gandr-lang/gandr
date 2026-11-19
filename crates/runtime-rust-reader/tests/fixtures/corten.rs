//! Corten's running example, whose bodies the reader stages as THIR, and two
//! bodies outside the fragment.

/// Answers its argument.
pub fn identity(x: u8) -> u8
{
    x
}

/// Returns early from inside `identity`'s argument.
pub fn example(b: bool) -> u8
{
    return identity(if b {
        1
    }
    else {
        return 0;
    });
}

/// Adds one: an operator, outside the fragment.
pub fn outside(x: u8) -> u8
{
    x + 1
}

/// Calls a function that the request does not hold.
pub fn escapes(x: u8) -> u8
{
    core::convert::identity(x)
}
