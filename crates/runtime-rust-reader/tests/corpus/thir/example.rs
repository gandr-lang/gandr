//! Corten's running example as a crate of one file, whose bodies the reader
//! stages as THIR for `example.gandr`.

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
