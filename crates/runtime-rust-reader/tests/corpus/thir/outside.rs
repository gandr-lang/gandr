//! Bodies that stage no expression of `Expr Item` for `outside.gandr`.

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

/// Answers its argument.
pub fn helper(x: u8) -> u8
{
    x
}

/// Calls `helper`, which no item of `Item` names.
pub fn calls(x: u8) -> u8
{
    helper(x)
}
