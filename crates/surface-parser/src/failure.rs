//! The failure of a unit test: each error that the unit tests propagate, as a
//! variant of its own type, so no test boxes a trait object (#7385).

use alloc::string::String;

/// The failure of a unit test.
#[derive(Debug)]
#[expect(
    dead_code,
    reason = "a failing test prints its failure through the derived Debug, which the dead-code analysis does not count as a read"
)]
pub enum Failure
{
    /// The test finds no value where it expects one, and the text names it.
    Absent(&'static str),
    /// The test states its failure in words.
    Stated(String),
}

impl From<&'static str> for Failure
{
    /// # Specification
    /// trivial.
    fn from(text: &'static str) -> Self
    {
        Self::Absent(text)
    }
}

impl From<String> for Failure
{
    /// # Specification
    /// trivial.
    fn from(text: String) -> Self
    {
        Self::Stated(text)
    }
}
