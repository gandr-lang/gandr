//! Public-API floor and lifecycle witnesses.

extern crate alloc;

#[cfg(test)]
#[path = "cases/dropping.rs"]
mod dropping;
#[cfg(test)]
#[path = "cases/handle.rs"]
mod handle;
#[cfg(test)]
#[path = "cases/nda.rs"]
mod nda;
#[cfg(test)]
#[path = "cases/rnna.rs"]
mod rnna;
#[cfg(test)]
#[path = "cases/rnta.rs"]
mod rnta;
#[cfg(test)]
#[path = "cases/validation.rs"]
mod validation;

/// Caller-owned names; the automaton never allocates identities.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Name
{
    /// A permanently remembered administrator.
    Admin,
    /// One lifecycle participant.
    User,
    /// A second participant.
    Other,
}

/// A small ranked test vocabulary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Symbol
{
    /// An internal node.
    Node,
    /// A leaf.
    Leaf,
}
