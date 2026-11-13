//! The records of the exits the lowering infers.
//!
//! They also record the `return`s the lowering would infer. The lowering puts
//! every exit where its body ends. Its families write these records, and a face
//! and the `explicit-exits` lint read them.

use core::fmt;

use gandr_surface_syntax::ByteSpan;

/// The exit a tail's polarity determines: `return` over a value, `become`
/// over a computation.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one variant per exit keyword.
/// - provides: the keyword an inferred exit stands for, and the text a fix that
///   writes it inserts.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a value tail and a computation tail, each asserted as its
///   exact exit.
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Exit
{
    /// `return v`: the tail is a value, and the body returns it.
    Return,
    /// `become c`: the tail is a computation, and the body runs it in tail
    /// position.
    Become,
}

impl fmt::Display for Exit
{
    /// Writes the keyword: `return` or `become`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Return => "return",
            Self::Become => "become",
        })
    }
}

/// Whether an attribute on the declaration or the module holding an inferred
/// exit asks for its keyword to be written.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one variant for an `explicit_exits` attribute on the owning
///   declaration or an enclosing module, one for none.
/// - provides: the module's half of the `explicit-exits` lint's switch; the
///   driver's flag is the other.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a module and a declaration carrying the attribute and a
///   declaration carrying none, each asserted as its exact answer.
/// - witness: `gandr-surface-lowering::lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Explicitness
{
    /// An `explicit_exits` attribute decorates the declaration or a module
    /// enclosing it.
    Asked,
    /// No attribute asks.
    Unasked,
}

/// An exit the lowering inferred where a path through a body ends in a form
/// that is no exit.
///
/// The lowering writes the exit the tail's polarity determines and checks it
/// as a written one; this record is what a face reads to show the keyword the
/// source left out, and what the `explicit-exits` lint reports.
///
/// # Specification
/// - requires: nothing to construct this data; the lowering produces it over
///   the tree it lowered.
/// - ensures: the span is the tail's own bytes, so no diagnostic names a
///   keyword the source did not write; the exit is the one the tail's polarity
///   names.
/// - provides: the inferred exits of a lowered module, in source order.
/// - fails: not applicable to the record itself.
/// - panics: not applicable to the record itself.
///
/// # Adequacy
/// - hypothesis: L3 — tails of each polarity, nested in matches and blocks,
///   asserted at their exact spans and exits.
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InferredExit
{
    /// The bytes of the tail the exit was inferred at.
    pub span: ByteSpan,
    /// The exit the tail's polarity names.
    pub exit: Exit,
    /// Whether an attribute asks for the keyword.
    pub explicitness: Explicitness,
}

/// A written `return` the lowering would infer were it left out: the sugared
/// form's tail, written as its value.
///
/// The `return` stands where a path through a body ends and is no statement
/// before the closing brace; it does not cross a handler's frame; and its
/// declaration lowered, under no `explicit_exits` attribute. Its operand is a
/// value, through any grouping, so the exit the bare value's polarity names is
/// the `return` written and leaving the keyword out mints the same term
/// ([`Returned::Value`]); or it is a computation written where the value is
/// read, through any grouping, which the bare tail runs as the computation it
/// is: another term, which the checker elaborates as it does the `return`
/// where it runs the computation there ([`Returned::Run`]). An early exit —
/// one in a statement whose rest it distributes — is no tail and is never
/// listed, nor is a `become`, which a sugared tail keeps.
///
/// # Specification
/// - requires: nothing to construct this data; the lowering produces it over
///   the tree it lowered.
/// - ensures: the span is the `return` form's own bytes and the value's lies
///   inside it, after the keyword.
/// - provides: the exits a formatter may leave out of a lowered module, in
///   source order.
/// - fails: not applicable to the record itself.
/// - panics: not applicable to the record itself.
///
/// # Adequacy
/// - hypothesis: L3 — a tail `return` of a value, in a body, a match arm and a
///   grouping, is listed, and so is one of a call and of an operator, bare and
///   grouped; one of a grouped type, one written as a statement, an early one,
///   one an attribute asks for and one in a refused declaration are not; each
///   listed value lowers as its tail written bare does.
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_return_of_a_value_is_listed_as_elidable_1327`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ElidableExit
{
    /// The bytes of the `return` form.
    pub span: ByteSpan,
    /// The bytes of the value it returns: the tail left without the keyword.
    pub value: ByteSpan,
    /// What the operand is, which decides what the bare tail lowers to.
    pub returned: Returned,
}

/// What an elidable `return` returns.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Returned
{
    /// A value: the bare tail lowers to the same term.
    Value,
    /// A computation written where the value is read: the bare tail lowers to
    /// the computation, and the `return` to the computation run there, which
    /// the checker elaborates to the same body where it runs it.
    Run,
}

/// What the paths through a node do with the body it stands in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the variants are ordered never, sometimes, always, so the greater
///   of two children's is what a form holding both does at least.
/// - provides: the survey's answer, which the classification reads at every
///   statement of a block a path runs through.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a computation with no exit, one with an exit in one arm
///   and one with an exit in every arm, each at one and two depths.
/// - witness: `gandr-surface-lowering::lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Leaves
{
    /// No path leaves: the node holds no exit outside a body of its own.
    #[default]
    Never,
    /// Some path leaves and some ends where the node stands.
    Sometimes,
    /// Every path leaves.
    Always,
}

/// Where the rest of a block goes after one of its statements.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a bound rest is bound once, after the statement's computation
///   returns; a distributed rest continues every local end of it.
/// - provides: the statement half of the commuting.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a statement whose computation holds no exit binds its
///   rest once, and one whose match exits in one arm continues the other.
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Rest
{
    /// The rest is bound once over the statement's computation.
    Bound,
    /// The rest continues every local end of the statement's computation,
    /// which holds an exit.
    Distributed,
}
