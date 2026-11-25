//! The records of the runs the checker infers.
//!
//! They record which runs an `explicit_runs` attribute asks to be written, how
//! `run` is written for each, and the `let` statements that only sequence a
//! call. The lowering's families write them, and a face and the `explicit-runs`
//! lint read them.

use gandr_core_term::effect::Purity;
use gandr_surface_syntax::ByteSpan;

/// Which runs an `explicit_runs` attribute asks to be written, ordered from
/// none to all, so the wider of two asks is the greater.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one variant for no attribute, one for the `effects` option, one
///   for the bare attribute, ascending in what they ask for.
/// - provides: the module's half of the `explicit-runs` lint's switch; the
///   driver's flag is the other.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a module asking for every run, a declaration asking for
///   the effectful ones and a declaration asking nothing, each asserted as its
///   exact answer.
/// - witness: `gandr-surface-lowering::lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AskedRuns
{
    /// No attribute asks.
    #[default]
    Unasked,
    /// `explicit_runs("effects")`: the runs whose returner performs an
    /// effect.
    Effectful,
    /// `explicit_runs`: every run.
    Every,
}

/// How the `run` the source could write for a nested computation is spelled.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one variant for a computation written after a bare `run`, and one
///   for a call or a selection at an application's head, written parenthesised
///   after `run`.
/// - provides: the fix a face proposes, which the parser reads back as the run
///   it means.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a nested call after `return`, one first in a block's tail
///   and one at an application's head, each written as spelled and checked
///   again.
/// - witness: `gandr-surface-lowering::lower::runs::tests::a_nested_run_is_spelled_as_its_written_run_reads_back`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RunSpelling
{
    /// `run c`: the computation stands anywhere but an application's head.
    #[default]
    Bare,
    /// `(run c)`: the computation is a call or a selection at an application's
    /// head.
    Parenthesised,
}

/// How the computation a nested run stands for is written after `run`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one variant for a computation the run's operand position takes as
///   written, and one for a computation as loose as `run` or looser, grouped in
///   parentheses after it.
/// - provides: the fix a face proposes, which the parser reads back as a run of
///   the whole computation rather than of its first operand.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a nested call written bare and a nested operator call
///   written grouped, each written as spelled and checked again.
/// - witness: `gandr-surface-lowering::lower::runs::tests::a_nested_run_is_spelled_as_its_written_run_reads_back`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RunOperand
{
    /// `run c`: a call, a projection, an instantiation or an atom.
    #[default]
    Tight,
    /// `run (c)`: an operator or a prefix form.
    Grouped,
}

/// What the lowering records of one computation it held nested: which runs
/// an attribute asks for where it stands, and how its `run` is spelled.
///
/// # Specification
/// - requires: nothing to construct this data; the lowering produces it.
/// - ensures: the fields are the lowering's answers for one syntax node.
/// - provides: the lowering's half of
///   [`LoweredModule::inferred_runs`](crate::module::LoweredModule::inferred_runs).
/// - fails: not applicable to the record itself.
/// - panics: not applicable to the record itself.
///
/// # Adequacy
/// - hypothesis: L3 — nested calls under a module's attribute, a declaration's
///   and none, asserted as their exact asks.
/// - witness: `gandr-surface-lowering::lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NestedSite
{
    /// Which runs an attribute asks to be written where it stands.
    pub asked: AskedRuns,
    /// Whether its `run` is parenthesised.
    pub spelling: RunSpelling,
    /// Whether the computation is grouped after `run`.
    pub operand: RunOperand,
}

/// A run the checker inferred where a computation stands in a position that
/// reads a value.
///
/// # Specification
/// - requires: nothing to construct this data;
///   [`LoweredModule::inferred_runs`](crate::module::LoweredModule::inferred_runs)
///   produces it from the checker's decisions.
/// - ensures: the span is the nested computation's own bytes, where `run` would
///   be written; the purity is the checker's, read off the returner it ran; the
///   site is the lowering's.
/// - provides: the inferred runs of a checked module, in source order.
/// - fails: not applicable to the record itself.
/// - panics: not applicable to the record itself.
///
/// # Adequacy
/// - hypothesis: L3 — nested calls in a module and a declaration asked
///   differently, asserted at their exact spans.
/// - witness: `gandr-surface-lowering::lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InferredRun
{
    /// The bytes of the computation the run was inferred at.
    pub span: ByteSpan,
    /// Whether the computation's returner performs an effect.
    pub purity: Purity,
    /// Which runs an attribute asks for there, and how its `run` is spelled.
    pub site: NestedSite,
}

/// A `let x = c ;` statement the sugared form writes away: `c` written at
/// the binder's one read, the statement left out.
///
/// # Specification
/// - requires: nothing to construct this data; the lowering produces it.
/// - ensures: `bound` is the bytes of the call `c`, and `read` the bytes of the
///   binder's one read in the step after the statement.
/// - provides: the lowering's half of the formatter's linear-run rewrite.
/// - fails: not applicable to the record itself.
/// - panics: not applicable to the record itself.
///
/// # Adequacy
/// - hypothesis: L3 — a block's final runs read once each, first and in order,
///   in its tail, a chain's last link and a pair among them, beside runs read
///   in a later statement, out of order, twice, after another run, as the
///   tail's value and asked by an attribute.
/// - witness: `gandr-surface-lowering::lower::runs::tests::a_run_read_once_first_is_linear`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinearRun
{
    /// The bytes of the computation the statement runs.
    pub bound: ByteSpan,
    /// The bytes of the binder's one read.
    pub read: ByteSpan,
}
