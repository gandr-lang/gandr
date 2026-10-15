//! The runs the checker infers: which ones an `explicit_runs` attribute asks
//! to be written, how `run` is written for each, and the record a face reads.
//!
//! The lowering holds a computation written where a value is read as a
//! nested node ([`Insertion::Nested`]) and cannot say whether it runs: that
//! is the type expected there, which only the checker reads. What the
//! lowering knows is where each nested node stands and which runs an
//! attribute on its declaration or module asks for there. The checker's
//! decisions, joined with that record by
//! [`LoweredModule::inferred_runs`](crate::LoweredModule::inferred_runs), are
//! the runs a face shows and the `explicit-runs` lint reports.
//!
//! # Which runs an attribute asks for
//!
//! `@[ explicit_runs ]` asks for every run inferred under the form it
//! decorates; `@[ explicit_runs("effects") ]` asks only for the runs whose
//! returner performs an effect, so pure arithmetic written nested stays
//! silent and an effectful call written nested asks for its `run`. A
//! declaration under a module asked both ways is asked the wider way. The
//! alternative was a second registered name for the effectful option, and a
//! second name for one lint would split its vocabulary. Reversal: a second
//! option is a second spelling the schema names.
//!
//! # How `run` is written for each run
//!
//! `run` is a prefix form at the unary precedence and takes no operand as
//! loose as itself, so a nested computation written with an operator or a
//! prefix keyword, as `id(n) + 1` is, is grouped after it: `run (id(n) + 1)`.
//! A call, a projection, an instantiation and every atom go after it bare.
//! A block reads `run` where a statement or its tail begins as the bind
//! statement `run x <- c ;`, so a nested computation that begins one, as
//! `f(x)` does in `{ f(x) + 1 }`, is written `(run f(x))`. The alternative
//! was a parser that reads `run` at a statement's start inline unless a
//! binder and `<-` follow, which moves the statement grammar for one
//! spelling. Reversal: that parser.

use alloc::collections::BTreeMap;

use anodized::spec;
use gandr_core_term::effect::Purity;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use crate::attribute::AttributeEntry;
use crate::attribute::RegisteredAttribute;
use crate::form::Former;
use crate::form::Shape;
use crate::form::shape_of;
use crate::module::SlotIndex;
use crate::origin::Insertion;
use crate::origin::OriginTable;
use crate::origin::Provenance;

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
/// - witness: `lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
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
/// - ensures: one variant for a computation that begins no statement of its
///   block, written after a bare `run`, and one for a computation that begins
///   one, written parenthesised after `run`.
/// - provides: the fix a face proposes, which the parser reads back as the run
///   it means.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a nested call after `return` and one first in a block's
///   tail, each written as spelled and checked again.
/// - witness: `lower::runs::tests::a_nested_run_is_spelled_as_its_written_run_reads_back`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RunSpelling
{
    /// `run c`: the computation begins no statement.
    #[default]
    Bare,
    /// `(run c)`: the computation begins a statement or a block's tail.
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
/// - witness: `lower::runs::tests::a_nested_run_is_spelled_as_its_written_run_reads_back`
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
///   [`LoweredModule::inferred_runs`](crate::LoweredModule::inferred_runs).
/// - fails: not applicable to the record itself.
/// - panics: not applicable to the record itself.
///
/// # Adequacy
/// - hypothesis: L3 — nested calls under a module's attribute, a declaration's
///   and none, asserted as their exact asks.
/// - witness: `lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
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
///   [`LoweredModule::inferred_runs`](crate::LoweredModule::inferred_runs)
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
/// - witness: `lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
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

impl Lowerer<'_, '_>
{
    /// The site of every nested node `origins` records.
    ///
    /// # Specification
    /// - requires: the attribute pass has run, so every asking slot is marked.
    /// - ensures: one entry per syntax node a value of `origins` was nested at,
    ///   asked the widest ask an `explicit_runs` attribute reaching its
    ///   declaration makes, or none, spelled parenthesised exactly when its
    ///   first byte begins a statement or tail of a block, and its operand
    ///   grouped unless its form binds tighter than `run`.
    /// - provides: the lowering's half of the join
    ///   [`LoweredModule::inferred_runs`](crate::LoweredModule::inferred_runs)
    ///   makes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested calls under a module's attribute, a
    ///   declaration's and none, asserted as their exact asks.
    /// - witness: `lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
    #[spec(ensures: |ret| ret.len() <= origins.values().len())]
    pub(super) fn nested_sites(
        &self,
        origins: &OriginTable,
    ) -> BTreeMap<NodeIndex, NestedSite>
    {
        origins
            .values()
            .iter()
            .filter(|&&(_, origin)| origin.provenance() == Provenance::Inserted(Insertion::Nested))
            .map(|&(_, origin)| {
                let asked = match self.collected.owner_of(origin.node()) {
                    Maybe::Present(slot) => self.asked_runs.get(&slot).copied().unwrap_or_default(),
                    Maybe::Absent(_) => AskedRuns::Unasked,
                };
                let spelling = if self.leading.contains(&origin.span().start()) {
                    RunSpelling::Parenthesised
                }
                else {
                    RunSpelling::Bare
                };
                let operand = operand_of(self.pbg, self.tree.node(origin.node()));
                (origin.node(), NestedSite {
                    asked,
                    spelling,
                    operand,
                })
            })
            .collect()
    }

    /// Mark `slots` as asked for the runs `entry` asks for, when it is an
    /// `explicit_runs` attribute: every run for the bare attribute, the
    /// effectful ones for its option.
    ///
    /// # Specification
    /// - requires: `entry` was admitted by its schema, so a payload of
    ///   `explicit_runs` spells its one option.
    /// - ensures: each of `slots` is asked at least what `entry` asks for, and
    ///   keeps a wider ask it already held; any other attribute marks nothing.
    ///   The predicate observes the table's size, which only an `explicit_runs`
    ///   attribute grows; the witness reads each slot's ask.
    /// - provides: the filing half of the module's switch.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member asked for every run by its module and for
    ///   the effectful ones by itself keeps every run.
    /// - witness: `lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
    #[spec(
        captures: before = self.asked_runs.len(),
        ensures: self.asked_runs.len() >= before
            && (entry.name() == RegisteredAttribute::EXPLICIT_RUNS || self.asked_runs.len() == before),
    )]
    pub(super) fn ask_runs<Slots>(
        &mut self,
        entry: &AttributeEntry,
        slots: Slots,
    ) where
        Slots: IntoIterator<Item = SlotIndex>,
    {
        if entry.name() != RegisteredAttribute::EXPLICIT_RUNS {
            return;
        }
        let asked = match entry.payload() {
            Maybe::Absent(_) => AskedRuns::Every,
            Maybe::Present(_) => AskedRuns::Effectful,
        };
        for slot in slots {
            let held = self.asked_runs.entry(slot).or_default();
            *held = (*held).max(asked);
        }
    }
}

/// How the computation at `node` is written after `run`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`RunOperand::Tight`] exactly for a form whose former is read at
///   the postfix or atom precedence; a prefix form at or below `run`'s, an
///   operator, a form outside the fragment and a node that is no form are
///   [`RunOperand::Grouped`], which reads back as written wherever it stands.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a nested call and a nested operator call, each written as
///   grouped and checked again.
/// - witness: `lower::runs::tests::a_nested_run_is_spelled_as_its_written_run_reads_back`
#[spec(ensures: |ret| match node.map(|node| shape_of(pbg, node)) {
    | Some(Ok(Shape::Form { former, .. })) => (ret == RunOperand::Grouped) == matches!(
        former,
        Former::Return
            | Former::Exit
            | Former::Become
            | Former::Force
            | Former::Run
            | Former::Binary
            | Former::Unary
            | Former::Unadmitted
    ),
    | Some(Ok(_) | Err(_)) | None => ret == RunOperand::Grouped,
})]
fn operand_of(
    pbg: &Pbg,
    node: Option<&Node>,
) -> RunOperand
{
    let Some(Ok(Shape::Form { former, .. })) = node.map(|node| shape_of(pbg, node))
    else {
        return RunOperand::Grouped;
    };
    match former {
        Former::Return
        | Former::Exit
        | Former::Become
        | Former::Force
        | Former::Run
        | Former::Binary
        | Former::Unary
        | Former::Unadmitted => RunOperand::Grouped,
        Former::Name
        | Former::Constructor
        | Former::Hole
        | Former::Number
        | Former::Text
        | Former::Parenthesized
        | Former::Unit
        | Former::Thunk
        | Former::Lambda
        | Former::Block
        | Former::Loop
        | Former::While
        | Former::For
        | Former::Break
        | Former::Continue
        | Former::Call
        | Former::Case
        | Former::Scope
        | Former::Telescope
        | Former::Injection
        | Former::LazyRecord
        | Former::Projection
        | Former::Instantiation
        | Former::TypeHead
        | Former::TypePath
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::SumType
        | Former::LazyProductType
        | Former::TelescopeType
        | Former::CapabilityType
        | Former::AtType
        | Former::LabelledSumType
        | Former::LazyRecordType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType
        | Former::PathType
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::SessionType
        | Former::Action
        | Former::Offer
        | Former::Access
        | Former::Reserved => RunOperand::Tight,
    }
}

#[cfg(test)]
mod tests;
