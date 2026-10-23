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
//!
//! # Which `run` statements only sequence a call
//!
//! The `run x <- c ;` statements ending a block whose binders the tail reads
//! once each, in the statements' order, before it runs anything, only
//! linearise the code: written nested, each `c` stands where its `x` is read
//! and the checker runs them there, in that order, at the same point. The
//! lowering lists each such statement as a [`LinearRun`], for the sugared form
//! to write away. It reads that off the core it minted:
//!
//! - the statement binds a plain name, with no type written, and its rest is
//!   bound, not distributed to an exit's local ends;
//! - `c` is a call, which the operand position takes bare;
//! - no `explicit_runs` attribute reaching its declaration asks for runs, so
//!   the rewrite never writes a run the lint would report;
//! - every statement after it in the block is listed too, and none of their
//!   calls reads its binder;
//! - in the tail its binder's one read stands as an argument of a call or a
//!   field of a value, reached through applications, forces, returns, tuples,
//!   injections, list cells and constructors alone — the part of the tail the
//!   checker runs before anything under a binder — after the reads of the
//!   statements before it and before those after it, with no nested run and no
//!   other computation before the last of them.
//!
//! The suffix is listed whole, so one pass writes away all a block allows and
//! a second finds none. A read as the tail's whole value (`run m <- c ; m`)
//! stays: written as `c` alone it is a computation rather than a run of one,
//! a different core. A read under a thunk, a function or an arm stays, since
//! there `c` would run later or more than once. A read out of the statements'
//! order stays, since nested the calls would run in the reads' order. A read
//! in a later statement's computation stays too, a chain of statements among
//! them: the checker runs a nested run inside the computation that holds it,
//! so `run y <- g(c) ;` binds `c` inside `g`'s computation where
//! `run x <- c ; run y <- g(x) ;` binds it before — one program by the bind's
//! associativity, two cores. Such a chain sheds its last link and then stays,
//! its next read standing after the nested run.
//! Whether the two spellings mean one program is still the checker's to say:
//! the formatter compares the bodies it elaborates
//! (`gandr_surface_format::Elaborate`). The alternative was a syntactic list
//! the formatter's lowering comparison would refuse, since a nested run and
//! its bind lower to different cores. Reversal: a lowering that writes the
//! bind for a nested call itself, or a comparison up to the bind's
//! associativity, which would also admit a chain whole.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::effect::Purity;
use gandr_core_term::support::ThinningRef;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Resumed;
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

/// A `run x <- c ;` statement the sugared form writes away: `c` written at
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
/// - witness: `lower::runs::tests::a_run_read_once_first_is_linear`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinearRun
{
    /// The bytes of the computation the statement runs.
    pub bound: ByteSpan,
    /// The bytes of the binder's one read.
    pub read: ByteSpan,
}

impl Lowerer<'_, '_>
{
    /// The site of every nested node the values of `origins` record: those
    /// past the mark when `resumed` gives the closure's marks.
    ///
    /// # Specification
    /// - requires: the attribute pass has run, so every asking slot is marked.
    /// - ensures: one entry per syntax node a value of `origins` was nested at,
    ///   a value past `resumed`'s mark when it is given, asked the widest ask
    ///   an `explicit_runs` attribute reaching its declaration makes, or none,
    ///   spelled parenthesised exactly when its first byte begins a statement
    ///   or tail of a block, and its operand grouped unless its form binds
    ///   tighter than `run`.
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
        resumed: Option<Resumed<'_>>,
    ) -> BTreeMap<NodeIndex, NestedSite>
    {
        origins
            .values()
            .get(resumed.map_or(0, |resumed| resumed.values) ..)
            .unwrap_or_default()
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

    /// The `run` statements a block's tail reads once each, first and in
    /// order, each as a [`LinearRun`] in source order, read off the core
    /// minted into `arena` with its origins `origins`.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so each statement's binds are
    ///   recorded in `origins` at its `run` tile; the attribute pass has run,
    ///   so every asking slot is marked.
    /// - ensures: one entry per statement binding a plain name with its rest
    ///   bound, whose computation is a call and whose declaration no
    ///   `explicit_runs` attribute reaches, when, at each bind minted for it,
    ///   every statement after it in its block is one too, no later one's call
    ///   reads its binder, and the tail reads the binders as [`linear_read`]
    ///   finds, at one read for every bind: a match's branch, minted more than
    ///   once, holds its statements once per copy; sorted, without duplicates.
    /// - provides: the lowering's half of the formatter's linear-run rewrite.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`LinearRun`].
    /// - witness: `lower::runs::tests::a_run_read_once_first_is_linear`
    /// - witness: `lower::runs::tests::a_run_in_a_match_branch_is_linear_1935`
    #[spec(ensures: |ret| ret.len() <= self.statements.len() && ret.is_sorted())]
    pub(super) fn linear_runs(
        &self,
        arena: &CoreArena,
        origins: &OriginTable,
    ) -> Vec<LinearRun>
    {
        // Every bind minted for a statement, by the statement's `run` tile.
        let mut binds: Vec<(NodeIndex, ComputationId)> = origins
            .computations()
            .iter()
            .filter(|&&(id, origin)| {
                origin.provenance() == Provenance::Written
                    && matches!(arena.computation(id), Some(&Computation::Bind(..)))
            })
            .map(|&(id, origin)| (origin.node(), id))
            .collect();
        binds.sort_unstable();
        let minted = |origin: NodeIndex| {
            let start = binds.partition_point(|&(node, _)| node < origin);
            binds
                .get(start ..)
                .unwrap_or_default()
                .iter()
                .take_while(move |&&(node, _)| node == origin)
                .map(|&(_, bind)| bind)
        };
        // Each statement's binds, beside the statement and the call it runs
        // when the statement could be written away, as far as it alone says.
        let mut statements: BTreeMap<ComputationId, (usize, Option<ByteSpan>)> = BTreeMap::new();
        let mut listed: Vec<bool> = Vec::with_capacity(self.statements.len());
        for (index, statement) in self.statements.iter().enumerate() {
            let call = self.linear_call(statement);
            listed.push(call.is_some());
            for bind in minted(statement.origin) {
                let _held = statements.insert(bind, (index, call));
            }
        }
        // The run `bind` is, while the statements `listed` holds are written
        // away.
        let linear = |listed: &[bool], bind: ComputationId| {
            let call = statements.get(&bind)?.1?;
            let Some(&Computation::Bind(_, mut rest)) = arena.computation(bind)
            else {
                return None;
            };
            // The statements after this one, each written away too: none of
            // their calls may read a binder before it.
            let mut depth = DeBruijnIndex::from(0_u32);
            while let Some(&Computation::Bind(next, after)) = arena.computation(rest) {
                match statements.get(&rest) {
                    Some(&(later, Some(_)))
                        if listed.get(later).copied().unwrap_or_default()
                            && reading(arena.computation_support(next), depth)
                                == Reading::Unread =>
                    {
                        depth = DeBruijnIndex::from(u32::from(depth).checked_add(1)?);
                        rest = after;
                    },
                    Some(_) => return None,
                    // A bind no statement wrote is the tail's own.
                    None => break,
                }
            }
            let Maybe::Present(read) = origins.value(linear_read(arena, rest, depth)?)
            else {
                return None;
            };
            Some(LinearRun {
                bound: call,
                read: read.span(),
            })
        };
        // A statement minted more than once, as a match's branch is, is
        // written away only where every copy reads it at one read; an exit's
        // commuting copies, each with its own rest, do not. Dropping one
        // statement can drop one before it, so the listing settles first.
        let run_of = |listed: &[bool], statement: &super::Statement| {
            let mut runs = minted(statement.origin).map(|bind| linear(listed, bind));
            let first = runs.next()??;
            runs.all(|run| run == Some(first)).then_some(first)
        };
        loop {
            let dropped: Vec<usize> = self
                .statements
                .iter()
                .enumerate()
                .filter(|&(index, statement)| {
                    listed.get(index).copied().unwrap_or_default()
                        && run_of(&listed, statement).is_none()
                })
                .map(|(index, _)| index)
                .collect();
            if dropped.is_empty() {
                break;
            }
            for index in dropped {
                if let Some(held) = listed.get_mut(index) {
                    *held = false;
                }
            }
        }
        let mut found: Vec<LinearRun> = self
            .statements
            .iter()
            .enumerate()
            .filter(|&(index, _)| listed.get(index).copied().unwrap_or_default())
            .filter_map(|(_, statement)| run_of(&listed, statement))
            .collect();
        found.sort_unstable();
        found.dedup();
        found
    }

    /// The span of the call `statement` runs, when the statement alone allows
    /// writing it at its binder's read: it binds a plain name with its rest
    /// bound, its computation is a call, and no `explicit_runs` attribute
    /// reaching its declaration asks for runs.
    ///
    /// # Specification
    /// trivial.
    fn linear_call(
        &self,
        statement: &super::Statement,
    ) -> Option<ByteSpan>
    {
        if !matches!(statement.binding, super::StatementBinding::Named(_))
            || statement.rest != super::exits::Rest::Bound
        {
            return None;
        }
        let bound = self.tree.node(statement.bound)?;
        if !matches!(
            shape_of(self.pbg, bound),
            Ok(Shape::Form {
                former: Former::Call,
                ..
            })
        ) {
            return None;
        }
        let asked = match self.collected.owner_of(statement.origin) {
            Maybe::Present(slot) => self.asked_runs.get(&slot).copied().unwrap_or_default(),
            Maybe::Absent(_) => AskedRuns::Unasked,
        };
        (asked == AskedRuns::Unasked).then(|| bound.span())
    }
}

/// The read, in `rest`, a block's tail, of the binder `depth` statements out
/// from it, when the tail reads that binder and each statement's after it
/// once, in the statements' order, before it runs or reads anything else.
///
/// # Specification
/// - requires: `rest` is a computation of `arena`.
/// - ensures: the read is the value [`Region`] finds in `rest` for the
///   intuitionistic index `depth`, the indices below it read after it in
///   descending order, and nothing else in `rest` reads any of them; the
///   predicate checks the read is a variable at `depth`.
/// - fails: never; absent when no such reads stand.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`LinearRun`].
/// - witness: `lower::runs::tests::a_run_read_once_first_is_linear`
#[spec(ensures: |ret| ret.is_none_or(|read| matches!(
    arena.value(read),
    Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if index == depth
)))]
fn linear_read(
    arena: &CoreArena,
    rest: ComputationId,
    depth: DeBruijnIndex,
) -> Option<ValueId>
{
    let mut region = Region {
        arena,
        depth,
        expected: Some(depth),
        read: None,
        refused: false,
    };
    region.walk(rest);
    region
        .read
        .filter(|_| !region.refused && region.expected.is_none())
}

/// Whether a node reads one of the binders a walk tracks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// It reads one, or carries no support to say it does not.
    Reads,
    /// It reads none.
    Unread,
}

/// Whether `support` selects an intuitionistic index at most `depth`; a node
/// with no support recorded is taken to.
///
/// # Specification
/// trivial.
fn reading(
    support: Option<ThinningRef<'_>>,
    depth: DeBruijnIndex,
) -> Reading
{
    let reads = support.is_none_or(|support| {
        support
            .indices(Zone::Intuitionistic)
            .any(|selected| u32::from(selected) <= u32::from(depth))
    });
    if reads {
        Reading::Reads
    }
    else {
        Reading::Unread
    }
}

/// One node the region walk has still to visit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Step
{
    /// A computation.
    Computation(ComputationId),
    /// A value, standing as given.
    Value(ValueId, Standing),
}

/// The walk over what a block's tail runs before anything under a binder,
/// finding the reads of the binders of the statements written away.
struct Region<'arena>
{
    /// The arena the tail is minted in.
    arena: &'arena CoreArena,
    /// The index of the outermost statement's binder; every index at most it
    /// is a statement's.
    depth: DeBruijnIndex,
    /// The index whose read comes next, none once every one is read.
    expected: Option<DeBruijnIndex>,
    /// The read of the outermost statement's binder.
    read: Option<ValueId>,
    /// Whether something refuses the tail: a read out of order or under a
    /// binder, or a run before the last read.
    refused: bool,
}

impl Region<'_>
{
    /// Walk the computation `tail` in the order the checker runs it, until
    /// something refuses it.
    ///
    /// # Specification
    /// trivial.
    fn walk(
        &mut self,
        tail: ComputationId,
    )
    {
        let mut pending = Vec::from([Step::Computation(tail)]);
        while let Some(step) = pending.pop() {
            if self.refused {
                return;
            }
            match step {
                Step::Computation(id) => self.computation(id, &mut pending),
                Step::Value(id, standing) => self.value(id, standing, &mut pending),
            }
        }
    }

    /// Visit the computation `id`: an application's function, then its
    /// argument, a force's or a return's value, pushed onto `pending` to be
    /// visited in that order; anything else refuses.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        &mut self,
        id: ComputationId,
        pending: &mut Vec<Step>,
    )
    {
        match self.arena.computation(id) {
            Some(&Computation::Application(function, argument)) => {
                pending.push(Step::Value(argument, Standing::Field));
                pending.push(Step::Computation(function));
            },
            Some(&(Computation::Force(value) | Computation::Return(value))) => {
                pending.push(Step::Value(value, Standing::Whole));
            },
            // Any other computation runs before what follows it, or holds the
            // reads under its own binders.
            Some(_) | None => self.refused = true,
        }
    }

    /// Visit the value `id`, standing as `standing`: a statement's binder is
    /// read in its turn, a nested run refuses unless every read came before
    /// it, and a tuple's, an injection's, a list cell's and a constructor's
    /// fields are pushed onto `pending` to be visited in order; anything else
    /// must not read a binder.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        id: ValueId,
        standing: Standing,
        pending: &mut Vec<Step>,
    )
    {
        let arena = self.arena;
        let unread = |support| reading(support, self.depth) == Reading::Unread;
        match arena.value(id) {
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            }) if u32::from(index) <= u32::from(self.depth) => {
                if self.expected != Some(index) || standing == Standing::Whole {
                    self.refused = true;
                }
                else {
                    if index == self.depth {
                        self.read = Some(id);
                    }
                    self.expected = u32::from(index).checked_sub(1).map(DeBruijnIndex::from);
                }
            },
            Some(&(Value::Nested(run) | Value::Run(run) | Value::Returned(run))) => {
                if self.expected.is_some() || !unread(arena.computation_support(run)) {
                    self.refused = true;
                }
            },
            Some(&Value::Tuple(ref components)) => {
                pending.extend(
                    components
                        .iter()
                        .rev()
                        .map(|&component| Step::Value(component, Standing::Field)),
                );
            },
            Some(&Value::Injection(_, injected)) => {
                pending.push(Step::Value(injected, Standing::Field));
            },
            Some(&Value::ListCons(head, tail)) => {
                pending.push(Step::Value(tail, Standing::Field));
                pending.push(Step::Value(head, Standing::Field));
            },
            Some(&Value::Constructor {
                datatype,
                ref fields,
                ..
            }) => {
                if !unread(arena.value_type_support(datatype)) {
                    self.refused = true;
                }
                pending.extend(
                    fields
                        .iter()
                        .rev()
                        .map(|&field| Step::Value(field, Standing::Field)),
                );
            },
            Some(_) | None => {
                if !unread(arena.value_support(id)) {
                    self.refused = true;
                }
            },
        }
    }
}

/// Where a value the region walk meets stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Standing
{
    /// As the whole of a force or a return: a call written there would not be
    /// a run of it.
    Whole,
    /// As an argument or a field.
    Field,
}

/// How the computation at `node` is written after `run`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`RunOperand::Tight`] exactly for a form whose former is read at
///   the postfix or atom precedence; a prefix form at or below `run`'s, an
///   operator, a world form (a `hold` is a prefix form, and a migration shares
///   its former), a form outside the fragment and a node that is no form are
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
            | Former::ForgetModel
            | Former::Binary
            | Former::Unary
            | Former::World
            | Former::Unadmitted(_)
            | Former::Misplaced
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
        | Former::ForgetModel
        | Former::Binary
        | Former::Unary
        | Former::World
        | Former::Unadmitted(_)
        | Former::Misplaced => RunOperand::Grouped,
        Former::Name
        | Former::Constructor
        | Former::Hole
        | Former::Number
        | Former::Text
        | Former::Character
        | Former::TypeQuote
        | Former::Parenthesized
        | Former::Unit
        | Former::Boolean
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
        | Former::If
        | Former::Scope
        | Former::Telescope
        | Former::List
        | Former::PackModel
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
        | Former::StagedType
        | Former::ModedType
        | Former::LabelledSumType
        | Former::LazyRecordType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType
        | Former::PathType
        | Former::RelationType
        | Former::ManifestType
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::Mutual
        | Former::SessionType
        | Former::Action
        | Former::Offer
        | Former::Access
        | Former::WorldDeclaration
        | Former::Reserved(_) => RunOperand::Tight,
    }
}

#[cfg(test)]
mod tests;
