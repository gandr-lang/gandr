//! Early exits: a `return` or a `become` wherever a path through a body
//! passes, lowered so that every exit stands where its body ends; and a
//! loop's `break`, `continue` and re-entry, which the same commuting puts where
//! the loop's body ends.
//!
//! # Three passes, one per sweep
//!
//! A **survey**, descending before the classification, records what every
//! node's paths do with the body it stands in: never leave it, sometimes, or
//! always. A function, a lambda, a thunk and a copattern block never do,
//! since an exit inside one, or inside one of its clauses, leaves it and not
//! the body around it. A capability scope never does either: its clauses are
//! bodies of their own, and a `return` in its subject leaves by unwinding,
//! not by the commuting. A `break` and a `continue` always leave the loop
//! body they stand in; a loop sometimes leaves where it stands, through a
//! `break` of its own, and always leaves without one, since its body only
//! runs again or exits.
//!
//! The **classification** reads the survey at each block a path runs through.
//! A statement whose computation sometimes leaves distributes the rest of the
//! block: its computation joins the block, answers what the block answers, and
//! every position in tail position of it joins too. A statement whose
//! computation always leaves makes the rest of the block unreachable, which is
//! refused. An exit standing where no path passes — a call's head, outside any
//! body — is refused as not in tail. A handled subject is a block a path runs
//! through on its way through the body the scope stands in: its tail is the
//! subject's result, and every position on its paths is framed.
//!
//! The **mint** sweep commutes each body once, when the function, the lambda
//! or the thunk that owns it is minted: a bind whose rest is distributed
//! disappears into its computation, whose every local end binds a copy of the
//! rest, carried under the binders between the statement and the end, and
//! every exit is left where it stands, which is then where the body ends. The
//! walk enters a loop's fixpoint: a local end inside it is a `break`, which
//! continues what the loop's own position continues, or an exit — a
//! `return`, a `become`, a `continue` or a re-entry — which stays. A match
//! leaf's copy of an arm body carries the exits, the `break`s, the loops and
//! the distributed binds of the arm with it. A handled subject is commuted as
//! a body is, its own; a `return` framed in it is a capture its body's
//! delimiter discards, and that body is minted under the delimiter.
//!
//! The decision, the alternatives and what reverses it are the crate's: see
//! the crate documentation's section on exits.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::ArenaWatermark;
use gandr_core_term::Binders;
use gandr_core_term::Carried;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::SplitMotive;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::session::SessionAction;
use gandr_core_term::world::WorldForm;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Lowerer;
use super::Sink;
use super::lowered;
use super::native::Answer;
use super::native::answered;
use crate::error::LoweringRefusal;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::origin::Insertion;
use crate::origin::Label;
use crate::origin::Labelled;
use crate::origin::Origin;
use crate::origin::Provenance;

#[cfg(test)]
pub(in crate::lower) mod tests;

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
/// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Leaves
{
    /// No path leaves: the node holds no exit outside a body of its own.
    #[default]
    Never,
    /// Some path leaves and some ends where the node stands.
    Sometimes,
    /// Every path leaves.
    Always,
}

/// Whether a node holds a `break` of the loop around it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the variants are ordered, so the greater of two children's is
///   what a form holding both holds.
/// - provides: the half of the survey that tells a loop which a `break` leaves
///   from apart from one that only runs again or exits.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a loop with a `break`, one without, and a `break` inside
///   a nested loop, each surveyed exactly.
/// - witness: `lower::loops::tests::a_loop_leaves_where_it_stands_only_through_its_breaks`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Breaks
{
    /// No `break` of the loop around the node stands in it.
    #[default]
    Never,
    /// A `break` of the loop around the node stands in it.
    Held,
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
/// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Rest
{
    /// The rest is bound once over the statement's computation.
    Bound,
    /// The rest continues every local end of the statement's computation,
    /// which holds an exit.
    Distributed,
}

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
/// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
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
/// - witness: `lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
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
/// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
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
/// before the closing brace; its operand is a value, through any grouping, so
/// the exit the bare value's polarity names is the `return` written; it does
/// not cross a handler's frame; and its declaration lowered, under no
/// `explicit_exits` attribute. Leaving the keyword out therefore mints the
/// same term. An early exit — one in a statement whose rest it distributes —
/// is no tail and is never listed, nor is a `become`, which a sugared tail
/// keeps.
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
///   grouping, is listed; one of a computation, one of a grouped type, one
///   written as a statement, an early one, one an attribute asks for and one in
///   a refused declaration are not; each listed one lowers as its tail written
///   bare does.
/// - witness: `lower::exits::tests::a_tail_return_of_a_value_is_listed_as_elidable_1327`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ElidableExit
{
    /// The bytes of the `return` form.
    pub span: ByteSpan,
    /// The bytes of the value it returns: the tail left without the keyword.
    pub value: ByteSpan,
}

quenchant_shape::reason_enum! {
    /// Why a rest continues no rest of its own.
    pub mod enclosing {
        /// The statement's computation is where its body's own path runs.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No local end of another statement holds the statement.
            Outermost,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a rest has no commuted form yet.
    pub mod settled {
        /// The commuting has not reached it.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No local end has asked for it.
            Pending,
        }
    }
}

/// A rest of a block the commuting holds, by its position in its list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct RestAt(usize);

/// The rests a computation's local ends continue: an ordinary end's, and a
/// `break`'s.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: an absent rest leaves its ends where they stand; a `break`'s is
///   the rest of the position its loop stands at.
/// - executable: none — the record holds no list of rests to check against.
///
/// # Adequacy
/// - hypothesis: L3 — a `break` inside a statement of a loop's body continues
///   the block after the loop, while the statement's own ends continue the
///   body's block.
/// - witness: `lower::loops::tests::a_break_continues_what_follows_its_loop`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Ends
{
    /// What an ordinary local end continues.
    rests: Maybe<RestAt, enclosing::Absent>,
    /// What a `break` of the nearest loop continues.
    breaks: Maybe<RestAt, enclosing::Absent>,
}

/// A distributed rest: what continues each local end of its statement.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the rest is read under the statement's binder, `depth` binders
///   below the body's root.
/// - executable: none — the record holds no arena to check the depth against.
///
/// # Adequacy
/// - hypothesis: L3 — a rest continuing the local ends of a match nested in
///   another match's arm continues the outer rest in turn.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Pending
{
    /// The rest, under the statement's one binder.
    rest: ComputationId,
    /// The binders between the body's root and the statement.
    depth: Binders,
    /// The statement's origin, which every bind of the rest carries.
    origin: Origin,
    /// What the statement's own position continues: the rest of the
    /// statement it stands at a local end of, and the rest a `break` in it
    /// continues.
    outer: Ends,
}

/// One unit of the commuting's work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Step
{
    /// Commute a computation at a depth, under the rests it continues.
    Open(ComputationId, Ends, Binders),
    /// Rebuild a computation over its children's commuted forms.
    Close(ComputationId),
    /// Keep the result on top as a rest's commuted form.
    Settle(RestAt),
    /// Bind a local end at a depth over a rest's commuted form.
    Continue(ComputationId, RestAt, Binders),
}

impl<'source> Lowerer<'_, 'source>
{
    /// Survey what every node's paths do with the body it stands in.
    ///
    /// # Specification
    /// - requires: nothing; the survey reads the tree alone.
    /// - ensures: every node holds its [`Leaves`], children before parents:
    ///   `return`, `become`, `break` and `continue` always leave; a function, a
    ///   lambda, a thunk, a copattern block, a capability scope and a temporary
    ///   access never do, since an exit inside one leaves it, unwinds past it
    ///   or is refused there; a `loop` sometimes does when a `break` of its own
    ///   stands in it and always does otherwise, and a `while` or a `for`
    ///   sometimes does; a form holding no exit outside such a body never does;
    ///   a block or a grouping does what the child that leaves most does; a
    ///   match always leaves when every arm does; every other form holding an
    ///   exit sometimes does.
    /// - provides: what the classification of a block reads to decide where the
    ///   rest of the block goes, before any statement in it is classified.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the sweep outruns the
    ///   allowance, a step per node.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a computation with no exit, one with an exit in one
    ///   arm and one with an exit in every arm, each at one and two depths, an
    ///   exit inside a thunk, and loops with and without a `break`, each
    ///   asserted as its exact survey.
    /// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
    /// - witness: `lower::loops::tests::a_loop_leaves_where_it_stands_only_through_its_breaks`
    #[spec(
        captures: before = (self.fuel.remaining, self.leaves.len()),
        ensures: |ret| {
            self.leaves.len() == before.1
                && (ret.is_err()
                    || self.fuel.remaining
                        <= before.0.saturating_sub(self.own.len()))
        },
    )]
    pub(super) fn survey(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        let mut remaining = self.own.len();
        let mut breaks = Vec::new();
        breaks.resize(usize::from(self.tree.node_count()), Breaks::Never);
        let mut outcome = Ok(());
        while let Some(next) = remaining.checked_sub(1_usize) {
            remaining = next;
            if let Err(refusal) = self.fuel.spend() {
                outcome = Err(refusal);
                break;
            }
            let Some(&position) = self.own.get(next)
            else {
                continue;
            };
            let (leaves, broken) = self.leaves_of(position, &mut pieces, &breaks);
            if let Some(held) = self.leaves.get_mut(usize::from(position)) {
                *held = leaves;
            }
            if let Some(held) = breaks.get_mut(usize::from(position)) {
                *held = broken;
            }
        }
        self.pieces = pieces;

        outcome
    }

    /// What the paths of the node at `position` do, and whether it holds a
    /// `break` of the loop around it, its children surveyed into `breaks` and
    /// the leaves.
    ///
    /// # Specification
    /// - requires: every child of `position` is surveyed.
    /// - ensures: as [`Self::survey`] states it, for one node; a node that is
    ///   no form sometimes leaves when a child does and never otherwise; a
    ///   `break` holds one, a loop, a function, a lambda, a thunk, a copattern
    ///   block, a capability scope and a temporary access hold none, and every
    ///   other node holds one when a child does; a node holding a `break`
    ///   leaves at least sometimes.
    /// - provides: the per-node half of [`Self::survey`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::survey`].
    /// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
    /// - witness: `lower::loops::tests::a_loop_leaves_where_it_stands_only_through_its_breaks`
    #[spec(ensures: |ret| ret.1 == Breaks::Never || ret.0 != Leaves::Never)]
    fn leaves_of(
        &self,
        position: NodeIndex,
        pieces: &mut Pieces,
        breaks: &[Breaks],
    ) -> (Leaves, Breaks)
    {
        let (held, broken) = self.tree.children(position).fold(
            (Leaves::Never, Breaks::Never),
            |(leaves, broken), child| {
                (
                    leaves.max(self.leaves_at(child)),
                    broken.max(breaks.get(usize::from(child)).copied().unwrap_or_default()),
                )
            },
        );
        let Some(node) = self.tree.node(position)
        else {
            return (Leaves::Never, Breaks::Never);
        };
        let Ok(Shape::Form { former, .. }) = shape_of(self.pbg, node)
        else {
            return (held.min(Leaves::Sometimes), broken);
        };
        match former {
            Former::Break => (Leaves::Always, Breaks::Held),
            Former::Exit | Former::Become | Former::Continue => (Leaves::Always, Breaks::Never),
            Former::Thunk
            | Former::Lambda
            | Former::LazyRecord
            | Former::Scope
            | Former::Access
            | Former::World
            | Former::Declaration
            | Former::WorldDeclaration
            | Former::Module => (Leaves::Never, Breaks::Never),
            Former::Loop if broken == Breaks::Never => (Leaves::Always, Breaks::Never),
            Former::Loop | Former::While | Former::For => (Leaves::Sometimes, Breaks::Never),
            _ if held == Leaves::Never => (Leaves::Never, Breaks::Never),
            Former::Block | Former::Parenthesized => (held, broken),
            Former::Case | Former::Offer => (self.arms_leave(position, pieces), broken),
            Former::If => (self.branches_leave(position, pieces), broken),
            Former::Name
            | Former::Constructor
            | Former::Hole
            | Former::Number
            | Former::Text
            | Former::TypeQuote
            | Former::Unit
            | Former::Boolean
            | Former::Return
            | Former::Force
            | Former::Run
            | Former::Call
            | Former::Telescope
            | Former::List
            | Former::PackModel
            | Former::Injection
            | Former::Binary
            | Former::Unary
            | Former::Projection
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
            | Former::LabelledSumType
            | Former::LazyRecordType
            | Former::ValueFunctionType
            | Former::StaticAbstraction
            | Former::ParenthesizedType
            | Former::PathType
            | Former::RelationType
            | Former::ManifestType
            | Former::CapabilityType
            | Former::AtType
            | Former::StagedType
            | Former::ModedType
            | Former::AttributeBlock
            | Former::Import
            | Former::Data
            | Former::Mutual
            | Former::Instantiation
            | Former::SessionType
            | Former::Action
            | Former::Reserved(_)
            | Former::Unadmitted(_)
            | Former::Misplaced => (Leaves::Sometimes, broken),
        }
    }

    /// What the paths of the match or the offer at `position`, which holds an
    /// exit, do: always leave when every arm always does.
    ///
    /// # Specification
    /// - requires: every arm body of the match or the offer is surveyed, and
    ///   one of its children holds an exit.
    /// - ensures: always when the form has an arm and every arm body always
    ///   leaves; sometimes otherwise, a form whose pieces do not read included.
    /// - provides: the match and offer half of [`Self::leaves_of`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::survey`].
    /// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
    #[spec(ensures: |ret| ret != Leaves::Never)]
    fn arms_leave(
        &self,
        position: NodeIndex,
        pieces: &mut Pieces,
    ) -> Leaves
    {
        if read_pieces(self.pbg, self.tree, position, pieces).is_err() {
            return Leaves::Sometimes;
        }
        let mut arrow = false;
        let mut leaves = Leaves::Sometimes;
        let mut every = Leaves::Always;
        for piece in &pieces.pieces {
            match *piece {
                Piece::Tile { label, .. } => arrow = label == TileName::FAT_ARROW,
                Piece::Operand(body) if arrow => {
                    arrow = false;
                    every = every.min(self.leaves_at(body.node));
                    leaves = every.max(Leaves::Sometimes);
                },
                Piece::Operand(_) => {},
            }
        }

        leaves
    }

    /// What the paths of the conditional at `position`, which holds an exit,
    /// do: always leave when every branch always does.
    ///
    /// # Specification
    /// - requires: every computation of every branch of the conditional is
    ///   surveyed, and one of its children holds an exit.
    /// - ensures: always when the form has a branch and every branch has a
    ///   computation that always leaves; sometimes otherwise, a form whose
    ///   pieces do not read included.
    /// - provides: the conditional's half of [`Self::leaves_of`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a conditional both of whose branches return ends its
    ///   function with nothing after it, and one only one of whose branches
    ///   returns continues its block.
    /// - witness: `lower::conditional::tests::a_conditional_runs_the_branch_its_condition_selects`
    #[spec(ensures: |ret| ret != Leaves::Never)]
    fn branches_leave(
        &self,
        position: NodeIndex,
        pieces: &mut Pieces,
    ) -> Leaves
    {
        if read_pieces(self.pbg, self.tree, position, pieces).is_err() {
            return Leaves::Sometimes;
        }
        let mut branch = None;
        let mut every = None;
        for piece in &pieces.pieces {
            match *piece {
                Piece::Tile { label, .. } if label == TileName::BRACE_OPEN => {
                    branch = Some(Leaves::Never);
                },
                Piece::Tile { label, .. } if label == TileName::BRACE_CLOSE => {
                    let ended = branch.take().unwrap_or(Leaves::Never);
                    every = Some(every.map_or(ended, |held: Leaves| held.min(ended)));
                },
                Piece::Operand(computation) => {
                    if let Some(held) = branch.as_mut() {
                        *held = (*held).max(self.leaves_at(computation.node));
                    }
                },
                Piece::Tile { .. } => {},
            }
        }

        every.unwrap_or(Leaves::Sometimes).max(Leaves::Sometimes)
    }

    /// What the paths of the node at `position` do, as surveyed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the surveyed answer of a node the tree holds; never for a
    ///   position past the tree.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::survey`].
    /// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
    #[spec(ensures: |ret| ret == self.leaves.get(usize::from(position)).copied().unwrap_or_default())]
    pub(super) fn leaves_at(
        &self,
        position: NodeIndex,
    ) -> Leaves
    {
        self.leaves
            .get(usize::from(position))
            .copied()
            .unwrap_or_default()
    }

    /// Mark `inner`, standing in tail position of `outer`, with the paths
    /// through `outer`: where a path ends, where an exit may stand, where a
    /// local end continues a block, where a path through a loop's body ends,
    /// where a `break` or a `continue` may stand, where a handled subject's
    /// result is, where a handler's frame is live, the body the path runs
    /// through, and whether a statement written `c ;` holds it.
    ///
    /// # Specification
    /// - requires: `inner` stands in tail position of `outer`: a block's last
    ///   computation, a match's arm, a grouping's operand.
    /// - ensures: `inner` carries each mark `outer` carries, and keeps its own.
    /// - provides: the one way a path is passed down the classification.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path through a grouping, a block and a match
    ///   reaches an exit in each, an exit under none is refused, and a path
    ///   through nested matches without its exit takes the inferred one where
    ///   it ends.
    /// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    /// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    #[spec(
        captures: before = (
            self.exits.contains(&inner) || self.exits.contains(&outer),
            self.exitable.contains(&inner) || self.exitable.contains(&outer),
            self.joined.contains(&inner) || self.joined.contains(&outer),
            self.iterated.contains(&inner) || self.iterated.contains(&outer),
            self.looping.contains(&inner) || self.looping.contains(&outer),
            self.framed.contains(&inner) || self.framed.contains(&outer),
        ),
        ensures: self.exits.contains(&inner) == before.0
            && self.exitable.contains(&inner) == before.1
            && self.joined.contains(&inner) == before.2
            && self.iterated.contains(&inner) == before.3
            && self.looping.contains(&inner) == before.4
            && self.framed.contains(&inner) == before.5,
    )]
    pub(super) fn pass_paths(
        &mut self,
        outer: NodeIndex,
        inner: NodeIndex,
    )
    {
        for marks in [
            &mut self.exits,
            &mut self.exitable,
            &mut self.joined,
            &mut self.iterated,
            &mut self.looping,
            &mut self.results,
            &mut self.framed,
            &mut self.looped_past,
        ] {
            if marks.contains(&outer) {
                let _marked = marks.insert(inner);
            }
        }
        if let Some(&body) = self.bodies.get(&outer) {
            let _owner = self.bodies.insert(inner, body);
        }
        if self.stated.contains_key(&outer) || self.stated_tails.contains(&outer) {
            let _held = self.stated_tails.insert(inner);
        }
    }

    /// Read `body`, the block of a function's, a lambda's or a thunk's body,
    /// as one a path runs through, its last computation where the body ends.
    ///
    /// # Specification
    /// - requires: `body` is the block just read for the body at `site`, and
    ///   `answer` the type the body states, when it states one.
    /// - ensures: the block's last computation is where a path ends, in the
    ///   body it ends, and the block's statements as [`Self::paths_through`]
    ///   marks them.
    /// - provides: the one opening of a body every function, lambda, thunk and
    ///   copattern clause shares.
    /// - fails: [`LoweringRefusal::Unreachable`], as [`Self::paths_through`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::Unreachable`] for statements no path reaches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::paths_through`].
    /// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
    /// - witness: `lower::exits::tests::code_no_path_reaches_is_refused`
    #[spec(ensures: |ret| ret.is_err() || (self.exits.contains(&body.last) && self.exitable.contains(&body.last)
        && self.bodies.get(&body.last) == Some(&body.last)))]
    pub(super) fn open_body(
        &mut self,
        site: super::Site,
        body: Block,
        answer: Maybe<Answer, answered::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _tail = self.exits.insert(body.last);
        let _owner = self.bodies.insert(body.last, body.last);
        self.paths_through(site, body, answer)
    }

    /// Record that the form at `site`, a block's last statement that is not
    /// an exit, runs with its result discarded, the block returning the unit
    /// after it.
    ///
    /// # Specification
    /// - requires: `site` is a block's last computation written as a statement
    ///   and no exit, outside a loop's end.
    /// - ensures: a form whose every path leaves is left as it is, the end of
    ///   its block; any other is recorded as trailing, is not where a path
    ///   ends, so nothing in its tail position takes an inferred exit, and
    ///   either joins what follows it, when a path through it leaves, or
    ///   answers nothing, since its result is discarded.
    /// - provides: the reading of `{ s… c ; }` as Rust reads it: `c` runs and
    ///   the block's value is the unit.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call, a `pure` and a session action ending a body
    ///   as a statement each run before the unit is returned; a match whose
    ///   every arm returns stays the body's end.
    /// - witness: `lower::exits::tests::a_block_ending_in_a_statement_returns_the_unit_1205`
    #[spec(ensures: (self.leaves_at(site.at.node) == Leaves::Always) != self.trailing.contains(&site.at.node)
        && (!self.trailing.contains(&site.at.node) || !self.exits.contains(&site.at.node)))]
    pub(super) fn trail(
        &mut self,
        site: super::Site,
    )
    {
        let leaves = self.leaves_at(site.at.node);
        if leaves == Leaves::Always {
            return;
        }
        let _first = self.trailing.insert(site.at.node);
        // A path passes the statement on to the unit returned after it.
        let _passed = self.exits.remove(&site.at.node);
        if leaves == Leaves::Never {
            let _discarded = self.answers.remove(&site.at.node);
        }
        else {
            let _joined = self.joined.insert(site.at.node);
        }
    }

    /// `end`, minted at `position` where a block ends in a statement, with
    /// its result discarded and the unit returned after it.
    ///
    /// # Specification
    /// - requires: `position` trails, as [`Self::trail`] records; `end` is the
    ///   node's bridged computation.
    /// - ensures: `x ← end; split x (); return ()`, `end` ascribed the returner
    ///   of the unit when no path through it leaves, every inserted node at
    ///   `origin` marked as the statement's insertion, the `return` recorded as
    ///   an exit, and the bind recorded as distributed when a path through
    ///   `end` leaves.
    /// - provides: the minting half of [`Self::trail`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a body ending in `c ;` lowers to the body written
    ///   with the unit returned after `c`. L3 — the checker accepts it.
    /// - witness: `lower::exits::tests::a_block_ending_in_a_statement_returns_the_unit_1205`
    #[spec(ensures: |ret| sink.arena.computation(ret).is_some())]
    pub(super) fn conclude(
        &self,
        position: NodeIndex,
        end: ComputationId,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ComputationId
    {
        let inserted = origin.inserted(Insertion::Statement);
        let discarded = sink
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        sink.origins.record_value(discarded, inserted);
        let unit = sink.arena.value_unit();
        sink.origins.record_value(unit, inserted);
        let returned = sink.arena.computation_return(unit);
        sink.origins.record_computation(returned, inserted);
        let _exit = sink.exits.insert(returned);
        let split = sink
            .arena
            .computation_split(discarded, ComponentCount::default(), returned);
        sink.origins.record_computation(split, inserted);
        let leaves = self.leaves_at(position);
        // The discarded result is the unit, so a statement no path leaves is
        // ascribed the returner of the unit: the bind then checks it against
        // that type rather than synthesising one.
        let ran = if leaves == Leaves::Never {
            let unit = sink.arena.value_type_unit();
            sink.origins.record_value_type(unit, inserted);
            let returner = sink.arena.comp_type_returner(unit);
            sink.origins.record_comp_type(returner, inserted);
            let ascribed = sink.arena.computation_ascribe(end, returner);
            sink.origins.record_computation(ascribed, inserted);
            ascribed
        }
        else {
            end
        };
        let bound = sink.arena.computation_bind(ran, split);
        sink.origins.record_computation(bound, inserted);
        if leaves != Leaves::Never {
            let _first = sink.distributed.insert(bound, inserted);
        }

        bound
    }

    /// Read `subject`, the block the capability scope at `site` handles, as
    /// one a path runs through on its way through the body the scope stands
    /// in.
    ///
    /// # Specification
    /// - requires: `subject` is the block just read for the scope at `site`.
    /// - ensures: the block's last computation is where a path through the
    ///   subject ends, its result, and no exit; every position on the block's
    ///   paths is framed, belongs to the body `site` belongs to, when a path
    ///   through one passes `site`, and stands past the loop whose body `site`
    ///   stands in, when one does; the block's statements as
    ///   [`Self::paths_through`] marks them.
    /// - provides: the opening of a handled subject, which is no body: a
    ///   `return` in it leaves the body around the scope.
    /// - fails: [`LoweringRefusal::Unreachable`], as [`Self::paths_through`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::Unreachable`] for statements no path reaches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `return` in a subject leaves its function, its
    ///   `pure` clause not run; a `become`, and a `break` of a loop around the
    ///   scope, are refused; a loop inside the subject runs as any loop.
    /// - witness: `lower::capability::tests::a_return_in_a_subject_leaves_past_the_handler`
    /// - witness: `lower::capability::tests::an_exit_that_would_run_in_a_live_frame_is_refused`
    #[spec(ensures: |ret| ret.is_err() || (self.results.contains(&subject.last)
        && self.framed.contains(&subject.last) && !self.exits.contains(&subject.last)
        && self.bodies.get(&subject.last) == self.bodies.get(&site.at.node)))]
    pub(super) fn open_subject(
        &mut self,
        site: super::Site,
        subject: Block,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _result = self.results.insert(subject.last);
        let _framed = self.framed.insert(subject.last);
        if self.looping.contains(&site.at.node) || self.looped_past.contains(&site.at.node) {
            let _past = self.looped_past.insert(subject.last);
        }
        if let Some(&body) = self.bodies.get(&site.at.node) {
            let _owner = self.bodies.insert(subject.last, body);
        }
        self.paths_through(site, subject, Maybe::Absent(answered::Absent::Unstated))
    }

    /// Run the paths through `block` on to its statements.
    ///
    /// # Specification
    /// - requires: `block` is the block just read at `site`, a path passes it,
    ///   and `answer` is the type the block answers, when one is stated.
    /// - ensures: the last computation and every statement's computation are
    ///   where an exit may stand, and where a `break` or a `continue` may when
    ///   the last computation is on a path through a loop's body; every
    ///   statement's computation carries the last computation's frame, its loop
    ///   past the frame, and its body; a statement whose computation sometimes
    ///   leaves distributes the rest of the block, its computation joining the
    ///   block and answering `answer`; a statement whose computation never
    ///   leaves keeps its rest bound.
    /// - provides: the statement half of the classification of exits.
    /// - fails: [`LoweringRefusal::Unreachable`] for a statement whose
    ///   computation always leaves, at the bytes from the next statement to the
    ///   block's last computation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::Unreachable`] for statements no path reaches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a statement leaving in one arm distributes its rest,
    ///   one leaving in every arm refuses what follows, and one never leaving
    ///   keeps its rest bound.
    /// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
    /// - witness: `lower::exits::tests::code_no_path_reaches_is_refused`
    #[spec(ensures: |ret| ret.is_err() || (self.exitable.contains(&block.last)
        && super::stretch(&self.statements, block.statements).iter().all(|statement| {
            self.exitable.contains(&statement.bound)
                && (!self.looping.contains(&block.last) || self.looping.contains(&statement.bound))
                && (!self.framed.contains(&block.last) || self.framed.contains(&statement.bound))
                && self.bodies.get(&block.last).is_none_or(|body| self.bodies.get(&statement.bound) == Some(body))
                && (statement.rest == Rest::Distributed) == (self.leaves_at(statement.bound) == Leaves::Sometimes)
                && (statement.rest == Rest::Bound || self.joined.contains(&statement.bound))
        })))]
    pub(super) fn paths_through(
        &mut self,
        site: super::Site,
        block: Block,
        answer: Maybe<Answer, answered::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _last = self.exitable.insert(block.last);
        let looping = self.looping.contains(&block.last);
        let framed = self.framed.contains(&block.last);
        let past = self.looped_past.contains(&block.last);
        let body = self.bodies.get(&block.last).copied();
        for position in block.statements.start .. block.statements.end {
            let Some(&statement) = self.statements.get(position)
            else {
                continue;
            };
            let _path = self.exitable.insert(statement.bound);
            if looping {
                let _iteration = self.looping.insert(statement.bound);
            }
            if framed {
                let _framed = self.framed.insert(statement.bound);
            }
            if past {
                let _past = self.looped_past.insert(statement.bound);
            }
            if let Some(body) = body {
                let _owner = self.bodies.insert(statement.bound, body);
            }
            match self.leaves_at(statement.bound) {
                Leaves::Never => {},
                Leaves::Sometimes => {
                    if let Some(held) = self.statements.get_mut(position) {
                        held.rest = Rest::Distributed;
                    }
                    let _joined = self.joined.insert(statement.bound);
                    if let Maybe::Present(stated) = answer {
                        let _first = self.answers.insert(statement.bound, stated);
                    }
                },
                Leaves::Always => {
                    let after = super::Stretch {
                        start: position.saturating_add(1_usize),
                        end: block.statements.end,
                    };
                    return Err(LoweringRefusal::Unreachable {
                        span: self.unreached(site, block, after),
                    });
                },
            }
        }

        Ok(())
    }

    /// The bytes no path reaches in `block` once a statement always leaves:
    /// from the first statement of `after`, or the last computation, to the
    /// last computation.
    ///
    /// # Specification
    /// - requires: `after` is the stretch of `block`'s statements that follow
    ///   the leaving one, `block` read at `site`.
    /// - ensures: the span from the first node after the statement to the
    ///   block's last computation; the site's span when the tree holds neither.
    /// - provides: the locus of [`LoweringRefusal::Unreachable`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused rest of one statement and of none before
    ///   the last computation, each at its exact bytes.
    /// - witness: `lower::exits::tests::code_no_path_reaches_is_refused`
    #[spec(ensures: |ret| self.tree.node(block.last).is_none_or(|node| ret.end() >= node.span().end()))]
    fn unreached(
        &self,
        site: super::Site,
        block: Block,
        after: super::Stretch,
    ) -> ByteSpan
    {
        let first = if after.start < after.end {
            self.statements
                .get(after.start)
                .map_or(block.last, |statement| statement.origin)
        }
        else {
            block.last
        };
        let span_of = |node: NodeIndex| self.tree.node(node).map(gandr_surface_syntax::Node::span);
        match (span_of(first), span_of(block.last)) {
            (Some(start), Some(end)) => start.join(end),
            (Some(only), None) | (None, Some(only)) => only,
            (None, None) => site.at.span,
        }
    }

    /// Mint `body`, the block of a function's, a lambda's or a thunk's body, a
    /// copattern clause or a handled subject, with every exit put where the
    /// body ends.
    ///
    /// # Specification
    /// - requires: every node the block names is already minted or absent;
    ///   `origin` is the body's owner's.
    /// - ensures: the block [`Self::mint_block`] mints, commuted by [`commute`]
    ///   once any bind with a distributed rest is minted, and delimited by a
    ///   reset, inserted at `origin`, when a `return` framed in a subject
    ///   leaves the body; nothing when the block did not lower.
    /// - provides: the body half of thunks, lambdas, copattern clauses,
    ///   function tails and handled subjects.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body with no early exit is the block itself, one
    ///   with an exit two matches deep leaves from where it stands, and one
    ///   holding a scope whose subject returns is delimited.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
    /// - witness: `lower::capability::tests::a_return_in_a_subject_leaves_past_the_handler`
    #[spec(ensures: |ret| match ret {
        | Maybe::Absent(_) => true,
        | Maybe::Present(id) => sink.arena.computation(id).is_some()
            && (!self.delimited.contains(&body.last) || matches!(sink.arena.computation(id), Some(&Computation::Reset(_)))),
    })]
    pub(super) fn mint_body(
        &self,
        body: Block,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        self.mint_block(body, sink).map(|minted| {
            let commuted = if sink.distributed.is_empty() {
                minted
            }
            else {
                commute(sink, minted, origin)
            };
            if self.delimited.contains(&body.last) {
                let id = sink.arena.computation_reset(commuted);
                sink.origins
                    .record_computation(id, origin.inserted(Insertion::Unwind));
                id
            }
            else {
                commuted
            }
        })
    }

    /// The `return` minted as `returned`, written in a handled subject, as the
    /// capture that leaves its body: every handler frame up to the body's
    /// delimiter is captured and discarded, and the delimiter returns the
    /// value.
    ///
    /// # Specification
    /// - requires: `returned` is the returner a `return` at `origin` minted.
    /// - ensures: a shift, inserted at `origin`, over `returned` with every
    ///   free index raised past the shift's own binder, which binds the
    ///   captured stack the body never resumes; every node the raise minted at
    ///   its source's origin.
    /// - provides: the mint half of a `return` across a handler's frame.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `return` of a parameter in a subject leaves its
    ///   function with the parameter's value, the return clause not run.
    /// - witness: `lower::capability::tests::a_return_in_a_subject_leaves_past_the_handler`
    #[spec(ensures: |ret| matches!(sink.arena.computation(ret), Some(&Computation::Shift(_))))]
    pub(super) fn unwind(
        sink: &mut Sink<'_>,
        returned: ComputationId,
        origin: Origin,
    ) -> ComputationId
    {
        let mark = sink.arena.watermark();
        let mut carried = Vec::new();
        let raised = gandr_core_term::shift_computation_under(
            sink.arena,
            returned,
            Binders::NONE,
            Binders::from(1_u32),
        )
        .settle_traced(sink.arena, &mut carried);
        record_copies(sink, mark, &carried, origin);
        let id = sink.arena.computation_shift(raised);
        sink.origins
            .record_computation(id, origin.inserted(Insertion::Unwind));
        id
    }

    /// Every exit the mint sweep inferred in a declaration that lowered, in
    /// source order.
    ///
    /// # Specification
    /// - requires: the attribute pass and the documentation pass have run, so
    ///   every refusal is offered and every asked slot is marked.
    /// - ensures: one record per inferred exit minted under a declaration that
    ///   holds no refusal, at its tail's span, asked exactly when its owning
    ///   slot is; sorted by span.
    /// - provides: the inferred exits a lowered module exposes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — tails of each polarity in a lowered declaration, and
    ///   one in a declaration an attribute refuses, asserted as the exact list.
    /// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    /// - witness: `lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
    #[spec(ensures: |ret| ret.len() <= self.elided.len() && ret.is_sorted())]
    pub(super) fn inferred_exits(&self) -> Vec<InferredExit>
    {
        let mut found: Vec<InferredExit> = self
            .elided
            .iter()
            .filter(|&&(position, _)| !self.collected.refused(position).0)
            .filter_map(|&(position, exit)| {
                let tail = self.tree.node(position)?;
                let explicitness = match self.collected.owner_of(position) {
                    Maybe::Present(slot) if self.asked.contains(&slot) => Explicitness::Asked,
                    Maybe::Present(_) | Maybe::Absent(_) => Explicitness::Unasked,
                };
                Some(InferredExit {
                    span: tail.span(),
                    exit,
                    explicitness,
                })
            })
            .collect();
        found.sort_unstable();

        found
    }

    /// The operand of the `return` at `position`, when the lowering would
    /// infer that `return` were it left out.
    ///
    /// # Specification
    /// - requires: the classification has read the body `position` stands in
    ///   and the mint sweep has not left it, so its paths are still surveyed.
    /// - ensures: the operand exactly when `position` is a written `return`
    ///   where a path ends, written as no statement and in tail position of
    ///   none, crossing no handler's frame, over an operand bridged bare as a
    ///   value, as is every form a grouping of it holds: a grouped type is
    ///   quoted, and a type bare at a tail takes no exit; and the form held is
    ///   no hole, which a tail would read as a computation's.
    /// - provides: what the mint sweep records of a written exit for
    ///   [`Self::elidable_exits`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ElidableExit`].
    /// - witness: `lower::exits::tests::a_tail_return_of_a_value_is_listed_as_elidable_1327`
    #[spec(ensures: |ret| ret.is_none_or(|operand| self.exits.contains(&position)
        && !self.stated.contains_key(&position)
        && !self.stated_tails.contains(&position)
        && matches!(self.plans.get(position), Some(&super::Plan::Return(written)) if written == operand)))]
    pub(super) fn elidable_at(
        &self,
        position: NodeIndex,
    ) -> Option<NodeIndex>
    {
        let tail = self.exits.contains(&position)
            && !self.inferred.contains(&position)
            && !self.stated.contains_key(&position)
            && !self.stated_tails.contains(&position)
            && !self.crossing.contains(&position);
        let Some(&super::Plan::Return(operand)) = self.plans.get(position)
        else {
            return None;
        };
        if !tail {
            return None;
        }
        let mut held = operand;
        loop {
            if self.bridges.get(usize::from(held)) != Some(&super::Bridge::Bare) {
                return None;
            }
            match self.plans.get(held) {
                Some(&super::Plan::Transparent(inner)) if !self.stand_ins.contains(&held) => {
                    held = inner;
                },
                Some(&super::Plan::ValueHole(_)) => return None,
                _ => return Some(operand),
            }
        }
    }

    /// Every written `return` the lowering would infer, in a declaration that
    /// lowered, in source order.
    ///
    /// # Specification
    /// - requires: the attribute pass and the documentation pass have run, so
    ///   every refusal is offered and every asked slot is marked.
    /// - ensures: one record per `return` the mint sweep found elidable, as
    ///   [`Self::elidable_at`] reads it, under a slot no `explicit_exits` asks
    ///   and holding no refusal; sorted by span.
    /// - provides: the elidable exits a lowered module exposes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ElidableExit`].
    /// - witness: `lower::exits::tests::a_tail_return_of_a_value_is_listed_as_elidable_1327`
    #[spec(ensures: |ret| ret.len() <= self.elidable.len() && ret.is_sorted())]
    pub(super) fn elidable_exits(&self) -> Vec<ElidableExit>
    {
        let mut found: Vec<ElidableExit> = self
            .elidable
            .iter()
            .filter(|&&(position, _)| {
                !self.collected.refused(position).0
                    && !matches!(
                        self.collected.owner_of(position),
                        Maybe::Present(slot) if self.asked.contains(&slot)
                    )
            })
            .filter_map(|&(position, operand)| {
                Some(ElidableExit {
                    span: self.tree.node(position)?.span(),
                    value: self.tree.node(operand)?.span(),
                })
            })
            .collect();
        found.sort_unstable();

        found
    }
}

/// Record, for every copy a rewrite made of an exit, a `break`, a loop or a
/// bind whose rest is distributed, that the copy is one too.
///
/// # Specification
/// - requires: `carried` is what one rewrite reported.
/// - ensures: every computation `carried` maps an exit, a `break` or a loop to
///   is one; every one it maps a distributed bind to is distributed, at the
///   original's origin.
/// - provides: what keeps a match leaf's copy of an arm body commutable.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exit in an arm that binds a field leaves from the
///   leaf's copy of the arm, and a `break` in an arm continues what follows its
///   loop from the leaf's copy.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `lower::loops::tests::a_break_continues_what_follows_its_loop`
#[spec(ensures: carried.iter().all(|pair| match *pair {
    Carried::Computation(held, written) => (!sink.exits.contains(&held) || sink.exits.contains(&written))
        && (!sink.breaks.contains(&held) || sink.breaks.contains(&written))
        && (!sink.loops.contains(&held) || sink.loops.contains(&written))
        && (!sink.distributed.contains_key(&held) || sink.distributed.contains_key(&written)),
    Carried::Value(..) | Carried::ValueType(..) | Carried::CompType(..) => true,
}))]
pub(super) fn mark_copies(
    sink: &mut Sink<'_>,
    carried: &[Carried],
)
{
    for pair in carried {
        if let Carried::Computation(held, written) = *pair {
            for marks in [&mut sink.exits, &mut sink.breaks, &mut sink.loops] {
                if marks.contains(&held) {
                    let _first = marks.insert(written);
                }
            }
            if let Some(&origin) = sink.distributed.get(&held) {
                let _first = sink.distributed.insert(written, origin);
            }
        }
    }
}

/// `body` with every bind whose rest is distributed commuted into its
/// computation.
///
/// # Specification
/// - requires: `body` is the computation of one function's, lambda's or thunk's
///   body, every body nested in it already commuted; `fallback` is the body's
///   owner's origin.
/// - ensures: the body with each distributed bind `x ← M; N`, depth `d` below
///   the root, replaced by `M` with every local end of `M`, `d'` below the
///   root, continuing `N'`, where `N'` is `N`, itself commuted, with every
///   index past its binder raised by `d' - d`: a returner `return v` is
///   replaced by `N'[v/x]`, the beta step of the returner, so no producer the
///   checker cannot synthesise is bound; any other end `e` by `x ← e; N'`. A
///   local end is a node the walk through binds' rests, case branches, a data
///   case's field functions, a split's body, an offer's arms, a fork's parent
///   and a loop's fixpoint reaches that is none of those and no exit; an exit
///   resets the rests it continues to none, so it stays where it stands. An
///   offer's arm and a fork's parent bind no intuitionistic variable, so the
///   rest reaches them at the depth it reaches the form. A loop's fixpoint is
///   walked with no rest of its own, its `break`s continuing the rest its
///   position continues, so a `break` is that rest's local end and every other
///   end in the loop's body stays. The rest is copied once per depth it is
///   carried to. Every rebuilt node takes its original's origin and match
///   record, and a rebuilt loop stays one, every bind of a rest its statement's
///   origin, and every copied node its source's; `body` itself when nothing was
///   distributed in it.
/// - provides: the mint half of early exits: every exit focuses as the cut of
///   its value against the body's own return continuation.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// Each step opens a node of the finite body or a rest, which is settled
/// once, or closes one opened before.
///
/// # Adequacy
/// - hypothesis: L2 — the commuted body of a return two matches deep agrees
///   with the body written with the rest in each arm by hand. L3 — the checker
///   accepts it, its exit is the body's own tail, and every node has an origin;
///   the rest reaches through a split arm, a fork's parent, an offer's arms and
///   a hold's scope.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::exits::tests::a_bound_match_continues_its_block_through_a_split_arm`
/// - witness: `lower::session::tests::an_exit_commutes_through_a_fork_s_parent_and_an_offer_s_arms`
/// - witness: `lower::access::tests::an_exit_inside_an_access_is_refused`
#[spec(ensures: |ret| sink.arena.computation(ret).is_some() || ret == body)]
pub(super) fn commute(
    sink: &mut Sink<'_>,
    body: ComputationId,
    fallback: Origin,
) -> ComputationId
{
    let mut pending: Vec<Pending> = Vec::new();
    let mut settled: Vec<Maybe<ComputationId, settled::Absent>> = Vec::new();
    // economy: a rest is copied once per depth a local end continues it at,
    // so the commuted body grows with the rest times its distinct end depths;
    // a join point would share it, at the cost of a typed binder the core
    // does not have.
    let mut copies: BTreeMap<(RestAt, Binders), ComputationId> = BTreeMap::new();
    let mut carried: Vec<Carried> = Vec::new();
    let mut results: Vec<ComputationId> = Vec::new();
    let outermost = Ends {
        rests: Maybe::Absent(enclosing::Absent::Outermost),
        breaks: Maybe::Absent(enclosing::Absent::Outermost),
    };
    let mut steps = Vec::from([Step::Open(body, outermost, Binders::NONE)]);
    while let Some(step) = steps.pop() {
        match step {
            Step::Open(node, ends, depth) => {
                let ends = if sink.exits.contains(&node) {
                    Ends {
                        rests: Maybe::Absent(enclosing::Absent::Outermost),
                        ..ends
                    }
                }
                else if sink.breaks.contains(&node) {
                    Ends {
                        rests: ends.breaks,
                        ..ends
                    }
                }
                else {
                    ends
                };
                let held = sink.arena.computation(node);
                match held {
                    Some(&Computation::Bind(bound, rest)) => {
                        if let Some(&origin) = sink.distributed.get(&node) {
                            let at = RestAt(pending.len());
                            pending.push(Pending {
                                rest,
                                depth,
                                origin,
                                outer: ends,
                            });
                            settled.push(Maybe::Absent(settled::Absent::Pending));
                            let continued = Ends {
                                rests: Maybe::Present(at),
                                ..ends
                            };
                            steps.push(Step::Open(bound, continued, depth));
                        }
                        else {
                            steps.push(Step::Close(node));
                            steps.push(Step::Open(rest, ends, depth.deeper()));
                        }
                    },
                    Some(&Computation::Fixpoint { body: under, .. })
                        if sink.loops.contains(&node) =>
                    {
                        steps.push(Step::Close(node));
                        let iterated = Ends {
                            rests: Maybe::Absent(enclosing::Absent::Outermost),
                            breaks: ends.rests,
                        };
                        steps.push(Step::Open(under, iterated, depth.deeper()));
                    },
                    // A `for` loop is its fixpoint applied to the list: the
                    // application stands where the loop does, so its ends
                    // are the loop's.
                    Some(&Computation::Application(head, _)) if sink.loops.contains(&head) => {
                        steps.push(Step::Close(node));
                        steps.push(Step::Open(head, ends, depth));
                    },
                    Some(&Computation::Case { ref branches, .. }) => {
                        steps.push(Step::Close(node));
                        for &branch in branches.iter().rev() {
                            steps.push(Step::Open(branch, ends, depth.deeper()));
                        }
                    },
                    Some(&Computation::ListCase {
                        on_nil, on_cons, ..
                    }) => {
                        steps.push(Step::Close(node));
                        steps.push(Step::Open(on_cons, ends, depth.deeper().deeper()));
                        steps.push(Step::Open(on_nil, ends, depth));
                    },
                    Some(&Computation::DataCase { ref branches, .. }) => {
                        steps.push(Step::Close(node));
                        for &branch in branches.iter().rev() {
                            steps.push(Step::Open(branch, ends, depth));
                        }
                    },
                    Some(&Computation::Split {
                        arity, body: under, ..
                    }) => {
                        steps.push(Step::Close(node));
                        steps.push(Step::Open(under, ends, depth.deeper_by(arity)));
                    },
                    Some(&Computation::Lambda(under)) => {
                        steps.push(Step::Close(node));
                        steps.push(Step::Open(under, ends, depth.deeper()));
                    },
                    Some(&Computation::Session(SessionAction::Offer { ref arms, .. })) => {
                        steps.push(Step::Close(node));
                        for &arm in arms.values().rev() {
                            steps.push(Step::Open(arm, ends, depth));
                        }
                    },
                    // A fork's parent, a receive's body and a hold's scope are
                    // the tail, under a linear binder, so no intuitionistic one
                    // deeper.
                    Some(
                        &Computation::Session(
                            SessionAction::Fork { parent: scope, .. }
                            | SessionAction::Receive { body: scope, .. },
                        )
                        | &Computation::Memory(MemoryForm::Hold { body: scope, .. }),
                    ) => {
                        steps.push(Step::Close(node));
                        steps.push(Step::Open(scope, ends, depth));
                    },
                    // A `leta`'s body is its tail, one binder deeper; a
                    // migration's body is not, for what follows a migration
                    // runs back at the world it left.
                    Some(&Computation::World(WorldForm::Leta { body: scope, .. })) => {
                        steps.push(Step::Close(node));
                        steps.push(Step::Open(scope, ends, depth.deeper()));
                    },
                    _ => match ends.rests {
                        Maybe::Absent(_) => results.push(node),
                        Maybe::Present(at) => match settled.get(at.0) {
                            Some(&Maybe::Present(rest)) => {
                                let Some(&continued) = pending.get(at.0)
                                else {
                                    results.push(node);
                                    continue;
                                };
                                results.push(continue_end(
                                    sink,
                                    (node, depth),
                                    (at, rest, continued),
                                    &mut copies,
                                    &mut carried,
                                ));
                            },
                            Some(&Maybe::Absent(_)) | None => {
                                let Some(&continued) = pending.get(at.0)
                                else {
                                    results.push(node);
                                    continue;
                                };
                                steps.push(Step::Continue(node, at, depth));
                                steps.push(Step::Settle(at));
                                steps.push(Step::Open(
                                    continued.rest,
                                    continued.outer,
                                    continued.depth.deeper(),
                                ));
                            },
                        },
                    },
                }
            },
            Step::Close(node) => {
                let rebuilt = rebuild(sink, node, &mut results, fallback);
                results.push(rebuilt);
            },
            Step::Settle(at) => {
                if let Some(commuted) = results.pop()
                    && let Some(slot) = settled.get_mut(at.0)
                {
                    *slot = Maybe::Present(commuted);
                }
            },
            Step::Continue(node, at, depth) => {
                let (Some(&Maybe::Present(rest)), Some(&continued)) =
                    (settled.get(at.0), pending.get(at.0))
                else {
                    results.push(node);
                    continue;
                };
                results.push(continue_end(
                    sink,
                    (node, depth),
                    (at, rest, continued),
                    &mut copies,
                    &mut carried,
                ));
            },
        }
    }

    results.pop().unwrap_or(body)
}

/// Continue the local end `end`, `depth` below the body's root, with the
/// commuted rest `rest` of the statement `continued`, carried down to it.
///
/// # Specification
/// - requires: `rest` is the commuted rest of `continued`, held at `at`, and
///   `depth` is at least the statement's.
/// - ensures: with `rest'` the rest with every index past its binder raised by
///   the depth between the statement and the end, one copy per depth kept in
///   `copies`: `rest'` instantiated at `v` for an end `return v`, its nodes at
///   their sources' origins and each written use of the binder labelled with
///   what replaced it; `x ← end; rest'` at the statement's origin for any other
///   end.
/// - provides: the continuation half of [`commute`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`commute`]; a use the instantiation replaces answers
///   at its bytes.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
/// - witness: `lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
#[spec(captures: returned = matches!(sink.arena.computation(end.0), Some(&Computation::Return(_))),
    ensures: |ret| returned || matches!(sink.arena.computation(ret), Some(&Computation::Bind(bound, _)) if bound == end.0))]
fn continue_end(
    sink: &mut Sink<'_>,
    end: (ComputationId, Binders),
    continued: (RestAt, ComputationId, Pending),
    copies: &mut BTreeMap<(RestAt, Binders), ComputationId>,
    carried: &mut Vec<Carried>,
) -> ComputationId
{
    let (node, depth) = end;
    let (at, rest, statement) = continued;
    // reason: a binder count uses u32::MAX as its conservative ceiling, and an
    // end stands at least as deep as its statement.
    let amount = Binders::from(u32::from(depth).saturating_sub(u32::from(statement.depth)));
    let copy = if let Some(&copy) = copies.get(&(at, amount)) {
        copy
    }
    else {
        let copy = carry(sink, rest, amount, statement.origin, carried);
        let _first = copies.insert((at, amount), copy);
        copy
    };
    if let Some(&Computation::Return(value)) = sink.arena.computation(node) {
        let mark = sink.arena.watermark();
        carried.clear();
        let instantiated =
            gandr_core_term::instantiate_computation_traced(sink.arena, copy, value, carried);
        record_copies(sink, mark, carried, statement.origin);
        return instantiated;
    }
    let bound = sink.arena.computation_bind(node, copy);
    sink.origins.record_computation(bound, statement.origin);

    bound
}

/// Label each written variable a rewrite replaced with the value that stands
/// for it now, when that value answers at other bytes, and carry every label
/// naming a replaced variable or session action over to its replacement; keep
/// each written value type a rewrite replaced as a stand-in for its
/// replacement.
///
/// # Specification
/// - requires: every node `carried` reports has its origin recorded.
/// - ensures: one label per variable `carried` reports replaced whose origin is
///   written and whose replacement's origin spans other bytes, naming the
///   replacement; a label that named a replaced variable, or the endpoint of a
///   replaced session action, names its replacement; one stand-in per value
///   type `carried` reports replaced whose origin is written and whose
///   replacement's origin spans other bytes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a use of a bound match's binder, instantiated at the
///   value an arm passes, answers at that value's type, through a chain of such
///   instantiations too; a scrutinee a leaf's copy replaces answers at its
///   bytes; a functor's parameter type, renamed to an argument's, answers where
///   the template writes it; an endpoint written in an offer the lowering
///   rebuilds answers at the rebuilt offer.
/// - witness: `lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
/// - witness: `lower::tests::a_type_head_answers_at_what_it_stands_for`
/// - witness: `lower::session::tests::each_endpoint_answers_at_its_action`
/// - witness: `lower::exits::tests::a_variable_answering_at_its_own_bytes_gains_no_label`
/// - witness: `lower::exits::tests::a_renamed_parameter_type_stands_in_only_at_other_bytes`
#[spec(captures: before = sink.origins.labels().len(), ensures: sink.origins.labels().len() >= before)]
pub(super) fn label_replaced(
    sink: &mut Sink<'_>,
    carried: &[Carried],
)
{
    for pair in carried {
        match *pair {
            Carried::Value(replaced, standing) => {
                if !matches!(sink.arena.value(replaced), Some(&Value::Variable { .. })) {
                    continue;
                }
                sink.origins
                    .relabel(&Labelled::Value(replaced), &Labelled::Value(standing));
                let (Maybe::Present(written), Maybe::Present(now)) =
                    (sink.origins.value(replaced), sink.origins.value(standing))
                else {
                    continue;
                };
                if written.provenance() == Provenance::Written && now.span() != written.span() {
                    sink.origins.record_label(Label {
                        span: written.span(),
                        labelled: Labelled::Value(standing),
                    });
                }
            },
            Carried::ValueType(replaced, standing) => {
                let (Maybe::Present(written), Maybe::Present(now)) = (
                    sink.origins.value_type(replaced),
                    sink.origins.value_type(standing),
                )
                else {
                    continue;
                };
                if written.provenance() == Provenance::Written && now.span() != written.span() {
                    sink.origins.record_stand_in(standing, written);
                }
            },
            Carried::Computation(replaced, standing) => {
                if matches!(
                    sink.arena.computation(replaced),
                    Some(&Computation::Session(_))
                ) {
                    sink.origins.relabel_action(replaced, standing);
                }
            },
            Carried::CompType(..) => {},
        }
    }
}

/// `rest`, under one binder, with every index past that binder raised by
/// `amount`, every node it mints recorded at its source's origin.
///
/// # Specification
/// - requires: every node of `rest` has an origin, or `fallback` stands for it.
/// - ensures: the shifted rest; `rest` itself, minting nothing, when `amount`
///   is none; every node minted carries the origin and the match record of the
///   node it was rewritten from, or `fallback`.
/// - provides: the copy half of [`commute`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a rest carried under a match's field binder reads the
///   function's parameter past it, and keeps its origins.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
#[spec(ensures: |ret| amount != Binders::NONE || ret == rest)]
fn carry(
    sink: &mut Sink<'_>,
    rest: ComputationId,
    amount: Binders,
    fallback: Origin,
    carried: &mut Vec<Carried>,
) -> ComputationId
{
    let mark = sink.arena.watermark();
    carried.clear();
    let copy = gandr_core_term::shift_computation_under(sink.arena, rest, Binders::ONE, amount)
        .settle_traced(sink.arena, carried);
    record_copies(sink, mark, carried, fallback);

    copy
}

/// Record the origin of every node minted since `mark`, each its source's in
/// `carried`.
///
/// # Specification
/// - requires: nothing has been recorded for a node minted since `mark`, and
///   `carried` reports the rewrite that minted them.
/// - ensures: every node minted since `mark` carries the origin of the first
///   node `carried` reports it rewritten from, or `fallback`; every computation
///   rewritten from a match's root carries the match's record; each written
///   variable the rewrite replaced is labelled as [`label_replaced`] labels it.
/// - provides: the origin half of [`carry`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`carry`].
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
#[spec(ensures: sink.arena.computations_since(mark).all(|id| matches!(sink.origins.computation(id), Maybe::Present(_)))
    && sink.arena.values_since(mark).all(|id| matches!(sink.origins.value(id), Maybe::Present(_))))]
pub(super) fn record_copies(
    sink: &mut Sink<'_>,
    mark: ArenaWatermark,
    carried: &[Carried],
    fallback: Origin,
)
{
    let sources = Sources::of(carried);
    for id in sink.arena.values_since(mark) {
        let origin = sources.value(sink, id, fallback);
        sink.origins.record_value(id, origin);
    }
    for id in sink.arena.computations_since(mark) {
        let origin = sources.computation(sink, id, fallback);
        sink.origins.record_computation(id, origin);
        sources.keep_case(sink, id);
    }
    for id in sink.arena.value_types_since(mark) {
        let origin = sources.value_type(sink, id, fallback);
        sink.origins.record_value_type(id, origin);
    }
    for id in sink.arena.comp_types_since(mark) {
        let origin = sources.comp_type(sink, id, fallback);
        sink.origins.record_comp_type(id, origin);
    }
    label_replaced(sink, carried);
}

/// The node each copy one rewrite reported was made from, family by family:
/// the first it reports for that copy.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each map sends a copy to the node `carried` first reports it
///   rewritten from.
/// - executable: none — the record holds no arena to check either id against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`record_copies`].
/// - witness: `lower::tests::every_minted_node_has_an_origin`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Sources
{
    /// The value each value copy was made from.
    values: BTreeMap<ValueId, ValueId>,
    /// The computation each computation copy was made from.
    computations: BTreeMap<ComputationId, ComputationId>,
    /// The value type each value type copy was made from.
    value_types: BTreeMap<ValueTypeId, ValueTypeId>,
    /// The computation type each computation type copy was made from.
    comp_types: BTreeMap<CompTypeId, CompTypeId>,
}

impl Sources
{
    /// The sources `carried` reports, each copy's first.
    ///
    /// # Specification
    /// - requires: `carried` is what rewrites reported.
    /// - ensures: a computation copy maps to the first computation `carried`
    ///   pairs it with; every other family alike.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`record_copies`].
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(ensures: |ret| carried.iter().all(|pair| match *pair {
        Carried::Computation(_, written) => ret.computations.contains_key(&written),
        Carried::Value(_, written) => ret.values.contains_key(&written),
        Carried::ValueType(_, written) => ret.value_types.contains_key(&written),
        Carried::CompType(_, written) => ret.comp_types.contains_key(&written),
    }))]
    pub(super) fn of(carried: &[Carried]) -> Self
    {
        let mut sources = Self::default();
        for pair in carried {
            match *pair {
                Carried::Value(held, written) => {
                    let _first = sources.values.entry(written).or_insert(held);
                },
                Carried::Computation(held, written) => {
                    let _first = sources.computations.entry(written).or_insert(held);
                },
                Carried::ValueType(held, written) => {
                    let _first = sources.value_types.entry(written).or_insert(held);
                },
                Carried::CompType(held, written) => {
                    let _first = sources.comp_types.entry(written).or_insert(held);
                },
            }
        }
        sources
    }

    /// The origin of value `id`: its source's, or `fallback`.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn value(
        &self,
        sink: &Sink<'_>,
        id: ValueId,
        fallback: Origin,
    ) -> Origin
    {
        match self.values.get(&id) {
            Some(&held) => found_or(sink.origins.value(held), fallback),
            None => fallback,
        }
    }

    /// The origin of computation `id`: its source's, or `fallback`.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn computation(
        &self,
        sink: &Sink<'_>,
        id: ComputationId,
        fallback: Origin,
    ) -> Origin
    {
        match self.computations.get(&id) {
            Some(&held) => found_or(sink.origins.computation(held), fallback),
            None => fallback,
        }
    }

    /// The origin of value type `id`: its source's, or `fallback`.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn value_type(
        &self,
        sink: &Sink<'_>,
        id: ValueTypeId,
        fallback: Origin,
    ) -> Origin
    {
        match self.value_types.get(&id) {
            Some(&held) => found_or(sink.origins.value_type(held), fallback),
            None => fallback,
        }
    }

    /// The origin of computation type `id`: its source's, or `fallback`.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn comp_type(
        &self,
        sink: &Sink<'_>,
        id: CompTypeId,
        fallback: Origin,
    ) -> Origin
    {
        match self.comp_types.get(&id) {
            Some(&held) => found_or(sink.origins.comp_type(held), fallback),
            None => fallback,
        }
    }

    /// Record for computation `id` the match record of the computation it was
    /// copied from, when that one roots a match, and the family it eliminates,
    /// when it is a data case.
    ///
    /// # Specification
    /// - requires: `id` has no match record yet.
    /// - ensures: a copy of a match's root carries that match's record; where
    ///   the source eliminates the value its record names and the copy
    ///   eliminates a value of its own, the copy's record names the copy's, so
    ///   the patterns answer where the run judged the copy (#298); a copy of a
    ///   data case eliminates the source's family.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match carried under a binder keeps its patterns, a
    ///   match bound by a `run` whose block continues its local ends answers
    ///   its patterns at the copy's scrutinee, and a match written in an arm
    ///   that binds a field names its own arms in the leaf's copy.
    /// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
    /// - witness: `lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
    /// - witness: `lower::native::tests::a_data_case_names_the_family_it_eliminates_809`
    #[spec(ensures: self.computations.get(&id).is_none_or(|&held|
        (matches!(sink.origins.case(held), Maybe::Absent(_)) || matches!(sink.origins.case(id), Maybe::Present(_)))
        && (matches!(sink.origins.elimination(held), Maybe::Absent(_)) || matches!(sink.origins.elimination(id), Maybe::Present(_)))))]
    pub(super) fn keep_case(
        &self,
        sink: &mut Sink<'_>,
        id: ComputationId,
    )
    {
        let Some(&held) = self.computations.get(&id)
        else {
            return;
        };
        if let Maybe::Present(family) = sink.origins.elimination(held) {
            sink.origins.record_elimination(id, family);
        }
        if let Maybe::Present(case) = sink.origins.case(held) {
            let mut kept = case.clone();
            if let (Some(source), Some(copy)) = (
                eliminated(sink.arena.computation(held)),
                eliminated(sink.arena.computation(id)),
            ) && kept.scrutinised == Maybe::Present(source)
            {
                kept.scrutinised = Maybe::Present(copy);
            }
            sink.origins.record_case(id, kept);
        }
    }
}

/// The value a case, a data case or a list case eliminates; nothing for any
/// other node.
///
/// # Specification
/// trivial.
fn eliminated(node: Option<&Computation>) -> Option<ValueId>
{
    match node {
        Some(
            &(Computation::Case { scrutinee, .. }
            | Computation::DataCase { scrutinee, .. }
            | Computation::ListCase {
                list: scrutinee, ..
            }),
        ) => Some(scrutinee),
        Some(_) | None => None,
    }
}

/// Rebuild `node` over its children's commuted forms, the last of `results`.
///
/// # Specification
/// - requires: `node` is a bind, a case, a data case, a split, a lambda, an
///   offer, a fork, a hold or a loop's fixpoint whose every commuted child — a
///   fork's parent alone, a hold's scope alone — stands on top of `results`, in
///   order.
/// - ensures: those results popped; `node` itself when each is the child it
///   stands for; else a node of the same former over them, recorded at `node`'s
///   origin, or `fallback`, and its match record, a loop's fixpoint keeping its
///   evidence and staying a loop.
/// - provides: the close half of [`commute`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`commute`], each former rebuilt over children that
///   changed.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `lower::access::tests::an_exit_inside_an_access_is_refused`
/// - witness: `lower::session::tests::an_exit_commutes_through_a_fork_s_parent_and_an_offer_s_arms`
#[spec(ensures: |ret| ret == node || sink.arena.computation(ret).is_some())]
fn rebuild(
    sink: &mut Sink<'_>,
    node: ComputationId,
    results: &mut Vec<ComputationId>,
    fallback: Origin,
) -> ComputationId
{
    let Some(held) = sink.arena.computation(node).cloned()
    else {
        return node;
    };
    let count = match held {
        Computation::Case { ref branches, .. } => branches.len(),
        Computation::DataCase { ref branches, .. } => branches.len(),
        Computation::Session(SessionAction::Offer { ref arms, .. }) => arms.len(),
        Computation::ListCase { .. } => 2_usize,
        Computation::Bind(..)
        | Computation::Split { .. }
        | Computation::Lambda(_)
        | Computation::Session(SessionAction::Fork { .. } | SessionAction::Receive { .. })
        | Computation::Memory(MemoryForm::Hold { .. })
        | Computation::World(WorldForm::Leta { .. }) => 1_usize,
        Computation::Fixpoint { .. } if sink.loops.contains(&node) => 1_usize,
        Computation::Application(head, _) if sink.loops.contains(&head) => 1_usize,
        Computation::Primitive { .. }
        | Computation::Transport(..)
        | Computation::PathTransport { .. }
        | Computation::Ride { .. }
        | Computation::TelescopeTransport { .. }
        | Computation::Fixpoint { .. }
        | Computation::Application(..)
        | Computation::Return(_)
        | Computation::Ascribe { .. }
        | Computation::Force(_)
        | Computation::RecordProjection(..)
        | Computation::TupleProjection(..)
        | Computation::Hole(_)
        | Computation::Mark { .. }
        | Computation::ListFold { .. }
        | Computation::Perform { .. }
        | Computation::Handle { .. }
        | Computation::Exercise { .. }
        | Computation::Scope { .. }
        | Computation::Resume(..)
        | Computation::Abandon(_)
        | Computation::Reset(_)
        | Computation::Shift(_)
        | Computation::With(..)
        | Computation::Project(..)
        | Computation::Session(_)
        | Computation::Memory(_)
        | Computation::World(_) => 0_usize,
    };
    let commuted = results.split_off(results.len().saturating_sub(count));
    let rebuilt = match (held, commuted.as_slice()) {
        (Computation::Bind(bound, rest), &[commuted]) if commuted != rest => {
            sink.arena.computation_bind(bound, commuted)
        },
        (Computation::Lambda(under), &[commuted]) if commuted != under => {
            sink.arena.computation_lambda(commuted)
        },
        (
            Computation::Split {
                scrutinee,
                arity,
                motive,
                body,
            },
            &[commuted],
        ) if commuted != body => match motive {
            SplitMotive::Ambient => sink.arena.computation_split(scrutinee, arity, commuted),
            SplitMotive::Scrutinee(motive) => sink
                .arena
                .computation_dependent_split(scrutinee, arity, motive, commuted),
        },
        (
            Computation::Case {
                scrutinee,
                ref branches,
            },
            branched,
        ) if **branches != *branched => sink.arena.computation_case(scrutinee, branched),
        (
            Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
                ref arities,
                equations,
            },
            branched,
        ) if branches.as_slice() != branched => sink.arena.computation_data_case_with_equations(
            scrutinee,
            motive,
            (branched.to_vec(), arities.clone()),
            equations,
        ),
        (
            Computation::ListCase {
                list,
                on_nil,
                on_cons,
            },
            &[nil, cons],
        ) if (nil, cons) != (on_nil, on_cons) => sink.arena.computation_list_case(list, nil, cons),
        (Computation::Session(SessionAction::Offer { endpoint, ref arms }), branched)
            if !arms.values().copied().eq(branched.iter().copied()) =>
        {
            let arms = arms.keys().cloned().zip(branched.iter().copied()).collect();
            sink.arena
                .computation_session(SessionAction::Offer { endpoint, arms })
        },
        (
            Computation::Session(SessionAction::Fork {
                protocol,
                child,
                parent,
            }),
            &[commuted],
        ) if commuted != parent => sink.arena.computation_session(SessionAction::Fork {
            protocol,
            child,
            parent: commuted,
        }),
        (Computation::Session(SessionAction::Receive { endpoint, body }), &[commuted])
            if commuted != body =>
        {
            sink.arena.computation_session(SessionAction::Receive {
                endpoint,
                body: commuted,
            })
        },
        (Computation::Memory(MemoryForm::Hold { value, body, grade }), &[commuted])
            if commuted != body =>
        {
            sink.arena.computation_memory(MemoryForm::Hold {
                value,
                body: commuted,
                grade,
            })
        },
        (Computation::World(WorldForm::Leta { value, body }), &[commuted]) if commuted != body => {
            sink.arena.computation_world(WorldForm::Leta {
                value,
                body: commuted,
            })
        },
        (Computation::Fixpoint { body, evidence }, &[commuted]) if commuted != body => {
            let looped = sink.arena.computation_fixpoint(commuted, evidence);
            let _first = sink.loops.insert(looped);
            looped
        },
        (Computation::Application(head, argument), &[commuted]) if commuted != head => {
            sink.arena.computation_application(commuted, argument)
        },
        _ => return node,
    };
    let origin = found_or(sink.origins.computation(node), fallback);
    sink.origins.record_computation(rebuilt, origin);
    if let Maybe::Present(case) = sink.origins.case(node) {
        let kept = case.clone();
        sink.origins.record_case(rebuilt, kept);
    }
    if let Maybe::Present(family) = sink.origins.elimination(node) {
        sink.origins.record_elimination(rebuilt, family);
    }

    rebuilt
}

/// The origin `found` holds, or `fallback`.
///
/// # Specification
/// trivial.
const fn found_or<Reason>(
    found: Maybe<Origin, Reason>,
    fallback: Origin,
) -> Origin
where
    Reason: Copy,
{
    match found {
        Maybe::Present(origin) => origin,
        Maybe::Absent(_) => fallback,
    }
}
