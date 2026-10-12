//! Native data in the lowering: a data family where a type is read, a
//! constructor applied to its fields, a data declaration's signature, and a
//! match compiled to native eliminations.
//!
//! # A constructor carries its whole classifier
//!
//! The core's constructor value names the nominal type it builds, arguments
//! and all, so the lowering has to know them where the constructor is
//! written. A family without parameters has one classifier, which the
//! lowering inserts; a family with parameters takes it from an annotation,
//! `(C(…) : T(…))`, and is refused as unannotated without one. Inferring the
//! arguments from the fields or the position is the checker's work, which
//! the lowering does not duplicate; reversal: a checker that synthesises a
//! constructor against an expected type makes the annotation optional.
//!
//! # A match is a decision tree of eliminations
//!
//! The core has no match: it eliminates native data by a data case with a
//! motive, a sum by a case, and compares integers by a primitive. A match
//! compiles to a tree of those over the scrutinee value itself, never bound,
//! by the column-wise pattern-matrix construction (Maranget, *Compiling
//! Pattern Matching to Good Decision Trees*, ML 2008): the leftmost column
//! the first row tests is switched on, each constructor's branch binds its
//! fields with ordinary lambdas, and the rows that survive it are
//! specialised. A leaf runs its arm, a hole the first surviving row holds
//! leaves the tree stuck on that hole, and a matrix no row survives is a
//! non-exhaustive match, refused where it is written.
//!
//! An arm body reached from several leaves is copied, not joined: every arm
//! body is read under the case's frame and its own variables alone, and each
//! leaf substitutes the body's variables by the tree binders that settled
//! them and its frame by the case's context shifted under the leaf's depth.
//! No thunk of unknown type is bound and no binder is padded, so nothing the
//! checker cannot type is introduced; reversal: a join point becomes worth
//! its thunk once an arm body's duplication costs more than the binding of
//! its type, which needs the answer type at every join.
//!
//! A match with no arms, `case e {}`, is declined by the view's name, under
//! which the grammar reserves it: no pattern names the family it would
//! eliminate. Reversal: a scrutinee whose type the lowering reads, an
//! annotation or a parameter's written type, names it.
//!
//! # The motive is the answer the source states
//!
//! A data case checks against a motive under one scrutinee binder. The
//! lowering reads it from the match's own answer, `case e -> T { … }`, or
//! from the result type of the function whose body ends in the match,
//! relocated into the match's context; a match with neither is refused as
//! unannotated when its tree eliminates native data. Reversal: a checker that
//! takes the motive from the checking direction makes the answer optional.
//!
//! # The patterns are kept beside the tree
//!
//! The tree does not keep the patterns, so the origin table does: per match,
//! the core pattern table its arms are written in, one record per arm
//! alternative, and the syntax nodes of the scrutinee and every pattern and
//! body. A pattern hole's identity is its syntax node's position, the
//! identity a term hole takes, so a live match reads one seam.
//!
//! # A recursive function is one fixpoint over its last parameter
//!
//! The core's fixpoint `fix x. M` binds its own thunk, and the structural
//! descent it may claim replays only over `fix x. λy. case y [C] of { c_i ↦
//! λf̄_i. N_i }`: a fixpoint at a function out of nominal data whose body
//! cases on the argument it takes, every self call `(force x) a` at a field
//! of the scrutinised constructor (Giménez, *Structural Recursive Definitions
//! in Type Theory*, ICALP 1998). `def rec f(p₁, …, pₖ, y) -> C { b }`
//! therefore lowers to `thunk (λp₁ … λpₖ. fix f. λy. b)`, and a call
//! `f[<](p₁, …, pₖ, a)` to `(force f) a`. The parameters before the last are
//! the uniform parameters of an inductive definition (Coquand and Paulin,
//! *Inductively defined types*, COLOG 1988): bound outside the fixpoint, so
//! every recursive call must pass them as themselves, and a call passing
//! anything else is refused as non-uniform. The last parameter is the one
//! the fixpoint recurses on, and whether `a` is one of its fields is the
//! replay's to judge, which a call at anything else fails as
//! `DescentNotReplayed`; the lowering neither searches for a decreasing
//! argument nor duplicates the check.
//!
//! `<` is the claim. A fixpoint carries structural-descent evidence when one
//! of its calls writes it and partial evidence when none does, so the checker
//! and the kernel replay every claim the source makes and none it does not.
//! The function's own name is bound by one more frame, between the last
//! parameter and the ones before it, typed by the declaration form so no
//! signature telescope counts it — the binder exists in the body alone — and
//! it resolves only as the head of a claim: written bare it is refused with
//! the claim's spelling, `f[<](…)`. Every other resident of an
//! instantiation, `>` for productivity among them, is declined as the
//! grammar's reserved form until its termination rung lands.
//!
//! Alternative: the recursive argument first and every later parameter
//! pushed into the case's motive and re-bound under each branch's fields, as
//! an eliminator's methods take them (`McBride`, *Elimination with a Motive*,
//! TYPES 2000), which admits a recursive call that varies them, an
//! accumulator, at the cost of re-indexing every branch. Reversal: a
//! recursive definition that must vary an earlier parameter.
//!
//! A mutual block, `rec { def …; def … }`, is declined: the grammar parses
//! it as one item whose members are inline tiles of the block, so the module
//! reads no declaration in it and refuses the whole source at the block's
//! form. Reversal: one fixpoint over a bundle of the members' thunks, each
//! member its projection, with partial evidence until a descent judgment
//! spans the bundle; this needs the members collected as declarations from
//! inside one form, and is its own unit.

use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::TermId;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::Operator;
use gandr_core_term::primitive::PRELUDE;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::FormName;
use super::Former;
use super::Function;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Sink;
use super::Site;
use super::Stretch;
use super::closed;
use super::exhausted;
use super::lowered;
use super::parse_literal;
use super::recursion;
use super::stretch;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::module::Constructor;
use crate::module::DataIndex;
use crate::module::Half;
use crate::module::Operand;
use crate::origin::ArmOrigin;
use crate::origin::CaseOrigin;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;

#[cfg(test)]
mod tests;

quenchant_shape::reason_enum! {
    /// Why a constructor carries no written classifier.
    pub mod classified {
        /// The constructor stands under no annotation.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Its family has no parameters, so the lowering inserts the one
            /// classifier it has.
            Inserted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a match states no answer.
    pub mod answered {
        /// Neither the match nor its position states one.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `-> T` follows the scrutinee and no function result reaches
            /// the match.
            Unstated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node names no constructor.
    pub mod constructed {
        /// No data family declared strictly earlier has a constructor so named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The name is no constructor's, or its family is not yet declared.
            Unnamed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a name is no data family.
    pub mod family {
        /// The declaration at the constant is not a data declaration.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration writes a value, a function or nothing.
            Undeclared,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why the nodes minted since a mark carry no written root.
    pub mod rooted {
        /// No node among them is the written form's own.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The tree did not lower, so what was minted toward it is all
            /// inserted.
            Unminted,
            /// The match is its first arm's body, minted before and adopted.
            Adopted,
            /// The nodes carry a classifier the lowering inserted.
            Classifier,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a row is not stuck.
    pub mod stuck {
        /// The row has matched through no hole.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Its own written patterns decide whether it matches.
            Decided,
        }
    }
}

/// How many tree binders stand above a node of a match's decision tree; as a
/// variable's index, how many binders stand between the variable and its
/// binder.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Depth(usize);

/// A value a match's decision tree scrutinises: level zero is the scrutinee
/// itself, and the binder a node under `depth` tree binders introduces for
/// its field `field` is level `depth + field + 1`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct TreeLevel(usize);

/// A column of a pattern matrix.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Column(usize);

/// A node of a decision tree, by its position in the tree's node list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct TestAt(usize);

/// A pattern, by its position in one match's pattern store.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct PatternAt(usize);

/// An arm of a match, by its position in source order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ArmAt(usize);

/// A data declaration, by its position in the collection's data list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct FormAt(usize);

/// An arm variable, numbered in source order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct VariableAt(usize);

/// A match, by its position in the lowering's match store.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct CaseIndex(usize);

/// Whether a recursive call claims descent.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Claimed(pub bool);

/// A recursive function's own name, which the frame of its fixpoint binds.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: the parameters every recursive call passes unchanged and whether
///   a call claims descent stay together under the frame binding the name.
/// - provides: what a descent claim checks its call against, and the evidence
///   the fixpoint carries.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the scope and the parameter store are not retained;
///   `function`, `instantiation` and `mint_function` interpret the record.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive function over one parameter and over a
///   uniform leading parameter each close their fixpoint over the last
///   parameter, with descent evidence exactly when a call claims it.
/// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_last_parameter`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Recursion
{
    /// The parameters before the last, in the lowerer's parameter store: the
    /// ones every recursive call passes unchanged.
    pub uniform: Stretch,
    /// Whether a call claims descent, which makes the fixpoint's evidence
    /// structural rather than partial.
    pub claimed: Claimed,
}

/// A recursive call as its call form read it: what its head's claim checks.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: the call form and every argument it wrote, the leading ones
///   included, which the call itself neither reads nor applies.
/// - provides: the arguments a descent claim checks for uniformity and arity.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the operand store is not retained; `instantiation`
///   reads it.
///
/// # Adequacy
/// - hypothesis: L3 — a call passing a leading parameter as itself, as
///   something else and with the wrong argument count each meet their own
///   outcome at the claim.
/// - witness: `lower::native::tests::a_recursive_call_passes_its_leading_parameters_unchanged`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Descent
{
    /// The call form.
    pub call: Site,
    /// Every argument the call wrote, in the lowerer's operand store.
    pub arguments: Stretch,
}

/// The column entry no written pattern fills: it matches anything and binds
/// nothing, as a field a catch-all row was specialised over.
///
/// # Specification
/// trivial.
const UNWRITTEN: PatternAt = PatternAt(usize::MAX);

/// The computation type a position answers, as a function's result or a
/// match's answer states it, with the frame it was read under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the node is read where a result is read, under `frame`.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — an answer written on the match and one taken from the
///   function result each become the motive of the same tree.
/// - witness: `lower::native::tests::a_match_takes_its_answer_from_the_function_result`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Answer
{
    /// The type's syntax node.
    pub node: NodeIndex,
    /// The frame the type was read under.
    pub frame: Frame,
}

/// A constructor applied to its fields, as the classification planned it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the fields are a stretch of the operand store, as many as the
///   constructor takes.
/// - executable: none — the plan holds no store to check its stretch against.
///
/// # Adequacy
/// - hypothesis: L3 — nullary and three-field constructors, annotated and not,
///   lower to the constructor value over their fields.
/// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Constructed
{
    /// The family's admission position.
    pub family: ConstantIndex,
    /// The constructor's tag.
    pub tag: ConstructorTag,
    /// The fields, in the operand store.
    pub fields: Stretch,
    /// The annotation's type, when the source wrote one.
    pub classifier: Maybe<NodeIndex, classified::Absent>,
}

/// One pattern, as the match compiler reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a constructor's fields are a stretch of the match's part store; a
///   binder numbers its arm variable.
/// - executable: none — the pattern holds no store to check its stretch
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses compile every shape into the tree they
///   assert.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Matcher
{
    /// `_`: matches anything, binds nothing.
    Wild,
    /// A name: matches anything and binds the arm variable numbered here.
    Binder(VariableAt),
    /// `?`: a pattern the author has not written.
    Hole(HoleId),
    /// A constructor of the data declaration at `form`, with its fields.
    Constructor
    {
        /// The family's position in the collection's data list.
        form: FormAt,
        /// The constructor's tag.
        tag: usize,
        /// The field patterns, in the part store.
        fields: Stretch,
    },
    /// `true` or `false`.
    Boolean(bool),
    /// An integer literal.
    Integer(Literal),
}

/// One row of a pattern matrix.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one pattern per column of its matrix; every binding names a tree
///   level its variable was settled at.
/// - executable: none — the row holds no matrix to check its width against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Matcher`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, PartialEq)]
struct Row
{
    /// The patterns still to test, one per column.
    columns: Vec<PatternAt>,
    /// The arm the row runs.
    arm: ArmAt,
    /// Each arm variable settled so far, with the level that settled it.
    bindings: Vec<(VariableAt, TreeLevel)>,
    /// The first hole the row matched through, which decides whether it
    /// matches.
    stuck: Maybe<HoleId, stuck::Absent>,
}

/// One node of a match's decision tree.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a child's position is after its parent's, so minting the tree in
///   descending position order mints every child first; level zero is the
///   scrutinee itself, and the binder a node introduces under `depth` tree
///   binders is level `depth + 1`.
/// - executable: none — the node holds no tree to check its children against.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses read each kind of node back out of the
///   arena.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
/// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
#[derive(Clone, Debug, Eq, PartialEq)]
enum Test
{
    /// A node the compiler has not reached yet.
    Pending,
    /// Run arm `arm`, reached under `depth` tree binders, its variables
    /// settled at these levels, in variable order.
    Leaf
    {
        /// The arm.
        arm: ArmAt,
        /// The tree binders above the leaf.
        depth: Depth,
        /// The level that settled each arm variable.
        bindings: Vec<TreeLevel>,
    },
    /// The hole that decides whether the first surviving row matches.
    Stuck(HoleId),
    /// Switch on the native data value at `level`: one child per
    /// constructor, with the constructor's arity.
    Data
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the switch.
        depth: Depth,
        /// Each constructor's arity and child.
        branches: Vec<(usize, TestAt)>,
    },
    /// Switch on the boolean at `level`: true on the left.
    Boolean
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the switch.
        depth: Depth,
        /// The child for `true`.
        yes: TestAt,
        /// The child for `false`.
        no: TestAt,
    },
    /// Compare the integer at `level` with `literal`.
    Integer
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the test.
        depth: Depth,
        /// The literal compared with.
        literal: Literal,
        /// The child for an equal integer.
        yes: TestAt,
        /// The child for any other.
        no: TestAt,
    },
}

/// One match, compiled to its decision tree.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the tree's first node is its root; every arm body is read under
///   the case's frame and the arm's variables.
/// - executable: none — the record holds no tree to check its nodes against.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses lower matches of each shape and read the
///   tree back.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CaseForm
{
    /// The scrutinee's syntax node.
    scrutinee: NodeIndex,
    /// The frame the match is read under.
    frame: Frame,
    /// The answer the motive is read from.
    answer: Maybe<Answer, answered::Absent>,
    /// Each arm's body.
    bodies: Vec<NodeIndex>,
    /// The decision tree.
    tests: Vec<Test>,
    /// What the origin table keeps of the arms.
    origin: CaseOrigin,
}

/// One pattern matrix the compiler has yet to reduce, and the tree node it
/// fills.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one level per column, each row as wide.
/// - executable: none — the item holds no tree.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Test`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, PartialEq)]
struct Work
{
    /// The tree node the matrix compiles to.
    slot: TestAt,
    /// The tree binders above it.
    depth: Depth,
    /// The level each column scrutinises.
    levels: Vec<TreeLevel>,
    /// The rows.
    rows: Vec<Row>,
}

/// The patterns of one match, as the compiler reads them.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a pattern's parts are minted after it, so a descending walk meets
///   every part before the pattern holding it.
/// - executable: none — the store is filled by the reader.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Matcher`].
/// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Written
{
    /// Each pattern, with its syntax.
    shapes: Vec<(Placed, Matcher)>,
    /// The field patterns of every constructor pattern, stretch by stretch.
    parts: Vec<PatternAt>,
}

/// The matcher every unwritten column entry reads as.
///
/// # Specification
/// trivial.
static WILD: Matcher = Matcher::Wild;

impl Written
{
    /// The pattern `row` holds in `column`; the wildcard for an entry no
    /// written pattern fills.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stored pattern the column names, or the wildcard.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a catch-all row specialised at a constructor of two
    ///   fields tests neither field.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    #[spec(ensures: |ret| row.columns.get(column.0).and_then(|&at| self.shapes.get(at.0)).map_or(*ret == Matcher::Wild, |held| *ret == held.1))]
    fn entry(
        &self,
        row: &Row,
        column: Column,
    ) -> &Matcher
    {
        row.columns
            .get(column.0)
            .and_then(|&at| self.shapes.get(at.0))
            .map_or(&WILD, |held| &held.1)
    }
}

/// What the leftmost written pattern of a matrix's first row tests.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one head per testing pattern shape.
/// - executable: none — the head holds no matrix.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Test`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, PartialEq)]
enum Head
{
    /// A hole: the row's match is undecided.
    Hole(HoleId),
    /// A constructor of the data declaration at this position of the
    /// collection's data list.
    Data(FormAt),
    /// A boolean.
    Boolean,
    /// This integer.
    Integer(Literal),
}

/// The column a switch tests, and the refusal a row of another kind there
/// earns.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the level is the one the column scrutinises.
/// - executable: none — the switch holds no matrix.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Test`].
/// - witness: `lower::native::tests::patterns_outside_the_fragment_are_declined_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Switch<'source>
{
    /// The column.
    column: Column,
    /// The tree level it scrutinises.
    level: TreeLevel,
    /// The refusal for a pattern of the wrong kind in the column.
    wrong: LoweringRefusal<'source>,
}

/// A decision tree under construction: its nodes, and the matrices still to
/// reduce into them.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: every queued matrix names a pending node.
/// - executable: none — the pairing is maintained by [`Compiling::queue`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`Test`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Compiling
{
    /// The tree's nodes.
    tests: Vec<Test>,
    /// The matrices still to reduce.
    work: Vec<Work>,
}

impl Compiling
{
    /// Allocate a pending node and queue the matrix that fills it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the new node's position, after every earlier node, and one
    ///   more queued matrix naming it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child's position follows its parent's.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    #[spec(
        captures: before = (self.tests.len(), self.work.len()),
        ensures: |ret| ret == TestAt(before.0) && self.tests.len() == before.0.saturating_add(1) && self.work.len() == before.1.saturating_add(1),
    )]
    fn queue(
        &mut self,
        depth: Depth,
        levels: Vec<TreeLevel>,
        rows: Vec<Row>,
    ) -> TestAt
    {
        let slot = TestAt(self.tests.len());
        self.tests.push(Test::Pending);
        self.work.push(Work {
            slot,
            depth,
            levels,
            rows,
        });

        slot
    }
}

impl<'source> Lowerer<'_, 'source>
{
    /// Seed every data declaration's types: each parameter's type under the
    /// parameters before it, the universe at the outermost frame, and each
    /// field's type under all the parameters.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: one frame per parameter, typed with its written type and
    ///   mentioned, so a type naming it counts it, and one seed per type the
    ///   declarations write, appended to `seeds`.
    /// - provides: the data half of [`Self::seed`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-parameter family whose field names its first
    ///   parameter lowers with the field scoped under both.
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    #[spec(
        captures: before = seeds.len(),
        ensures: seeds.len() >= before,
    )]
    pub(super) fn seed_data(
        &mut self,
        seeds: &mut Vec<(NodeIndex, Reading)>,
    )
    {
        for form in &self.collected.data {
            let mut frame = Frame::Outermost;
            for parameter in &form.parameters {
                seeds.push((parameter.classifier.node, Reading::ValueType(frame)));
                let name = SurfaceName::from(self.text_at(parameter.named));
                let bound = self
                    .scope
                    .extend_typed(frame, name, parameter.classifier.node);
                self.scope.mention(bound);
                frame = Frame::Inner(bound);
            }
            if let Maybe::Present(kind) = form.kind {
                seeds.push((kind.node, Reading::ValueType(Frame::Outermost)));
            }
            for generator in &form.generators {
                for field in &generator.fields {
                    seeds.push((field.node, Reading::ValueType(frame)));
                }
            }
        }
    }

    /// The constructor `name`, written at `site`, names: one of a data family
    /// admitted strictly before the declaration `site` belongs to.
    ///
    /// # Specification
    /// - requires: `site` is the name's node or the form holding it.
    /// - ensures: the constructor entered under `name` when its family's
    ///   admission position is strictly earlier than the site's declaration's;
    ///   otherwise the unnamed absence.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor of an earlier family resolves, and a
    ///   name no family declares does not.
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(found) => self.collected.constructors.get(&name) == Some(&found),
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn constructor_named(
        &self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Maybe<Constructor, constructed::Absent>
    {
        match (
            self.collected.constructors.get(&name),
            self.collected.owner_of(site.at.node),
        ) {
            | (Some(&found), Maybe::Present(own)) if found.family < own => Maybe::Present(found),
            | _ => Maybe::Absent(constructed::Absent::Unnamed),
        }
    }

    /// The constructor `head`, the head of a call written at `site`, names.
    ///
    /// # Specification
    /// - requires: `head` is the first operand of the call at `site`.
    /// - ensures: as [`Self::constructor_named`] for a capitalised name; the
    ///   unnamed absence for any other form.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor head and a function head take their own
    ///   readings.
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    pub(super) fn constructor_head(
        &self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(head.node)
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };
        let Shape::Form {
            former: Former::Constructor,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };

        Ok(self.constructor_named(site, SurfaceName::from(self.text_at(head))))
    }

    /// Classify `constructor` applied to the fields `fields` holds in the
    /// operand store, written at `site`.
    ///
    /// # Specification
    /// - requires: `fields` is a stretch of the operand store, each entry a
    ///   field the site was written with, left to right.
    /// - ensures: the constructor stands as a value, each field read as a value
    ///   under the site's frame, its classifier the annotation the site stands
    ///   under when there is one.
    /// - provides: constructor application, bare and called.
    /// - fails: yields the arity refusal for a field count other than the
    ///   constructor's; the wrong-sort refusal outside value position; the
    ///   unannotated refusal for a constructor of a family with parameters
    ///   under no annotation.
    /// - panics: none.
    ///
    /// # Errors
    /// The constructor's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nullary, unary and three-field constructors, a wrong
    ///   field count and a parameterised family without its annotation, each
    ///   asserted as the exact plan's core node or refusal.
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Constructor(planned)) if planned.fields == fields))]
    pub(super) fn construct(
        &mut self,
        site: Site,
        constructor: Constructor,
        fields: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let count = fields.end.saturating_sub(fields.start);
        if count != constructor.arity {
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))));
        }
        let frame = self.require(site, Produced::Value)?;
        let parameters = self
            .collected
            .data
            .get(constructor.form)
            .map_or(0_usize, |form| form.parameters.len());
        let classifier = match self.classifiers.get(&site.at.node) {
            | Some(&written) => Maybe::Present(written),
            | None if parameters == 0 => Maybe::Absent(classified::Absent::Inserted),
            | None => return Err(site.out(FragmentBoundary::Unannotated)),
        };
        let family = self
            .collected
            .slots
            .get(usize::from(constructor.family))
            .map_or_else(|| ConstantIndex::from(0_usize), |slot| slot.constant);
        for position in fields.start .. fields.end {
            if let Some(&field) = self.operands.get(position) {
                self.read(field, Reading::Value(frame));
            }
        }
        self.plan(
            site,
            Plan::Constructor(Constructed {
                family,
                tag: ConstructorTag::from(constructor.tag),
                fields,
                classifier,
            }),
        );

        Ok(())
    }

    /// Classify `(e : T)`, its `(` and `e` read, the cursor at its `:`.
    ///
    /// # Specification
    /// - requires: `run` is the parenthesised expression's first hole and
    ///   `cursor` stands at its `:`.
    /// - ensures: an annotation over a constructor standing as a value reads
    ///   `T` as a value type under the same frame, records it as the
    ///   constructor's classifier, and adopts the constructor.
    /// - fails: the unadmitted annotation refusal for any other annotation; the
    ///   hole's and the tiles' own faults.
    /// - panics: none.
    ///
    /// # Errors
    /// The annotation's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an annotated parameterised constructor lowers over
    ///   the annotation's type, and an annotated name is refused.
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Transparent(_))))]
    pub(super) fn annotated(
        &mut self,
        site: Site,
        run: Run,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let declined = site.folded(FormName::ANNOTATION, FragmentBoundary::Unadmitted);
        let (Run::One(inner), Reading::Value(frame)) = (run, site.reading)
        else {
            return Err(declined);
        };
        if let Maybe::Absent(_) = self.applied_constructor(site, inner)? {
            return Err(declined);
        }
        let _colon = cursor.tile(TileName::COLON);
        let classifier = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        exhausted(site, &cursor)?;
        self.read(classifier.node, Reading::ValueType(frame));
        self.read(inner.node, site.reading);
        let _first = self.classifiers.insert(inner.node, classifier.node);
        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// The constructor `inner`, written inside the parentheses at `site`,
    /// applies: a bare constructor, or a call whose head is one.
    ///
    /// # Specification
    /// - requires: `inner` is the operand of the parenthesised form at `site`.
    /// - ensures: the constructor a constructor name or a call's head names, as
    ///   [`Self::constructor_head`] answers it; the unnamed absence for any
    ///   other form.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::annotated`].
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    fn applied_constructor(
        &mut self,
        site: Site,
        inner: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let bare = self.constructor_head(site, inner)?;
        if let Maybe::Present(_) = bare {
            return Ok(bare);
        }
        let Some(node) = self.tree.node(inner.node)
        else {
            return Ok(bare);
        };
        let Shape::Form {
            former: Former::Call,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Ok(bare);
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let head =
            read_pieces(self.pbg, self.tree, inner.node, &mut scratch).map(|()| {
                match scratch.pieces.first() {
                    | Some(&Piece::Operand(head)) => Some(head),
                    | Some(&Piece::Tile { .. }) | None => None,
                }
            });
        self.scratch = scratch;
        match head? {
            | Some(head) => self.constructor_head(site, head),
            | None => Ok(bare),
        }
    }

    /// The number of parameters of the data family declared at `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the parameter count of the data declaration whose slot takes
    ///   `constant`; the undeclared absence for any other declaration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family and a value declaration separate the hit
    ///   from the miss.
    /// - witness: `lower::native::tests::a_data_family_applies_to_its_parameters`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || self.collected.slots.get(usize::from(constant)).is_some())]
    pub(super) fn data_family(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<OperandCount, family::Absent>
    {
        match self
            .collected
            .slots
            .get(usize::from(constant))
            .map(|slot| slot.definition)
        {
            | Some(Maybe::Present(Half {
                operand: Operand::Data(form),
                ..
            })) => self
                .collected
                .data
                .get(form)
                .map_or(Maybe::Absent(family::Absent::Undeclared), |written| {
                    Maybe::Present(OperandCount::from(written.parameters.len()))
                }),
            | _ => Maybe::Absent(family::Absent::Undeclared),
        }
    }

    /// Classify the data family at `constant`, of `arity` parameters,
    /// applied to the arguments `applied` holds in the operand store.
    ///
    /// # Specification
    /// - requires: `applied` is a stretch of the operand store.
    /// - ensures: the family stands as a value type over its arguments, each
    ///   read as a value under the site's frame.
    /// - fails: the arity refusal for an argument count other than `arity`; the
    ///   wrong-sort refusal where no value type is read or reached.
    /// - panics: none.
    ///
    /// # Errors
    /// The family's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family over one and over two arguments, and over
    ///   too few, each asserted as the exact nominal type or refusal.
    /// - witness: `lower::native::tests::a_data_family_applies_to_its_parameters`
    #[spec(ensures: |ret| ret.is_err() || self.plans.get(usize::from(site.at.node)) == Some(&Plan::Data(constant, applied)))]
    pub(super) fn family(
        &mut self,
        site: Site,
        constant: ConstantIndex,
        arity: OperandCount,
        applied: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let count = applied.end.saturating_sub(applied.start);
        if OperandCount::from(count) != arity {
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))));
        }
        let frame = self.require(site, Produced::ValueType)?;
        for position in applied.start .. applied.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }
        self.plan(site, Plan::Data(constant, applied));

        Ok(())
    }

    /// Classify a match, `case e -> T? { p => c, … }`.
    ///
    /// # Specification
    /// - requires: `site` is a match in term position.
    /// - ensures: the match stands as a computation, its arms' patterns read
    ///   and compiled to a decision tree over the scrutinee, read as a value
    ///   under the site's frame; the written answer is read where a result is
    ///   read, and else the answer the position states is taken; each arm body
    ///   is read as a computation under the case's frame, the tree's anonymous
    ///   binders and its own variables, and answers what the match does.
    /// - provides: the reading of `case`.
    /// - fails: the wrong-sort refusal outside computation position; the view
    ///   form `case … with` and the absurd match `case e {}`, which no pattern
    ///   names the family of, by the view's name; a pattern the fragment does
    ///   not read by its own name; a pattern of the wrong kind for its column
    ///   as the wrong sort; a variable bound twice in one pattern; a
    ///   non-exhaustive match; a match whose tree eliminates native data with
    ///   no answer as unannotated; and the tiles' and holes' own faults.
    /// - panics: none.
    ///
    /// # Errors
    /// The match's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses lower each pattern shape and refusal,
    ///   asserting the tree read back out of the arena or the exact refusal.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    /// - witness: `lower::native::tests::a_non_exhaustive_match_is_refused`
    /// - witness: `lower::native::tests::a_match_without_an_answer_is_unannotated`
    /// - witness: `lower::native::tests::patterns_outside_the_fragment_are_declined_by_name`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Case(_))))]
    pub(super) fn case(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let _case = cursor.tile(TileName::CASE);
        let scrutinee = site.one(cursor.operands())?;
        if let Maybe::Present(with) = cursor.at(TileName::WITH) {
            return Err(LoweringRefusal::OutOfFragment {
                span: with.span,
                form: FormName::CASE_WITH_VIEW,
                sort: site.reading.sort(),
                boundary: FragmentBoundary::Unadmitted,
            });
        }
        let written = match cursor.tile(TileName::ARROW) {
            | Maybe::Present(_) => Maybe::Present(site.one(cursor.operands())?),
            | Maybe::Absent(_) => Maybe::Absent(answered::Absent::Unstated),
        };
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let mut arms: Vec<(Placed, Placed)> = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let pattern = site.one(cursor.operands())?;
            closed(site, &mut cursor, TileName::FAT_ARROW)?;
            let body = site.one(cursor.operands())?;
            arms.push((pattern, body));
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                closed(site, &mut cursor, TileName::BRACE_CLOSE)?;
                break;
            }
        }
        exhausted(site, &cursor)?;
        if arms.is_empty() {
            return Err(LoweringRefusal::OutOfFragment {
                span: site.at.span,
                form: FormName::CASE_WITH_VIEW,
                sort: site.reading.sort(),
                boundary: FragmentBoundary::Unadmitted,
            });
        }
        let mut patterns = Written::default();
        let mut rows = Vec::new();
        let mut variables: Vec<Vec<Placed>> = Vec::with_capacity(arms.len());
        let mut kept = CaseOrigin {
            written: site.at.node,
            scrutinee: scrutinee.node,
            patterns: Patterns::new(),
            arms: Vec::new(),
        };
        let mut roots = Vec::new();
        for (arm, &(pattern, body)) in arms.iter().enumerate() {
            let arm = ArmAt(arm);
            let alternatives = self.alternatives(pattern)?;
            let several = alternatives.len() > 1;
            let mut bound = Vec::new();
            for alternative in alternatives {
                let mut named = Vec::new();
                let root = self.pattern(site, alternative, &mut patterns, &mut named)?;
                if several && !named.is_empty() {
                    return Err(LoweringRefusal::OutOfFragment {
                        span: pattern.span,
                        form: FormName::OR_PATTERN,
                        sort: site.reading.sort(),
                        boundary: FragmentBoundary::Unadmitted,
                    });
                }
                bound = named;
                roots.push((arm, root, alternative.node, body.node));
                rows.push(Row {
                    columns: Vec::from([root]),
                    arm,
                    bindings: Vec::new(),
                    stuck: Maybe::Absent(stuck::Absent::Decided),
                });
            }
            variables.push(bound);
        }
        let tests = self.compile(site, &patterns, rows)?;
        let eliminates = tests.iter().any(|test| matches!(*test, Test::Data { .. }));
        let answer = match written {
            | Maybe::Present(node) => Maybe::Present(Answer {
                node: node.node,
                frame,
            }),
            | Maybe::Absent(reason) => self
                .answers
                .get(&site.at.node)
                .copied()
                .map_or(Maybe::Absent(reason), Maybe::Present),
        };
        if eliminates && matches!(answer, Maybe::Absent(_)) {
            return Err(site.out(FragmentBoundary::Unannotated));
        }
        Self::keep(&patterns, &roots, &mut kept);
        self.read(scrutinee.node, Reading::Value(frame));
        if let Maybe::Present(node) = written {
            self.read(node.node, Reading::Result(frame));
        }
        for (&(_pattern, body), bound) in arms.iter().zip(&variables) {
            let mut inner = frame;
            for &binder in bound {
                let name = SurfaceName::from(self.text_at(binder));
                self.note_binder(binder, name)?;
                inner = Frame::Inner(self.scope.extend(inner, name));
            }
            self.read(body.node, Reading::Computation(inner));
            if let Maybe::Present(stated) = answer {
                let _first = self.answers.insert(body.node, stated);
            }
        }
        let index = CaseIndex(self.cases.len());
        self.cases.push(CaseForm {
            scrutinee: scrutinee.node,
            frame,
            answer,
            bodies: arms.iter().map(|&(_pattern, body)| body.node).collect(),
            tests,
            origin: kept,
        });
        self.plan(site, Plan::Case(index));

        Ok(())
    }

    /// The alternatives of the arm pattern `pattern`: its or-pattern's
    /// operands in source order, flattened, or the pattern itself.
    ///
    /// # Specification
    /// - requires: `pattern` is an arm's pattern of the match at `site`.
    /// - ensures: at least one alternative, in source order.
    /// - fails: [`LoweringRefusal::UnknownMold`] and an or-pattern's repair.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] and [`LoweringRefusal::MalformedForm`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a three-way or-pattern keeps its alternatives in
    ///   order.
    /// - witness: `lower::native::tests::an_or_pattern_settles_each_alternative`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |alternatives| !alternatives.is_empty()))]
    fn alternatives(
        &mut self,
        pattern: Placed,
    ) -> Result<Vec<Placed>, LoweringRefusal<'source>>
    {
        let mut alternatives = Vec::new();
        let mut pending = Vec::from([pattern]);
        let mut pieces = Pieces::new();
        while let Some(next) = pending.pop() {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(next.node)
            else {
                continue;
            };
            let Shape::Form { name, .. } = shape_of(self.pbg, node)?
            else {
                alternatives.push(next);
                continue;
            };
            if name != FormName::OR_PATTERN {
                alternatives.push(next);
                continue;
            }
            read_pieces(self.pbg, self.tree, next.node, &mut pieces)?;
            if let Maybe::Present(repaired) = pieces.repair {
                return Err(repaired.refusal(FormName::OR_PATTERN));
            }
            for piece in pieces.pieces.iter().rev() {
                if let Piece::Operand(alternative) = *piece {
                    pending.push(alternative);
                }
            }
        }
        if alternatives.is_empty() {
            alternatives.push(pattern);
        }

        Ok(alternatives)
    }

    /// Read the or-free pattern `root` of the match at `site` into
    /// `patterns`, numbering its variables into `named`.
    ///
    /// # Specification
    /// - requires: `root` is an alternative of an arm of the match at `site`.
    /// - ensures: the root's position in `patterns`; every part after the
    ///   pattern holding it; each name bound once, numbered in source order.
    /// - fails: a pattern the fragment does not read, by its own name; a
    ///   constructor no earlier family declares, as unresolved; a constructor
    ///   applied to other than its arity; a variable bound twice; a repair.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the match witnesses read every admitted shape and
    ///   decline the others.
    /// - witness: `lower::native::tests::patterns_outside_the_fragment_are_declined_by_name`
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    #[spec(
        captures: before = patterns.shapes.len(),
        ensures: |ret| ret.as_ref().map_or(true, |&root| root == PatternAt(before) && patterns.shapes.len() > before),
    )]
    fn pattern(
        &mut self,
        site: Site,
        root: Placed,
        patterns: &mut Written,
        named: &mut Vec<Placed>,
    ) -> Result<PatternAt, LoweringRefusal<'source>>
    {
        let first = PatternAt(patterns.shapes.len());
        patterns.shapes.push((root, Matcher::Wild));
        let mut work = Vec::from([(root, first)]);
        let mut pieces = Pieces::new();
        while let Some((at, slot)) = work.pop() {
            self.fuel.spend()?;
            let shape = self.pattern_shape(site, at, &mut pieces, patterns, named, &mut work)?;
            if let Some(held) = patterns.shapes.get_mut(slot.0) {
                held.1 = shape;
            }
        }

        Ok(first)
    }

    /// The shape of the pattern at `at`, its field patterns allocated and
    /// queued on `work`.
    ///
    /// # Specification
    /// - requires: as [`Self::pattern`]; `pieces` is scratch.
    /// - ensures: as [`Self::pattern`], for one pattern.
    /// - fails: as [`Self::pattern`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::pattern`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pattern`].
    /// - witness: `lower::native::tests::patterns_outside_the_fragment_are_declined_by_name`
    #[spec(captures: before = patterns.shapes.len(), ensures: patterns.shapes.len() >= before)]
    fn pattern_shape(
        &self,
        site: Site,
        at: Placed,
        pieces: &mut Pieces,
        patterns: &mut Written,
        named: &mut Vec<Placed>,
        work: &mut Vec<(Placed, PatternAt)>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(at.node)
        else {
            return Ok(Matcher::Wild);
        };
        let name = match shape_of(self.pbg, node)? {
            | Shape::Form { name, .. } => name,
            | Shape::Repair(repair) => {
                return Err(LoweringRefusal::MalformedForm {
                    span: at.span,
                    form: FormName::CASE,
                    fault: FormFault::Repaired(repair),
                });
            },
            | Shape::Root | Shape::Layout => return Ok(Matcher::Wild),
        };
        let here = Site {
            at,
            name,
            reading: site.reading,
        };
        if name == FormName::WILDCARD {
            return Ok(Matcher::Wild);
        }
        if name == FormName::HOLE {
            let identity = u32::try_from(usize::from(at.node)).map_err(|_overflow| {
                LoweringRefusal::BudgetExceeded {
                    budget: self.fuel.budget,
                }
            })?;
            return Ok(Matcher::Hole(HoleId::from(identity)));
        }
        if name == FormName::IDENTIFIER {
            let spelled = self.text_at(at);
            if let Some(&earlier) = named
                .iter()
                .find(|&&binder| self.text_at(binder) == spelled)
            {
                return Err(LoweringRefusal::DuplicateDefinition {
                    span: at.span,
                    name: SurfaceName::from(spelled),
                    first: earlier.span,
                });
            }
            named.push(at);
            return Ok(Matcher::Binder(VariableAt(named.len().saturating_sub(1))));
        }
        if name == FormName::NUMBER {
            return integer(here, self.text_at(at));
        }
        if name == FormName::BOOLEAN {
            return Ok(Matcher::Boolean(self.text_at(at).as_ref() == "true"));
        }
        if name == FormName::CONSTRUCTOR {
            return self.constructor_pattern(site, here, at, &[], patterns, work);
        }
        read_pieces(self.pbg, self.tree, at.node, pieces)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(here.name));
        }
        if name == FormName::LITERAL_PATTERN {
            return match pieces.pieces.first() {
                | Some(&Piece::Tile { label, at: tile }) if label == TileName::NUMBER => {
                    integer(here, self.text_at(tile))
                },
                | Some(&Piece::Tile { label, .. }) if label == TileName::TRUE => {
                    Ok(Matcher::Boolean(true))
                },
                | Some(&Piece::Tile { label, .. }) if label == TileName::FALSE => {
                    Ok(Matcher::Boolean(false))
                },
                | _ => Err(here.out(FragmentBoundary::Unadmitted)),
            };
        }
        if name == FormName::CONSTRUCTOR_PATTERN {
            let mut cursor = Cursor::new(&pieces.pieces, at.span);
            let Maybe::Present(head) = cursor.tile(TileName::CONSTRUCTOR)
            else {
                return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
            };
            let mut fields = Vec::new();
            if let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN) {
                while let Maybe::Absent(_) = cursor.tile(TileName::PAREN_CLOSE) {
                    fields.push(here.one(cursor.operands())?);
                    if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                        closed(here, &mut cursor, TileName::PAREN_CLOSE)?;
                        break;
                    }
                }
            }
            exhausted(here, &cursor)?;
            return self.constructor_pattern(site, here, head, &fields, patterns, work);
        }

        Err(here.out(FragmentBoundary::Unadmitted))
    }

    /// The shape of the constructor pattern at `here`, the constructor
    /// spelled at `head`, its field patterns `fields` allocated and queued.
    ///
    /// # Specification
    /// - requires: `here` is a constructor pattern of the match at `site`.
    /// - ensures: the constructor, its fields a fresh stretch of the part
    ///   store, each field queued on `work` after its slot is allocated.
    /// - fails: the unresolved-name refusal for a name no earlier family's
    ///   constructor carries; the arity refusal for other than its arity.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pattern`].
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    #[spec(captures: before = work.len(), ensures: |ret| ret.is_err() || work.len() == before.saturating_add(fields.len()))]
    fn constructor_pattern(
        &self,
        site: Site,
        here: Site,
        head: Placed,
        fields: &[Placed],
        patterns: &mut Written,
        work: &mut Vec<(Placed, PatternAt)>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let name = SurfaceName::from(self.text_at(head));
        let Maybe::Present(constructor) = self.constructor_named(site, name)
        else {
            return Err(LoweringRefusal::UnresolvedName {
                span: head.span,
                name,
            });
        };
        if fields.len() != constructor.arity {
            return Err(here.out(FragmentBoundary::Arity(OperandCount::from(fields.len()))));
        }
        let start = patterns.parts.len();
        for &field in fields {
            let slot = PatternAt(patterns.shapes.len());
            patterns.shapes.push((field, Matcher::Wild));
            patterns.parts.push(slot);
        }
        let end = patterns.parts.len();
        for (offset, &field) in fields.iter().enumerate().rev() {
            if let Some(&slot) = patterns.parts.get(start.saturating_add(offset)) {
                work.push((field, slot));
            }
        }

        Ok(Matcher::Constructor {
            form: FormAt(constructor.form),
            tag: constructor.tag,
            fields: Stretch { start, end },
        })
    }

    /// Compile `rows` to a decision tree over the scrutinee at level zero.
    ///
    /// # Specification
    /// - requires: every row has one column, its arm's alternative.
    /// - ensures: the tree's nodes, its root first and every child after its
    ///   parent: a leaf where the first surviving row's columns all match
    ///   anything, a stuck node where its leftmost tested column is a hole or a
    ///   hole it passed decides it, and else a switch on that column.
    /// - fails: [`LoweringRefusal::NonExhaustiveMatch`] at the match where no
    ///   row survives; the wrong-sort refusal at a pattern whose kind its
    ///   column does not switch on; [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// The match's refusal.
    ///
    /// # Termination
    /// Every work item removes a column or a literal from the rows it hands
    /// on, or ends in a leaf, and the allowance is spent once per item and
    /// per row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses compile a catch-all, an or-pattern, two
    ///   arms at one head, literal columns, holes and a missing constructor.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    /// - witness: `lower::native::tests::a_non_exhaustive_match_is_refused`
    /// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
    /// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |tests| !tests.is_empty() && tests.iter().all(|test| *test != Test::Pending)))]
    fn compile(
        &mut self,
        site: Site,
        patterns: &Written,
        rows: Vec<Row>,
    ) -> Result<Vec<Test>, LoweringRefusal<'source>>
    {
        let mut tree = Compiling::default();
        let _root = tree.queue(Depth::default(), Vec::from([TreeLevel::default()]), rows);
        while let Some(item) = tree.work.pop() {
            self.fuel.spend()?;
            let test = self.reduce(site, patterns, &item, &mut tree)?;
            if let Some(held) = tree.tests.get_mut(item.slot.0) {
                *held = test;
            }
        }

        Ok(tree.tests)
    }

    /// Reduce one matrix to the tree node it fills, queueing its children.
    ///
    /// # Specification
    /// - requires: as [`Self::compile`], for one item.
    /// - ensures: the item's node: a leaf or a stuck node when the first row
    ///   tests nothing, a stuck node when its leftmost tested pattern is a
    ///   hole, and else the switch on that pattern's column, its children
    ///   queued on `tree`.
    /// - fails: as [`Self::compile`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::compile`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::compile`].
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| *test != Test::Pending))]
    fn reduce(
        &mut self,
        site: Site,
        patterns: &Written,
        item: &Work,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let Some(first) = item.rows.first()
        else {
            return Err(LoweringRefusal::NonExhaustiveMatch { span: site.at.span });
        };
        let tested = first
            .columns
            .iter()
            .enumerate()
            .find_map(|(column, &pattern)| {
                let &(written, ref shape) = patterns.shapes.get(pattern.0)?;
                let head = match *shape {
                    | Matcher::Wild | Matcher::Binder(_) => return None,
                    | Matcher::Hole(hole) => Head::Hole(hole),
                    | Matcher::Constructor { form, .. } => Head::Data(form),
                    | Matcher::Boolean(_) => Head::Boolean,
                    | Matcher::Integer(ref literal) => Head::Integer(literal.clone()),
                };
                Some((Column(column), written, head))
            });
        let Some((column, written, head)) = tested
        else {
            return Ok(leaf(patterns, first, &item.levels, item.depth));
        };
        let switch = Switch {
            column,
            level: item.levels.get(column.0).copied().unwrap_or_default(),
            wrong: LoweringRefusal::OutOfFragment {
                span: written.span,
                form: FormName::CASE,
                sort: site.reading.sort(),
                boundary: FragmentBoundary::WrongSort,
            },
        };
        match head {
            | Head::Hole(hole) => Ok(Test::Stuck(hole)),
            | Head::Data(form) => self.switch_data(patterns, item, switch, form, tree),
            | Head::Boolean => self.switch_boolean(patterns, item, switch, tree),
            | Head::Integer(literal) => self.switch_integer(patterns, item, switch, literal, tree),
        }
    }

    /// Switch on the native data value in `switch`'s column, a value of the
    /// data declaration at `form`: one child per constructor, its rows those
    /// that admit the constructor with its fields in the column's place.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds a constructor of `form` in the
    ///   item's first row.
    /// - ensures: a data switch with one branch per constructor of `form`, in
    ///   tag order, each child queued under the constructor's fields.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is no constructor of `form`;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a catch-all row and a nested constructor each reach
    ///   the branch they admit.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Data { .. })))]
    fn switch_data(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch<'source>,
        form: FormAt,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let arities: Vec<usize> = self
            .collected
            .data
            .get(form.0)
            .map(|written| {
                written
                    .generators
                    .iter()
                    .map(|generator| generator.fields.len())
                    .collect()
            })
            .unwrap_or_default();
        let mut branches = Vec::with_capacity(arities.len());
        for (tag, &arity) in arities.iter().enumerate() {
            let mut specialised = Vec::new();
            for row in &item.rows {
                self.fuel.spend()?;
                let mut next = row.clone();
                let held = patterns.entry(row, switch.column);
                let replacement = match *held {
                    | Matcher::Constructor {
                        form: other,
                        tag: written,
                        fields,
                    } => {
                        if other != form {
                            return Err(switch.wrong);
                        }
                        if written != tag {
                            continue;
                        }
                        patterns
                            .parts
                            .get(fields.start .. fields.end)
                            .map(<[PatternAt]>::to_vec)
                            .unwrap_or_default()
                    },
                    | Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                        through(&mut next, held, switch.level);
                        alloc::vec![UNWRITTEN; arity]
                    },
                    | Matcher::Boolean(_) | Matcher::Integer(_) => return Err(switch.wrong),
                };
                next.columns = splice(&row.columns, switch.column, &replacement);
                specialised.push(next);
            }
            let fresh: Vec<TreeLevel> = (0 .. arity)
                .map(|field| TreeLevel(item.depth.0.saturating_add(field).saturating_add(1)))
                .collect();
            let child = tree.queue(
                Depth(item.depth.0.saturating_add(arity)),
                splice(&item.levels, switch.column, &fresh),
                specialised,
            );
            branches.push((arity, child));
        }

        Ok(Test::Data {
            level: switch.level,
            depth: item.depth,
            branches,
        })
    }

    /// Switch on the boolean in `switch`'s column: `true` on the left.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds a boolean in the item's first row.
    /// - ensures: a boolean switch whose children hold the rows admitting
    ///   `true` and `false`, the column removed, each under the case's one unit
    ///   binder.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is a constructor or an integer;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `true` arm and a catch-all split into the two
    ///   sides.
    /// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Boolean { .. })))]
    fn switch_boolean(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch<'source>,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let mut left = Vec::new();
        let mut right = Vec::new();
        for row in &item.rows {
            self.fuel.spend()?;
            let held = patterns.entry(row, switch.column);
            let mut next = row.clone();
            next.columns = splice(&row.columns, switch.column, &[]);
            match *held {
                | Matcher::Boolean(true) => left.push(next),
                | Matcher::Boolean(false) => right.push(next),
                | Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut next, held, switch.level);
                    left.push(next.clone());
                    right.push(next);
                },
                | Matcher::Constructor { .. } | Matcher::Integer(_) => return Err(switch.wrong),
            }
        }
        let without = splice(&item.levels, switch.column, &[]);
        let depth = Depth(item.depth.0.saturating_add(1));
        let no = tree.queue(depth, without.clone(), right);
        let yes = tree.queue(depth, without, left);

        Ok(Test::Boolean {
            level: switch.level,
            depth: item.depth,
            yes,
            no,
        })
    }

    /// Compare the integer in `switch`'s column with `literal`.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds `literal` in the item's first row.
    /// - ensures: an integer test whose equal child holds the rows admitting
    ///   `literal`, the column removed, and whose other child holds the rows
    ///   admitting another integer, the column kept; both under the
    ///   comparison's binder and the case's unit binder.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is a constructor or a boolean;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two literal arms and a catch-all compile to two
    ///   comparisons, and the catch-all reaches both other sides.
    /// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Integer { .. })))]
    fn switch_integer(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch<'source>,
        literal: Literal,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let mut equal = Vec::new();
        let mut other = Vec::new();
        for row in &item.rows {
            self.fuel.spend()?;
            let held = patterns.entry(row, switch.column);
            let mut matched = row.clone();
            matched.columns = splice(&row.columns, switch.column, &[]);
            match *held {
                | Matcher::Integer(ref written) if *written == literal => equal.push(matched),
                | Matcher::Integer(_) => other.push(row.clone()),
                | Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut matched, held, switch.level);
                    equal.push(matched);
                    other.push(row.clone());
                },
                | Matcher::Constructor { .. } | Matcher::Boolean(_) => return Err(switch.wrong),
            }
        }
        let depth = Depth(item.depth.0.saturating_add(2));
        let no = tree.queue(depth, item.levels.clone(), other);
        let yes = tree.queue(depth, splice(&item.levels, switch.column, &[]), equal);

        Ok(Test::Integer {
            level: switch.level,
            depth: item.depth,
            literal,
            yes,
            no,
        })
    }

    /// Mint `patterns` into `kept`'s core pattern table and record one arm
    /// alternative per entry of `roots`.
    ///
    /// # Specification
    /// - requires: every root of `roots` names a pattern of `patterns`.
    /// - ensures: each pattern minted after its parts, in the core's shapes: a
    ///   binder, a wildcard, a hole, a constructor over its fields, a literal,
    ///   and a boolean as an injection over the unit; one arm record per root,
    ///   in order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match over nested constructors, a binder, a hole
    ///   and an or-pattern keeps each alternative's shape.
    /// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
    #[spec(captures: before = kept.arms.len(), ensures: kept.arms.len() == before.saturating_add(roots.len()))]
    fn keep(
        patterns: &Written,
        roots: &[(ArmAt, PatternAt, NodeIndex, NodeIndex)],
        kept: &mut CaseOrigin,
    )
    {
        let mut minted: Vec<Option<PatternId>> =
            Vec::from_iter(patterns.shapes.iter().map(|_shape| None));
        for (position, &(_at, ref shape)) in patterns.shapes.iter().enumerate().rev() {
            let pattern = match *shape {
                | Matcher::Wild => Pattern::Wildcard,
                | Matcher::Binder(_) => Pattern::Binder,
                | Matcher::Hole(hole) => Pattern::Hole(hole),
                | Matcher::Integer(ref literal) => Pattern::Literal(literal.clone()),
                | Matcher::Boolean(value) => {
                    let unit = kept.patterns.mint(Pattern::Unit);
                    Pattern::Injection(if value { Side::Left } else { Side::Right }, unit)
                },
                | Matcher::Constructor { tag, fields, .. } => Pattern::Constructor {
                    tag: ConstructorTag::from(tag),
                    fields: patterns
                        .parts
                        .get(fields.start .. fields.end)
                        .unwrap_or_default()
                        .iter()
                        .filter_map(|&part| minted.get(part.0).copied().flatten())
                        .collect(),
                },
            };
            let id = kept.patterns.mint(pattern);
            if let Some(held) = minted.get_mut(position) {
                *held = Some(id);
            }
        }
        for &(arm, root, written, body) in roots {
            if let Some(&Some(pattern)) = minted.get(root.0) {
                kept.arms.push(ArmOrigin {
                    arm: arm.0,
                    pattern,
                    written,
                    body,
                });
            }
        }
    }

    /// Mint every data declaration's signature, in source order, for those
    /// whose slot holds no refusal.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: each unrefused data declaration's signature over its minted
    ///   parameter types, field types and universe — `Type` at the fuss-free
    ///   level when none is written, its origin the declaration form — pushed
    ///   onto the module's list, its index recorded by the declaration's
    ///   position in the collection's data list.
    /// - provides: the
    ///   [`DeclarationOutcome::Data`](crate::DeclarationOutcome::Data)
    ///   outcome's signature.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two declarations, one with parameters and one without
    ///   a written universe, lower to their own signatures.
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    #[spec(captures: before = self.data.len(), ensures: self.data.len() >= before && self.signatures.len() >= before)]
    pub(super) fn mint_data(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        for (position, form) in self.collected.data.iter().enumerate() {
            let Some(slot) = self.collected.slots.get(usize::from(form.slot))
            else {
                continue;
            };
            let owned = matches!(slot.definition, Maybe::Present(Half { operand: Operand::Data(held), .. }) if held == position);
            if !owned || matches!(slot.refusal, Maybe::Present(_)) {
                continue;
            }
            let mut parameters = Vec::with_capacity(form.parameters.len());
            for parameter in &form.parameters {
                if let Maybe::Present(classifier) = self.value_type_at(parameter.classifier.node) {
                    parameters.push(classifier);
                }
            }
            let mut constructors = Vec::with_capacity(form.generators.len());
            for generator in &form.generators {
                let fields: Vec<ValueTypeId> = generator
                    .fields
                    .iter()
                    .filter_map(|field| match self.value_type_at(field.node) {
                        | Maybe::Present(id) => Some(id),
                        | Maybe::Absent(_) => None,
                    })
                    .collect();
                constructors.push(fields);
            }
            let complete = parameters.len() == form.parameters.len()
                && constructors
                    .iter()
                    .zip(&form.generators)
                    .all(|(fields, generator)| fields.len() == generator.fields.len());
            let kind = match form.kind {
                | Maybe::Present(written) => self.value_type_at(written.node),
                | Maybe::Absent(_) => match self.origin_at(form.declaration.node) {
                    | Maybe::Present(origin) => {
                        let id = sink.arena.value_type_universe(
                            Sort::Ground(GroundSort::Value),
                            Level::constant(super::Universe::FUSS_FREE.level),
                        );
                        sink.origins.record_value_type(id, origin);
                        Maybe::Present(id)
                    },
                    | Maybe::Absent(reason) => Maybe::Absent(reason),
                },
            };
            let Maybe::Present(kind) = kind
            else {
                continue;
            };
            if !complete {
                continue;
            }
            let index = DataIndex::from(self.data.len());
            self.data
                .push(Arc::new(DataSignature::new(parameters, constructors, kind)));
            let _first = self.signatures.insert(position, index);
        }
    }

    /// Mint the nominal type of the family at `constant` over the arguments
    /// `arguments` names in the operand store.
    ///
    /// # Specification
    /// - requires: every argument is already minted or absent.
    /// - ensures: the family over its arguments, left to right, with the
    ///   written origin; nothing when an argument did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::family`].
    /// - witness: `lower::native::tests::a_data_family_applies_to_its_parameters`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::ValueType(_))))]
    pub(super) fn mint_family(
        &self,
        constant: ConstantIndex,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut passed = Vec::with_capacity(arguments.end.saturating_sub(arguments.start));
        for position in arguments.start .. arguments.end {
            let Some(&argument) = self.operands.get(position)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            match self.value_at(argument) {
                | Maybe::Present(value) => passed.push(value),
                | Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_type_data(constant, passed);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Mint a constructor over its fields and its classifier.
    ///
    /// # Specification
    /// - requires: every field and the annotation's type are already minted or
    ///   absent.
    /// - ensures: the constructor value over its fields, its classifier the
    ///   annotation's type carried into the term's binders, or the family over
    ///   no arguments with an inserted origin; the written origin on the value;
    ///   nothing when a field or the annotation did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::construct`].
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Value(_))))]
    pub(super) fn mint_constructor(
        &self,
        constructed: Constructed,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut fields = Vec::new();
        for position in constructed.fields.start .. constructed.fields.end {
            let Some(&field) = self.operands.get(position)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            match self.value_at(field) {
                | Maybe::Present(value) => fields.push(value),
                | Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let classifier = match constructed.classifier {
            | Maybe::Present(written) => {
                let Maybe::Present(id) = self.value_type_at(written)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let frame = self.reading(written).frame();
                self.relocate_value_type(id, frame, sink, origin.inserted(Insertion::Classifier))
            },
            | Maybe::Absent(_) => {
                let id = sink.arena.value_type_data(constructed.family, Vec::new());
                sink.origins
                    .record_value_type(id, origin.inserted(Insertion::Classifier));
                id
            },
        };
        let id = sink
            .arena
            .value_constructor(classifier, constructed.tag, fields);

        Maybe::Present(sink.value(id, origin))
    }

    /// `ty`, a value type read under `frame` in a type's telescope, carried
    /// into the term context of the same frame.
    ///
    /// # Specification
    /// - requires: `ty` is minted under `frame`, counting only the frames that
    ///   bind in a telescope.
    /// - ensures: `ty` itself when every frame binds; otherwise `ty` with a
    ///   binder inserted for each frame that does not, each node the rewrite
    ///   mints recorded with `origin`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed annotation is carried unchanged.
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    #[spec(ensures: |ret| sink.arena.value_type(ret).is_some() || ret == ty)]
    fn relocate_value_type(
        &self,
        ty: ValueTypeId,
        frame: Frame,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId
    {
        if self.scope.telescope_binders(frame).all(|binds| binds) {
            return ty;
        }
        let mark = sink.arena.watermark();
        let wrapped = sink.arena.comp_type_returner(ty);
        let carried = self.relocate(sink.arena, wrapped, frame, Binders::default());
        let result = match sink.arena.comp_type(carried) {
            | Some(&CompType::Returner { result: inner, .. }) => inner,
            | _ => ty,
        };
        record_since(
            sink,
            mark,
            origin,
            Maybe::Absent(rooted::Absent::Classifier),
        );

        result
    }

    /// `ty`, a computation type read under `from` in a type's telescope,
    /// carried into the term context of `from` and then under `lift` more
    /// binders.
    ///
    /// # Specification
    /// - requires: `ty` is minted under `from`, counting only the frames that
    ///   bind in a telescope.
    /// - ensures: a binder inserted at each frame of `from`'s chain that does
    ///   not bind in a telescope, then every free index raised by `lift`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function result and a written answer become the
    ///   motive of a nested tree.
    /// - witness: `lower::native::tests::a_match_takes_its_answer_from_the_function_result`
    #[spec(ensures: |ret| arena.comp_type(ret).is_some() || ret == ty)]
    fn relocate(
        &self,
        arena: &mut CoreArena,
        ty: CompTypeId,
        from: Frame,
        lift: Binders,
    ) -> CompTypeId
    {
        let mut carried = ty;
        for (position, binds) in self.scope.telescope_binders(from).enumerate() {
            if !binds {
                let scope = Binders::from(u32::try_from(position).unwrap_or(u32::MAX));
                carried =
                    gandr_core_term::shift_comp_type_under(arena, carried, scope, Binders::ONE);
            }
        }
        if lift != Binders::default() {
            carried = gandr_core_term::shift_comp_type(arena, carried, lift);
        }

        carried
    }

    /// Mint the match at `case`: its scrutinee bound once over its decision
    /// tree.
    ///
    /// # Specification
    /// - requires: the scrutinee, every arm body and the answer are already
    ///   minted or absent.
    /// - ensures: the tree, every node minted descending: a data case over the
    ///   scrutinised level with the answer relocated under its binders and one
    ///   more as its motive, each branch a lambda per field; a sum case for a
    ///   boolean; an integer comparison bound and cased on; a hole for a stuck
    ///   node; and a leaf as its arm's body with each variable replaced by the
    ///   level that settled it and the case's context carried under the tree's
    ///   binders. Level zero is the scrutinee itself, carried under the binders
    ///   above its use, so no binding of it is minted. The root carries the
    ///   written origin, every other node the inserted match origin, and the
    ///   arms are recorded beside the root; a match whose first arm matches
    ///   anything is that arm's body. Nothing when the scrutinee, a reached
    ///   body or a needed answer did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses read each tree back out of the arena.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    /// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
    /// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
    /// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Computation(_))))]
    pub(super) fn mint_case(
        &self,
        case: CaseIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let Some(form) = self.cases.get(case.0)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let Maybe::Present(scrutinee) = self.value_at(form.scrutinee)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let mut bodies = Vec::with_capacity(form.bodies.len());
        for &body in &form.bodies {
            bodies.push(self.computation_at(body));
        }
        let mark = sink.arena.watermark();
        let motive = match form.answer {
            | Maybe::Present(answer) => match self.comp_type_at(answer.node) {
                | Maybe::Present(written) => {
                    let gap = Depth(
                        self.scope
                            .telescope_binders(form.frame)
                            .count()
                            .saturating_sub(self.scope.telescope_binders(answer.frame).count()),
                    );
                    let base = self.relocate(sink.arena, written, answer.frame, Binders::default());
                    Maybe::Present((base, gap))
                },
                | Maybe::Absent(reason) => Maybe::Absent(reason),
            },
            | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        let scrutinised = Scrutinised {
            scrutinee,
            outer: Depth(self.scope.telescope_binders(form.frame).count()),
        };
        let mut minted: Vec<Maybe<ComputationId, lowered::Absent>> = Vec::from_iter(
            form.tests
                .iter()
                .map(|_test| Maybe::Absent(lowered::Absent::Unminted)),
        );
        for (position, test) in form.tests.iter().enumerate().rev() {
            let id = mint_test(test, scrutinised, &bodies, &minted, motive, sink);
            if let Some(held) = minted.get_mut(position) {
                *held = id;
            }
        }
        let inserted = origin.inserted(Insertion::Match);
        let Some(&Maybe::Present(root)) = minted.first()
        else {
            record_since(
                sink,
                mark,
                inserted,
                Maybe::Absent(rooted::Absent::Unminted),
            );
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        if sink.arena.computations_since(mark).all(|id| id != root) {
            record_since(sink, mark, inserted, Maybe::Absent(rooted::Absent::Adopted));
            return Maybe::Present(Lowered::Computation(root));
        }
        record_since(sink, mark, inserted, Maybe::Present((root, origin)));
        sink.origins.record_case(root, form.origin.clone());

        Maybe::Present(Lowered::Computation(root))
    }
}

/// What every node of one match's tree reads: the scrutinee, and how many
/// term binders the case's frame holds.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the scrutinee is minted under the case's frame.
/// - executable: none — the record holds no scope to count against.
///
/// # Adequacy
/// - hypothesis: L3 — a leaf under a function's parameters reads them past the
///   tree's binders.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Scrutinised
{
    /// The scrutinee, under the case's frame.
    scrutinee: ValueId,
    /// The term binders of the case's frame.
    outer: Depth,
}

/// Mint one node of a match's tree over its already minted children.
///
/// # Specification
/// - requires: every child of `test` is minted in `minted` or absent.
/// - ensures: as [`Lowerer::mint_case`], for one node; nothing when a child,
///   the arm's body or a needed motive is absent.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::mint_case`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.computation(id).is_some()))]
fn mint_test(
    test: &Test,
    scrutinised: Scrutinised,
    bodies: &[Maybe<ComputationId, lowered::Absent>],
    minted: &[Maybe<ComputationId, lowered::Absent>],
    motive: Maybe<(CompTypeId, Depth), lowered::Absent>,
    sink: &mut Sink<'_>,
) -> Maybe<ComputationId, lowered::Absent>
{
    let child = |at: TestAt| {
        minted
            .get(at.0)
            .copied()
            .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
    };
    match *test {
        | Test::Pending => Maybe::Absent(lowered::Absent::Unminted),
        | Test::Stuck(hole) => Maybe::Present(sink.arena.computation_hole(hole)),
        | Test::Leaf {
            arm,
            depth,
            ref bindings,
        } => {
            let Some(&Maybe::Present(body)) = bodies.get(arm.0)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            if depth == Depth::default() && bindings.is_empty() {
                return Maybe::Present(body);
            }
            let mut environment =
                Vec::with_capacity(bindings.len().saturating_add(scrutinised.outer.0));
            for &level in bindings.iter().rev() {
                environment.push(level_value(sink.arena, scrutinised, depth, level));
            }
            for outer in 0 .. scrutinised.outer.0 {
                environment.push(variable(sink.arena, Depth(outer.saturating_add(depth.0))));
            }
            match gandr_core_term::substitute_environment(
                sink.arena,
                TermId::Computation(body),
                &environment,
            ) {
                | TermId::Computation(carried) => Maybe::Present(carried),
                | _ => Maybe::Absent(lowered::Absent::Unminted),
            }
        },
        | Test::Data {
            level,
            depth,
            ref branches,
        } => {
            let Maybe::Present((base, gap)) = motive
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let mut lowered_branches = Vec::with_capacity(branches.len());
            for &(arity, at) in branches {
                let Maybe::Present(mut branch) = child(at)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                for _field in 0 .. arity {
                    branch = sink.arena.computation_lambda(branch);
                }
                lowered_branches.push(branch);
            }
            let lift =
                u32::try_from(gap.0.saturating_add(depth.0).saturating_add(1)).unwrap_or(u32::MAX);
            let shifted = gandr_core_term::shift_comp_type(sink.arena, base, Binders::from(lift));
            let scrutinee = level_value(sink.arena, scrutinised, depth, level);
            Maybe::Present(
                sink.arena
                    .computation_data_case(scrutinee, shifted, lowered_branches),
            )
        },
        | Test::Boolean {
            level,
            depth,
            yes,
            no,
        } => match (child(yes), child(no)) {
            | (Maybe::Present(left), Maybe::Present(right)) => {
                let scrutinee = level_value(sink.arena, scrutinised, depth, level);
                Maybe::Present(sink.arena.computation_case(scrutinee, left, right))
            },
            | _ => Maybe::Absent(lowered::Absent::Unminted),
        },
        | Test::Integer {
            level,
            depth,
            ref literal,
            yes,
            no,
        } => {
            let (Maybe::Present(left), Maybe::Present(right)) = (child(yes), child(no))
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let Some(&equal) = PRELUDE.iter().find(|primitive| {
                matches!(primitive.operator(), Operator::Infix(spelled) if spelled == "==")
            })
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let scrutinee = level_value(sink.arena, scrutinised, depth, level);
            let compared = sink.arena.value_literal(literal.clone());
            let test = sink
                .arena
                .computation_primitive(equal, Arguments::Binary([scrutinee, compared]));
            let answer = variable(sink.arena, Depth::default());
            let branched = sink.arena.computation_case(answer, left, right);
            Maybe::Present(sink.arena.computation_bind(test, branched))
        },
    }
}

/// The value tree level `level` names under `depth` tree binders: the
/// scrutinee carried under them for level zero, and else the binder that
/// introduced the level.
///
/// # Specification
/// - requires: `level` is at most `depth`.
/// - ensures: the scrutinee itself at depth zero; its shift by `depth`
///   otherwise; the variable `depth - level` for a binder's level.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a nested switch reads its field and a leaf its binder.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[spec(ensures: |ret| arena.value(ret).is_some())]
fn level_value(
    arena: &mut CoreArena,
    scrutinised: Scrutinised,
    depth: Depth,
    level: TreeLevel,
) -> ValueId
{
    if level == TreeLevel::default() {
        if depth == Depth::default() {
            return scrutinised.scrutinee;
        }
        let lift = u32::try_from(depth.0).unwrap_or(u32::MAX);
        return gandr_core_term::shift_value(arena, scrutinised.scrutinee, Binders::from(lift));
    }

    variable(arena, Depth(depth.0.saturating_sub(level.0)))
}

/// The intuitionistic variable `index` binders out.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    index: Depth,
) -> ValueId
{
    arena.value_variable(
        Zone::Intuitionistic,
        DeBruijnIndex::from(u32::try_from(index.0).unwrap_or(u32::MAX)),
    )
}

/// The integer pattern `text` spells, written at `here`.
///
/// # Specification
/// - requires: `text` is a number's lexeme.
/// - ensures: the canonical integer the lexeme denotes.
/// - fails: the malformed-literal refusal for a lexeme that is not decimal
///   digits.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedLiteral`].
///
/// # Adequacy
/// - hypothesis: L3 — a literal column compares against the written integer.
/// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
#[spec(ensures: |ret| matches!(ret, Ok(Matcher::Integer(_)) | Err(LoweringRefusal::MalformedLiteral { .. })))]
fn integer<'source>(
    here: Site,
    text: gandr_surface_syntax::SourceFragment<'_>,
) -> Result<Matcher, LoweringRefusal<'source>>
{
    match parse_literal(Former::Number, text) {
        | Maybe::Present(literal) => Ok(Matcher::Integer(literal)),
        | Maybe::Absent(_) => Err(LoweringRefusal::MalformedLiteral {
            span: here.at.span,
            form: here.name,
        }),
    }
}

/// The node a matrix whose first row tests nothing reduces to: the hole it
/// matched through, or its arm with every variable at the level that settled
/// it.
///
/// # Specification
/// - requires: no column of `first` holds a pattern that tests.
/// - ensures: a stuck node on the first hole `first` passed; else a leaf of its
///   arm under `depth` binders, one level per arm variable in variable order,
///   the variables its binders in the remaining columns settle included.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a binder in the scrutinee's column and one in a field
///   each reach the arm body at their own level.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
#[spec(ensures: |ret| match first.stuck {
    | Maybe::Present(hole) => ret == Test::Stuck(hole),
    | Maybe::Absent(_) => matches!(ret, Test::Leaf { arm, depth: under, .. } if arm == first.arm && under == depth),
})]
fn leaf(
    patterns: &Written,
    first: &Row,
    levels: &[TreeLevel],
    depth: Depth,
) -> Test
{
    if let Maybe::Present(hole) = first.stuck {
        return Test::Stuck(hole);
    }
    let mut bindings = first.bindings.clone();
    for (&level, &pattern) in levels.iter().zip(&first.columns) {
        if let Some(&(_, Matcher::Binder(variable))) = patterns.shapes.get(pattern.0) {
            bindings.push((variable, level));
        }
    }
    bindings.sort_unstable();

    Test::Leaf {
        arm: first.arm,
        depth,
        bindings: bindings
            .into_iter()
            .map(|(_variable, level)| level)
            .collect(),
    }
}

/// Settle `held`, a pattern that matches anything, at `level` for `row`: a
/// binder binds its variable there, and a hole is the one the row passed
/// unless it passed an earlier one.
///
/// # Specification
/// - requires: `held` is the row's pattern in the column at `level`.
/// - ensures: one more binding for a binder; the hole recorded for a hole when
///   none was; nothing else changes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a binder and a hole each settle at a constructor's
///   column.
/// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
#[spec(
    captures: before = (row.bindings.len(), row.stuck),
    ensures: row.bindings.len() == before.0.saturating_add(usize::from(matches!(*held, Matcher::Binder(_))))
        && if let Matcher::Hole(hole) = *held && matches!(before.1, Maybe::Absent(_)) {
            row.stuck == Maybe::Present(hole)
        } else {
            row.stuck == before.1
        },
)]
fn through(
    row: &mut Row,
    held: &Matcher,
    level: TreeLevel,
)
{
    match *held {
        | Matcher::Binder(variable) => row.bindings.push((variable, level)),
        | Matcher::Hole(hole) => {
            if let Maybe::Absent(_) = row.stuck {
                row.stuck = Maybe::Present(hole);
            }
        },
        | Matcher::Wild
        | Matcher::Constructor { .. }
        | Matcher::Boolean(_)
        | Matcher::Integer(_) => {},
    }
}

/// `columns` with the entry at `column` replaced by `replacement`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the entries before `column`, then `replacement`, then the entries
///   after it; `columns` and then `replacement` when `column` is past the end.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a constructor's fields take its column's place.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[spec(ensures: |ret| ret.len() == columns.len().saturating_sub(usize::from(column.0 < columns.len())).saturating_add(replacement.len()))]
fn splice<Entry>(
    columns: &[Entry],
    column: Column,
    replacement: &[Entry],
) -> Vec<Entry>
where
    Entry: Copy,
{
    let mut spliced = Vec::with_capacity(columns.len().saturating_add(replacement.len()));
    spliced.extend(columns.iter().take(column.0).copied());
    spliced.extend_from_slice(replacement);
    spliced.extend(columns.iter().skip(column.0.saturating_add(1)).copied());

    spliced
}

/// Record `origin` for every node minted since `mark`, and the root's own
/// origin for the root.
///
/// # Specification
/// - requires: nothing has been recorded for a node minted since `mark`.
/// - ensures: every node minted since `mark` carries `origin`, in ascending
///   order in each family, except the root, which carries its own.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every node of a compiled tree has an origin.
/// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
#[spec(ensures: sink.arena.values_since(mark).all(|id| sink.origins.value(id) == Maybe::Present(origin))
    && sink.arena.computations_since(mark).all(|id| match root {
        | Maybe::Present((held, written)) if held == id => sink.origins.computation(id) == Maybe::Present(written),
        | _ => sink.origins.computation(id) == Maybe::Present(origin),
    }))]
fn record_since(
    sink: &mut Sink<'_>,
    mark: gandr_core_term::ArenaWatermark,
    origin: Origin,
    root: Maybe<(ComputationId, Origin), rooted::Absent>,
)
{
    for id in sink.arena.values_since(mark) {
        sink.origins.record_value(id, origin);
    }
    for id in sink.arena.computations_since(mark) {
        let recorded = match root {
            | Maybe::Present((held, written)) if held == id => written,
            | Maybe::Present(_) | Maybe::Absent(_) => origin,
        };
        sink.origins.record_computation(id, recorded);
    }
    for id in sink.arena.value_types_since(mark) {
        sink.origins.record_value_type(id, origin);
    }
    for id in sink.arena.comp_types_since(mark) {
        sink.origins.record_comp_type(id, origin);
    }
}

impl<'source> Lowerer<'_, 'source>
{
    /// Classify an instantiation, `f[<]`: the head of a recursive call
    /// claiming structural descent.
    ///
    /// # Specification
    /// - requires: `site` is an instantiation in term position.
    /// - ensures: an instantiation whose one resident is `<`, whose head is a
    ///   name the frame of a recursive function's fixpoint binds, and which
    ///   heads a call passing each of that function's parameters before the
    ///   last as itself and one argument more, stands as the variable the frame
    ///   binds and makes the function's fixpoint claim descent.
    /// - provides: the head of a recursive call.
    /// - fails: the reserved refusal for any other resident, a termination
    ///   claim the grammar reserves; the unadmitted refusal for an
    ///   instantiation whose head names no recursive function in scope or that
    ///   heads no call; the arity refusal, at the call, for a call passing
    ///   other than one argument per parameter; the non-uniform refusal, at the
    ///   argument, for a parameter before the last passed as anything but
    ///   itself; the wrong-sort refusal outside a head or value position; and
    ///   the allowance refusal from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The instantiation's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a descent call over one parameter and over a uniform
    ///   leading one lower to their variable; a productivity claim, a claim on
    ///   a function that is not recursive, a bare claim, a wrong argument count
    ///   and a varied leading parameter each refuse by their own boundary.
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_last_parameter`
    /// - witness: `lower::native::tests::a_recursive_call_passes_its_leading_parameters_unchanged`
    /// - witness: `lower::native::tests::only_the_descent_claim_heads_a_recursive_call`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Variable(_))))]
    pub(super) fn instantiation(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let head = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::BRACKET_OPEN)?;
        let resident = site.one(cursor.operands())?;
        if let Maybe::Present(_) = cursor.at(TileName::COMMA) {
            return Err(site.out(FragmentBoundary::Reserved));
        }
        closed(site, &mut cursor, TileName::BRACKET_CLOSE)?;
        exhausted(site, &cursor)?;
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, resident.node, &mut scratch);
        let descends = matches!(
            scratch.pieces.as_slice(),
            &[Piece::Tile { label, .. }] if label == TileName::LESS_THAN
        );
        self.scratch = scratch;
        read?;
        if !descends {
            let claim = Site {
                at: resident,
                ..site
            };
            return Err(claim.out(FragmentBoundary::Reserved));
        }
        let named = self.tree.node(head.node).is_some_and(|node| {
            matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::Name,
                    ..
                })
            )
        });
        if !named {
            return Err(site.out(FragmentBoundary::Unadmitted));
        }
        let name = self.name_at(head);
        let Maybe::Present(bound) = self.scope.resolve(frame, name, &mut self.fuel)?
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        let (Some(&recursion), Some(&descent)) = (
            self.recursions.get(&bound.binder),
            self.descents.get(&site.at.node),
        )
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        let uniform = stretch(&self.parameters, recursion.uniform);
        let arguments = stretch(&self.operands, descent.arguments);
        if arguments.len() != uniform.len().saturating_add(1) {
            return Err(descent
                .call
                .out(FragmentBoundary::Arity(OperandCount::from(arguments.len()))));
        }
        for (parameter, &argument) in uniform.iter().zip(arguments) {
            let Some(node) = self.tree.node(argument)
            else {
                return Err(descent.call.out(FragmentBoundary::NonUniform));
            };
            let passed = Placed::of(argument, node);
            let unchanged = match shape_of(self.pbg, node)? {
                | Shape::Form {
                    former: Former::Name,
                    ..
                } => {
                    let written = self.name_at(passed);
                    matches!(
                        self.scope.resolve(frame, written, &mut self.fuel)?,
                        Maybe::Present(found) if found.binder == parameter.frame
                    )
                },
                | Shape::Root | Shape::Form { .. } | Shape::Repair(_) | Shape::Layout => false,
            };
            if !unchanged {
                let varied = Site {
                    at: passed,
                    ..descent.call
                };
                return Err(varied.out(FragmentBoundary::NonUniform));
            }
        }
        if let Some(held) = self.recursions.get_mut(&bound.binder) {
            held.claimed = Claimed(true);
        }
        self.plan(site, Plan::Variable(bound.index));

        Ok(())
    }

    /// The evidence the fixpoint of `function` carries, when it recurses.
    ///
    /// # Specification
    /// - requires: the classification is complete, so every claim is recorded.
    /// - ensures: structural descent for a recursive tail one of whose calls
    ///   claims it, partial evidence for a recursive tail none of whose calls
    ///   does, and the plain absence for a tail that does not recurse.
    /// - provides: the claim [`Self::mint_function`] closes the fixpoint with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recursive function with a descent call and one with
    ///   no call each carry their own evidence.
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_last_parameter`
    #[spec(ensures: |ret| match function.recursion {
        | Maybe::Present(frame) => ret == Maybe::Present(if self.recursions.get(&frame).is_some_and(|held| held.claimed.0) { FixpointEvidence::StructuralDescent } else { FixpointEvidence::Partial }),
        | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
    })]
    pub(super) fn evidence(
        &self,
        function: &Function,
    ) -> Maybe<FixpointEvidence, recursion::Absent>
    {
        match function.recursion {
            | Maybe::Present(frame) => Maybe::Present(match self.recursions.get(&frame) {
                | Some(held) if held.claimed.0 => FixpointEvidence::StructuralDescent,
                | Some(_) | None => FixpointEvidence::Partial,
            }),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}
