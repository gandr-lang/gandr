//! The lowering itself: [`lower_module`], the [`LoweringBudget`] that bounds
//! it, and the two sweeps over the arena it is made of.
//!
//! # Two sweeps over one level-order arena, and no recursion anywhere
//!
//! The molded tree lays its nodes out in level order, so a walk in ascending
//! position order visits every parent before any of its children and a walk in
//! descending order visits every child before its parent. Lowering needs both
//! directions and gets each as a plain loop with no stack of its own.
//!
//! The **ascending sweep classifies**. A node's sort is fixed by its parent —
//! the same identifier is a binder, a type head or a term name depending on
//! where it sits — so the sort and the binder frame flow down. The sweep
//! dispatches every form on its grammar kind, reads its own tiles apart from
//! its operands, resolves every name, parses every literal, and decides every
//! refusal; what it decides for a form is recorded as that form's plan.
//!
//! The **descending sweep mints**. Every child is already lowered when its
//! parent is reached, which is exactly what the core arena's constructor-only
//! minting requires, so the sweep carries out each plan, records an origin,
//! and can fail at nothing. A node whose children did not lower simply does
//! not lower, which is how a refused declaration's subtree costs nothing.
//!
//! # A node's produced sort is a function of its own form
//!
//! The classification never pushes an expected sort into a place that has to
//! re-derive it: `+U` produces a value type and `-F` a computation type, a
//! thunk is a value and a lambda is a computation, and a grouping is whatever
//! it wraps. So a sort mismatch is decided where the node stands rather than
//! where its result is consumed, and every refusal carries the sort its own
//! position demanded.
//!
//! # Five insertions, by the sort of the position
//!
//! Where the source writes a value and the position reads a computation, or
//! the reverse, the fragment refuses — with five exceptions, each a site the
//! grammar's own shape names. An application's head reads a computation, and
//! a value standing there is forced; a function's result reads a computation
//! type, and a value type standing there gains a returner; a function's body is
//! a computation where the declaration takes a value, and is thunked; a type
//! standing where a value is read is quoted into its code; and a name standing
//! where a type is read, bound at a universe, is decoded out of it. Each
//! bridge is decided by the position and the name's binder, never searched
//! for, and its origin is the syntax node that demanded it, marked inserted,
//! so a reader can be shown the cast they did not write. Everywhere else the
//! mismatch stays a refusal: a lambda written where a value belongs is still
//! the author's mistake to suspend.
//!
//! # A parameter a type names binds a dependent arrow
//!
//! A function's declared type is a chain of arrows, one per parameter, and an
//! arrow binds its parameter in the codomain only when it is dependent. A
//! parameter whose name a later parameter's type or the result decodes is
//! recorded on its binder frame as the classification reads that type, so by
//! the time the signature is minted each frame knows whether its arrow binds.
//! A decode's code is the variable counted over the frames between it and its
//! binder that bind in the type: every frame a lambda binds, and a typed
//! parameter's only when its arrow is dependent.
//!
//! # One order of checks, the same at every form
//!
//! A form is checked in a fixed order, and the first check it fails is its
//! refusal: a kind the fragment has no reading for; a repair the parser made
//! among its children; a former of the wrong family for its position, a term
//! where a type belongs or the reverse; a reserved form; a former that does
//! not produce the sort its position demands; a variant of the form the
//! fragment does not admit, or a number of operands it does not take; and
//! last, the names and literals it holds.
//!
//! # The allowance is what bounds the work
//!
//! Every node visit and every binder frame walked spends one step of a caller's
//! allowance. Without it the binder-chain walk makes lowering quadratic in the
//! depth of a module nothing else bounds; with it the whole lowering is linear
//! in the allowance, and running out is an engine fault rather than a wrong
//! answer.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;
use core::ops::ControlFlow;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::FormRank;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeEntry;
use crate::attribute::AttributeRegistry;
use crate::attribute::AttributeTable;
use crate::attribute::PayloadForm;
use crate::attribute::PayloadVerdict;
use crate::attribute::RegisteredAttribute;
use crate::attribute::payload;
use crate::attribute::payload_form;
use crate::attribute::payload_verdict;
use crate::classify::FailureClass;
use crate::doc::Documentation;
use crate::doc::read_doc;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::import::ModuleImports;
use crate::module::Collected;
use crate::module::ComponentScope;
use crate::module::Container;
use crate::module::DataIndex;
use crate::module::DeclarationOutcome;
use crate::module::DeclarationParts;
use crate::module::DeclarationSlot;
use crate::module::Half;
use crate::module::LoweredDeclaration;
use crate::module::LoweredModule;
use crate::module::LoweredStructure;
use crate::module::ManifestComponent;
use crate::module::Member;
use crate::module::Operand;
use crate::module::Payload;
use crate::module::Role;
use crate::module::SlotIndex;
use crate::module::StructureIndex;
use crate::module::ValueComponent;
use crate::module::WrittenAttribute;
use crate::module::collect;
use crate::module::declaration_half;
use crate::module::manifest_type;
use crate::module::slot_refusal;
use crate::namespace::Binding;
use crate::namespace::NamePath;
use crate::namespace::PathResolution;
use crate::namespace::Recognition;
use crate::namespace::RecognitionSite;
use crate::namespace::Recognized;
use crate::namespace::Segment;
use crate::namespace::Trie;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::origin::OriginTable;
use crate::resolve::Bound;
use crate::resolve::Frame;
use crate::resolve::HeadArity;
use crate::resolve::OperandCount;
use crate::resolve::Scope;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;
use crate::resolve::TypeAtom;
use crate::resolve::TypeFormer;
use crate::resolve::binder_type;
use crate::resolve::type_atom;
use crate::resolve::type_former;

mod description;

mod exits;

mod native;

quenchant_shape::reason_enum! {
    /// Why a node has no lowered core node.
    pub mod lowered {
        /// The mint sweep produced nothing usable for the node.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node was not minted: unread, refused, or under a refusal.
            Unminted,
            /// The node was minted at another sort than the one asked for.
            OtherSort,
            /// The function tail states no type: a parameter or the result is
            /// untyped.
            Unstated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a lexeme denotes no literal.
    pub mod literal {
        /// The text is not a lexeme of the literal form asked about.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The text is not the form's lexeme.
            Malformed,
            /// The former is not a literal former at all.
            NotALiteral,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a tile in a block names no statement.
    pub mod statement {
        /// The tile opens none of the statements a block holds.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The tile is no statement's keyword.
            NotAKeyword,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node sees no manifest type component.
    pub mod scoped {
        /// The node lies in no module signature.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No signature type encloses the node.
            Unscoped,
        }
    }
}

/// The work one lowering may spend before it refuses.
///
/// One step is charged per node visited, per binder frame walked, per module
/// child and per attribute, so the allowance bounds the whole lowering rather
/// than any single sweep.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The limit is shared across the lowering run rather than renewed
///   for each pass.
/// - provides: A nominal bound on charged work, including the zero allowance.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The value has no work history to inspect; `Fuel::new`
///   and `Fuel::spend` check initialization and consumption.
///
/// # Adequacy
/// - hypothesis: L3 — the last allowed charge succeeds, the next charge names
///   the original limit, and a module exceeding its allowance is refused.
/// - witness: `lower::tests::the_last_step_of_an_allowance_is_spendable`
/// - witness: `lower::tests::a_step_past_the_allowance_is_refused`
/// - witness: `lower::tests::a_module_past_the_allowance_is_refused`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LoweringBudget(usize);

impl LoweringBudget
{
    /// The allowance a caller with no reason to bound the walk takes.
    pub const DEFAULT: Self = Self(1_000_000_usize);
}

impl From<usize> for LoweringBudget
{
    /// The allowance of `steps` steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: usize) -> Self
    {
        Self(steps)
    }
}

impl From<LoweringBudget> for usize
{
    /// The number of steps `budget` allows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(budget: LoweringBudget) -> Self
    {
        budget.0
    }
}

impl fmt::Display for LoweringBudget
{
    /// Writes the number of steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// One lowering's remaining allowance.
///
/// # Specification
/// - requires: Instances are created by new and changed only by spend.
/// - ensures: The remaining allowance never exceeds its original budget, and an
///   exhausted tank remains exhausted.
/// - provides: The shared state of all charged passes.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Type-level invariant expansion is unavailable in the
///   enabled specification facade; new and spend carry the executable state
///   relation.
///
/// # Adequacy
/// - hypothesis: L3 — initialization and the last-success/first-refusal
///   boundary distinguish off-by-one charging and preserve the reported
///   allowance.
/// - witness: `lower::tests::the_last_step_of_an_allowance_is_spendable`
/// - witness: `lower::tests::a_step_past_the_allowance_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Fuel
{
    /// How many steps are left.
    remaining: usize,
    /// The allowance the caller set, carried so a refusal can name it.
    budget: LoweringBudget,
}

impl Fuel
{
    /// A full tank at `budget`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the remaining allowance equals the supplied budget, whose
    ///   original value is retained.
    /// - provides: a shared tank for every charged pass.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the last permitted charge and first excess charge
    ///   distinguish initialization from an off-by-one allowance.
    /// - witness: `lower::tests::the_last_step_of_an_allowance_is_spendable`
    /// - witness: `lower::tests::a_step_past_the_allowance_is_refused`
    #[spec(
        ensures: |ret| ret.remaining == budget.0 && ret.budget.0 == budget.0,
    )]
    #[inline]
    #[must_use]
    pub const fn new(budget: LoweringBudget) -> Self
    {
        Self {
            remaining: budget.0,
            budget,
        }
    }

    /// Charge one step of work.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the remaining allowance is one lower on success, so a caller
    ///   that charges once per unit of work cannot outrun the allowance by more
    ///   than the unit it was charged for.
    /// - provides: the one place the allowance is spent, so no sweep can walk
    ///   uncharged.
    /// - fails: [`LoweringRefusal::BudgetExceeded`], naming the allowance the
    ///   caller set, once nothing remains; the tank stays empty, so every later
    ///   charge refuses alike.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance is spent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one checked subtraction, separated by the
    ///   boundary pair of the last successful charge and the first refused one
    ///   over an allowance of one, with the exact refusal variant and its
    ///   allowance asserted.
    /// - witness: `lower::tests::the_last_step_of_an_allowance_is_spendable`
    /// - witness: `lower::tests::a_step_past_the_allowance_is_refused`
    #[spec(
        captures: before = (self.remaining, self.budget),
        ensures: |ret| {
            self.budget == before.1
                && self.remaining == before.0.saturating_sub(1)
                && ret
                    == if before.0 == 0 {
                        Err(LoweringRefusal::BudgetExceeded { budget: before.1 })
                    }
                    else {
                        Ok(())
                    }
        },
    )]
    #[inline]
    pub fn spend<'refusal>(&mut self) -> Result<(), LoweringRefusal<'refusal>>
    {
        let Some(remaining) = self.remaining.checked_sub(1_usize)
        else {
            return Err(LoweringRefusal::BudgetExceeded {
                budget: self.budget,
            });
        };
        self.remaining = remaining;

        Ok(())
    }
}

/// How a node's position reads it.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A reading retains its positional sort and, for framed readings,
///   the binder frame used by its children.
/// - provides: The context for classification and insertion decisions.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The tag retains neither its source position nor its
///   scope; sort, family, frame and require specify its projections and
///   interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — lambda binding, forced heads and returner insertion
///   distinguish the framed term and type positions on the listed sources.
/// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Reading
{
    /// Not read: an own tile, layout, or a node under a form that refused.
    Unread,
    /// Read as a value type, under the binder frame named here.
    ValueType(Frame),
    /// Read as a computation type, under the binder frame named here.
    CompType(Frame),
    /// Read as a value, under the binder frame named here.
    Value(Frame),
    /// Read as a computation, under the binder frame named here.
    Computation(Frame),
    /// Read as an application's head: a computation under the binder frame
    /// named here, which a value standing here reaches by an inserted force.
    Head(Frame),
    /// Read as a function's result: a computation type under the binder frame
    /// named here, which a value type standing here reaches by an inserted
    /// returner.
    Result(Frame),
    /// Read as a function: the declaration form whose tail is one.
    Function,
}

impl Reading
{
    /// The sort a refusal at this position reports.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: unread and function positions report declarations, type
    ///   positions their own type sort, and heads/results the computation sort
    ///   they demand.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — wrong-sort refusals distinguish the expected value,
    ///   computation and type positions; function sites report a declaration.
    /// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
    /// - witness: `lower::tests::a_computation_codomain_of_a_static_pi_is_refused`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, ret),
                (Self::Unread | Self::Function, FragmentSort::Declaration)
                    | (Self::ValueType(_), FragmentSort::ValueType)
                    | (Self::CompType(_) | Self::Result(_), FragmentSort::CompType)
                    | (Self::Value(_), FragmentSort::Value)
                    | (
                        Self::Computation(_) | Self::Head(_),
                        FragmentSort::Computation
                    )
            )
        },
    )]
    const fn sort(self) -> FragmentSort
    {
        match self {
            | Self::Unread | Self::Function => FragmentSort::Declaration,
            | Self::ValueType(_frame) => FragmentSort::ValueType,
            | Self::CompType(_frame) | Self::Result(_frame) => FragmentSort::CompType,
            | Self::Value(_frame) => FragmentSort::Value,
            | Self::Computation(_frame) | Self::Head(_frame) => FragmentSort::Computation,
        }
    }

    /// The family of formers this reading admits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: type and result readings admit the type family, term and head
    ///   readings the term family, and unread/function readings neither.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — term and type fixtures exercise their reading
    ///   families; a type in value position is quoted rather than rejected as a
    ///   wrong family.
    /// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, ret),
                (Self::Unread | Self::Function, Family::Neither)
                    | (
                        Self::ValueType(_) | Self::CompType(_) | Self::Result(_),
                        Family::Type
                    )
                    | (
                        Self::Value(_) | Self::Computation(_) | Self::Head(_),
                        Family::Term
                    )
            )
        },
    )]
    const fn family(self) -> Family
    {
        match self {
            | Self::Unread | Self::Function => Family::Neither,
            | Self::ValueType(_frame) | Self::CompType(_frame) | Self::Result(_frame) => {
                Family::Type
            },
            | Self::Value(_frame) | Self::Computation(_frame) | Self::Head(_frame) => Family::Term,
        }
    }

    /// The binder frame this reading is under, the outermost for a reading
    /// that names none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: framed readings retain their frame, while unread and function
    ///   readings use the outermost frame.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda body resolves its binder at the exact index;
    ///   a reading without a binder is interpreted in the outermost scope.
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, ret),
                (
                    Self::Unread
                        | Self::Function
                        | Self::ValueType(Frame::Outermost)
                        | Self::CompType(Frame::Outermost)
                        | Self::Value(Frame::Outermost)
                        | Self::Computation(Frame::Outermost)
                        | Self::Head(Frame::Outermost)
                        | Self::Result(Frame::Outermost),
                    Frame::Outermost
                ) | (
                    Self::ValueType(Frame::Inner(_))
                        | Self::CompType(Frame::Inner(_))
                        | Self::Value(Frame::Inner(_))
                        | Self::Computation(Frame::Inner(_))
                        | Self::Head(Frame::Inner(_))
                        | Self::Result(Frame::Inner(_)),
                    Frame::Inner(_)
                )
            )
        },
    )]
    const fn frame(self) -> Frame
    {
        match self {
            | Self::Unread | Self::Function => Frame::Outermost,
            | Self::ValueType(frame)
            | Self::CompType(frame)
            | Self::Value(frame)
            | Self::Computation(frame)
            | Self::Head(frame)
            | Self::Result(frame) => frame,
        }
    }

    /// The universe a decode stands at when nothing was written to say, at
    /// the fuss-free level: the computation types where only a computation
    /// type is read, the value types everywhere else — a function's result
    /// included, which takes a value type under an inserted returner.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: only a computation-type reading defaults to the computation
    ///   universe; every other reading defaults to the value universe, all at
    ///   level zero.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — static application decodes at the written universe or
    ///   at the sort demanded by its position when no universe is written.
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    #[spec(
        ensures: |ret| {
            matches!(ret.level, LevelConstant::ZERO)
                && matches!(
                    (self, ret.sort),
                    (Self::CompType(_), GroundSort::Computation)
                        | (
                            Self::Unread
                                | Self::Function
                                | Self::ValueType(_)
                                | Self::Value(_)
                                | Self::Computation(_)
                                | Self::Head(_)
                                | Self::Result(_),
                            GroundSort::Value
                        )
                )
        },
    )]
    const fn positional_universe(self) -> Universe
    {
        match self {
            | Self::CompType(_) => Universe {
                sort: GroundSort::Computation,
                level: LevelConstant::ZERO,
            },
            | Self::Unread
            | Self::Function
            | Self::ValueType(_)
            | Self::Value(_)
            | Self::Computation(_)
            | Self::Head(_)
            | Self::Result(_) => Universe::FUSS_FREE,
        }
    }
}

/// Whether a former is a term, a type, or neither.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The family distinguishes term, type and non-expression forms
///   without forbidding the explicitly admitted type-in-value reading.
/// - provides: The coarse family check preceding former-specific admission.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No originating former is retained; `family_of` and
///   `classify_form` check classification and its quoting exception.
///
/// # Adequacy
/// - hypothesis: L3 — a computation in value position is refused, while a type
///   in value position can be quoted or used as a static code.
/// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
/// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
/// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Family
{
    /// Values and computations.
    Term,
    /// Value types and computation types.
    Type,
    /// Neither: a declaration or an attribute block.
    Neither,
}

/// How a form standing where a body ends treats that end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the variants partition what a form does at a body's end.
/// - provides: the vocabulary of the exit requirement.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exit, a match passing its end to its arms and a
///   returner ending a body distinguish the three.
/// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Ending
{
    /// The form is the exit: `return` or `become`.
    Exit,
    /// The form passes the end on to what ends it — a block's last
    /// computation, a match's arms, a grouping's operand, a lambda's own body,
    /// which answers the function type the end has — or is a hole, which the
    /// author has yet to fill.
    Passes,
    /// The form ends the body without an exit.
    Missing,
}

/// How `former`, standing where a body ends, treats that end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `return` and `become` are the exit; a block, a match, a grouping,
///   a lambda and a hole pass the end on; every other former is missing an
///   exit.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exits settle, a match ending in exits settles, and a
///   returner or a call ending a body is refused at itself.
/// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
#[spec(ensures: |ret| match former {
    Former::Exit | Former::Become => ret == Ending::Exit,
    Former::Block | Former::Case | Former::Parenthesized | Former::Lambda | Former::Hole => ret == Ending::Passes,
    _ => ret == Ending::Missing,
})]
fn ending(former: Former) -> Ending
{
    match former {
        | Former::Exit | Former::Become => Ending::Exit,
        | Former::Block | Former::Case | Former::Parenthesized | Former::Lambda | Former::Hole => {
            Ending::Passes
        },
        | Former::Name
        | Former::Constructor
        | Former::Number
        | Former::Text
        | Former::Unit
        | Former::Thunk
        | Former::Return
        | Former::Force
        | Former::Call
        | Former::Binary
        | Former::Unary
        | Former::Projection
        | Former::Instantiation
        | Former::TypeHead
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::LazyProductType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::Unadmitted => Ending::Missing,
    }
}

/// The family `former` belongs to.
///
/// # Specification
/// - requires: nothing.
/// - ensures: syntax formers are classified as terms, types or neither
///   independently of the demanded reading; static abstractions belong to the
///   type-former family.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — term and type formers distinguish ordinary interpretation
///   from the positional quote, including a static abstraction.
/// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
/// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
/// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
#[spec(
    ensures: |ret| {
        matches!(
            (former, ret),
            (
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
                    | Former::Return
                    | Former::Exit
                    | Former::Become
                    | Former::Force
                    | Former::Call
                    | Former::Binary
                    | Former::Unary
                    | Former::Projection
                    | Former::Case
                    | Former::Instantiation,
                Family::Term
            ) | (
                Former::TypeHead
                    | Former::Universe
                    | Former::TypeApplication
                    | Former::ThunkType
                    | Former::ReturnerType
                    | Former::ArrowType
                    | Former::ProductType
                    | Former::LazyProductType
                    | Former::ValueFunctionType
                    | Former::StaticAbstraction
                    | Former::ParenthesizedType,
                Family::Type
            ) | (
                Former::Declaration
                    | Former::AttributeBlock
                    | Former::Import
                    | Former::Module
                    | Former::Data
                    | Former::Unadmitted,
                Family::Neither
            )
        )
    },
)]
const fn family_of(former: Former) -> Family
{
    match former {
        | Former::Name
        | Former::Constructor
        | Former::Hole
        | Former::Number
        | Former::Text
        | Former::Parenthesized
        | Former::Unit
        | Former::Thunk
        | Former::Lambda
        | Former::Block
        | Former::Return
        | Former::Exit
        | Former::Become
        | Former::Force
        | Former::Call
        | Former::Binary
        | Former::Unary
        | Former::Projection
        | Former::Case
        | Former::Instantiation => Family::Term,
        | Former::TypeHead
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::LazyProductType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType => Family::Type,
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::Unadmitted => Family::Neither,
    }
}

/// The sort a former produces before positional bridges.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The tag describes the former’s own core family before any
///   positional bridge is inserted.
/// - provides: The input sort to the positional admission relation.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The producing former and demanded reading are not
///   retained; require states the complete admission and insertion relation.
///
/// # Adequacy
/// - hypothesis: L3 — explicit and inserted force remain distinct, and a
///   positive result acquires one returner rather than changing its source
///   type.
/// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Produced
{
    /// A value.
    Value,
    /// A computation.
    Computation,
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
}

/// What the mint sweep writes over a node's own core node.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A bare result is unchanged; an insertion request is interpreted
///   against the lowered child family.
/// - provides: The conversion to apply after the node’s own plan is minted.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The child is not retained on the tag; require selects
///   requests and `Sink::bridge` checks the result family and provenance.
///
/// # Adequacy
/// - hypothesis: L3 — forcing, returner insertion and quotation record the
///   inserted node while preserving the authored child’s origin.
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
/// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Bridge
{
    /// Nothing: the node's sort is the sort its position reads.
    Bare,
    /// The bridge from the node's sort to the one its position reads.
    Inserted(Insertion),
}

quenchant_shape::reason_enum! {
    /// Why a function's parameter or result carries no type.
    pub mod stated {
        /// The function tail leaves the type to a signature written apart.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source wrote no `: T` after the binder, or no `-> T` after
            /// the parameter list.
            Unstated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a function tail closes no fixpoint.
    pub mod recursion {
        /// The function names nothing recursively.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration was not written `def rec`.
            Plain,
        }
    }
}

/// A stretch of one of the lowerer's flat stores, which a plan reads its list
/// from rather than owning one.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The endpoints denote a half-open range in a caller-selected flat
///   store; they do not certify order or bounds by themselves.
/// - provides: A borrowed-store coordinate rather than an owned list.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No store is retained, and reversed ranges are admitted
///   inputs to stretch; the accessor checks the borrowed range and empty
///   fallback.
///
/// # Adequacy
/// - hypothesis: L3 — empty, full, interior, reversed and past-end ranges
///   distinguish a valid selection from an invalid range.
/// - witness: `lower::tests::recorded_ranges_keep_valid_members_and_reject_invalid_bounds`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Stretch
{
    /// The first entry.
    start: usize,
    /// One past the last entry.
    end: usize,
}

/// What a block statement does with the value its computation returns.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum StatementBinding
{
    /// `run x <- c ;` names the value for the rest of the block.
    Named,
    /// `c ;` discards it, splitting it as the unit under a binder no name
    /// reaches.
    Discarded,
    /// `run (x, y, …) <- c ;` splits the tuple it returns, under a binder no
    /// name reaches, into one named binder per component.
    Split(gandr_core_term::ComponentCount),
}

/// One `run x <- c ;` or `c ;` statement of a block.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The origin position supplies the bind’s origin while the bound
///   position supplies its computation; the rest says whether the block after
///   the statement is bound once or continues every local end of the
///   computation.
/// - provides: One source-ordered block binding.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Neither the source tree nor the lowered-node table is
///   retained; statement and `mint_block` check the coordinate roles.
///
/// # Adequacy
/// - hypothesis: L3 — consecutive run bindings scope over the following
///   computation and preserve their own source origins.
/// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
/// - witness: `lower::tests::a_discarded_statement_splits_its_unit`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Statement
{
    /// The origin of the bind: the `run` tile, or a discarded statement's
    /// computation.
    origin: NodeIndex,
    /// The computation whose returned value the statement binds.
    bound: NodeIndex,
    /// Whether the rest of the block names the value or discards it.
    binding: StatementBinding,
    /// Where the rest of the block goes.
    rest: exits::Rest,
}

/// A block: its statements, in source order, and its last computation.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The statement range precedes one final computation, which is not
///   replaced by an empty block result.
/// - provides: A block plan over the shared statement store.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The statement store and child results are absent; block
///   and `mint_block` check the range, final computation and bind order.
///
/// # Adequacy
/// - hypothesis: L3 — chained binds preserve order; a block without its final
///   computation is refused at the arity boundary.
/// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
/// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Block
{
    /// The block's statements, in the lowerer's statement store.
    statements: Stretch,
    /// The computation the block ends with.
    last: NodeIndex,
}

/// One parameter of a function tail.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The binder’s origin, introduced frame and optional written type
///   remain separate coordinates.
/// - provides: The data used to build a function’s lambda and signature spines.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The source, scope and lowered types are not retained;
///   function, `mint_function` and `mint_signature` interpret those
///   coordinates.
///
/// # Adequacy
/// - hypothesis: L3 — a typed parameter contributes to both spines, while an
///   unstated type does not prevent the function body from lowering.
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Parameter
{
    /// The binder tile, the origin of the parameter's lambda and arrow.
    binder: NodeIndex,
    /// The frame the parameter binds, which says whether a type names it.
    frame: ScopeId,
    /// The parameter's type, when the source wrote one.
    declared: Maybe<NodeIndex, stated::Absent>,
}

/// A universe as the source wrote it: its sort and its level, each defaulted
/// when left off.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The ground sort and nonnegative level are retained independently
///   after explicit or positional defaulting.
/// - provides: The universe at which a source type or code is read.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The spelling and reading position are absent;
///   `universe_of` and `positional_universe` state their distinct defaulting
///   rules.
///
/// # Adequacy
/// - hypothesis: L3 — bare, explicitly sorted and explicitly levelled spellings
///   keep their universes, including the universe of a decoded bound code.
/// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
/// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Universe
{
    /// The sort, `+` for the value types and `-` for the computation types.
    sort: GroundSort,
    /// The level.
    level: LevelConstant,
}

impl Universe
{
    /// The universe a bare `Type` names and an unwritten one defaults to:
    /// the value types at the fuss-free level.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value sort at level zero, not the computation sort.
    /// - provides: the universe of a bare `Type` and the context-free default.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the specification attribute does not accept
    ///   constant items; `universe_of` checks the resulting sort and level.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bare and explicitly sorted universe spellings
    ///   distinguish the value default from a computation universe.
    /// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
    const FUSS_FREE: Self = Self {
        sort: GroundSort::Value,
        level: LevelConstant::ZERO,
    };
}

/// The code a decode reads its type from, and the head a static application
/// applies.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A bound code retains the use frame and binder identity until
///   telescope indexing; a constant retains its admission coordinate.
/// - provides: The common head of static applications and decoded types.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The scope and declaration store needed for resolution
///   are absent; `resolve_name`, `static_application` and `mint_code` check
///   their uses.
///
/// # Adequacy
/// - hypothesis: L3 — bound and declared codes decode at their written universe
///   and static applications retain source argument order.
/// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
/// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Code
{
    /// A binder, named from a use site under the frame `from`, whose index is
    /// counted in the signature's telescope once every type has been read.
    Bound
    {
        /// The use site's frame.
        from: Frame,
        /// The binder's frame.
        binder: ScopeId,
    },
    /// A declaration at this admission position.
    Constant(ConstantIndex),
}

quenchant_shape::reason_enum! {
    /// Why a name resolves to nothing.
    pub mod named {
        /// Neither scope carries the name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No enclosing binder and no earlier declaration is named so.
            Unresolved,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a `run` statement's binder splits no tuple.
    pub mod untupled {
        /// The binder is a name, a wildcard or another pattern.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The binder is not a tuple pattern.
            OtherPattern,
        }
    }
}

/// What a name resolved to.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A binder retains its bound coordinate; a declaration retains its
///   constant and available written signature.
/// - provides: A resolved name that can become a term or static code.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No name, lookup frame or declaration table is retained;
///   `resolve_name` checks lookup and term checks the projection.
///
/// # Adequacy
/// - hypothesis: L3 — local binders and earlier declarations produce different
///   core references, and self-reference remains unresolved.
/// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
/// - witness: `lower::tests::an_earlier_declaration_resolves_as_a_constant`
/// - witness: `lower::tests::a_self_reference_is_unresolved`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Resolved
{
    /// An enclosing binder.
    Binder(Bound),
    /// A declaration strictly earlier than the name's own.
    Declaration
    {
        /// The declaration's admission position.
        constant: ConstantIndex,
        /// The type its signature was written with, when it has one.
        declared: Maybe<NodeIndex, binder_type::Absent>,
    },
}

impl Resolved
{
    /// The plan of the value the name stands for in term position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a resolved binder becomes a variable plan and a resolved
    ///   declaration a constant plan, retaining the respective index.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — binder uses become de Bruijn variables, while earlier
    ///   declarations become constants with their admission position.
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `modules::modules::a_backward_member_reference_resolves`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, &ret),
                (Self::Binder(_), &Plan::Variable(_))
                    | (Self::Declaration { .. }, &Plan::Constant(_))
            )
        },
    )]
    const fn term(self) -> Plan
    {
        match self {
            | Self::Binder(bound) => Plan::Variable(bound.index),
            | Self::Declaration { constant, .. } => Plan::Constant(constant),
        }
    }
}

/// A function tail's reading: `(params) -> T? { … }`.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The parameter range, optional result and block are retained
///   separately so an incomplete signature does not discard the body; a
///   recursive tail retains the frame binding its own name.
/// - provides: The two spines of a function tail.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The parameter store and lowered children are not
///   retained; function, `mint_function` and `mint_signature` check the stored
///   ranges and outcomes.
///
/// # Adequacy
/// - hypothesis: L3 — zero and multiple parameters preserve the body and
///   signature distinction, including tails with an unstated type.
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Function
{
    /// The parameters, in the lowerer's parameter store.
    parameters: Stretch,
    /// The result type, when the source wrote one.
    result: Maybe<NodeIndex, stated::Absent>,
    /// The body.
    block: Block,
    /// The frame binding the function's own name, between the last parameter
    /// and the ones before it, when the tail recurses.
    recursion: Maybe<ScopeId, recursion::Absent>,
}

/// What the mint sweep does for one node, decided by the classification.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The selected former retains the child coordinates and flat-store
///   ranges needed by the later mint sweep; transparent plans adopt their
///   child.
/// - provides: The classification-to-minting boundary without recursive source
///   re-reading.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The source, stores and child results are absent; the
///   readers specify each plan and `mint_plan` checks its output family and
///   transparent case.
///
/// # Adequacy
/// - hypothesis: L3 — the admitted term and type formers retain their concrete
///   core structure, while grouping adds no constructor.
/// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
/// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
/// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
#[derive(Clone, Debug, Eq, PartialEq)]
enum Plan
{
    /// Mint nothing.
    Unplanned,
    /// A value hole at its source occurrence.
    ValueHole(gandr_core_term::hole::HoleId),
    /// A computation hole at its source occurrence.
    CompHole(gandr_core_term::hole::HoleId),
    /// A variable at this index.
    Variable(DeBruijnIndex),
    /// A constant at this admission position.
    Constant(ConstantIndex),
    /// A table-typed native prelude thunk.
    Primitive(gandr_core_term::primitive::Primitive),
    /// A saturated table operation selected by source operator syntax.
    PrimitiveCall(
        gandr_core_term::primitive::Primitive,
        gandr_core_term::primitive::Arguments<NodeIndex>,
    ),
    /// The unit value.
    Unit,
    /// A literal, already parsed from the node's own text.
    Literal(Literal),
    /// A nullary type atom.
    Atom(TypeAtom),
    /// A universe.
    Universe(Universe),
    /// The type a code denotes, in the universe it was declared at: the code
    /// is the head applied statically to the arguments in the lowerer's
    /// operand store, none for a bare name.
    Decode(Code, Stretch, Universe),
    /// A static application of the head to the arguments in the lowerer's
    /// operand store, left to right.
    StaticApplication(Code, Stretch),
    /// A static lambda over its body.
    StaticLambda(NodeIndex),
    /// A type former over its argument.
    Former(TypeFormer, NodeIndex),
    /// An arrow over its domain and codomain.
    Arrow(NodeIndex, NodeIndex),
    /// A static Pi over its domain and codomain.
    StaticPi(NodeIndex, NodeIndex),
    /// One eager product of the value types in the lowerer's operand store,
    /// in order: an unparenthesized `*` chain is one former.
    Product(Stretch),
    /// A case of no arms over its scrutinee: the eliminator of the empty sum.
    EmptyCase(NodeIndex),
    /// One tuple of the values in the lowerer's operand store, in order.
    Tuple(Stretch),
    /// The thunked arrow from the domains in the lowerer's operand store to
    /// the returner of the codomain.
    ValueFunction(Stretch, NodeIndex),
    /// Adopt the child's lowered node unchanged.
    Transparent(NodeIndex),
    /// A thunk over its block.
    Thunk(Block),
    /// A returner over its value.
    Return(NodeIndex),
    /// A force over its value.
    Force(NodeIndex),
    /// A lambda over its block.
    Lambda(Block),
    /// A block's statements bound over its last computation.
    Block(Block),
    /// An application of its head to its arguments, left to right, in the
    /// lowerer's operand store.
    Application(NodeIndex, Stretch),
    /// A function tail's declared type and body.
    Function(Function),
    /// The nominal family declared at this admission position, over the
    /// arguments in the lowerer's operand store, left to right.
    Data(ConstantIndex, Stretch),
    /// A constructor applied to its fields.
    Constructor(native::Constructed),
    /// A match, compiled to the decision tree at this position of the
    /// lowerer's match store.
    Case(native::CaseIndex),
}

/// A node's lowered core node, at the sort its own form produced.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The family tag prevents reading a value as a computation or type;
///   a function can retain a body without a signature.
/// - provides: A family-indexed result for later parents and declaration
///   assembly.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Arena membership cannot be checked from numeric
///   identifiers alone; minting functions and family accessors state the
///   executable result relations.
///
/// # Adequacy
/// - hypothesis: L3 — completed and one-sided declarations preserve their
///   available halves, and function tails keep their body when a type is
///   absent.
/// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
/// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Lowered
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
    /// A function tail: its declared type, when it states one, and its body.
    Function
    {
        /// `+U (A1 -> … -> An -> C)`, from the parameter and result types.
        signature: Maybe<ValueTypeId, lowered::Absent>,
        /// `thunk (λ … λ. block)`.
        body: ValueId,
    },
}

/// Whether a form can stand where a value is expected.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The flag denotes admission to the syntactic value class, not
///   successful name resolution or type checking.
/// - provides: A value-form decision kept distinct from other Boolean
///   decisions.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The tested former is not retained; `is_value_form`
///   specifies the finite membership relation.
///
/// # Adequacy
/// - hypothesis: L3 — the finite former table distinguishes syntactic values
///   from computations and type forms before payload schema checks.
/// - witness: `lower::tests::only_the_value_forms_can_stand_as_a_payload`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ValueForm(bool);

/// Whether a spelling is a numeric lexeme with a fraction or an exponent.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The flag distinguishes a well-formed but unsupported fractional
///   spelling from a malformed integer spelling.
/// - provides: A lexical refusal decision distinct from numeric evaluation.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No input text is retained; fractional states the
///   executable numeric-language predicate.
///
/// # Adequacy
/// - hypothesis: L3 — decimal and exponent markers, missing fields, signs and
///   non-ASCII digits separate unsupported numbers from malformed lexemes.
/// - witness: `lower::tests::fractional_spellings_distinguish_unsupported_numbers_from_malformed_ones`
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Fractional(bool);

/// Whether a node lies inside an attribute payload, which lowers whatever
/// its declaration's outcome.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The flag marks nodes that remain eligible for minting despite an
///   enclosing declaration’s refusal.
/// - provides: The payload exception to ordinary refusal pruning.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The node and enclosing attributes are absent; seed,
///   `inherit_payload` and `mint_at` check marking and its effect.
///
/// # Adequacy
/// - hypothesis: L3 — an otherwise refused declaration retains its valid
///   attribute payload, and invalid attributes still receive their diagnostics.
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
/// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct InPayload(bool);

/// One form being classified: where it stands, what it is called, and how
/// its position reads it.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The location, form name and positional reading stay available
///   together when constructing a located refusal.
/// - provides: The source context shared by the form readers.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The grammar and source tree are not retained; readers
///   check admission and one checks the operand-count projection.
///
/// # Adequacy
/// - hypothesis: L3 — misplaced tiles, extra operands and wrong operand counts
///   retain their distinct refusal kinds and source positions.
/// - witness: `lower::tests::closing_and_exhaustion_distinguish_tiles_operands_and_gaps`
/// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
/// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Site
{
    /// The form.
    at: Placed,
    /// The form's kind, as a diagnostic writes it.
    name: FormName,
    /// How the form's position reads it.
    reading: Reading,
}

impl Site
{
    /// The refusal this form earns for leaving the fragment by `boundary`.
    ///
    /// # Specification
    /// trivial.
    const fn out<'source>(
        self,
        boundary: FragmentBoundary,
    ) -> LoweringRefusal<'source>
    {
        self.folded(self.name, boundary)
    }

    /// The refusal this form earns as the folded form `form`.
    ///
    /// # Specification
    /// - requires: the site identifies the refused source form.
    /// - ensures: the refusal retains the supplied form and boundary at the
    ///   site, with the sort demanded by its reading.
    /// - provides: a positional refusal for a nested former.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declined value, computation and type forms keep the
    ///   position’s sort, distinct from the former’s own family.
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
    #[spec(
        ensures: |ret| {
            matches!(
                (self.reading, ret),
                (
                    Reading::Unread | Reading::Function,
                    LoweringRefusal::OutOfFragment {
                        sort: FragmentSort::Declaration,
                        ..
                    }
                ) | (Reading::ValueType(_), LoweringRefusal::OutOfFragment {
                    sort: FragmentSort::ValueType,
                    ..
                }) | (
                    Reading::CompType(_) | Reading::Result(_),
                    LoweringRefusal::OutOfFragment {
                        sort: FragmentSort::CompType,
                        ..
                    }
                ) | (Reading::Value(_), LoweringRefusal::OutOfFragment {
                    sort: FragmentSort::Value,
                    ..
                }) | (
                    Reading::Computation(_) | Reading::Head(_),
                    LoweringRefusal::OutOfFragment {
                        sort: FragmentSort::Computation,
                        ..
                    }
                )
            )
        },
    )]
    const fn folded<'source>(
        self,
        form: FormName,
        boundary: FragmentBoundary,
    ) -> LoweringRefusal<'source>
    {
        LoweringRefusal::OutOfFragment {
            span: self.at.span,
            form,
            sort: self.reading.sort(),
            boundary,
        }
    }

    /// The refusal this form earns for `fault` at `span`.
    ///
    /// # Specification
    /// trivial.
    const fn fault<'source>(
        self,
        span: ByteSpan,
        fault: FormFault,
    ) -> LoweringRefusal<'source>
    {
        LoweringRefusal::MalformedForm {
            span,
            form: self.name,
            fault,
        }
    }

    /// The operand a one-operand hole holds, or the fault its run earns.
    ///
    /// # Specification
    /// - requires: `run` is a hole of this form.
    /// - ensures: the operand of a one-operand run; an empty run is a missing
    ///   operand at its gap, and a longer run an extra operand at its second.
    /// - provides: the one-hole reading every former shares.
    /// - fails: yields the missing-operand or extra-operand refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a hole not holding one form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — single-operand forms and an overfull hole distinguish
    ///   success from an arity fault at the extra operand.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
    #[spec(
        ensures: |ret| {
            matches!(
                (run, ret),
                (Run::One(_), Ok(_))
                    | (
                        Run::Empty(_),
                        Err(LoweringRefusal::MalformedForm {
                            fault: FormFault::MissingOperand,
                            ..
                        })
                    )
                    | (
                        Run::Several { .. },
                        Err(LoweringRefusal::MalformedForm {
                            fault: FormFault::ExtraOperand,
                            ..
                        })
                    )
            )
        },
    )]
    const fn one<'source>(
        self,
        run: Run,
    ) -> Result<Placed, LoweringRefusal<'source>>
    {
        match run {
            | Run::One(operand) => Ok(operand),
            | Run::Empty(gap) => Err(self.fault(gap, FormFault::MissingOperand)),
            | Run::Several { extra, .. } => Err(self.fault(extra.span, FormFault::ExtraOperand)),
        }
    }
}

/// The lowering's working state, shared by both sweeps.
///
/// # Specification
/// - requires: The grammar, tree and collected declarations describe one
///   lowering run.
/// - ensures: Per-node tables share the tree’s coordinate space; planned
///   flat-store ranges and declaration ownership are interpreted only in that
///   run.
/// - provides: The state linking collection, classification, minting and
///   assembly.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Type-level invariant expansion is unavailable in the
///   enabled specification facade; new and the phase boundaries carry
///   executable table and state relations.
///
/// # Adequacy
/// - hypothesis: L3 — declaration isolation, manifest dependencies, origins and
///   attribute retention are observed through parsed multi-declaration modules,
///   not inferred from table lengths alone.
/// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
/// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
struct Lowerer<'run, 'source>
{
    /// The grammar the tree was molded under.
    pbg: &'run Pbg,
    /// The tree being lowered.
    tree: &'run SyntaxTree<'source>,
    /// The module's declarations and the slot each node belongs to.
    collected: Collected<'source>,
    /// How each node's position reads it.
    readings: Vec<Reading>,
    /// What the mint sweep does for each node.
    plans: Vec<Plan>,
    /// What the mint sweep writes over each node's own core node.
    bridges: Vec<Bridge>,
    /// Each node's lowered core node.
    lowered: Vec<Maybe<Lowered, lowered::Absent>>,
    /// Which nodes lie inside an attribute payload.
    payload: Vec<InPayload>,
    /// The manifest type components each node sees, where it lies in a
    /// module signature.
    scopes: Vec<Maybe<ComponentScope, scoped::Absent>>,
    /// Each type head that named a manifest type component, with the held
    /// slot owning that component's type.
    manifests: Vec<(SlotIndex, NodeIndex)>,
    /// Each exported value component's full path, with the member's slot.
    exported: BTreeMap<NamePath, SlotIndex>,
    /// Each witness's body, by slot.
    witnessed: BTreeMap<SlotIndex, ValueId>,
    /// The arguments every planned application reads, stretch by stretch.
    operands: Vec<NodeIndex>,
    /// The statements every planned block reads, stretch by stretch.
    statements: Vec<Statement>,
    /// The parameters every planned function reads, stretch by stretch.
    parameters: Vec<Parameter>,
    /// The binder frames the lambdas, the parameters and the statements
    /// extended.
    scope: Scope<'source>,
    /// The outermost scope every declared name is declared in and every
    /// binder is reported against.
    recognition: Recognition,
    /// The remaining allowance.
    fuel: Fuel,
    /// The scratch reading of the form being classified.
    pieces: Pieces,
    /// The scratch reading of a written universe a decode reads its sort and
    /// level from.
    scratch: Pieces,
    /// Each constructor written under an annotation, with the annotation's
    /// type.
    classifiers: BTreeMap<NodeIndex, NodeIndex>,
    /// The type each computation position answers, where a function's result
    /// or a match's answer states it, or the block a statement's local ends
    /// continue answers.
    answers: BTreeMap<NodeIndex, native::Answer>,
    /// What every node's paths do with the body it stands in, surveyed before
    /// the classification reads it.
    leaves: Vec<exits::Leaves>,
    /// The computation positions where a path through a body ends: the last
    /// computation of a function's, a lambda's or a thunk's body, and what
    /// stands in tail position of one — a block's last computation, a match's
    /// arm, a grouping's operand. A form there that is not an exit is a
    /// missing one.
    exits: BTreeSet<NodeIndex>,
    /// The computation positions a path through a body passes, where an exit
    /// may stand: every position where a path ends, and every statement's
    /// computation in a block on a path, with what stands in tail position of
    /// one.
    exitable: BTreeSet<NodeIndex>,
    /// The computation positions whose local ends continue a block: the
    /// computation of a statement that holds an exit, and what stands in tail
    /// position of one.
    joined: BTreeSet<NodeIndex>,
    /// The exits read: every `return` and `become`, whose minted computation
    /// the commuting keeps where it stands.
    leaving: BTreeSet<NodeIndex>,
    /// Each block's last computation written as a statement, `c ;` before the
    /// closing brace, with the statement's span: admitted only as an exit.
    stated: BTreeMap<NodeIndex, ByteSpan>,
    /// The matches, each compiled to its decision tree.
    cases: Vec<native::CaseForm>,
    /// The position each lowered data declaration's signature takes, by its
    /// position in the collection's data list.
    signatures: BTreeMap<usize, DataIndex>,
    /// The position each described family's decoded signature takes, by its
    /// slot: a family the native data reading does not own.
    described: BTreeMap<SlotIndex, DataIndex>,
    /// The data declarations' signatures, by [`DataIndex`].
    data: Vec<Arc<DataSignature>>,
    /// Each recursive function's own name, by the frame that binds it.
    recursions: BTreeMap<ScopeId, native::Recursion>,
    /// Each recursive call, by its head: the instantiation whose claim checks
    /// it.
    descents: BTreeMap<NodeIndex, native::Descent>,
    /// Each callable operation's minted type and body, by slot.
    operated: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
}

/// Where the mint sweep writes: the arena and the origin table, with the
/// computations the commuting of early exits reads.
///
/// # Specification
/// - requires: The arena and origin table belong to the current minting run;
///   pre-existing arena nodes need not have entries in the new table.
/// - ensures: Minting operations pair newly allocated nodes with written or
///   inserted origins rather than treating an identifier as proof of ownership.
/// - provides: The shared targets of core allocation and provenance recording.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Allocation history is not a property of the pair of
///   references; value, computation, atom and bridge specify each recording
///   operation.
///
/// # Adequacy
/// - hypothesis: L3 — authored nodes, inserted force and derived function
///   thunks retain distinct provenance on the listed source forms.
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
struct Sink<'run>
{
    /// The arena the core nodes are minted into.
    arena: &'run mut CoreArena,
    /// The table every minted node's origin is recorded in.
    origins: &'run mut OriginTable,
    /// Every computation an exit minted, and each copy a match leaf made of
    /// one.
    exits: BTreeSet<ComputationId>,
    /// Every bind whose rest is distributed to its computation's local ends,
    /// and each copy a match leaf made of one, with its statement's origin.
    distributed: BTreeMap<ComputationId, Origin>,
}

/// Lower one module into `arena`, declaring its names over `outermost`.
///
/// # Specification
/// - requires: `tree` was molded under `pbg` over the source being lowered;
///   `arena` is the arena the lowered module's ids are read against; `budget`
///   bounds the work; `outermost` holds the seed tables and the shadow policy
///   the module's names are declared against.
/// - ensures: one declaration per distinct declared name, in admission order,
///   each carrying its admission position, the content identity of each of its
///   declaration forms, an origin token, and what its declarations amount to —
///   a completed pair, an uncompleted signature, a bodiless definition, or the
///   declaration's first refusal by arena position; a function tail is a
///   definition, and a signature too when it types every parameter and its
///   result. Every core node the module minted has an origin recorded, terms
///   and types alike, the force, thunk, returner, quote and decode the lowering
///   inserted marked as inserted, and every attribute the module carries is
///   resolved against the registry and filed under the content identity of the
///   declaration form it decorates. Every import is kept in source order with
///   its alias bound in the import scope and no address resolved. Every
///   declared name is declared over `outermost` in admission order, tagged with
///   its name's bytes, and every lambda, parameter and `run` binder is reported
///   against it; the outermost scope is returned with the module.
/// - provides: the whole surface-to-core step, in one pass over one tree with
///   one strictness and one verdict per name.
/// - fails: [`LoweringRefusal::GrammarMismatch`] when the tree was molded under
///   another grammar; [`LoweringRefusal::OutOfFragment`] and
///   [`LoweringRefusal::MalformedForm`] when the module's own shape is wrong —
///   a root that is not a module, a root child that is neither a declaration
///   nor an import, a declaration with no name, an import out of shape, or an
///   attribute block decorating nothing;
///   [`LoweringRefusal::DuplicateImportAlias`] when two imports bind one alias;
///   [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold; and
///   [`LoweringRefusal::BudgetExceeded`] when the work outruns `budget`. A
///   refusal inside a declaration is carried by that declaration instead —
///   [`LoweringRefusal::ShadowedBuiltin`], a declared name or a binder over a
///   builtin under the reject policy, included — so one bad declaration does
///   not hide the rest of the module.
/// - panics: none. Every tree lookup is checked and a position the tree does
///   not hold contributes nothing.
///
/// # Errors
/// [`LoweringRefusal::GrammarMismatch`] for a tree of another grammar,
/// [`LoweringRefusal::OutOfFragment`], [`LoweringRefusal::MalformedForm`] and
/// [`LoweringRefusal::DuplicateImportAlias`] for a module whose own shape is
/// not a list of declarations and well-formed imports,
/// [`LoweringRefusal::UnknownMold`] for a foreign mold, and
/// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
///
/// # Adequacy
/// - hypothesis: L2 — the listed parser fixtures compare produced core nodes
///   with pinned semantic goldens read from the receiving arena. L3 — the
///   listed malformed forms and budget boundaries distinguish located refusals,
///   declaration isolation and origin coverage. These observations cover those
///   fixtures and finite spelling tables, not every program or arbitrary
///   grammar extensions.
/// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
/// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
/// - witness: `lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
/// - witness: `lower::tests::an_arrow_lowers_under_a_thunk_type`
/// - witness: `lower::tests::every_type_atom_lowers_to_its_core_type`
/// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
/// - witness: `lower::tests::u_and_f_are_names`
/// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
/// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
/// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
/// - witness: `lower::tests::the_producer_does_not_admit_a_graded_bridge`
/// - witness: `lower::tests::a_graded_bridge_is_refused_by_name`
/// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
/// - witness: `lower::tests::an_earlier_declaration_resolves_as_a_constant`
/// - witness: `lower::tests::the_unit_keyword_lowers_to_the_unit_value`
/// - witness: `lower::tests::the_empty_parentheses_are_never_the_unit`
/// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
/// - witness: `lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
/// - witness: `lower::tests::force_and_application_lower_over_their_children`
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
/// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
/// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
/// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
/// - witness: `lower::tests::a_self_reference_is_unresolved`
/// - witness: `lower::tests::an_undefined_term_name_is_refused`
/// - witness: `lower::tests::an_undefined_type_head_is_refused`
/// - witness: `lower::tests::an_applied_nullary_head_is_refused`
/// - witness: `lower::tests::an_applied_head_no_former_answers_is_refused`
/// - witness: `lower::tests::the_reserved_lazy_product_is_declined`
/// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
/// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
/// - witness: `lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
/// - witness: `lower::tests::a_computation_codomain_of_a_static_pi_is_refused`
/// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
/// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
/// - witness: `static_operators::static_operators::the_relative_monad_witness_elaborates_identically_in_both_spellings`
/// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
/// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
/// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
/// - witness: `lower::tests::a_malformed_text_literal_is_refused`
/// - witness: `lower::tests::a_repaired_declaration_is_refused`
/// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
/// - witness: `lower::tests::a_tile_out_of_place_is_refused`
/// - witness: `lower::tests::a_root_that_is_not_a_module_is_refused`
/// - witness: `lower::tests::a_tree_of_another_grammar_is_refused`
/// - witness: `lower::tests::a_mold_the_grammar_does_not_hold_is_refused`
/// - witness: `lower::tests::an_unknown_attribute_is_refused_with_its_suggestion`
/// - witness: `lower::tests::an_attribute_written_twice_for_one_name_is_refused`
/// - witness: `lower::tests::a_schema_taking_a_payload_refuses_an_absent_one`
/// - witness: `lower::tests::a_non_value_payload_is_refused`
/// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
/// - witness: `lower::tests::a_marker_given_a_payload_is_refused`
/// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
/// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
/// - witness: `lower::tests::a_module_past_the_allowance_is_refused`
/// - witness: `namespace::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `namespace::namespace::an_import_binds_its_alias_and_resolves_no_address`
/// - witness: `namespace::namespace::source_import_without_alias_becomes_a_refusal`
/// - witness: `namespace::namespace::duplicate_source_import_alias_becomes_a_refusal`
/// - witness: `recognition::recognition::a_shadowed_builtin_is_reported_as_a_warning`
/// - witness: `recognition::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
/// - witness: `recognition::recognition::user_shadowing_is_the_only_observable_delta`
/// - witness: `recognition::recognition::a_binder_shadowing_a_builtin_is_rejected_under_policy`
#[spec(
    ensures: |ret| {
        let agrees = tree.grammar() == pbg.fingerprint();
        match ret.as_ref() {
            | Ok(module) => {
                agrees
                    && usize::from(module.origins().declaration_count())
                        == module.declarations().len()
                    && module.declarations().windows(2).all(|pair| match *pair {
                        | [ref left, ref right] => left.constant() < right.constant(),
                        | _ => false,
                    })
                    && module.declarations().iter().all(|declaration| {
                        match module.origins().declaration(declaration.origin()) {
                            | Maybe::Present(origin) => {
                                origin.span() == declaration.span()
                                    && tree.node(origin.node()).is_some()
                            },
                            | Maybe::Absent(_) => false,
                        }
                    })
            },
            | Err(&LoweringRefusal::GrammarMismatch {
                tree: found,
                grammar,
            }) => !agrees && found == tree.grammar() && grammar == pbg.fingerprint(),
            | Err(_) => agrees,
        }
    },
)]
#[inline]
pub fn lower_module<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    arena: &mut CoreArena,
    budget: LoweringBudget,
    outermost: Recognition,
) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
{
    if tree.grammar() != pbg.fingerprint() {
        return Err(LoweringRefusal::GrammarMismatch {
            tree: tree.grammar(),
            grammar: pbg.fingerprint(),
        });
    }
    let empty = |outermost| {
        LoweredModule::new(
            Vec::new(),
            Vec::new(),
            Vec::new(),
            AttributeTable::new(),
            OriginTable::new(),
            ModuleImports::new(),
            outermost,
        )
    };
    let Some(root) = tree.node(tree.root())
    else {
        return Ok(empty(outermost));
    };
    match shape_of(pbg, root)? {
        | Shape::Root => {},
        | Shape::Layout => return Ok(empty(outermost)),
        | Shape::Form { name, .. } => {
            return Err(LoweringRefusal::OutOfFragment {
                span: root.span(),
                form: name,
                sort: FragmentSort::Module,
                boundary: FragmentBoundary::WrongSort,
            });
        },
        | Shape::Repair(repair) => {
            return Err(LoweringRefusal::MalformedForm {
                span: root.span(),
                form: FormName::ROOT,
                fault: FormFault::Repaired(repair),
            });
        },
    }
    let mut fuel = Fuel::new(budget);
    let collected = collect(pbg, tree, &mut fuel)?;
    let mut lowerer = Lowerer::new(pbg, tree, collected, fuel, outermost);
    lowerer.declare();
    lowerer.seed()?;
    lowerer.survey()?;
    lowerer.classify()?;
    lowerer.propagate_manifests();
    let mut origins = OriginTable::new();
    let mut sink = Sink {
        arena,
        origins: &mut origins,
        exits: BTreeSet::new(),
        distributed: BTreeMap::new(),
    };
    lowerer.mint(&mut sink)?;
    lowerer.mint_data(&mut sink);
    lowerer.mint_descriptions(&mut sink)?;
    lowerer.mint_operations(&mut sink);
    let mut attributes = AttributeTable::new();
    lowerer.attribute(&mut attributes)?;
    let documentation = lowerer.document()?;
    let declarations = lowerer.assemble(&mut origins);
    let structures = lowerer.structures();
    let Lowerer {
        collected,
        recognition,
        data,
        ..
    } = lowerer;

    Ok(LoweredModule::new(
        declarations,
        data,
        structures,
        attributes,
        origins,
        collected.imports,
        recognition,
    )
    .with_descriptions(
        crate::description::DescriptionReport {
            declarations: collected.descriptions.into_values().collect(),
            diagnostics: collected.description_diagnostics,
        },
        collected.cells,
    )
    .with_documentation(documentation))
}

impl<'run, 'source> Lowerer<'run, 'source>
{
    /// The state for lowering `tree`, everything unread.
    ///
    /// # Specification
    /// - requires: the collected names and ownership positions describe this
    ///   tree.
    /// - ensures: one unread, unplanned, unminted, unbridged and unscoped cell
    ///   is allocated per syntax node; scratch stores and export indexes start
    ///   empty.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty working state is consumed by paired
    ///   declarations, nested modules and attributed refusals without leaking
    ///   prior node state.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `modules::modules::deeply_nested_modules_lower_and_resolve_at_every_depth`
    #[spec(
        ensures: |ret| {
            let count = usize::from(tree.node_count());
            ret.readings.len() == count
                && ret
                    .readings
                    .iter()
                    .all(|reading| matches!(*reading, Reading::Unread))
                && ret.plans.len() == count
                && ret
                    .plans
                    .iter()
                    .all(|plan| matches!(*plan, Plan::Unplanned))
                && ret.bridges.len() == count
                && ret.bridges.iter().all(|bridge| *bridge == Bridge::Bare)
                && ret.lowered.len() == count
                && ret
                    .lowered
                    .iter()
                    .all(|node| matches!(*node, Maybe::Absent(lowered::Absent::Unminted)))
                && ret.payload.len() == count
                && ret.payload.iter().all(|flag| !flag.0)
                && ret.scopes.len() == count
                && ret
                    .scopes
                    .iter()
                    .all(|scope| matches!(*scope, Maybe::Absent(_)))
                && ret.manifests.is_empty()
                && ret.exported.is_empty()
                && ret.witnessed.is_empty()
                && ret.operands.is_empty()
                && ret.statements.is_empty()
                && ret.parameters.is_empty()
                && ret.classifiers.is_empty()
                && ret.answers.is_empty()
                && ret.cases.is_empty()
                && ret.signatures.is_empty()
                && ret.data.is_empty()
                && ret.fuel == fuel
        },
    )]
    fn new(
        pbg: &'run Pbg,
        tree: &'run SyntaxTree<'source>,
        collected: Collected<'source>,
        fuel: Fuel,
        recognition: Recognition,
    ) -> Self
    {
        let count = usize::from(tree.node_count());
        let mut readings = Vec::new();
        readings.resize(count, Reading::Unread);
        let mut plans = Vec::new();
        plans.resize(count, Plan::Unplanned);
        let mut bridges = Vec::new();
        bridges.resize(count, Bridge::Bare);
        let mut lowered = Vec::new();
        lowered.resize(count, Maybe::Absent(lowered::Absent::Unminted));
        let mut payload = Vec::new();
        payload.resize(count, InPayload(false));
        let mut scopes = Vec::new();
        scopes.resize(count, Maybe::Absent(scoped::Absent::Unscoped));
        let mut leaves = Vec::new();
        leaves.resize(count, exits::Leaves::Never);

        Self {
            pbg,
            tree,
            collected,
            readings,
            plans,
            bridges,
            lowered,
            payload,
            scopes,
            manifests: Vec::new(),
            exported: BTreeMap::new(),
            witnessed: BTreeMap::new(),
            operands: Vec::new(),
            statements: Vec::new(),
            parameters: Vec::new(),
            scope: Scope::new(),
            recognition,
            fuel,
            pieces: Pieces::new(),
            scratch: Pieces::new(),
            classifiers: BTreeMap::new(),
            answers: BTreeMap::new(),
            leaves,
            exits: BTreeSet::new(),
            exitable: BTreeSet::new(),
            joined: BTreeSet::new(),
            leaving: BTreeSet::new(),
            stated: BTreeMap::new(),
            cases: Vec::new(),
            signatures: BTreeMap::new(),
            described: BTreeMap::new(),
            data: Vec::new(),
            recursions: BTreeMap::new(),
            descents: BTreeMap::new(),
            operated: BTreeMap::new(),
        }
    }

    /// Declare every top-level name over the outermost scope: each top-level
    /// declaration, then each top-level module with the namespace it exports.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: each top-level declaration is declared as a definition, and
    ///   each top-level module as a namespace governing exactly the components
    ///   it exports — a value component as a component, a nested module as a
    ///   namespace of its own, walked by an explicit worklist — each tagged
    ///   with its name tile's bytes and displacing the builtin subtree it lands
    ///   on; every exported value component's full path is recorded with its
    ///   member. A declaration the shadow policy refuses holds
    ///   [`LoweringRefusal::ShadowedBuiltin`] at its name, offered at its
    ///   declaration form, and a module so refused files a held slot carrying
    ///   it; the scope keeps the builtin. Module members and hidden members are
    ///   declared nowhere in the outermost scope.
    /// - provides: the outermost half of the module's names, and the governance
    ///   of every module path.
    /// - fails: never; a refusal is carried by its declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration over a builtin under each policy and
    ///   over nothing, asserted as the exact record, outcome and resolution; a
    ///   module exporting a component, hiding a member and exporting a nested
    ///   module, each path asserted as the exact resolution. Every exported
    ///   member is checked here once, after the last module, rather than by
    ///   each module's declaration.
    /// - witness: `recognition::recognition::a_shadowed_builtin_is_reported_as_a_warning`
    /// - witness: `recognition::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
    /// - witness: `recognition::recognition::user_shadowing_is_the_only_observable_delta`
    /// - witness: `modules::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `modules::modules::a_hidden_member_is_admitted_and_absent_from_the_namespace`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every slot and every module's exports; the check reads each appended slot and each exported member once"
        )
    )]
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.structures.len()),
        ensures: |_| {
            self.collected.structures.len() == before.1
                && self.collected.slots.len() >= before.0
                && self.collected.slots.iter().enumerate().skip(before.0).all(
                    |(index, slot)| {
                        slot.role == Role::Held
                            && slot.container == Container::TopLevel
                            && usize::from(slot.constant) == index
                            && matches!(
                                slot.refusal,
                                Maybe::Present((_, LoweringRefusal::ShadowedBuiltin { .. }))
                            )
                    },
                )
                && self.exported.values().all(|slot| {
                    self.collected
                        .slots
                        .get(usize::from(*slot))
                        .is_some_and(|entry| entry.role == Role::Declared)
                })
        },
    )]
    fn declare(&mut self)
    {
        for slot in &mut self.collected.slots {
            if slot.container != Container::TopLevel || slot.role != Role::Declared {
                continue;
            }
            let site = slot.named.span;
            let mut subtree = Trie::empty();
            let _fresh = subtree.insert(
                &NamePath::root(),
                Binding::new(Recognized::Definition, RecognitionSite::Source(site)),
            );
            let declared =
                self.recognition
                    .declare(Segment::from(slot.name.as_ref()), subtree, site);
            if let Err(_refused) = declared {
                slot.refuse(slot.introduced_by.node, LoweringRefusal::ShadowedBuiltin {
                    span: site,
                    name: slot.name,
                });
            }
        }
        let tops: Vec<StructureIndex> = self
            .collected
            .structures
            .iter()
            .enumerate()
            .filter(|&(_position, structure)| structure.container == Container::TopLevel)
            .map(|(position, _structure)| StructureIndex::from(position))
            .collect();
        for top in tops {
            self.declare_module(top);
        }
    }

    /// Declare the top-level module at `top` with the namespace it exports.
    ///
    /// # Specification
    /// - requires: `top` names a closed top-level module.
    /// - ensures: as [`Self::declare`] for one module.
    /// - provides: the per-module half of [`Self::declare`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — only exported value paths enter the module namespace,
    ///   while a hidden member stays absent and nested namespaces govern their
    ///   own paths. The predicate reads only the slot this call may append;
    ///   [`Self::declare`] checks every exported member once, after the last
    ///   module.
    /// - witness: `modules::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `modules::modules::a_hidden_member_is_admitted_and_absent_from_the_namespace`
    #[spec(
        captures: before = (self.exported.len(), self.collected.slots.len()),
        ensures: |_| {
            self.exported.len() >= before.0
                && self.collected.slots.len() >= before.1
                && self.collected.slots.len() <= before.1.saturating_add(1)
                && self.collected.slots.get(before.1 ..).is_some_and(|appended| {
                    appended.iter().all(|slot| {
                        slot.role == Role::Held
                            && matches!(
                                slot.refusal,
                                Maybe::Present((_, LoweringRefusal::ShadowedBuiltin { .. }))
                            )
                    })
                })
        },
    )]
    fn declare_module(
        &mut self,
        top: StructureIndex,
    )
    {
        let Some(module) = self.collected.structures.get(usize::from(top))
        else {
            return;
        };
        let (name, named, declared_by) = (module.name, module.named, module.declared_by);
        let root = NamePath::from(Vec::from([Segment::from(name.as_ref())]));
        let mut subtree = Trie::empty();
        let _root = subtree.insert(
            &NamePath::root(),
            Binding::new(
                Recognized::ModuleNamespace,
                RecognitionSite::Source(named.span),
            ),
        );
        let mut work = Vec::from([(top, NamePath::root())]);
        while let Some((structure, relative)) = work.pop() {
            let Some(entry) = self.collected.structures.get(usize::from(structure))
            else {
                continue;
            };
            for &export in &entry.exports {
                let (segment, site, recognized) = match export {
                    | Member::Slot(slot) => {
                        let Some(member) = self.collected.slots.get(usize::from(slot))
                        else {
                            continue;
                        };
                        (member.name, member.named.span, Recognized::ModuleComponent)
                    },
                    | Member::Module(nested) => {
                        let Some(member) = self.collected.structures.get(usize::from(nested))
                        else {
                            continue;
                        };
                        (member.name, member.named.span, Recognized::ModuleNamespace)
                    },
                };
                let path = relative.extended(&NamePath::from(Vec::from([Segment::from(
                    segment.as_ref(),
                )])));
                let _fresh = subtree.insert(
                    &path,
                    Binding::new(recognized, RecognitionSite::Source(site)),
                );
                match export {
                    | Member::Slot(slot) => {
                        let _replaced = self.exported.insert(root.extended(&path), slot);
                    },
                    | Member::Module(nested) => work.push((nested, path)),
                }
            }
        }
        let declared = self
            .recognition
            .declare(Segment::from(name.as_ref()), subtree, named.span);
        if let Err(_refused) = declared {
            let held = SlotIndex::from(self.collected.slots.len());
            let mut slot = DeclarationSlot {
                name,
                container: Container::TopLevel,
                role: Role::Held,
                constant: ConstantIndex::from(usize::from(held)),
                introduced_by: declared_by,
                named,
                signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                definition: Maybe::Absent(declaration_half::Absent::Unwritten),
                attributes: Vec::new(),
                docs: Vec::new(),
                refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
            };
            slot.refuse(declared_by.node, LoweringRefusal::ShadowedBuiltin {
                span: named.span,
                name,
            });
            self.collected.slots.push(slot);
        }
    }

    /// Report the binder `binder`, spelling `name`, against the outermost
    /// scope.
    ///
    /// # Specification
    /// - requires: `binder` is a lambda, parameter or `run` binder.
    /// - ensures: a binder over a builtin root is recorded under
    ///   warn-and-allow; the outermost scope is never changed.
    /// - provides: the binder half of the outermost report.
    /// - fails: [`LoweringRefusal::ShadowedBuiltin`] at the binder for a
    ///   builtin root under the reject policy.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ShadowedBuiltin`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda binder over a builtin under each policy,
    ///   asserted as the exact record and outcome.
    /// - witness: `recognition::recognition::a_binder_shadowing_a_builtin_is_rejected_under_policy`
    #[spec(
        ensures: |ret| {
            ret == Ok(())
                || ret
                    == Err(LoweringRefusal::ShadowedBuiltin {
                        span: binder.span,
                        name,
                    })
        },
    )]
    fn note_binder(
        &mut self,
        binder: Placed,
        name: SurfaceName<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let noted = self
            .recognition
            .note_binder(Segment::from(name.as_ref()), binder.span);
        match noted {
            | Ok(()) => Ok(()),
            | Err(_refused) => Err(LoweringRefusal::ShadowedBuiltin {
                span: binder.span,
                name,
            }),
        }
    }

    /// Read every declaration's operands at the sort the declaration demands.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: a signature's type is read as a value type, a definition's
    ///   body as a value in the outermost frame, a function tail's declaration
    ///   form as a function, which reads both halves it wrote at once, a
    ///   manifest type component's type as a value type, a data declaration's
    ///   parameter types, universe and field types as value types under the
    ///   parameters before them, and an attribute's payload as a value when its
    ///   form can stand as one; a witness's body, a member rather than a form,
    ///   is read nowhere. Every other node stays unread. Every written payload
    ///   is marked as one, whatever its form, and every signature type's root
    ///   with the manifest components it sees.
    /// - provides: the entry points of the ascending sweep.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a payload of a mold the
    ///   grammar does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] for a foreign mold.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signatures and definitions seed different readings;
    ///   manifest types and attribute payloads retain their own roots,
    ///   including attributes of refused declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body visits every slot and each of its attributes; the check reads each attribute's payload flag once"
        )
    )]
    #[spec(
        captures: before = (self.readings.len(), self.payload.len(), self.scopes.len()),
        ensures: |ret| {
            self.readings.len() == before.0
                && self.payload.len() == before.1
                && self.scopes.len() == before.2
                && (ret.is_err()
                    || self.collected.slots.iter().all(|slot| {
                        slot.attributes
                            .iter()
                            .all(|attribute| match attribute.payload {
                                | Payload::Unwritten => true,
                                | Payload::Written(payload) => self
                                    .payload
                                    .get(usize::from(payload.node))
                                    .is_none_or(|flag| flag.0),
                            })
                    }))
        },
    )]
    fn seed(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        let mut seeds: Vec<(NodeIndex, Reading)> = Vec::new();
        let mut payloads: Vec<NodeIndex> = Vec::new();
        for structure in &self.collected.structures {
            for manifest in &structure.types {
                seeds.push((manifest.defined.node, Reading::ValueType(Frame::Outermost)));
            }
        }
        for &(root, seen) in &self.collected.scopes {
            if let Some(held) = self.scopes.get_mut(usize::from(root)) {
                *held = Maybe::Present(seen);
            }
        }
        for slot in &self.collected.slots {
            if let Maybe::Present(half) = slot.signature
                && let Operand::Written(operand) = half.operand
            {
                seeds.push((operand.node, Reading::ValueType(Frame::Outermost)));
            }
            if let Maybe::Present(half) = slot.definition {
                match half.operand {
                    | Operand::Written(operand) => {
                        seeds.push((operand.node, Reading::Value(Frame::Outermost)));
                    },
                    | Operand::Function => {
                        seeds.push((half.declaration.node, Reading::Function));
                    },
                    | Operand::Member(_)
                    | Operand::Data(_)
                    | Operand::Operation
                    | Operand::Signature => {},
                }
            }
            for written in &slot.attributes {
                let Payload::Written(payload) = written.payload
                else {
                    continue;
                };
                payloads.push(payload.node);
                let (_shape, value) = self.payload_former(payload)?;
                if value.0 {
                    seeds.push((payload.node, Reading::Value(Frame::Outermost)));
                }
            }
        }
        self.seed_data(&mut seeds);
        self.seed_descriptions(&mut seeds)?;
        for (position, reading) in seeds {
            self.read(position, reading);
        }
        for position in payloads {
            if let Some(held) = self.payload.get_mut(usize::from(position)) {
                *held = InPayload(true);
            }
        }

        Ok(())
    }

    /// The form a payload is written as, and whether it can stand as a value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a known form yields its classification and value-form
    ///   verdict; a missing node yields layout and a negative verdict.
    /// - fails: with an unknown-mold refusal when the grammar cannot classify
    ///   the node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — value and non-value payloads take distinct schema
    ///   paths while every eligible former is covered by the value-form
    ///   classification table.
    /// - witness: `lower::tests::only_the_value_forms_can_stand_as_a_payload`
    /// - witness: `lower::tests::a_non_value_payload_is_refused`
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    #[spec(
        ensures: |ret| {
            ret == self.tree.node(payload.node).map_or(
                Ok((Shape::Layout, ValueForm(false))),
                |node| {
                    shape_of(self.pbg, node).map(|shape| {
                        (shape, match shape {
                            | Shape::Form { former, .. } => is_value_form(former),
                            | Shape::Root | Shape::Repair(_) | Shape::Layout => ValueForm(false),
                        })
                    })
                },
            )
        },
    )]
    fn payload_former(
        &self,
        payload: Placed,
    ) -> Result<(Shape, ValueForm), LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(payload.node)
        else {
            return Ok((Shape::Layout, ValueForm(false)));
        };
        let shape = shape_of(self.pbg, node)?;
        let value = match shape {
            | Shape::Form { former, .. } => is_value_form(former),
            | Shape::Root | Shape::Repair(_) | Shape::Layout => ValueForm(false),
        };

        Ok((shape, value))
    }

    /// The ascending sweep: classify every read node and plan its mint.
    ///
    /// # Specification
    /// - requires: the seeds have been read.
    /// - ensures: every node carries the reading its parent fixed, the owner
    ///   its parent belongs to and its parent's payload mark, every read form
    ///   has its plan or has offered its refusal to the declaration that owns
    ///   it, and a node under a form that refused stays unread, so a refusal
    ///   costs its subtree nothing.
    /// - provides: everything the mint sweep needs, so the mint sweep decides
    ///   nothing and can fail at nothing.
    /// - fails: every engine fault — [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] — aborts the sweep; every other
    ///   refusal is offered to its declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declaration refusals remain local while grammar and
    ///   budget faults abort the run; classification spends at least one step
    ///   per source node and does not allocate declaration slots.
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `lower::tests::a_tree_of_another_grammar_is_refused`
    /// - witness: `lower::tests::a_module_past_the_allowance_is_refused`
    #[spec(
        captures: before = (
            self.fuel.remaining,
            self.collected.slots.len(),
            self.plans.len(),
        ),
        ensures: |ret| {
            self.collected.slots.len() == before.1
                && self.plans.len() == before.2
                && self.fuel.remaining <= before.0
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err()
                    || self.fuel.remaining
                        <= before.0.saturating_sub(usize::from(self.tree.node_count())))
        },
    )]
    fn classify(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        for position in self.tree.positions() {
            self.fuel.spend()?;
            self.inherit_owner(position);
            self.inherit_payload(position);
            self.inherit_scope(position);
            if let Err(refusal) = self.classify_node(position) {
                if refusal.classify() == FailureClass::EngineFault {
                    return Err(refusal);
                }
                self.collected.offer(position, refusal);
            }
        }

        Ok(())
    }

    /// Give every unowned child of `position` the declaration its parent
    /// belongs to.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   owner is already set when its children are reached.
    /// - ensures: every child of an owned node is owned by the same slot,
    ///   unless the collection pass gave it an owner of its own — a signature
    ///   type written inside a member signature it does not type — so a refusal
    ///   anywhere under a declaration reaches the declaration its type or body
    ///   belongs to.
    /// - provides: the ownership half of the one-refusal-per-declaration rule.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refusal and payload nodes remain owned by the correct
    ///   declaration, including payloads lowered after their declaration is
    ///   refused.
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    #[spec(
        captures: before = (
            self.collected.owner.len(),
            self.collected.owner_of(position),
        ),
        ensures: |_| {
            self.collected.owner.len() == before.0
                && self.collected.owner_of(position) == before.1
                && (!matches!(before.1, Maybe::Present(_))
                    || self
                        .tree
                        .children(position)
                        .all(|child| matches!(self.collected.owner_of(child), Maybe::Present(_))))
        },
    )]
    fn inherit_owner(
        &mut self,
        position: NodeIndex,
    )
    {
        let Maybe::Present(slot) = self.collected.owner_of(position)
        else {
            return;
        };
        for child in self.tree.children(position) {
            if let Maybe::Absent(_) = self.collected.owner_of(child) {
                self.collected.own(child, slot);
            }
        }
    }

    /// Give every child of `position` the manifest type components `position`
    /// sees.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   scope is already set when its children are reached.
    /// - ensures: every node under a signature type's root sees that root's
    ///   manifest components, an inner root keeping its own.
    /// - provides: the scope a type head inside a signature resolves against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — manifest names in later component types resolve
    ///   through the enclosing signature prefix rather than ambient source
    ///   declarations.
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    #[spec(
        captures: before = (
            self.scopes.len(),
            self.scopes.get(usize::from(position)).copied(),
        ),
        ensures: |_| {
            self.scopes.len() == before.0
                && self.scopes.get(usize::from(position)).copied() == before.1
                && (!matches!(before.1, Some(Maybe::Present(_)))
                    || self.tree.children(position).all(|child| {
                        self.scopes
                            .get(usize::from(child))
                            .is_none_or(|scope| matches!(*scope, Maybe::Present(_)))
                    }))
        },
    )]
    fn inherit_scope(
        &mut self,
        position: NodeIndex,
    )
    {
        let Some(&Maybe::Present(seen)) = self.scopes.get(usize::from(position))
        else {
            return;
        };
        for child in self.tree.children(position) {
            if let Some(held) = self.scopes.get_mut(usize::from(child))
                && let Maybe::Absent(_) = *held
            {
                *held = Maybe::Present(seen);
            }
        }
    }

    /// Mark every child of `position` as inside a payload when `position` is.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   mark is already set when its children are reached.
    /// - ensures: every node under a written payload carries the mark, so the
    ///   mint sweep can tell a payload's subtree from the rest of its
    ///   declaration.
    /// - provides: the payload half of what the mint sweep skips.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused declaration still mints its attribute
    ///   payload without minting the refused signature or body.
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    #[spec(
        captures: before = (self.payload.len(), self.in_payload(position)),
        ensures: |_| {
            self.payload.len() == before.0
                && self.in_payload(position) == before.1
                && (!before.1.0
                    || self.tree.children(position).all(|child| {
                        self.payload
                            .get(usize::from(child))
                            .is_none_or(|flag| flag.0)
                    }))
        },
    )]
    fn inherit_payload(
        &mut self,
        position: NodeIndex,
    )
    {
        if !self.in_payload(position).0 {
            return;
        }
        for child in self.tree.children(position) {
            if let Some(held) = self.payload.get_mut(usize::from(child)) {
                *held = InPayload(true);
            }
        }
    }

    /// Whether `position` lies inside an attribute payload.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position yields its stored payload flag; an
    ///   out-of-range position is outside every payload.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refused declarations keep payload interpretation
    ///   separate from their signature and body.
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    #[spec(
        ensures: |ret| {
            ret.0
                == self
                    .payload
                    .get(usize::from(position))
                    .is_some_and(|flag| flag.0)
        },
    )]
    fn in_payload(
        &self,
        position: NodeIndex,
    ) -> InPayload
    {
        self.payload
            .get(usize::from(position))
            .copied()
            .unwrap_or(InPayload(false))
    }

    /// Classify one node at the reading its parent fixed.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order.
    /// - ensures: an unread node, an own tile, layout and repairs are skipped;
    ///   a read form is checked in the crate's one order and either planned,
    ///   with its operands read at the sorts it demands, or refused.
    /// - provides: the per-node half of [`Self::classify`].
    /// - fails: yields the form's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's first refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a read form gets its own plan or a located refusal;
    ///   unread source and grammar faults are not mistaken for admitted terms.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_mold_the_grammar_does_not_hold_is_refused`
    /// - witness: `lower::tests::a_repaired_declaration_is_refused`
    #[spec(
        captures: active = self.reading(position) != Reading::Unread
            && self
                .tree
                .node(position)
                .is_some_and(|node| matches!(shape_of(self.pbg, node), Ok(Shape::Form { .. }))),
        ensures: |ret| {
            (!active
                || ret.is_err()
                || self
                    .plans
                    .get(usize::from(position))
                    .is_some_and(|plan| *plan != Plan::Unplanned))
                && (self.reading(position) != Reading::Unread || ret.is_ok())
        },
    )]
    fn classify_node(
        &mut self,
        position: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let reading = self.reading(position);
        if reading == Reading::Unread {
            return Ok(());
        }
        let Some(node) = self.tree.node(position)
        else {
            return Ok(());
        };
        let Shape::Form { name, former } = shape_of(self.pbg, node)?
        else {
            return Ok(());
        };
        let site = Site {
            at: Placed::of(position, node),
            name,
            reading,
        };
        if former == Former::Unadmitted {
            return Err(site.out(FragmentBoundary::Unadmitted));
        }
        let mut pieces = core::mem::take(&mut self.pieces);
        let outcome = read_pieces(self.pbg, self.tree, position, &mut pieces)
            .and_then(|()| self.classify_form(site, former, &pieces));
        self.pieces = pieces;

        outcome
    }

    /// Classify one read form over its pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the form at `site`.
    /// - ensures: a repair refuses the form; a block's last computation written
    ///   as a statement that is not an exit refuses as an unadmitted expression
    ///   statement at the statement's bytes; a former of the wrong family for
    ///   the position refuses as the wrong sort, except a type standing where a
    ///   value is read, which is quoted; a form where a body ends that is
    ///   neither an exit nor a form that passes the end on — a block, a match,
    ///   a grouping — nor a hole refuses as a missing exit at its bytes; every
    ///   other former is handed to its own reader, a declaration form to the
    ///   function reader, the one reading of the family that seeds one.
    /// - provides: the dispatch on the grammar's named kind.
    /// - fails: yields the form's first refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's first refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repairs take precedence over admission, wrong
    ///   families are refused, and a type read as a value is the explicit
    ///   quoting exception.
    /// - witness: `lower::tests::a_repaired_declaration_is_refused`
    /// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    #[spec(
        ensures: |ret| {
            if let Maybe::Present(repaired) = pieces.repair {
                ret == Err(repaired.refusal(site.name))
            }
            else if let Some(&statement) = self.stated.get(&site.at.node)
                && ending(former) != Ending::Exit
            {
                ret == Err(LoweringRefusal::OutOfFragment {
                    span: statement,
                    form: FormName::EXPRESSION_STATEMENT,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::Unadmitted,
                })
            }
            else if family_of(former) != site.reading.family()
                && !(family_of(former) == Family::Type && matches!(site.reading, Reading::Value(_)))
            {
                ret == Err(site.out(FragmentBoundary::WrongSort))
            }
            else if self.exits.contains(&site.at.node) && ending(former) == Ending::Missing {
                ret == Err(LoweringRefusal::MissingExit { span: site.at.span })
            }
            else {
                ret.is_err()
                    || self
                        .plans
                        .get(usize::from(site.at.node))
                        .is_some_and(|plan| *plan != Plan::Unplanned)
            }
        },
    )]
    fn classify_form(
        &mut self,
        site: Site,
        former: Former,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(site.name));
        }
        let family = family_of(former);
        if let Some(&statement) = self.stated.get(&site.at.node)
            && ending(former) != Ending::Exit
        {
            return Err(LoweringRefusal::OutOfFragment {
                span: statement,
                form: FormName::EXPRESSION_STATEMENT,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::Unadmitted,
            });
        }
        let quoted = family == Family::Type && matches!(site.reading, Reading::Value(_));
        if family != site.reading.family() && !quoted {
            return Err(site.out(FragmentBoundary::WrongSort));
        }
        if self.exits.contains(&site.at.node) && ending(former) == Ending::Missing {
            return Err(LoweringRefusal::MissingExit { span: site.at.span });
        }
        let cursor = Cursor::new(&pieces.pieces, site.at.span);
        match former {
            | Former::Name => self.name(site),
            | Former::Constructor => self.constructor(site),
            | Former::Hole => {
                let identity = u32::try_from(usize::from(site.at.node)).map_err(|_overflow| {
                    LoweringRefusal::BudgetExceeded {
                        budget: self.fuel.budget,
                    }
                })?;
                let hole = gandr_core_term::hole::HoleId::from(identity);
                let plan = if matches!(site.reading, Reading::Computation(_) | Reading::Head(_)) {
                    let _frame = self.require(site, Produced::Computation)?;
                    Plan::CompHole(hole)
                }
                else {
                    let _frame = self.require(site, Produced::Value)?;
                    Plan::ValueHole(hole)
                };
                self.plan(site, plan);
                Ok(())
            },
            | Former::Number => self.number(site),
            | Former::Text => self.text(site, pieces),
            | Former::Parenthesized => self.parenthesized(site, cursor),
            | Former::Unit => {
                let _frame = self.require(site, Produced::Value)?;
                self.plan(site, Plan::Unit);
                Ok(())
            },
            | Former::Thunk => self.thunk(site, cursor),
            | Former::Lambda => self.lambda(site, cursor),
            | Former::Block => self.sequenced(site, cursor),
            | Former::Return => self.keyed(site, cursor, TileName::PURE),
            | Former::Exit => self.keyed(site, cursor, TileName::RETURN),
            | Former::Become => self.tail_call(site, cursor),
            | Former::Force => self.keyed(site, cursor, TileName::FORCE),
            | Former::Call => self.call(site, cursor),
            | Former::Case => self.case(site, cursor),
            | Former::Binary | Former::Unary => self.operator(site, pieces),
            | Former::Projection => self.projection(site, pieces),
            | Former::TypeHead => self.type_head(site),
            | Former::Universe => self.universe(site, cursor),
            | Former::TypeApplication => self.type_application(site, cursor),
            | Former::ThunkType | Former::ReturnerType => self.formed_type(site, cursor),
            | Former::ArrowType => self.arrow(site, cursor),
            | Former::ProductType => self.product(site, cursor),
            | Former::LazyProductType => Err(site.out(FragmentBoundary::Reserved)),
            | Former::ValueFunctionType => self.value_function(site, cursor),
            | Former::StaticAbstraction => self.static_abstraction(site, cursor),
            | Former::ParenthesizedType => self.parenthesized_type(site, cursor),
            | Former::Instantiation => self.instantiation(site, cursor),
            | Former::Declaration | Former::Module => self.function(site, cursor),
            | Former::AttributeBlock | Former::Import | Former::Data | Former::Unadmitted => {
                Err(site.out(FragmentBoundary::WrongSort))
            },
        }
    }

    /// The binder frame of a form whose position demands `produced`, with the
    /// bridge the position writes over it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the frame the position carries when it reads the produced
    ///   sort. An application's head reads a computation and reaches a value by
    ///   a force; a function's result reads a computation type and reaches a
    ///   value type by a returner; a value position reaches a type of either
    ///   sort by a quote; the bridge is recorded for the form's node, and every
    ///   other match records none.
    /// - provides: the sort check every former takes, and the three insertions
    ///   decided by the sort of a position.
    /// - fails: yields the wrong-sort refusal when the position reads another
    ///   sort no bridge reaches.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each bridge separated from its bare neighbour: a
    ///   value and a computation at a head, a value type and a computation type
    ///   at a result, a value and a type at a value, each asserted through the
    ///   lowered node and its origin's provenance.
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    #[spec(
        ensures: |ret| {
            let expected = match (site.reading, produced) {
                | (Reading::Value(frame), Produced::Value)
                | (Reading::Computation(frame) | Reading::Head(frame), Produced::Computation)
                | (Reading::ValueType(frame), Produced::ValueType)
                | (Reading::CompType(frame) | Reading::Result(frame), Produced::CompType) => {
                    Some((frame, Bridge::Bare))
                },
                | (Reading::Head(frame), Produced::Value) => {
                    Some((frame, Bridge::Inserted(Insertion::Force)))
                },
                | (Reading::Result(frame), Produced::ValueType) => {
                    Some((frame, Bridge::Inserted(Insertion::Returner)))
                },
                | (Reading::Value(frame), Produced::ValueType | Produced::CompType) => {
                    Some((frame, Bridge::Inserted(Insertion::Quote)))
                },
                | _ => None,
            };
            match expected {
                | Some((frame, bridge)) => {
                    ret == Ok(frame)
                        && self
                            .bridges
                            .get(usize::from(site.at.node))
                            .is_none_or(|held| *held == bridge)
                },
                | None => ret == Err(site.out(FragmentBoundary::WrongSort)),
            }
        },
    )]
    fn require(
        &mut self,
        site: Site,
        produced: Produced,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let (frame, bridge) = match (site.reading, produced) {
            | (Reading::Value(frame), Produced::Value)
            | (Reading::Computation(frame) | Reading::Head(frame), Produced::Computation)
            | (Reading::ValueType(frame), Produced::ValueType)
            | (Reading::CompType(frame) | Reading::Result(frame), Produced::CompType) => {
                (frame, Bridge::Bare)
            },
            | (Reading::Head(frame), Produced::Value) => {
                (frame, Bridge::Inserted(Insertion::Force))
            },
            | (Reading::Result(frame), Produced::ValueType) => {
                (frame, Bridge::Inserted(Insertion::Returner))
            },
            | (Reading::Value(frame), Produced::ValueType | Produced::CompType) => {
                (frame, Bridge::Inserted(Insertion::Quote))
            },
            | _ => return Err(site.out(FragmentBoundary::WrongSort)),
        };
        if let Some(held) = self.bridges.get_mut(usize::from(site.at.node)) {
            *held = bridge;
        }

        Ok(frame)
    }

    /// What `name`, written at `site` under `frame`, resolves to: the
    /// innermost binder carrying it, else a declaration strictly earlier than
    /// the one `site` belongs to, or that declaration itself when it is a data
    /// declaration, searched from that declaration's own module outward to
    /// the top level.
    ///
    /// # Specification
    /// - requires: `site` is the name's own node.
    /// - ensures: the binder with its index and its written type; else the
    ///   first module, innermost first, whose body declares the name: its
    ///   member when that member's admission position is strictly earlier, and
    ///   the forward-member refusal when it is not; else a top-level
    ///   declaration strictly earlier, with its admission position and its
    ///   signature's written type; the data declaration `site` belongs to,
    ///   untyped, for its own name: a family's self reference, whose positivity
    ///   the checker judges; else a callable operation admitted strictly
    ///   earlier, untyped; the unresolved absence when nothing answers.
    /// - provides: the one resolution term names, capitalised names and type
    ///   heads share.
    /// - fails: [`LoweringRefusal::UnmarkedSelfReference`] for the name a
    ///   recursive function's fixpoint binds, which only a descent claim reads;
    ///   [`LoweringRefusal::ForwardMemberReference`] for a member of an
    ///   enclosing module declared at or after the referring declaration;
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnmarkedSelfReference`],
    /// [`LoweringRefusal::ForwardMemberReference`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member named by an earlier sibling, by a later one,
    ///   by itself, from a nested module and from the top level, each asserted
    ///   as the exact constant or refusal.
    /// - witness: `modules::modules::a_forward_member_reference_is_refused_by_position`
    /// - witness: `modules::modules::a_backward_member_reference_resolves`
    /// - witness: `lower::tests::a_self_reference_is_unresolved`
    /// - witness: `lower::native::tests::a_recursive_family_names_itself_in_its_fields`
    /// - witness: `lower::tests::an_earlier_declaration_resolves_as_a_constant`
    /// - witness: `lower::native::tests::an_unmarked_self_reference_is_refused_with_its_claim`
    #[spec(
        captures: before = self.fuel.remaining,
        ensures: |ret| {
            self.fuel.remaining <= before
                && match ret {
                    | Ok(Maybe::Present(Resolved::Declaration { constant, declared })) => {
                        matches!(self.collected.owner_of(site.at.node), Maybe::Present(own) if self.collected.slots.get(usize::from(constant)).is_some_and(|entry| entry.name == name && entry.constant == constant && (usize::from(constant) < usize::from(own) || (usize::from(constant) == usize::from(own) && matches!(entry.definition, Maybe::Present(Half { operand: Operand::Data(_), .. })))) && declared == match entry.signature { Maybe::Present(Half { operand: Operand::Written(written), .. }) => Maybe::Present(written.node), _ => Maybe::Absent(binder_type::Absent::Untyped) }))
                    },
                    | Err(
                        LoweringRefusal::ForwardMemberReference {
                            span,
                            name: refused,
                            ..
                        }
                        | LoweringRefusal::UnmarkedSelfReference {
                            span,
                            name: refused,
                        },
                    ) => span == site.at.span && refused == name,
                    | _ => true,
                }
        },
    )]
    fn resolve_name(
        &mut self,
        site: Site,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        if let Maybe::Present(bound) = self.scope.resolve(frame, name, &mut self.fuel)? {
            if self.recursions.contains_key(&bound.binder) {
                return Err(LoweringRefusal::UnmarkedSelfReference {
                    span: site.at.span,
                    name,
                });
            }
            return Ok(Maybe::Present(Resolved::Binder(bound)));
        }
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        let mut container = self
            .collected
            .slots
            .get(usize::from(own))
            .map_or(Container::TopLevel, |slot| slot.container);
        loop {
            self.fuel.spend()?;
            if let Some(&target) = self.collected.by_name.get(&(container, name))
                && let Some(entry) = self.collected.slots.get(usize::from(target))
            {
                let own_family = target == own
                    && matches!(
                        entry.definition,
                        Maybe::Present(Half {
                            operand: Operand::Data(_),
                            ..
                        })
                    );
                if target < own || own_family {
                    let declared = match entry.signature {
                        | Maybe::Present(Half {
                            operand: Operand::Written(written),
                            ..
                        }) => Maybe::Present(written.node),
                        | Maybe::Present(_) | Maybe::Absent(_) => {
                            Maybe::Absent(binder_type::Absent::Untyped)
                        },
                    };
                    return Ok(Maybe::Present(Resolved::Declaration {
                        constant: entry.constant,
                        declared,
                    }));
                }
                if let Container::Module(_) = container {
                    return Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name,
                        declared: entry.named.span,
                    });
                }
            }
            let Container::Module(module) = container
            else {
                if let Some(&target) = self.collected.operation_names.get(&name)
                    && target < own
                    && let Some(entry) = self.collected.slots.get(usize::from(target))
                {
                    return Ok(Maybe::Present(Resolved::Declaration {
                        constant: entry.constant,
                        declared: Maybe::Absent(binder_type::Absent::Untyped),
                    }));
                }
                return Ok(Maybe::Absent(named::Absent::Unresolved));
            };
            container = self
                .collected
                .structures
                .get(usize::from(module))
                .map_or(Container::TopLevel, |structure| structure.container);
        }
    }

    /// Classify a term name.
    ///
    /// # Specification
    /// - requires: `site` is an identifier in term position.
    /// - ensures: a name standing as a value resolves against the binder frame
    ///   first and the declarations strictly earlier than its own second, and
    ///   is planned as the variable or constant it resolved to.
    /// - provides: the term-name half of resolution.
    /// - fails: yields the wrong-sort refusal for a name in computation
    ///   position, and the unresolved-name refusal when no scope answers;
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — local binders and earlier declarations resolve to
    ///   their own variable or constant, while an undefined name keeps its
    ///   source span.
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `lower::tests::an_undefined_term_name_is_refused`
    /// - witness: `modules::modules::a_backward_member_reference_resolves`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Variable(_) | Plan::Constant(_) | Plan::Primitive(_)))
                )
        },
    )]
    fn name(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let name = self.name_at(site.at);
        match self.resolve_name(site, frame, name)? {
            | Maybe::Present(resolved) => {
                self.plan(site, resolved.term());
                Ok(())
            },
            | Maybe::Absent(_) => {
                let path = NamePath::from(Vec::from([Segment::from(name.as_ref())]));
                if let PathResolution::Complete(Recognized::BuiltinPrimitive {
                    primitive, ..
                }) = self.recognition.resolve_path(&path)
                {
                    self.plan(site, Plan::Primitive(primitive));
                    Ok(())
                }
                else {
                    Err(LoweringRefusal::UnresolvedName {
                        span: site.at.span,
                        name,
                    })
                }
            },
        }
    }

    /// Classify a capitalised name in term position.
    ///
    /// # Specification
    /// - requires: `site` is a constructor in term position.
    /// - ensures: a constructor of a data family declared strictly earlier
    ///   stands as that constructor applied to no fields; otherwise a data
    ///   family an earlier declaration answers stands as its type, which a
    ///   value position quotes, and any other name a binder or an earlier
    ///   declaration answers stands as the value it resolved to; otherwise a
    ///   type atom, or `Type` for the value universe at the fuss-free level,
    ///   stands as a type, which a value position quotes.
    /// - provides: the term-position spelling of a type, of a nullary
    ///   constructor, and of a declaration named with a capital.
    /// - fails: yields the wrong-sort refusal for a resolved name or a type
    ///   where its position reads neither; a constructor's own refusals; the
    ///   arity refusal for a family of parameters named alone; a name nothing
    ///   answers is unadmitted.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration, a type atom, the universe and an
    ///   unanswered constructor each written where a value is read, asserted as
    ///   the exact core node or refusal.
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_data_family_named_where_a_value_is_read_is_quoted`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(
                        &(Plan::Variable(_)
                            | Plan::Constant(_)
                            | Plan::Atom(_)
                            | Plan::Universe(_)
                            | Plan::Constructor(_)
                            | Plan::Data(..))
                    )
                )
        },
    )]
    fn constructor(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let name = self.name_at(site.at);
        if let Maybe::Present(constructor) = self.constructor_named(site, name) {
            let none = Stretch {
                start: self.operands.len(),
                end: self.operands.len(),
            };
            return self.construct(site, constructor, none);
        }
        if let Maybe::Present(resolved) = self.resolve_name(site, site.reading.frame(), name)? {
            if let Resolved::Declaration { constant, .. } = resolved
                && let Maybe::Present(arity) = self.data_family(constant)
            {
                let none = Stretch {
                    start: self.operands.len(),
                    end: self.operands.len(),
                };
                return self.family(site, constant, arity, none);
            }
            let _frame = self.require(site, Produced::Value)?;
            self.plan(site, resolved.term());
            return Ok(());
        }
        let quoted = match type_atom(name) {
            | Maybe::Present(atom) => Plan::Atom(atom),
            | Maybe::Absent(_) if name.as_ref() == TileName::UNIVERSE.as_ref() => {
                Plan::Universe(Universe::FUSS_FREE)
            },
            | Maybe::Absent(_) => return Err(site.out(FragmentBoundary::Unadmitted)),
        };
        let _frame = self.require(site, Produced::ValueType)?;
        self.plan(site, quoted);

        Ok(())
    }

    /// Classify a number literal.
    ///
    /// # Specification
    /// - requires: `site` is a number.
    /// - ensures: a number standing as a value whose lexeme is decimal digits
    ///   is planned as its canonical integer.
    /// - provides: the integer half of the literal reading.
    /// - fails: yields the wrong-sort refusal outside value position; a
    ///   fraction or an exponent is a number the fragment does not admit; any
    ///   other text is a malformed literal.
    /// - panics: none.
    ///
    /// # Errors
    /// The number's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — canonical integer magnitudes, fractional syntax and
    ///   malformed lexemes separate successful literal plans from their
    ///   refusals.
    /// - witness: `lower::tests::an_integer_literal_is_its_canonical_magnitude`
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Literal(Literal::Integer(_)))
                )
        },
    )]
    fn number(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let text = self.text_at(site.at);
        if let Maybe::Present(literal) = parse_literal(Former::Number, text) {
            self.plan(site, Plan::Literal(literal));
            return Ok(());
        }
        if fractional(text).0 {
            return Err(site.out(FragmentBoundary::Unadmitted));
        }

        Err(LoweringRefusal::MalformedLiteral {
            span: site.at.span,
            form: site.name,
        })
    }

    /// Classify a string literal.
    ///
    /// # Specification
    /// - requires: `site` is a string; `pieces` is its reading.
    /// - ensures: a string standing as a value with no interpolation is planned
    ///   as its decoded text.
    /// - provides: the text half of the literal reading.
    /// - fails: yields the wrong-sort refusal outside value position; an
    ///   interpolation is a form the fragment does not admit; a string missing
    ///   a delimiter is a malformed literal.
    /// - panics: none.
    ///
    /// # Errors
    /// The string's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quoted strings decode their escapes; interpolation
    ///   and malformed text retain their distinct located refusals.
    /// - witness: `lower::tests::a_text_literal_is_the_bytes_between_its_quotes`
    /// - witness: `lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_malformed_text_literal_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Literal(Literal::Text(_)))
                )
        },
    )]
    fn text(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let interpolated = pieces.pieces.iter().any(
            |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::INTERPOLATION),
        );
        if interpolated {
            return Err(site.folded(FormName::INTERPOLATION, FragmentBoundary::Unadmitted));
        }
        let Maybe::Present(literal) = parse_literal(Former::Text, self.text_at(site.at))
        else {
            return Err(LoweringRefusal::MalformedLiteral {
                span: site.at.span,
                form: site.name,
            });
        };

        self.plan(site, Plan::Literal(literal));

        Ok(())
    }

    /// Classify a parenthesised expression: a grouping, a pair or an
    /// annotation.
    ///
    /// # Specification
    /// - requires: `site` is a parenthesised expression in term position.
    /// - ensures: `(e)` reads its operand at its own reading and adopts it, the
    ///   answer its position states passed on; a comma list is read as a pair;
    ///   `(C… : T)` over a constructor standing as a value reads `T` as a value
    ///   type under the same frame, records it as the constructor's classifier
    ///   and adopts the constructor.
    /// - provides: the reading of every form the grammar folds into
    ///   parentheses.
    /// - fails: yields the pair's own refusal, the unadmitted refusal for an
    ///   annotation over anything but a constructor standing as a value, the
    ///   empty-list refusal for `()`, which is never the unit, and the
    ///   extra-operand refusal for a juxtaposition.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — grouping preserves its operand while a
    ///   comma-separated tuple plans one tuple rather than treating the commas
    ///   as grouping.
    /// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::the_empty_parentheses_are_never_the_unit`
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Transparent(_) | Plan::Tuple(_)))
                )
        },
    )]
    fn parenthesized(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let list = cursor.clone();
        let _open = cursor.tile(TileName::PAREN_OPEN);
        let run = cursor.operands();
        if let Maybe::Present(_) = cursor.at(TileName::COMMA) {
            return self.pair(site, list);
        }
        if let Maybe::Present(_) = cursor.at(TileName::COLON) {
            return self.annotated(site, run, cursor);
        }
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        if let Run::Empty(_) = run {
            let unit = Site {
                name: FormName::UNIT,
                ..site
            };
            return Err(unit.out(FragmentBoundary::EmptyList));
        }
        let inner = site.one(run)?;
        self.read(inner.node, site.reading);
        if let Some(&answer) = self.answers.get(&site.at.node) {
            let _passed = self.answers.insert(inner.node, answer);
        }
        self.pass_paths(site.at.node, inner.node);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// Classify a tuple, `(v1, …, vn)`, the one-element `(v,)` included.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the `(` of a parenthesised expression
    ///   whose first member a comma follows.
    /// - ensures: the tuple stands as a value, reads every member as a value
    ///   under its own frame, and is planned over them as one tuple, as one `*`
    ///   chain is one product.
    /// - provides: the introduction of the eager product.
    /// - fails: yields the wrong-sort refusal where no value is read, and the
    ///   list's refusal for a member out of shape, both naming the tuple.
    /// - panics: none.
    ///
    /// # Errors
    /// The tuple's refusal.
    ///
    /// # Termination
    /// The member loop runs once per entry of the finite member stretch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple of one, of two and of three, and a tuple
    ///   where a computation is read, each asserted as the exact core node read
    ///   back out of the arena or the exact refusal.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Tuple(members)) if members.end.saturating_sub(members.start) >= 1_usize
                )
        },
    )]
    fn pair(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let tuple = Site {
            name: FormName::TUPLE,
            ..site
        };
        let frame = self.require(tuple, Produced::Value)?;
        let start = self.operands.len();
        if let Err(refusal) = arguments(tuple, &mut cursor, &mut self.operands) {
            self.operands.truncate(start);
            return Err(refusal);
        }
        let members = Stretch {
            start,
            end: self.operands.len(),
        };
        for position in members.start .. members.end {
            if let Some(&member) = self.operands.get(position) {
                self.read(member, Reading::Value(frame));
            }
        }

        self.plan(site, Plan::Tuple(members));

        Ok(())
    }

    /// Classify a thunk, `thunk { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a thunk in term position.
    /// - ensures: a thunk standing as a value reads its block in its own frame
    ///   as a body a path runs through, and is planned over it.
    /// - provides: the value former that suspends a computation.
    /// - fails: yields the wrong-sort refusal outside value position, the
    ///   unadmitted refusal for a grade, the block's own refusal, and the
    ///   unreachable refusal for statements after one every path of which
    ///   exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The thunk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk keeps its block computation under suspension;
    ///   an authored force reads that value before forcing its computation.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Thunk(Block { statements, .. })) if statements.start <= statements.end && statements.end <= self.statements.len())
        },
    )]
    fn thunk(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let _keyword = cursor.tile(TileName::THUNK);
        if let Maybe::Present(_) = cursor.at(TileName::BRACKET_OPEN) {
            return Err(site.folded(FormName::GRADE, FragmentBoundary::Unadmitted));
        }
        let body = self.block(site, &mut cursor, frame)?;
        self.open_body(
            site,
            body,
            Maybe::Absent(native::answered::Absent::Unstated),
        )?;

        self.plan(site, Plan::Thunk(body));

        Ok(())
    }

    /// Classify a lambda, `fn (x) { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a lambda in term position.
    /// - ensures: a lambda standing as a computation binds its one parameter in
    ///   a frame extending its own, reads its block under that frame as a body
    ///   a path runs through, and is planned over it.
    /// - provides: the binder of the fragment.
    /// - fails: yields the wrong-sort refusal outside computation position; the
    ///   unadmitted refusal for a type abstraction or a typed parameter; the
    ///   arity refusal for any parameter count but one; the block's own
    ///   refusal; and the unreachable refusal for statements after one every
    ///   path of which exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The lambda's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda body uses its newly introduced binder and a
    ///   lambda offered directly in value position is refused.
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Lambda(Block { statements, .. })) if statements.start <= statements.end && statements.end <= self.statements.len())
        },
    )]
    fn lambda(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let _keyword = cursor.tile(TileName::FN);
        if let Maybe::Present(_) = cursor.at(TileName::BRACKET_OPEN) {
            return Err(site.folded(FormName::TYPE_ABSTRACTION, FragmentBoundary::Unadmitted));
        }
        let binder = parameter(site, &mut cursor)?;
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;
        let extended = self.scope.extend(frame, name);
        let body = self.block(site, &mut cursor, Frame::Inner(extended))?;
        self.open_body(
            site,
            body,
            Maybe::Absent(native::answered::Absent::Unstated),
        )?;

        self.plan(site, Plan::Lambda(body));

        Ok(())
    }

    /// Classify a block standing as a computation, `{ run x <- c ; … c }`.
    ///
    /// # Specification
    /// - requires: `site` is a block in term position.
    /// - ensures: a block standing as a computation reads its statements and
    ///   its last computation as a thunk's or a lambda's block does, under its
    ///   own frame, passes the answer its position states and the paths through
    ///   its position to its last computation, runs the paths on to its
    ///   statements when a path passes it, and is planned over them.
    /// - provides: sequencing where one computation is read, a match arm's body
    ///   among them.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   block's own refusal, and the unreachable refusal for statements after
    ///   one every path of which exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block arm binds its statement over its last
    ///   computation, and a block where a value is read is refused.
    /// - witness: `lower::tests::a_block_standing_as_a_computation_binds_its_statements`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Block(Block { statements, .. })) if statements.start <= statements.end && statements.end <= self.statements.len())
        },
    )]
    fn sequenced(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let body = self.block(site, &mut cursor, frame)?;
        let answer = match self.answers.get(&site.at.node) {
            | Some(&answer) => {
                let _passed = self.answers.insert(body.last, answer);
                Maybe::Present(answer)
            },
            | None => Maybe::Absent(native::answered::Absent::Unstated),
        };
        self.pass_paths(site.at.node, body.last);
        if self.exitable.contains(&site.at.node) {
            self.paths_through(site, body, answer)?;
        }

        self.plan(site, Plan::Block(body));

        Ok(())
    }

    /// Classify a function tail, `def f(x: A, …) -> B { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a declaration form read as a function, whose tail
    ///   opens on `(`.
    /// - ensures: each parameter binds in a frame extending the one before it,
    ///   left to right, with its type, when written, read as a value type under
    ///   the frame before it and recorded on the binder; a recursive tail binds
    ///   its own name in one more frame, between its last parameter and the
    ///   ones before it, typed by the declaration form so no telescope counts
    ///   it, and records the parameters before it as the ones every recursive
    ///   call passes unchanged; the result, when written, is read at the result
    ///   position under the last parameter's frame, as the block is, and
    ///   recorded as the answer of the block's last computation and of every
    ///   statement whose local ends continue the block; the block is read as a
    ///   body a path runs through; the form is planned as the function's
    ///   declared type and body.
    /// - provides: the function tail, lowered once at the declaration form for
    ///   both halves it writes.
    /// - fails: yields the unadmitted refusal for a parameter spelled as a type
    ///   or a type variable, and, as a recursive tail, for one with no
    ///   parameter to descend on; a fault naming the function form for a
    ///   parameter list, a type or a result out of shape; the block's own
    ///   refusal; and the unreachable refusal for statements after one every
    ///   path of which exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The function's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the parameter count is separated by none and two,
    ///   each lowered tail asserted as the exact core node read back out of the
    ///   arena, and the refusals by a type-spelled parameter and a juxtaposed
    ///   parameter type, each asserted as the exact variant.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
    /// - witness: `lower::native::tests::a_match_takes_its_answer_from_the_function_result`
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_last_parameter`
    #[spec(
        captures: parameters = self.parameters.len(),
        ensures: |ret| {
            ret.is_err()
                || self
                    .plans
                    .get(usize::from(site.at.node))
                    .is_some_and(|plan| match *plan {
                        | Plan::Function(ref function) => {
                            function.parameters.start == parameters
                                && function.parameters.end == self.parameters.len()
                                && function.block.statements.start <= function.block.statements.end
                                && function.block.statements.end <= self.statements.len()
                        },
                        | _ => false,
                    })
        },
    )]
    fn function(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let function = Site {
            name: FormName::FUNCTION,
            ..site
        };
        loop {
            match cursor.read() {
                | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::DEF => break,
                | Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) => {},
                | Maybe::Absent(_) => {
                    return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
                },
            }
        }
        let recursive = cursor.tile(TileName::REC);
        let named = cursor.tile(TileName::IDENTIFIER);
        closed(function, &mut cursor, TileName::PAREN_OPEN)?;
        let start = self.parameters.len();
        let mut frame = Frame::Outermost;
        let mut recursion = Maybe::Absent(recursion::Absent::Plain);
        loop {
            let binder = match cursor.peek() {
                | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_CLOSE => {
                    let _close = cursor.tile(TileName::PAREN_CLOSE);
                    break;
                },
                | Maybe::Present(Piece::Tile { label, at }) if label == TileName::IDENTIFIER => at,
                | Maybe::Present(Piece::Tile { label, at }) if TileName::BINDERS.contains(&label) =>
                {
                    let parameter = Site {
                        at,
                        name: FormName::PARAMETER,
                        ..function
                    };
                    return Err(parameter.out(FragmentBoundary::Unadmitted));
                },
                | Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) | Maybe::Absent(_) => {
                    return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
                },
            };
            let _binder = cursor.tile(TileName::IDENTIFIER);
            let declared = match cursor.tile(TileName::COLON) {
                | Maybe::Present(_) => {
                    let declared = function.one(cursor.operands())?;
                    self.read(declared.node, Reading::ValueType(frame));
                    Maybe::Present(declared.node)
                },
                | Maybe::Absent(_) => Maybe::Absent(stated::Absent::Unstated),
            };
            let name = self.name_at(binder);
            self.note_binder(binder, name)?;
            let mut ahead = cursor.clone();
            let _comma = ahead.tile(TileName::COMMA);
            if let (Maybe::Present(_), Maybe::Present(own), Maybe::Present(_)) =
                (recursive, named, ahead.at(TileName::PAREN_CLOSE))
            {
                let own = self.name_at(own);
                let bound = self.scope.extend_typed(frame, own, site.at.node);
                let _first = self.recursions.insert(bound, native::Recursion {
                    uniform: Stretch {
                        start,
                        end: self.parameters.len(),
                    },
                    claimed: native::Claimed(false),
                });
                recursion = Maybe::Present(bound);
                frame = Frame::Inner(bound);
            }
            let bound = match declared {
                | Maybe::Present(written) => self.scope.extend_typed(frame, name, written),
                | Maybe::Absent(_) => self.scope.extend(frame, name),
            };
            self.parameters.push(Parameter {
                binder: binder.node,
                frame: bound,
                declared,
            });
            frame = Frame::Inner(bound);
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
            {
                return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
            }
        }
        if let (Maybe::Present(_), Maybe::Absent(_)) = (recursive, recursion) {
            let recursive = Site {
                name: FormName::RECURSIVE,
                ..site
            };
            return Err(recursive.out(FragmentBoundary::Unadmitted));
        }
        let parameters = Stretch {
            start,
            end: self.parameters.len(),
        };
        let result = match cursor.tile(TileName::ARROW) {
            | Maybe::Present(_) => {
                let result = function.one(cursor.operands())?;
                self.read(result.node, Reading::Result(frame));
                Maybe::Present(result.node)
            },
            | Maybe::Absent(_) => Maybe::Absent(stated::Absent::Unstated),
        };
        let block = self.block(function, &mut cursor, frame)?;
        let answer = match result {
            | Maybe::Present(node) => {
                let answer = native::Answer { node, frame };
                let _first = self.answers.insert(block.last, answer);
                Maybe::Present(answer)
            },
            | Maybe::Absent(_) => Maybe::Absent(native::answered::Absent::Unstated),
        };
        self.open_body(function, block, answer)?;

        self.plan(
            site,
            Plan::Function(Function {
                parameters,
                result,
                block,
                recursion,
            }),
        );

        Ok(())
    }

    /// Read a block, `{ s… c }`, whose first statement reads under `frame`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the block's `{`, which the form's last
    ///   piece closes.
    /// - ensures: each `run x <- c ;` statement reads its computation under the
    ///   frame the statements before it extended and binds `x` in a frame
    ///   extending that one; the last computation, written bare or as a
    ///   statement `c ;` before the closing `}` and then recorded as stated,
    ///   reads under the frame every statement extended; the statements and the
    ///   last computation are returned, with the cursor past the closing `}`
    ///   and nothing after it.
    /// - provides: the body reading of thunks, lambdas and function tails.
    /// - fails: yields the unadmitted refusal for a statement the fragment does
    ///   not read, by the statement's own name; the arity refusal, as a block,
    ///   for a block with no last computation; and each statement's and hole's
    ///   own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the statement count is separated by none and two, the
    ///   second binding over the first, each asserted as the exact bind chain
    ///   read back out of the arena; the residue by one witness row per refused
    ///   statement form, asserted as the exact refusal.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
    #[spec(
        captures: before = (self.statements.len(), frame),
        ensures: |ret| {
            ret.as_ref().map_or(true, |block| {
                block.statements.start == before.0
                    && block.statements.end == self.statements.len()
                    && matches!(self.reading(block.last), Reading::Computation(_))
                    && (block.statements.start != block.statements.end
                        || self.reading(block.last) == Reading::Computation(before.1))
                    && matches!(cursor.peek(), Maybe::Absent(_))
            })
        },
    )]
    fn block(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<Block, LoweringRefusal<'source>>
    {
        let Maybe::Present(open) = cursor.tile(TileName::BRACE_OPEN)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let start = self.statements.len();
        let mut frame = frame;
        loop {
            match cursor.peek() {
                | Maybe::Present(Piece::Tile { label, at }) if label == TileName::RUN => {
                    let _run = cursor.tile(TileName::RUN);
                    frame = self.statement(cursor, at, frame)?;
                },
                | Maybe::Present(Piece::Operand(_)) => {
                    let run = cursor.operands();
                    if let Maybe::Present(semicolon) = cursor.at(TileName::SEMICOLON) {
                        let first = match run {
                            | Run::One(written) | Run::Several { first: written, .. } => {
                                written.span
                            },
                            | Run::Empty(gap) => gap,
                        };
                        let span = first.join(semicolon.span);
                        let mut ahead = cursor.clone();
                        let _semicolon = ahead.tile(TileName::SEMICOLON);
                        if let (Run::One(written), Maybe::Present(_)) =
                            (run, ahead.at(TileName::BRACE_CLOSE))
                        {
                            let _semicolon = cursor.tile(TileName::SEMICOLON);
                            let _first = self.stated.insert(written.node, span);
                            closed(site, cursor, TileName::BRACE_CLOSE)?;
                            exhausted(site, cursor)?;
                            self.read(written.node, Reading::Computation(frame));
                            return Ok(Block {
                                statements: Stretch {
                                    start,
                                    end: self.statements.len(),
                                },
                                last: written.node,
                            });
                        }
                        let discarded = site.one(run)?;
                        let _semicolon = cursor.tile(TileName::SEMICOLON);
                        self.read(discarded.node, Reading::Computation(frame));
                        self.statements.push(Statement {
                            origin: discarded.node,
                            bound: discarded.node,
                            binding: StatementBinding::Discarded,
                            rest: exits::Rest::Bound,
                        });
                        frame = Frame::Inner(self.scope.extend(frame, SurfaceName::from("")));
                        continue;
                    }
                    let last = site.one(run)?;
                    closed(site, cursor, TileName::BRACE_CLOSE)?;
                    exhausted(site, cursor)?;
                    self.read(last.node, Reading::Computation(frame));
                    return Ok(Block {
                        statements: Stretch {
                            start,
                            end: self.statements.len(),
                        },
                        last: last.node,
                    });
                },
                | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::BRACE_CLOSE => {
                    let braced = ByteSpan::new(open.span.start(), site.at.span.end())
                        .unwrap_or(site.at.span);
                    let as_block = Site {
                        at: Placed {
                            node: site.at.node,
                            span: braced,
                        },
                        name: FormName::BLOCK,
                        reading: Reading::Computation(frame),
                    };
                    return Err(as_block.out(FragmentBoundary::Arity(OperandCount::from(0_usize))));
                },
                | Maybe::Present(Piece::Tile { label, at }) => {
                    return Err(match statement_form(label, cursor) {
                        | Maybe::Present(form) => LoweringRefusal::OutOfFragment {
                            span: at.span,
                            form,
                            sort: FragmentSort::Computation,
                            boundary: FragmentBoundary::Unadmitted,
                        },
                        | Maybe::Absent(_) => site.fault(at.span, FormFault::MisplacedTile),
                    });
                },
                | Maybe::Absent(_) => {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                },
            }
        }
    }

    /// Read one `run p <- c ;` statement, its `run` tile already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's `run` tile `run`;
    ///   `frame` is the frame the statement reads under.
    /// - ensures: the statement's computation is read under `frame` and the
    ///   statement recorded with its `run` tile; the frame binding the
    ///   statement's name over `frame`, which the rest of the block reads
    ///   under, is returned. A tuple pattern `(x, y, …)` binds the returned
    ///   tuple under a nameless binder and each component's name over it, in
    ///   order, and the statement is recorded as that split.
    /// - provides: the one statement the fragment reads.
    /// - fails: yields the unadmitted refusal for an annotated binder and for a
    ///   binder pattern other than a name, a wildcard or a tuple of those, and
    ///   a fault naming the bind statement for a hole or a tile out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each run statement reads its bound computation in the
    ///   previous frame and introduces its names only for subsequent
    ///   computations; a two-component tuple binds both names in order, so a
    ///   swapped binding reads the other component.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::a_tuple_binder_splits_the_returned_tuple_in_order`
    #[spec(
        captures: before = self.statements.len(),
        ensures: |ret| match ret {
            | Ok(Frame::Inner(_)) => {
                self.statements.len() == before.saturating_add(1_usize)
                    && self.statements.last().is_some_and(|last| {
                        last.origin == run.node
                            && matches!(last.binding, StatementBinding::Named | StatementBinding::Split(_))
                            && self.reading(last.bound) == Reading::Computation(frame)
                    })
            },
            | Ok(Frame::Outermost) => false,
            | Err(_) => self.statements.len() == before,
        },
    )]
    fn statement(
        &mut self,
        cursor: &mut Cursor<'_>,
        run: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let statement = Site {
            at: run,
            name: FormName::BIND_STATEMENT,
            reading: Reading::Computation(frame),
        };
        let binder = statement.one(cursor.operands())?;
        if let Maybe::Present(colon) = cursor.at(TileName::COLON) {
            return Err(LoweringRefusal::OutOfFragment {
                span: colon.span,
                form: FormName::ANNOTATION,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::Unadmitted,
            });
        }
        closed(statement, cursor, TileName::BIND)?;
        let bound = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::SEMICOLON)?;
        if let Maybe::Present(components) = self.tuple_binders(statement, binder)? {
            let mut names = Vec::with_capacity(components.len());
            for &component in &components {
                let name = self.binder_name(statement, component)?;
                self.note_binder(component, name)?;
                names.push(name);
            }
            self.read(bound.node, Reading::Computation(frame));
            self.statements.push(Statement {
                origin: run.node,
                bound: bound.node,
                binding: StatementBinding::Split(gandr_core_term::ComponentCount::from(
                    names.len(),
                )),
                rest: exits::Rest::Bound,
            });
            let mut inner = self.scope.extend(frame, SurfaceName::from(""));
            for name in names {
                inner = self.scope.extend(Frame::Inner(inner), name);
            }
            return Ok(Frame::Inner(inner));
        }
        let name = self.binder_name(statement, binder)?;
        self.note_binder(binder, name)?;
        self.read(bound.node, Reading::Computation(frame));
        self.statements.push(Statement {
            origin: run.node,
            bound: bound.node,
            binding: StatementBinding::Named,
            rest: exits::Rest::Bound,
        });

        Ok(Frame::Inner(self.scope.extend(frame, name)))
    }

    /// The component patterns of a tuple pattern standing as a `run`
    /// statement's binder, in order.
    ///
    /// # Specification
    /// - requires: `binder` is the pattern operand of the statement at
    ///   `statement`.
    /// - ensures: each component operand of a tuple pattern, in order; absent
    ///   for any other pattern.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold, and a
    ///   fault naming the bind statement for a repaired pattern or a tile out
    ///   of place among the components.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-component tuple binds both names in order, and
    ///   a name pattern reads as no tuple.
    /// - witness: `lower::tests::a_tuple_binder_splits_the_returned_tuple_in_order`
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |components| match *components { Maybe::Present(ref parts) => parts.len() >= 2, Maybe::Absent(_) => true }))]
    fn tuple_binders(
        &self,
        statement: Site,
        binder: Placed,
    ) -> Result<Maybe<Vec<Placed>, untupled::Absent>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(binder.node)
        else {
            return Ok(Maybe::Absent(untupled::Absent::OtherPattern));
        };
        let Shape::Form { name, .. } = shape_of(self.pbg, node)?
        else {
            return Ok(Maybe::Absent(untupled::Absent::OtherPattern));
        };
        if name != FormName::TUPLE_PATTERN {
            return Ok(Maybe::Absent(untupled::Absent::OtherPattern));
        }
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, binder.node, &mut pieces)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(FormName::TUPLE_PATTERN));
        }
        let mut cursor = Cursor::new(&pieces.pieces, binder.span);
        closed(statement, &mut cursor, TileName::PAREN_OPEN)?;
        let mut components = Vec::new();
        loop {
            components.push(statement.one(cursor.operands())?);
            if let Maybe::Present(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
            {
                continue;
            }
            closed(statement, &mut cursor, TileName::PAREN_CLOSE)?;
            break;
        }
        if components.len() < 2 {
            return Err(statement.fault(binder.span, FormFault::MisplacedTile));
        }
        Ok(Maybe::Present(components))
    }

    /// The name a `run` statement's pattern binds.
    ///
    /// # Specification
    /// - requires: `binder` is the pattern operand of the statement at
    ///   `statement`.
    /// - ensures: the name an identifier pattern spells; the empty name, which
    ///   no identifier resolves to, for a wildcard, so `run _ <- c;` discards
    ///   `c`'s value at any type.
    /// - provides: the binder reading of the bind statement.
    /// - fails: yields the unadmitted refusal, at pattern sort and by the
    ///   pattern's own name, for every other pattern;
    ///   [`LoweringRefusal::UnknownMold`] for a foreign mold.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary run binders introduce the spelled name, a
    ///   wildcard binds a name nothing reads, and other patterns are refused
    ///   rather than becoming ordinary names. The predicate asks for the
    ///   binder's own source bytes, by address and length, rather than reading
    ///   the name.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::a_discarded_statement_splits_its_unit`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |name| {
                self.tree.node(binder.node).is_some_and(|node| {
                    match shape_of(self.pbg, node) {
                        | Ok(Shape::Form {
                            former: Former::Name,
                            ..
                        }) => core::ptr::eq(
                            core::ptr::from_ref::<str>(name.as_ref()),
                            core::ptr::from_ref::<str>(self.name_at(binder).as_ref()),
                        ),
                        | Ok(Shape::Form { name: form, .. }) => {
                            form == FormName::WILDCARD && name.as_ref().is_empty()
                        },
                        | _ => false,
                    }
                })
            })
        },
    )]
    fn binder_name(
        &self,
        statement: Site,
        binder: Placed,
    ) -> Result<SurfaceName<'source>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(binder.node)
        else {
            return Err(statement.fault(binder.span, FormFault::MisplacedTile));
        };
        match shape_of(self.pbg, node)? {
            | Shape::Form {
                former: Former::Name,
                ..
            } => Ok(self.name_at(binder)),
            | Shape::Form { name, .. } if name == FormName::WILDCARD => Ok(SurfaceName::from("")),
            | Shape::Form { name, .. } => Err(LoweringRefusal::OutOfFragment {
                span: binder.span,
                form: name,
                sort: FragmentSort::Pattern,
                boundary: FragmentBoundary::Unadmitted,
            }),
            | Shape::Repair(repair) => {
                Err(statement.fault(binder.span, FormFault::Repaired(repair)))
            },
            | Shape::Root | Shape::Layout => {
                Err(statement.fault(binder.span, FormFault::MisplacedTile))
            },
        }
    }

    /// Classify a keyword form of one value operand: `ret v`, `return v` or
    /// `force v`.
    ///
    /// # Specification
    /// - requires: `site` is a returner, a return or a force in term position,
    ///   whose keyword tile is `keyword`.
    /// - ensures: the form standing as a computation reads its one operand as a
    ///   value in its own frame and is planned over it; a return is planned as
    ///   the returner and recorded as an exit, which leaves the function
    ///   because the commuting puts every exit where the function's body ends.
    /// - provides: the computation formers over a value, and the exit that
    ///   leaves a function with a value.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   not-in-tail refusal for a return that stands where no path through a
    ///   function's, a lambda's or a thunk's body passes, and the hole's own
    ///   refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — force and return plan their own former over a value
    ///   operand, and an author-written force is not marked as inserted; a
    ///   return on a path lowers as the returner and one in a call's head is
    ///   refused.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || match self.plans.get(usize::from(site.at.node)) {
                    | Some(&Plan::Force(operand)) => {
                        keyword == TileName::FORCE
                            && self.reading(operand) == Reading::Value(site.reading.frame())
                    },
                    | Some(&Plan::Return(operand)) => {
                        keyword != TileName::FORCE
                            && (keyword != TileName::RETURN
                                || (self.exitable.contains(&site.at.node)
                                    && self.leaving.contains(&site.at.node)))
                            && self.reading(operand) == Reading::Value(site.reading.frame())
                    },
                    | _ => false,
                }
        },
    )]
    fn keyed(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        keyword: TileName,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        if keyword == TileName::RETURN {
            if !self.exitable.contains(&site.at.node) {
                return Err(site.out(FragmentBoundary::NotInTail));
            }
            let _exit = self.leaving.insert(site.at.node);
        }
        let _keyword = cursor.tile(keyword);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(operand.node, Reading::Value(frame));
        let plan = if keyword == TileName::FORCE {
            Plan::Force(operand.node)
        }
        else {
            Plan::Return(operand.node)
        };

        self.plan(site, plan);

        Ok(())
    }

    /// Classify a tail call, `become c`.
    ///
    /// # Specification
    /// - requires: `site` is a `become` in term position.
    /// - ensures: the form standing as a computation where a path through a
    ///   function's, a lambda's or a thunk's body passes reads its one operand
    ///   as a computation in its own frame, the answer its position states
    ///   passed on, is recorded as an exit and adopts the operand: the operand
    ///   runs under the caller's continuation, so the exit adds the guarantee,
    ///   not a frame. The operand is not itself where the body ends: `become`
    ///   is the exit, so the operand needs none; a path passes it, so an exit
    ///   inside it leaves the function too.
    /// - provides: the exit that leaves a function by running a computation.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   not-in-tail refusal for a `become` where no path passes, and the
    ///   hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `become` ending a body lowers as its operand, one
    ///   in a bound computation leaves the function, and one in a call's head
    ///   is refused.
    /// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Transparent(operand))
                    if self.exitable.contains(&site.at.node) && self.leaving.contains(&site.at.node)
                        && !self.exits.contains(&operand) && self.exitable.contains(&operand)
                        && self.reading(operand) == Reading::Computation(site.reading.frame()))
        },
    )]
    fn tail_call(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        if !self.exitable.contains(&site.at.node) {
            return Err(site.out(FragmentBoundary::NotInTail));
        }
        let _exit = self.leaving.insert(site.at.node);
        let _keyword = cursor.tile(TileName::BECOME);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(operand.node, Reading::Computation(frame));
        if let Some(&answer) = self.answers.get(&site.at.node) {
            let _passed = self.answers.insert(operand.node, answer);
        }
        let _path = self.exitable.insert(operand.node);
        self.plan(site, Plan::Transparent(operand.node));

        Ok(())
    }

    /// Classify an application, `c(v, …)`.
    ///
    /// # Specification
    /// - requires: `site` is a call in term position.
    /// - ensures: a call whose head is a constructor of a data family declared
    ///   strictly earlier is that constructor applied to the arguments as its
    ///   fields; any other call standing as a computation reads its head at the
    ///   head position and each argument as a value, all in its own frame, and
    ///   is planned as the head applied to the arguments left to right; a call
    ///   whose head is an instantiation, a recursive call, records every
    ///   argument for the head's claim to check and reads and applies its last
    ///   alone, the one its fixpoint takes; a call of no arguments is its head.
    /// - provides: the elimination of a lambda, curried over any argument
    ///   count.
    /// - fails: yields the wrong-sort refusal outside computation position, and
    ///   the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the argument count is separated by none, one and two,
    ///   each asserted as the exact application chain read back out of the
    ///   arena. The predicate reads only the operands this call appended.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_last_parameter`
    #[spec(
        captures: start = self.operands.len(),
        ensures: |ret| {
            ret.is_err()
                || match self.plans.get(usize::from(site.at.node)) {
                    | Some(&Plan::Application(head, arguments)) => {
                        let end = self.operands.len();
                        let descends = self.descents.get(&head).is_some_and(|descent| {
                            descent.arguments == Stretch { start, end } && descent.call == site
                        });
                        (arguments.start == start
                            || (descends && arguments.start == end.saturating_sub(1).max(start)))
                            && arguments.end == end
                            && self.reading(head) == Reading::Head(site.reading.frame())
                            && self.operands.get(arguments.start ..).is_some_and(|appended| {
                                appended.iter().all(|&argument| {
                                    self.reading(argument) == Reading::Value(site.reading.frame())
                                })
                            })
                    },
                    | Some(&Plan::Constructor(constructed)) => {
                        constructed.fields.start == start
                            && constructed.fields.end == self.operands.len()
                    },
                    | _ => false,
                }
        },
    )]
    fn call(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(constructor) = self.constructor_head(site, head)?
        {
            let _head = cursor.operands();
            let start = self.operands.len();
            arguments(site, &mut cursor, &mut self.operands)?;
            let fields = Stretch {
                start,
                end: self.operands.len(),
            };
            return self.construct(site, constructor, fields);
        }
        let frame = self.require(site, Produced::Computation)?;
        let head = site.one(cursor.operands())?;
        let start = self.operands.len();
        arguments(site, &mut cursor, &mut self.operands)?;
        let written = Stretch {
            start,
            end: self.operands.len(),
        };
        let descends = self.tree.node(head.node).is_some_and(|node| {
            matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::Instantiation,
                    ..
                })
            )
        });
        let applied = if descends {
            let _first = self.descents.insert(head.node, native::Descent {
                call: site,
                arguments: written,
            });
            Stretch {
                start: written.end.saturating_sub(1).max(written.start),
                end: written.end,
            }
        }
        else {
            written
        };
        self.read(head.node, Reading::Head(frame));
        for position in applied.start .. applied.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(site, Plan::Application(head.node, applied));

        Ok(())
    }

    /// Lower native prefix and infix syntax using the shared vocabulary.
    ///
    /// # Specification
    /// - ensures: the table row selected by the operator receives value
    ///   operands in source order.
    /// - fails: malformed tiles or operators outside the admitted vocabulary
    ///   are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the form or fragment refusal at the source operator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric operands separate order and operator
    ///   choice; unsupported operators are rejected.
    /// - witness: `lower::tests::native_operator_plans_preserve_order`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(Plan::PrimitiveCall(..))))]
    fn operator(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        use gandr_core_term::primitive::Arguments;
        use gandr_core_term::primitive::Operator;
        use gandr_core_term::primitive::PRELUDE;
        let frame = self.require(site, Produced::Computation)?;
        let (label, arguments) = match pieces.pieces.as_slice() {
            | &[Piece::Tile { label, .. }, Piece::Operand(argument)] => {
                (label, Arguments::Unary(argument.node))
            },
            | &[
                Piece::Operand(first),
                Piece::Tile { label, .. },
                Piece::Operand(second),
            ] => (label, Arguments::Binary([first.node, second.node])),
            | _ => return Err(site.fault(site.at.span, FormFault::MisplacedTile)),
        };
        let Some(&primitive) =
            PRELUDE
                .iter()
                .find(|primitive| match (primitive.operator(), arguments) {
                    | (Operator::Prefix(spelling), Arguments::Unary(_))
                    | (Operator::Infix(spelling), Arguments::Binary(_)) => {
                        spelling == label.as_ref()
                    },
                    | _ => false,
                })
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        for argument in arguments.iter() {
            self.read(*argument, Reading::Value(frame));
        }
        self.plan(site, Plan::PrimitiveCall(primitive, arguments));
        Ok(())
    }

    /// Classify a selection `e.name`.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading.
    /// - ensures: a chain of selections whose head is a capitalised name is a
    ///   path, resolved through the outermost scope at the depth that binds it:
    ///   a path ending at an exported value component stands as that member's
    ///   constant when the member is declared strictly before the declaration
    ///   the path is written in. The chain is walked by an explicit loop, and
    ///   its links are left unread.
    /// - provides: the governed reading of a module path.
    /// - fails: yields [`LoweringRefusal::UnknownMember`], naming the module as
    ///   the path spells it and the member, for a selection a governing module
    ///   does not export; the forward-member refusal for a member declared at
    ///   or after the referring declaration; the wrong-sort refusal for a path
    ///   ending at a module, which is not a value; the wrong-sort refusal
    ///   outside value position; and the unadmitted refusal for a selection no
    ///   module governs, a record projection the fragment does not admit.
    /// - panics: none.
    ///
    /// # Errors
    /// The selection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path to an exported component at depth two and at
    ///   depth nine, to a hidden member, to an absent member at each depth, to
    ///   a module, to a member declared later, and a selection off a free name,
    ///   each asserted as the exact constant or refusal.
    /// - witness: `modules::modules::a_user_module_selection_is_governed_and_a_free_target_still_projects`
    /// - witness: `modules::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `modules::modules::a_deep_module_path_is_governed_at_the_depth_that_binds_it`
    /// - witness: `modules::modules::a_module_namespace_is_not_a_projectable_record`
    /// - witness: `modules::modules::a_hidden_or_absent_user_module_component_is_declined_as_a_hole`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Constant(_) | Plan::Primitive(_)))
                )
        },
    )]
    fn projection(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let mut links: Vec<(Placed, Placed)> = Vec::new();
        let (mut target, member) = Self::link(site, &pieces.pieces, site.at.span)?;
        links.push((target, member));
        let mut chain = Pieces::new();
        let head = loop {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(target.node)
            else {
                return Err(site.out(FragmentBoundary::Unadmitted));
            };
            match shape_of(self.pbg, node)? {
                | Shape::Form {
                    former: Former::Projection,
                    ..
                } => {
                    read_pieces(self.pbg, self.tree, target.node, &mut chain)?;
                    if let Maybe::Present(repaired) = chain.repair {
                        return Err(repaired.refusal(site.name));
                    }
                    let (inner, selected) = Self::link(site, &chain.pieces, target.span)?;
                    links.push((inner, selected));
                    target = inner;
                },
                | Shape::Form {
                    former: Former::Constructor | Former::Name,
                    ..
                } => break target,
                | Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                },
            }
        };
        let mut segments = Vec::with_capacity(links.len().saturating_add(1_usize));
        segments.push(Segment::from(self.text_at(head).as_ref()));
        for &(_prefix, selected) in links.iter().rev() {
            segments.push(Segment::from(self.text_at(selected).as_ref()));
        }
        let path = NamePath::from(segments);
        match self.recognition.resolve_path(&path) {
            | PathResolution::Complete(Recognized::BuiltinPrimitive { primitive, .. }) => {
                self.plan(site, Plan::Primitive(primitive));
                Ok(())
            },
            | PathResolution::Complete(Recognized::ModuleComponent) => {
                let Some(&exported) = self.exported.get(&path)
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                };
                self.select(site, exported)
            },
            | PathResolution::Complete(Recognized::ModuleNamespace) => {
                Err(site.out(FragmentBoundary::WrongSort))
            },
            | PathResolution::UnknownMember { depth, .. } => {
                let Some(&(prefix, selected)) = links
                    .len()
                    .checked_sub(usize::from(depth))
                    .and_then(|link| links.get(link))
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                };
                Err(LoweringRefusal::UnknownMember {
                    span: selected.span,
                    module: self.name_at(prefix),
                    member: self.name_at(selected),
                })
            },
            | PathResolution::Complete(_) | PathResolution::Ungoverned => {
                Err(site.out(FragmentBoundary::Unadmitted))
            },
        }
    }

    /// The target and the selected name of one selection, read from its
    /// pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of a projection covering `span`.
    /// - ensures: the operand the selection is taken from and the name tile
    ///   after its dot.
    /// - provides: the one-link half of [`Self::projection`].
    /// - fails: yields the misplaced-tile refusal when the pieces are not an
    ///   operand, a dot and a name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a malformed selection.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — single and deeply nested selections preserve their
    ///   target and own member positions, which locate an unknown member at its
    ///   depth.
    /// - witness: `modules::modules::nested_modules_lower_as_parent_members_and_project`
    /// - witness: `modules::modules::a_deep_module_path_is_governed_at_the_depth_that_binds_it`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |&(target, selected)| {
                pieces.first() == Some(&Piece::Operand(target))
                    && matches!(
                        pieces.get(1),
                        Some(&Piece::Tile {
                            label: TileName::DOT,
                            ..
                        })
                    )
                    && pieces.get(2)
                        == Some(&Piece::Tile {
                            label: TileName::IDENTIFIER,
                            at: selected,
                        })
            })
        },
    )]
    fn link(
        site: Site,
        pieces: &[Piece],
        span: ByteSpan,
    ) -> Result<(Placed, Placed), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(pieces, span);
        let Maybe::Present(Piece::Operand(target)) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let (Maybe::Present(_dot), Maybe::Present(selected)) = (
            cursor.tile(TileName::DOT),
            cursor.tile(TileName::IDENTIFIER),
        )
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };

        Ok((target, selected))
    }

    /// Plan the selection at `site` as the exported member at `target`.
    ///
    /// # Specification
    /// - requires: `target` is the member an exported path resolved to.
    /// - ensures: the member's constant, when the member is declared strictly
    ///   before the declaration `site` belongs to.
    /// - provides: the position rule for a path.
    /// - fails: yields [`LoweringRefusal::ForwardMemberReference`] for a member
    ///   declared at or after it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ForwardMemberReference`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a backward member becomes its declared constant while
    ///   a forward member is refused at the use, with the declaration retained.
    /// - witness: `modules::modules::a_backward_member_reference_resolves`
    /// - witness: `modules::modules::a_forward_member_reference_is_refused_by_position`
    #[spec(
        ensures: |ret| match self.collected.slots.get(usize::from(target)) {
            | None => ret == Err(site.out(FragmentBoundary::Unadmitted)),
            | Some(entry) => {
                if matches!(self.collected.owner_of(site.at.node), Maybe::Present(own) if target >= own)
                {
                    ret == Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name: entry.name,
                        declared: entry.named.span,
                    })
                }
                else {
                    ret.is_ok()
                        && matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Constant(constant)) if constant == entry.constant)
                }
            },
        },
    )]
    fn select(
        &mut self,
        site: Site,
        target: SlotIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(entry) = self.collected.slots.get(usize::from(target))
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        let (constant, name, declared) = (entry.constant, entry.name, entry.named.span);
        if let Maybe::Present(own) = self.collected.owner_of(site.at.node)
            && target >= own
        {
            return Err(LoweringRefusal::ForwardMemberReference {
                span: site.at.span,
                name,
                declared,
            });
        }
        self.plan(site, Plan::Constant(constant));

        Ok(())
    }

    /// Classify a bare type head.
    ///
    /// # Specification
    /// - requires: `site` is a primitive type, a type identifier or a type
    ///   variable in type position.
    /// - ensures: inside a module signature, a head naming a manifest type
    ///   component written before the head's own component stands for the type
    ///   that component names, adopted as it lowered. Otherwise a head a binder
    ///   or an earlier declaration answers is that code, read as the static
    ///   application of it to no arguments. Any other head resolves against the
    ///   nullary table and is planned as its atom.
    /// - provides: the type-head half of resolution, the expansion of a
    ///   manifest type component, and the decode of a value name in type
    ///   position.
    /// - fails: yields the wrong-sort refusal for a head whose sort does not
    ///   suit the position and the unresolved-head refusal for a head nothing
    ///   answers.
    /// - panics: none.
    ///
    /// # Errors
    /// The head's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder written at the bare universe, a binder
    ///   written at a sorted and levelled one, a declaration, an atom and a
    ///   manifest component, each asserted as the exact core type read back out
    ///   of the arena.
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::tests::every_type_atom_lowers_to_its_core_type`
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    #[spec(
        captures: before = self.manifests.len(),
        ensures: |ret| {
            self.manifests.len() >= before
                && self.manifests.len() <= before.saturating_add(1_usize)
                && (ret.is_err()
                    || matches!(
                        self.plans.get(usize::from(site.at.node)),
                        Some(
                            &(Plan::Transparent(_)
                                | Plan::Atom(_)
                                | Plan::Decode(_, _, _)
                                | Plan::StaticApplication(_, _)
                                | Plan::Data(_, _))
                        )
                    ))
        },
    )]
    fn type_head(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let name = self.name_at(site.at);
        if let Some(&Maybe::Present(seen)) = self.scopes.get(usize::from(site.at.node))
            && let Some(manifest) = self
                .collected
                .structures
                .get(usize::from(seen.structure))
                .and_then(|structure| structure.types.get(.. seen.before))
                .and_then(|visible| visible.iter().rev().find(|manifest| manifest.name == name))
        {
            let (held, defined) = (manifest.held, manifest.defined.node);
            let _frame = self.require(site, Produced::ValueType)?;
            self.manifests.push((held, site.at.node));
            self.plan(site, Plan::Transparent(defined));
            return Ok(());
        }
        let from = site.reading.frame();
        if let Maybe::Present(resolved) = self.resolve_name(site, from, name)? {
            let none = Stretch {
                start: self.operands.len(),
                end: self.operands.len(),
            };
            return self.static_application(site, resolved, none);
        }
        let _frame = self.require(site, Produced::ValueType)?;
        let Maybe::Present(atom) = type_atom(name)
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: site.at.span,
                name,
                arity: HeadArity::Nullary,
            });
        };

        self.plan(site, Plan::Atom(atom));

        Ok(())
    }

    /// Classify a universe, `Type[s, l]`.
    ///
    /// # Specification
    /// - requires: `site` is a universe in type position, or in value position
    ///   where it is quoted.
    /// - ensures: a universe standing as a value type is planned at the sort
    ///   and level written, the value sort and the fuss-free level supplied for
    ///   whichever is left off.
    /// - provides: the universe former of the fragment.
    /// - fails: yields the wrong-sort refusal where its position reads no value
    ///   type, a misplaced-tile fault for a bracket out of shape, and the
    ///   unadmitted refusal for a level beyond the core's level width.
    /// - panics: none.
    ///
    /// # Errors
    /// The universe's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the bare spelling, a sort alone and a sort with a
    ///   level at each sort, each asserted as the exact core universe.
    /// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Universe(_))
                )
        },
    )]
    fn universe(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::ValueType)?;
        let universe = self.universe_of(site, &mut cursor)?;

        self.plan(site, Plan::Universe(universe));

        Ok(())
    }

    /// The universe a universe form's pieces spell.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the form's `Type` tile.
    /// - ensures: the sort `+` or `-` and the level numeral written, the value
    ///   sort and level zero for whichever is left off.
    /// - provides: the one reading of a universe's spelling, shared by the
    ///   universe former and the decode that reads a binder's written type.
    /// - fails: a misplaced-tile fault for a bracket out of shape; the
    ///   unadmitted refusal for a level numeral wider than a level constant.
    /// - panics: none.
    ///
    /// # Errors
    /// The universe's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the supported spellings consume the complete form and
    ///   the spelling without brackets denotes the fuss-free universe. Explicit
    ///   sort and level values are checked by the same bounded spelling table.
    /// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
    #[spec(
        captures: plain = {
            let mut input = cursor.clone();
            let _keyword = input.tile(TileName::UNIVERSE);
            matches!(input.at(TileName::BRACKET_OPEN), Maybe::Absent(_))
        },
        ensures: |ret| {
            ret.as_ref().map_or(true, |universe| {
                matches!(cursor.peek(), Maybe::Absent(_))
                    && (!plain || *universe == Universe::FUSS_FREE)
            })
        },
    )]
    fn universe_of(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        let _keyword = cursor.tile(TileName::UNIVERSE);
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACKET_OPEN) {
            exhausted(site, cursor)?;
            return Ok(Universe::FUSS_FREE);
        }
        let sort = match (cursor.tile(TileName::PLUS), cursor.tile(TileName::MINUS)) {
            | (Maybe::Present(_), _) => GroundSort::Value,
            | (Maybe::Absent(_), Maybe::Present(_)) => GroundSort::Computation,
            | (Maybe::Absent(_), Maybe::Absent(_)) => {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            },
        };
        let level = match cursor.tile(TileName::COMMA) {
            | Maybe::Present(_) => {
                let Maybe::Present(numeral) = cursor.tile(TileName::NUMBER)
                else {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                };
                let text = self.text_at(numeral);
                let spelled: &str = text.as_ref();
                let Ok(level) = spelled.parse::<u64>()
                else {
                    let level = Site {
                        at: numeral,
                        ..site
                    };
                    return Err(level.out(FragmentBoundary::Unadmitted));
                };
                LevelConstant::from(level)
            },
            | Maybe::Absent(_) => LevelConstant::ZERO,
        };
        closed(site, cursor, TileName::BRACKET_CLOSE)?;
        exhausted(site, cursor)?;

        Ok(Universe { sort, level })
    }

    /// The universe a code of the type at `declared`, applied statically to
    /// `applied` arguments, decodes in; `fallback` where the type does not
    /// say.
    ///
    /// # Specification
    /// - requires: `declared`, when present, is a node of the tree.
    /// - ensures: read through any grouping parentheses, each of the first
    ///   `applied` arrows of the type steps to its codomain, and the universe
    ///   form the walk then reaches is the universe it spells; `fallback` for
    ///   an absent type, for a walk that meets any other form or an arrow too
    ///   few or too many, and for a universe out of shape, whose own reading
    ///   reports it.
    /// - provides: the sort and level a decode of a binder, a declaration or a
    ///   static application of either is minted at.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Termination
    /// Every turn spends one unit of the lowerer's allowance and steps to an
    /// operand of the node it read, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder written at a sorted, levelled universe
    ///   inside a grouping, a declaration signed at one, an operator's codomain
    ///   reached through one static arrow, and an unwritten type at each sort
    ///   of position, each observed through the decode it mints.
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(declared, Maybe::Present(_))
                || ret.as_ref().is_ok_and(|universe| *universe == fallback)
        },
    )]
    fn written_universe(
        &mut self,
        declared: Maybe<NodeIndex, binder_type::Absent>,
        applied: OperandCount,
        fallback: Universe,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        let Maybe::Present(mut position) = declared
        else {
            return Ok(fallback);
        };
        let mut remaining = usize::from(applied);
        loop {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(position)
            else {
                return Ok(fallback);
            };
            let Ok(Shape::Form { name, former }) = shape_of(self.pbg, node)
            else {
                return Ok(fallback);
            };
            let mut scratch = core::mem::take(&mut self.scratch);
            let read = read_pieces(self.pbg, self.tree, position, &mut scratch);
            let site = Site {
                at: Placed::of(position, node),
                name,
                reading: Reading::ValueType(Frame::Outermost),
            };
            let mut cursor = Cursor::new(&scratch.pieces, site.at.span);
            let step = match (read, former) {
                | (Ok(()), Former::Universe) if remaining == 0_usize => {
                    ControlFlow::Break(self.universe_of(site, &mut cursor).unwrap_or(fallback))
                },
                | (Ok(()), Former::ParenthesizedType) => {
                    let _open = cursor.tile(TileName::PAREN_OPEN);
                    match cursor.operands() {
                        | Run::One(operand) => ControlFlow::Continue(operand.node),
                        | Run::Empty(_) | Run::Several { .. } => ControlFlow::Break(fallback),
                    }
                },
                | (Ok(()), Former::ArrowType) if remaining > 0_usize => {
                    remaining = remaining.saturating_sub(1_usize);
                    let _domain = cursor.operands();
                    let _arrow = cursor.tile(TileName::ARROW);
                    match cursor.operands() {
                        | Run::One(operand) => ControlFlow::Continue(operand.node),
                        | Run::Empty(_) | Run::Several { .. } => ControlFlow::Break(fallback),
                    }
                },
                | _ => ControlFlow::Break(fallback),
            };
            self.scratch = scratch;
            match step {
                | ControlFlow::Continue(operand) => position = operand,
                | ControlFlow::Break(universe) => return Ok(universe),
            }
        }
    }

    /// Classify a type head applied to arguments, `Foo(A)`.
    ///
    /// # Specification
    /// - requires: `site` is a type application in type position, or in value
    ///   position where a type is quoted.
    /// - ensures: a head a binder or an earlier declaration answers is read as
    ///   the static application of that code to the arguments, left to right;
    ///   any other head applied to one argument resolves against the unary
    ///   table, stands at the sort its former produces, reads its argument at
    ///   the sort the former takes, and is planned over it.
    /// - provides: the applied half of type-head resolution.
    /// - fails: yields the unresolved-head refusal for a head nothing answers
    ///   and no former takes at the arity it was written with, the wrong-sort
    ///   refusal for a former or an application whose sort does not suit the
    ///   position, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a former's head, a head no former takes, a head
    ///   written at two arguments, and an operator a declaration and a binder
    ///   name, each asserted as the exact core node read back out of the arena
    ///   or the exact refusal.
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::tests::an_applied_head_no_former_answers_is_refused`
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Former(..) | Plan::Decode(..) | Plan::StaticApplication(..) | Plan::Data(..)))
                )
        },
    )]
    fn type_application(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let head = match cursor.peek() {
            | Maybe::Present(Piece::Tile { label, at })
                if label == TileName::TYPE_IDENTIFIER || label == TileName::TYPE_VARIABLE =>
            {
                let _head = cursor.tile(label);
                at
            },
            | Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) | Maybe::Absent(_) => {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            },
        };
        let name = self.name_at(head);
        let start = self.operands.len();
        let read = arguments(site, &mut cursor, &mut self.operands);
        let resolved = read.and_then(|()| {
            let named = Site { at: head, ..site };
            self.resolve_name(named, site.reading.frame(), name)
        });
        match resolved {
            | Ok(Maybe::Present(resolved)) => {
                let applied = Stretch {
                    start,
                    end: self.operands.len(),
                };
                return self.static_application(site, resolved, applied);
            },
            | Ok(Maybe::Absent(named::Absent::Unresolved)) => {},
            | Err(refusal) => {
                self.operands.truncate(start);
                return Err(refusal);
            },
        }
        let count = self.operands.len().saturating_sub(start);
        let first = self.operands.get(start).copied();
        self.operands.truncate(start);
        let unresolved = |arity| LoweringRefusal::UnresolvedTypeHead {
            span: head.span,
            name,
            arity,
        };
        let (Some(argument), 1_usize) = (first, count)
        else {
            return Err(unresolved(HeadArity::Polyadic(OperandCount::from(count))));
        };
        let Maybe::Present(former) = type_former(name)
        else {
            return Err(unresolved(HeadArity::Unary));
        };

        self.apply_former(site, former, argument)
    }

    /// Classify the static application of the code `resolved` names to the
    /// arguments `applied` holds in the operand store.
    ///
    /// # Specification
    /// - requires: `applied` is a stretch of the operand store, each entry an
    ///   argument the application was written with, left to right.
    /// - ensures: a data family stands as the nominal type over its arguments,
    ///   each read as a value under the site's frame, which a value position
    ///   quotes. Otherwise, where a value is read, the application stands as
    ///   itself; where a type is read, it stands as the decode of the
    ///   application, in the universe the code's written type reaches after one
    ///   arrow per argument, and else in the universe the position reads — the
    ///   computation types where only a computation type is read, the value
    ///   types everywhere else, at the fuss-free level. Every argument is read
    ///   as a value under the site's frame, and a binder so named is recorded
    ///   as mentioned.
    /// - provides: the one reading of a type operator's use, bare or applied,
    ///   as a value or as the type it denotes.
    /// - fails: yields the arity refusal for a data family applied to other
    ///   than its parameter count; the wrong-sort refusal where the position
    ///   reads neither a value nor the sort of the decode's universe;
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the walk of the
    ///   code's type.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    ///
    /// # Termination
    /// The argument loop runs once per entry of the finite stretch `applied`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare head and an applied one, each where a value is
    ///   read and where a type is read, the decode's universe written by the
    ///   operator and left to the position, each asserted as the exact core
    ///   node read back out of the arena.
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::native::tests::a_data_family_applies_to_its_parameters`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || match self.plans.get(usize::from(site.at.node)) {
                    | Some(&Plan::StaticApplication(_, planned)) => {
                        planned == applied && matches!(site.reading, Reading::Value(_))
                    },
                    | Some(&Plan::Decode(_, planned, _)) => {
                        planned == applied && !matches!(site.reading, Reading::Value(_))
                    },
                    | Some(&Plan::Data(_, planned)) => planned == applied,
                    | _ => false,
                }
        },
    )]
    fn static_application(
        &mut self,
        site: Site,
        resolved: Resolved,
        applied: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Resolved::Declaration { constant, .. } = resolved
            && let Maybe::Present(arity) = self.data_family(constant)
        {
            return self.family(site, constant, arity, applied);
        }
        let from = site.reading.frame();
        let (code, declared) = match resolved {
            | Resolved::Binder(bound) => (
                Code::Bound {
                    from,
                    binder: bound.binder,
                },
                bound.declared,
            ),
            | Resolved::Declaration { constant, declared } => (Code::Constant(constant), declared),
        };
        let (plan, produced) = if let Reading::Value(_) = site.reading {
            (Plan::StaticApplication(code, applied), Produced::Value)
        }
        else {
            let count = OperandCount::from(applied.end.saturating_sub(applied.start));
            let universe =
                self.written_universe(declared, count, site.reading.positional_universe())?;
            let produced = match universe.sort {
                | GroundSort::Value => Produced::ValueType,
                | GroundSort::Computation => Produced::CompType,
            };
            (Plan::Decode(code, applied, universe), produced)
        };
        let frame = self.require(site, produced)?;
        if let Code::Bound { binder, .. } = code {
            self.scope.mention(binder);
        }
        for position in applied.start .. applied.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(site, plan);

        Ok(())
    }

    /// Classify a type former written as its own keyword: `+U C` or `-F A`.
    ///
    /// # Specification
    /// - requires: `site` is a thunk type or a returner type in type position.
    /// - ensures: the keyword resolves against the unary table, a thunk type's
    ///   grade `[ω]` reads as no grade written, the form stands at the sort its
    ///   former produces, reads its one operand at the sort the former takes,
    ///   and is planned over it.
    /// - provides: the keyword spelling of the two type formers.
    /// - fails: yields the unresolved-head refusal for a keyword no former
    ///   answers, [`LoweringRefusal::GradedBridge`] for a thunk type graded
    ///   other than `ω`, the unadmitted refusal for a grade on a returner type,
    ///   the wrong-sort refusal for a former whose sort does not suit the
    ///   position, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the thunk and returner spellings plan their
    ///   respective bridge former, while unsupported grades produce a located
    ///   refusal.
    /// - witness: `lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
    /// - witness: `lower::tests::a_graded_bridge_is_refused_by_name`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Former(_, _))
                )
        },
    )]
    fn formed_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.peek()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let _keyword = cursor.tile(label);
        let name = self.name_at(at);
        let Maybe::Present(former) = type_former(name)
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: at.span,
                name,
                arity: HeadArity::Unary,
            });
        };
        if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_OPEN) {
            if former != TypeFormer::Thunk {
                return Err(site.folded(FormName::GRADE, FragmentBoundary::Unadmitted));
            }
            self.grade(site, &mut cursor)?;
        }
        let argument = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;

        self.apply_former(site, former, argument.node)
    }

    /// Read a bridge's grade, `[r]`, admitting only the default `ω`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the grade's `[`.
    /// - ensures: `ω` followed by `]` reads as the bridge with no grade
    ///   written, the cursor past the `]`.
    /// - provides: the one grade the core's bridge carries.
    /// - fails: [`LoweringRefusal::GradedBridge`] for a numeral or a name as
    ///   the grade, at the grade; a misplaced-tile fault for a grade out of
    ///   shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The grade's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the default grade, a numeral and a name, each
    ///   asserted as the lowered bridge or the exact refusal.
    /// - witness: `lower::tests::a_graded_bridge_is_refused_by_name`
    #[spec(
        captures: input = {
            let mut input = cursor.clone();
            (input.read(), input.read(), input.peek())
        },
        ensures: |ret| {
            ret.is_ok()
                == matches!(
                    input,
                    (
                        Maybe::Present(Piece::Tile {
                            label: TileName::OMEGA,
                            ..
                        }),
                        Maybe::Present(Piece::Tile {
                            label: TileName::BRACKET_CLOSE,
                            ..
                        }),
                        _
                    )
                )
                && (ret.is_err() || cursor.peek() == input.2)
        },
    )]
    fn grade(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.peek()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        if label == TileName::NUMBER || label == TileName::IDENTIFIER {
            return Err(LoweringRefusal::GradedBridge {
                span: at.span,
                grade: self.name_at(at),
            });
        }
        closed(site, cursor, TileName::OMEGA)?;

        closed(site, cursor, TileName::BRACKET_CLOSE)
    }

    /// Plan `former` applied to `argument` at `site`.
    ///
    /// # Specification
    /// - requires: `argument` is the one operand the former was written with.
    /// - ensures: the thunk former stands at value-type sort with its argument
    ///   read at computation-type sort, and the returner former stands at
    ///   computation-type sort with its argument read at value-type sort; the
    ///   former decides both, so nothing is pushed down that has to be
    ///   re-derived.
    /// - provides: the one place a type former's sorts are decided.
    /// - fails: yields the wrong-sort refusal for a former whose produced sort
    ///   does not suit the position.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — thunk and returner read the argument in opposite
    ///   sorts; each then lowers to its own core bridge former, not the other
    ///   one.
    /// - witness: `lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
    /// - witness: `lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Former(stored, child)) if stored == former && child == argument)
                    && self.reading(argument)
                        == match former {
                            | TypeFormer::Thunk => Reading::CompType(site.reading.frame()),
                            | TypeFormer::Returner => Reading::ValueType(site.reading.frame()),
                        })
        },
    )]
    fn apply_former(
        &mut self,
        site: Site,
        former: TypeFormer,
        argument: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let produced = match former {
            | TypeFormer::Thunk => Produced::ValueType,
            | TypeFormer::Returner => Produced::CompType,
        };
        let frame = self.require(site, produced)?;
        let inner = match former {
            | TypeFormer::Thunk => Reading::CompType(frame),
            | TypeFormer::Returner => Reading::ValueType(frame),
        };
        self.read(argument, inner);

        self.plan(site, Plan::Former(former, argument));

        Ok(())
    }

    /// Classify an arrow type: the computation arrow `A -> C`, or the static
    /// Pi `A -> B` where a value type is read.
    ///
    /// # Specification
    /// - requires: `site` is an arrow in type position, or in value position
    ///   where a type is quoted.
    /// - ensures: an arrow standing as a value type is the static Pi, its
    ///   domain and codomain each read as a value type under the arrow's own
    ///   frame, since the codomain binds nothing; any other arrow stands as a
    ///   computation type, reads its domain as a value type and its codomain as
    ///   a computation type. Either is planned over both operands.
    /// - provides: the function type of the fragment and the classifier of a
    ///   type operator.
    /// - fails: yields the wrong-sort refusal where neither sort suits the
    ///   position, and either hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The arrow's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an arrow where a computation type is read, where a
    ///   value type is read, nested to the right as an operator's classifier,
    ///   and over a computation codomain where a value type is read, each
    ///   asserted as the exact core node read back out of the arena or the
    ///   exact refusal.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
    /// - witness: `lower::tests::a_computation_codomain_of_a_static_pi_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || match self.plans.get(usize::from(site.at.node)) {
                    | Some(&Plan::StaticPi(..)) => matches!(site.reading, Reading::ValueType(_)),
                    | Some(&Plan::Arrow(..)) => !matches!(site.reading, Reading::ValueType(_)),
                    | _ => false,
                }
        },
    )]
    fn arrow(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let static_pi = matches!(site.reading, Reading::ValueType(_));
        let produced = if static_pi {
            Produced::ValueType
        }
        else {
            Produced::CompType
        };
        let frame = self.require(site, produced)?;
        let domain = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::ARROW)?;
        let codomain = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(domain.node, Reading::ValueType(frame));
        if static_pi {
            self.read(codomain.node, Reading::ValueType(frame));
            self.plan(site, Plan::StaticPi(domain.node, codomain.node));
        }
        else {
            self.read(codomain.node, Reading::CompType(frame));
            self.plan(site, Plan::Arrow(domain.node, codomain.node));
        }

        Ok(())
    }

    /// Classify an eager product type, `A * B`, and the chain it heads.
    ///
    /// # Specification
    /// - requires: `site` is a product in type position, or in value position
    ///   where a type is quoted.
    /// - ensures: the product stands as a value type; an operand that is itself
    ///   an unparenthesized product contributes its own operands instead, so a
    ///   chain `A * B * C` is one product of three components however it
    ///   associates, while `(A * B) * C` keeps the parenthesized product as one
    ///   component. Every component is read as a value type under the product's
    ///   frame, in written order, and the product is planned over them; the
    ///   inner products of the chain are not read.
    /// - provides: the eager product of the fragment.
    /// - fails: yields the wrong-sort refusal where no value type is read, and
    ///   the refusal of any product in the chain out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The product's refusal.
    ///
    /// # Termination
    /// Each round of the chain walk consumes fuel and replaces one product of
    /// the finite tree by its two operands.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a product of atoms, a chain of three, a parenthesized
    ///   inner product and a product where a computation type is read, each
    ///   asserted as the exact core node read back out of the arena or the
    ///   exact refusal.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Product(components)) if components.end.saturating_sub(components.start) >= 2_usize
                )
        },
    )]
    fn product(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let start = self.operands.len();
        let [first, second] = halves(site, &mut cursor)?;
        let mut pending = Vec::from([second, first]);
        while let Some(operand) = pending.pop() {
            match self.fuel.spend().and_then(|()| self.chained(site, operand)) {
                | Ok(Some([inner_first, inner_second])) => {
                    pending.extend([inner_second, inner_first]);
                },
                | Ok(None) => self.operands.push(operand),
                | Err(refusal) => {
                    self.operands.truncate(start);
                    return Err(refusal);
                },
            }
        }
        let components = Stretch {
            start,
            end: self.operands.len(),
        };
        for position in components.start .. components.end {
            if let Some(&component) = self.operands.get(position) {
                self.read(component, Reading::ValueType(frame));
            }
        }

        self.plan(site, Plan::Product(components));

        Ok(())
    }

    /// The two operands of `operand` when it is an unparenthesized product, a
    /// link of the chain a product heads.
    ///
    /// # Specification
    /// - requires: `operand` is an operand of a product at `site`.
    /// - ensures: a product form answers its operands in written order; any
    ///   other node, a parenthesized product included, answers nothing.
    /// - provides: the one place a product chain is followed.
    /// - fails: a repaired or ill-shaped product in the chain yields its own
    ///   refusal; [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// The inner product's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of three and a parenthesized inner product
    ///   separate the followed link from the kept component.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |halves| halves.is_none_or(|[first, second]| first != operand && second != operand)))]
    fn chained(
        &mut self,
        site: Site,
        operand: NodeIndex,
    ) -> Result<Option<[NodeIndex; 2]>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(operand)
        else {
            return Ok(None);
        };
        let Shape::Form {
            name,
            former: Former::ProductType,
        } = shape_of(self.pbg, node)?
        else {
            return Ok(None);
        };
        let link = Site {
            at: Placed::of(operand, node),
            name,
            reading: site.reading,
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, operand, &mut scratch).and_then(|()| {
            if let Maybe::Present(repaired) = scratch.repair {
                return Err(repaired.refusal(name));
            }
            halves(link, &mut Cursor::new(&scratch.pieces, link.at.span))
        });
        self.scratch = scratch;

        read.map(Some)
    }

    /// Classify a value function space, `A => B` or `(A1, …, An) => B`, `n`
    /// zero included.
    ///
    /// # Specification
    /// - requires: `site` is a value function space in type position, or in
    ///   value position where a type is quoted.
    /// - ensures: the alias stands as a value type; its domains — each member
    ///   of a parenthesised list written before `=>`, none for `()`, else the
    ///   one operand there — and its codomain are each read as value types
    ///   under its own frame, and it is planned as the thunked arrow over them.
    /// - provides: the value function space, the alias of `+U (A1 -> … -> An ->
    ///   -F B)`, which is `+U (-F B)` at no domain.
    /// - fails: yields the wrong-sort refusal where no value type is read,
    ///   either hole's own refusal, and a domain list's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The alias's refusal.
    ///
    /// # Termination
    /// The domain loop runs once per entry of the finite domain stretch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no domain, one domain, a list of two, and an alias
    ///   nested to the right, each asserted as the same core node the thunked
    ///   arrow it stands for lowers to.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::ValueFunction(domains, _)) if domains.start <= domains.end
                )
        },
    )]
    fn value_function(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let domain = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::FAT_ARROW)?;
        let codomain = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        let start = self.operands.len();
        if let Err(refusal) = self.domains(domain) {
            self.operands.truncate(start);
            return Err(refusal);
        }
        let domains = Stretch {
            start,
            end: self.operands.len(),
        };
        for position in domains.start .. domains.end {
            if let Some(&each) = self.operands.get(position) {
                self.read(each, Reading::ValueType(frame));
            }
        }
        self.read(codomain.node, Reading::ValueType(frame));

        self.plan(site, Plan::ValueFunction(domains, codomain.node));

        Ok(())
    }

    /// Append the domains a value function space's domain operand writes to
    /// the operand store.
    ///
    /// # Specification
    /// - requires: `domain` is the operand written before `=>`.
    /// - ensures: nothing for the empty list `()`, so `() => C` takes no
    ///   argument; each member of an unrepaired parenthesised list of more than
    ///   one, left to right; else `domain` itself, whose own reading groups or
    ///   reports a repair.
    /// - provides: the n-ary domain of the alias, the one place a type list is
    ///   read.
    /// - fails: yields the list's refusal for a member out of shape;
    ///   [`LoweringRefusal::UnknownMold`] for a mold the grammar does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// The list's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no domain, one domain and a list of two, each
    ///   asserted through the alias it lowers.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        captures: before = self.operands.len(),
        ensures: |ret| ret.is_err() || self.operands.len() >= before,
    )]
    fn domains(
        &mut self,
        domain: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(domain.node)
        else {
            self.operands.push(domain.node);
            return Ok(());
        };
        let Shape::Form {
            name,
            former: Former::ParenthesizedType,
        } = shape_of(self.pbg, node)?
        else {
            self.operands.push(domain.node);
            return Ok(());
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, domain.node, &mut scratch);
        let listed = read.and_then(|()| {
            let commas = scratch.pieces.iter().any(
                |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::COMMA),
            );
            let empty = !scratch
                .pieces
                .iter()
                .any(|piece| matches!(*piece, Piece::Operand(_)));
            if empty && let Maybe::Absent(_) = scratch.repair {
                Ok(())
            }
            else if commas && let Maybe::Absent(_) = scratch.repair {
                let list = Site {
                    at: domain,
                    name,
                    reading: Reading::Unread,
                };
                arguments(
                    list,
                    &mut Cursor::new(&scratch.pieces, domain.span),
                    &mut self.operands,
                )
            }
            else {
                self.operands.push(domain.node);
                Ok(())
            }
        });
        self.scratch = scratch;

        listed
    }

    /// Classify a static abstraction, `\A. T`.
    ///
    /// # Specification
    /// - requires: `site` is a static abstraction in term or type position.
    /// - ensures: an abstraction standing as a value binds its one type name in
    ///   a frame extending its own, untyped — the checker reads the type from
    ///   the operator's signature — reads its body as a value under that frame,
    ///   so a type written there is quoted, and is planned as the static lambda
    ///   over it.
    /// - provides: the introduction of a type operator.
    /// - fails: yields the wrong-sort refusal where no value is read, a
    ///   misplaced-tile fault for a binder out of shape, the binder policy's
    ///   refusal, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The abstraction's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one abstraction, two nested whose body names both
    ///   binders, and an abstraction where a value type is read, each asserted
    ///   as the exact core node read back out of the arena or the exact
    ///   refusal.
    /// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::StaticLambda(_))
                )
        },
    )]
    fn static_abstraction(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        closed(site, &mut cursor, TileName::BACKSLASH)?;
        let binder = match cursor.peek() {
            | Maybe::Present(Piece::Tile { label, at })
                if label == TileName::TYPE_IDENTIFIER || label == TileName::TYPE_VARIABLE =>
            {
                let _binder = cursor.tile(label);
                at
            },
            | Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) | Maybe::Absent(_) => {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            },
        };
        closed(site, &mut cursor, TileName::DOT)?;
        let body = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;
        let extended = self.scope.extend(frame, name);
        self.read(body.node, Reading::Value(Frame::Inner(extended)));

        self.plan(site, Plan::StaticLambda(body.node));

        Ok(())
    }

    /// Classify a parenthesised type, `(T)`.
    ///
    /// # Specification
    /// - requires: `site` is a parenthesised type in type position.
    /// - ensures: the one operand is read at the form's own reading and
    ///   adopted.
    /// - provides: grouping in type position.
    /// - fails: yields the empty-list refusal for `()`, which is never the unit
    ///   type, the hole's own refusal, and a misplaced-tile fault at the first
    ///   comma of a list, which only a value function space's domain reads.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — parenthesized type operands keep the surrounding
    ///   reading and lower to the wrapped type rather than introducing a core
    ///   constructor; empty parentheses are refused by name.
    /// - witness: `lower::tests::an_arrow_lowers_under_a_thunk_type`
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::tests::the_empty_parentheses_are_never_the_unit`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Transparent(child)) if self.reading(child) == site.reading)
        },
    )]
    fn parenthesized_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _open = cursor.tile(TileName::PAREN_OPEN);
        let run = cursor.operands();
        if let Run::Empty(_) = run {
            let unit = Site {
                name: FormName::UNIT,
                ..site
            };
            return Err(unit.out(FragmentBoundary::EmptyList));
        }
        let inner = site.one(run)?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        self.read(inner.node, site.reading);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// How `position` is read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position yields its stored reading; an absent position
    ///   is unread.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — paired declarations and refused siblings retain
    ///   distinct readings through the ascending classification sweep.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[spec(
        ensures: |ret| {
            ret == self
                .readings
                .get(usize::from(position))
                .copied()
                .unwrap_or(Reading::Unread)
        },
    )]
    fn reading(
        &self,
        position: NodeIndex,
    ) -> Reading
    {
        self.readings
            .get(usize::from(position))
            .copied()
            .unwrap_or(Reading::Unread)
    }

    /// Read `position` as `reading`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position takes the supplied reading without resizing
    ///   the table; an absent position changes nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signatures, definitions and nested binder bodies
    ///   receive their own expected sorts and frames.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    #[spec(
        captures: count = self.readings.len(),
        ensures: |_| {
            self.readings.len() == count
                && self
                    .readings
                    .get(usize::from(position))
                    .is_none_or(|held| *held == reading)
        },
    )]
    fn read(
        &mut self,
        position: NodeIndex,
        reading: Reading,
    )
    {
        if let Some(held) = self.readings.get_mut(usize::from(position)) {
            *held = reading;
        }
    }

    /// Record `plan` for the form at `site`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position takes the supplied plan without resizing the
    ///   table; an absent position changes nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — literals, applications and quoted types preserve
    ///   their planned former through the minting sweep; their concrete
    ///   operands are checked by the consumer witnesses rather than copied into
    ///   a snapshot.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    #[spec(
        captures: before = (self.plans.len(), core::mem::discriminant(&plan)),
        ensures: |_| {
            self.plans.len() == before.0
                && self
                    .plans
                    .get(usize::from(site.at.node))
                    .is_none_or(|held| core::mem::discriminant(held) == before.1)
        },
    )]
    fn plan(
        &mut self,
        site: Site,
        plan: Plan,
    )
    {
        if let Some(held) = self.plans.get_mut(usize::from(site.at.node)) {
            *held = plan;
        }
    }

    /// The source text of `placed`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a node with a source fragment yields that fragment; an absent
    ///   fragment yields empty text.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source literal text is interpreted at its own syntax
    ///   node and malformed lexemes retain their exact refusal span.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    /// - witness: `lower::tests::a_malformed_text_literal_is_refused`
    #[spec(
        ensures: |ret| {
            self.tree.fragment(placed.node).map_or_else(
                || ret.as_ref().is_empty(),
                |fragment| ret.as_ref() == fragment.as_ref(),
            )
        },
    )]
    fn text_at(
        &self,
        placed: Placed,
    ) -> SourceFragment<'source>
    {
        self.tree
            .fragment(placed.node)
            .unwrap_or_else(|| SourceFragment::from(""))
    }

    /// The name `placed` spells.
    ///
    /// # Specification
    /// trivial.
    fn name_at(
        &self,
        placed: Placed,
    ) -> SurfaceName<'source>
    {
        SurfaceName::from(self.text_at(placed))
    }

    /// The descending sweep: mint every planned node and record its origin.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: every manifest type component's type is minted first, one
    ///   component at a time in signature order, each subtree descending, so a
    ///   type head that stands for a component adopts a type already minted
    ///   wherever it sits; every answer type a match reads its motive from is
    ///   minted next, the same way, so a match deeper than its function's
    ///   result finds that result minted. Every other planned node is then
    ///   minted, with its children already minted because the level-order
    ///   layout puts them at strictly higher positions; every minted node gets
    ///   an origin naming the syntax node that produced it, terms and types
    ///   alike, while an adopted child keeps its own. A node whose position
    ///   bridges its sort has the bridge minted over its own core node, with
    ///   the same syntax node's origin marked as inserted. A node under a
    ///   declaration that refused is not minted, and neither is any node above
    ///   it, unless it lies inside an attribute payload: the side table files a
    ///   payload whatever its declaration's outcome, so an expectation about a
    ///   refused declaration stays readable. Last, the body of every witness
    ///   whose member and own type are unrefused is minted as that member's
    ///   constant, its origin the form that stated the second type.
    /// - provides: the whole allocation half of the lowering.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the sweep outruns the
    ///   allowance; nothing else, because every decision was made ascending.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifest component named before and after its own
    ///   position in the tree, and a witness agreeing and disagreeing with its
    ///   member, each asserted through the checker's verdict.
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `modules::modules::nested_member_signature_constrains_the_parent_binding`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body takes the plan of every node once; the check reads each plan once"
        )
    )]
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || self.plans.iter().enumerate().all(|(position, plan)| {
                    let position = NodeIndex::from(position);
                    (self.collected.refused(position).0 && !self.in_payload(position).0)
                        || *plan == Plan::Unplanned
                })
        },
    )]
    fn mint(
        &mut self,
        sink: &mut Sink<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut manifests: Vec<NodeIndex> = self
            .collected
            .structures
            .iter()
            .flat_map(|structure| structure.types.iter().map(|manifest| manifest.defined.node))
            .collect();
        manifests.extend(self.answers.values().map(|answer| answer.node));
        manifests.reverse();
        let mut subtree: Vec<NodeIndex> = Vec::new();
        let mut work: Vec<NodeIndex> = Vec::new();
        while let Some(root) = manifests.pop() {
            subtree.clear();
            work.push(root);
            while let Some(position) = work.pop() {
                self.fuel.spend()?;
                subtree.push(position);
                work.extend(self.tree.children(position));
            }
            subtree.sort_unstable_by(|left, right| right.cmp(left));
            for &position in &subtree {
                self.mint_at(position, sink);
            }
        }
        let mut remaining = usize::from(self.tree.node_count());
        while let Some(next) = remaining.checked_sub(1_usize) {
            remaining = next;
            self.fuel.spend()?;
            self.mint_at(NodeIndex::from(next), sink);
        }
        for (position, slot) in self.collected.slots.iter().enumerate() {
            if let Maybe::Present(Half {
                declaration,
                operand: Operand::Member(target),
            }) = slot.definition
                && let Maybe::Absent(_) = slot.refusal
                && let Some(member) = self.collected.slots.get(usize::from(target))
                && let Maybe::Absent(_) = member.refusal
                && let Maybe::Present(origin) = self.origin_at(declaration.node)
            {
                let id = sink.arena.value_constant(member.constant);
                let _minted = sink.value(id, origin);
                let _replaced = self.witnessed.insert(SlotIndex::from(position), id);
            }
        }

        Ok(())
    }

    /// Mint the node at `position` by its plan, once.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the node's plan is taken and minted, its bridge written over
    ///   it and the result kept as the node's lowered core node; a node with no
    ///   plan left, or under a refused declaration outside a payload, is left
    ///   as it is.
    /// - provides: the per-position half of [`Self::mint`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused declaration leaves its ordinary plans
    ///   untouched but still permits its attribute payloads to mint; consumed
    ///   plans are not minted twice when a manifest and the full traversal both
    ///   reach them.
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        captures: before = (
            self.collected.refused(position).0 && !self.in_payload(position).0,
            matches!(
                self.plans.get(usize::from(position)),
                None | Some(&Plan::Unplanned)
            ),
            self.lowered_at(position),
            self.plans.len(),
            self.lowered.len(),
        ),
        ensures: self.plans.len() == before.3
            && self.lowered.len() == before.4
            && (if before.0 || before.1 {
                self.lowered_at(position) == before.2
            }
            else {
                matches!(
                    self.plans.get(usize::from(position)),
                    Some(&Plan::Unplanned)
                )
            }),
    )]
    fn mint_at(
        &mut self,
        position: NodeIndex,
        sink: &mut Sink<'_>,
    )
    {
        if self.collected.refused(position).0 && !self.in_payload(position).0 {
            return;
        }
        let Some(planned) = self.plans.get_mut(usize::from(position))
        else {
            return;
        };
        let plan = core::mem::replace(planned, Plan::Unplanned);
        if plan == Plan::Unplanned {
            return;
        }
        let Maybe::Present(origin) = self.origin_at(position)
        else {
            return;
        };
        let bridge = self
            .bridges
            .get(usize::from(position))
            .copied()
            .unwrap_or(Bridge::Bare);
        let minted = self.mint_plan(plan, sink, origin);
        let bridged = sink.bridge(minted, bridge, origin);
        if self.leaving.contains(&position)
            && let Maybe::Present(Lowered::Computation(exit)) = bridged
        {
            let _first = sink.exits.insert(exit);
        }
        if let Some(held) = self.lowered.get_mut(usize::from(position)) {
            *held = bridged;
        }
    }

    /// The origin of a core node the syntax node at `position` wrote.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live syntax node yields its own position and span as
    ///   written provenance; a missing node is unminted.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each minted family records the syntax origin that
    ///   produced it, independently of inserted bridges.
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret == self
                .tree
                .node(position)
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |node| {
                    Maybe::Present(Origin::new(position, node.span()))
                })
        },
    )]
    fn origin_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<Origin, lowered::Absent>
    {
        self.tree
            .node(position)
            .map_or(Maybe::Absent(lowered::Absent::Unminted), |node| {
                Maybe::Present(Origin::new(position, node.span()))
            })
    }

    /// Carry out one plan.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the plan's core node, minted over its children's lowered
    ///   nodes with its origin recorded; an adopted child's own node for a
    ///   transparent plan; nothing when a child did not lower at the sort the
    ///   plan takes. Every variable is minted in the intuitionistic zone, the
    ///   only zone the fragment binds into; a decode's code carries the written
    ///   origin and its type the inserted one.
    /// - provides: the per-node half of [`Self::mint`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the admitted plan families lower to their matching
    ///   core families; grouping reuses its child result and an unplanned node
    ///   cannot manufacture a value. Concrete constructors and origins are
    ///   witnessed through complete declarations and the fragment-specific
    ///   examples.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        captures: promised = (
            match plan {
                | Plan::Variable(_)
                | Plan::ValueHole(_)
                | Plan::Constant(_)
                | Plan::Primitive(_)
                | Plan::Unit
                | Plan::Literal(_)
                | Plan::StaticApplication(..)
                | Plan::Tuple(_)
                | Plan::StaticLambda(_)
                | Plan::Thunk(_)
                | Plan::Constructor(_) => Some(Produced::Value),
                | Plan::CompHole(_) | Plan::PrimitiveCall(..) | Plan::Return(_) | Plan::Force(_) | Plan::Lambda(_) | Plan::Block(_) | Plan::Application(..) | Plan::Case(_) | Plan::EmptyCase(_) => {
                    Some(Produced::Computation)
                },
                | Plan::Atom(_)
                | Plan::Universe(_)
                | Plan::ValueFunction(..)
                | Plan::StaticPi(..)
                | Plan::Product(..)
                | Plan::Former(TypeFormer::Thunk, _)
                | Plan::Data(..) => Some(Produced::ValueType),
                | Plan::Arrow(..) | Plan::Former(TypeFormer::Returner, _) => {
                    Some(Produced::CompType)
                },
                | Plan::Decode(_, _, universe) => Some(match universe.sort {
                    | GroundSort::Value => Produced::ValueType,
                    | GroundSort::Computation => Produced::CompType,
                }),
                | Plan::Unplanned | Plan::Transparent(_) | Plan::Function(_) => None,
            },
            match plan {
                | Plan::Transparent(child) => Some(self.lowered_at(child)),
                | _ => None,
            },
            matches!(plan, Plan::Unplanned),
            matches!(plan, Plan::Function(_)),
        ),
        ensures: |ret| {
            promised.1.map_or_else(
                || {
                    if promised.2 {
                        ret == Maybe::Absent(lowered::Absent::Unminted)
                    }
                    else if promised.3 {
                        matches!(
                            ret,
                            Maybe::Absent(_) | Maybe::Present(Lowered::Function { .. })
                        )
                    }
                    else {
                        matches!(
                            (promised.0, ret),
                            (Some(_), Maybe::Absent(_))
                                | (Some(Produced::Value), Maybe::Present(Lowered::Value(_)))
                                | (
                                    Some(Produced::Computation),
                                    Maybe::Present(Lowered::Computation(_))
                                )
                                | (
                                    Some(Produced::ValueType),
                                    Maybe::Present(Lowered::ValueType(_))
                                )
                                | (
                                    Some(Produced::CompType),
                                    Maybe::Present(Lowered::CompType(_))
                                )
                        )
                    }
                },
                |child| ret == child,
            )
        },
    )]
    fn mint_plan(
        &self,
        plan: Plan,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match plan {
            | Plan::ValueHole(hole) => {
                let id = sink.arena.value_hole(hole);
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::CompHole(hole) => {
                let id = sink.arena.computation_hole(hole);
                Maybe::Present(sink.computation(id, origin))
            },
            | Plan::Primitive(primitive) => {
                let id = primitive.thunk(sink.arena);
                if let Some(&Value::Primitive { body, .. }) = sink.arena.value(id) {
                    let mut current = body;
                    let mut ancestors = [body; 3];
                    let mut count = 0_usize;
                    for ancestor in &mut ancestors {
                        *ancestor = current;
                        count = count.saturating_add(1);
                        match sink.arena.computation(current) {
                            | Some(&Computation::Lambda(inner)) => current = inner,
                            | Some(&Computation::Primitive { ref arguments, .. }) => {
                                for &argument in arguments.iter().rev() {
                                    sink.origins.record_value(argument, origin);
                                }
                                break;
                            },
                            | _ => break,
                        }
                    }
                    for &computation in ancestors.iter().take(count).rev() {
                        sink.origins.record_computation(computation, origin);
                    }
                }
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::PrimitiveCall(primitive, arguments) => {
                use gandr_core_term::primitive::Arguments;
                let arguments = match arguments {
                    | Arguments::Unary(argument) => self.value_at(argument).map(Arguments::Unary),
                    | Arguments::Binary([first, second]) => {
                        self.value_at(first).and_then(|first| {
                            self.value_at(second)
                                .map(|second| Arguments::Binary([first, second]))
                        })
                    },
                };
                arguments.map(|arguments| {
                    let id = sink.arena.computation_primitive(primitive, arguments);
                    sink.computation(id, origin)
                })
            },
            | Plan::Unplanned => Maybe::Absent(lowered::Absent::Unminted),
            | Plan::Variable(index) => {
                let id = sink.arena.value_variable(Zone::Intuitionistic, index);
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::Constant(constant) => {
                let id = sink.arena.value_constant(constant);
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::Unit => {
                let id = sink.arena.value_unit();
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::Literal(literal) => {
                let id = sink.arena.value_literal(literal);
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::Atom(atom) => Maybe::Present(sink.atom(atom, origin)),
            | Plan::Universe(universe) => {
                let id = sink.arena.value_type_universe(
                    Sort::Ground(universe.sort),
                    Level::constant(universe.level),
                );
                sink.origins.record_value_type(id, origin);
                Maybe::Present(Lowered::ValueType(id))
            },
            | Plan::Decode(code, arguments, universe) => {
                self.mint_decode(code, arguments, universe, sink, origin)
            },
            | Plan::StaticApplication(code, arguments) => self
                .mint_code(code, arguments, sink, origin)
                .map(Lowered::Value),
            | Plan::Tuple(members) => self.mint_tuple(members, sink, origin),
            | Plan::ValueFunction(domains, codomain) => {
                self.mint_value_function(domains, codomain, sink, origin)
            },
            | Plan::Transparent(child) => self.lowered_at(child),
            | Plan::Former(former, argument) => self.mint_former(former, argument, sink, origin),
            | Plan::Application(head, arguments) => {
                self.mint_application(head, arguments, sink, origin)
            },
            | Plan::Function(function) => self.mint_function(&function, sink, origin),
            | Plan::Data(constant, arguments) => {
                self.mint_family(constant, arguments, sink, origin)
            },
            | Plan::Constructor(constructed) => self.mint_constructor(constructed, sink, origin),
            | Plan::Case(case) => self.mint_case(case, sink, origin),
            | Plan::EmptyCase(scrutinee) => self.value_at(scrutinee).map(|scrutinised| {
                let id = sink.arena.computation_case(scrutinised, &[]);
                sink.computation(id, origin)
            }),
            | Plan::Product(components) => self.mint_product(components, sink, origin),
            | Plan::Block(block) => self.mint_block(block, sink).map(Lowered::Computation),
            | Plan::Arrow(..)
            | Plan::StaticPi(..)
            | Plan::StaticLambda(_)
            | Plan::Thunk(_)
            | Plan::Return(_)
            | Plan::Force(_)
            | Plan::Lambda(_) => self.mint_over(&plan, sink, origin),
        }
    }

    /// Mint a code: its head, applied statically to the arguments `arguments`
    /// names in the operand store, left to right.
    ///
    /// # Specification
    /// - requires: every type position has been classified, so every binder a
    ///   code names is recorded as mentioned; every argument is already minted
    ///   or absent.
    /// - ensures: a binder's head is the variable at its telescope index from
    ///   the use site and a declaration's the constant; `h(v1, …, vn)` mints as
    ///   `sapp(… sapp(h, v1) …, vn)`, every node with the written origin;
    ///   nothing is minted when an argument did not lower.
    /// - provides: the head of a decode and the value of a static application.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Both loops run once per entry of the finite stretch `arguments`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare binder, a bare declaration, and an operator
    ///   applied to one and to three arguments, each asserted as the exact core
    ///   node read back out of the arena.
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(id) => match sink.arena.value(id) {
                | Some(&gandr_core_term::Value::StaticApplication(..)) => {
                    arguments.start < arguments.end
                },
                | Some(
                    &(gandr_core_term::Value::Variable { .. }
                    | gandr_core_term::Value::Constant(_)),
                ) => arguments.start >= arguments.end,
                | _ => false,
            },
            | Maybe::Absent(_) => true,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — bound and constant codes are applied to their
    ///   arguments in source order; every node in the static application spine
    ///   records the written origin, rather than an inserted decode origin.
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| match stretch(&self.operands, arguments)
            .iter()
            .find_map(|&argument| match self.value_at(argument) {
                | Maybe::Present(_) => None,
                | Maybe::Absent(reason) => Some(reason),
            }) {
            | Some(reason) => ret == Maybe::Absent(reason),
            | None => {
                matches!(ret, Maybe::Present(id) if sink.origins.value(id) == Maybe::Present(origin))
            },
        },
    )]
    fn mint_code(
        &self,
        code: Code,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        let written = stretch(&self.operands, arguments);
        for &argument in written {
            if let Maybe::Absent(reason) = self.value_at(argument) {
                return Maybe::Absent(reason);
            }
        }
        let mut applied = match code {
            | Code::Bound { from, binder } => sink.arena.value_variable(
                Zone::Intuitionistic,
                self.scope.telescope_index(from, binder),
            ),
            | Code::Constant(constant) => sink.arena.value_constant(constant),
        };
        sink.origins.record_value(applied, origin);
        for &argument in written {
            let Maybe::Present(passed) = self.value_at(argument)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            applied = sink.arena.value_static_application(applied, passed);
            sink.origins.record_value(applied, origin);
        }

        Maybe::Present(applied)
    }

    /// Carry out a decode's plan: the code, and the type it denotes.
    ///
    /// # Specification
    /// - requires: as [`Self::mint_code`] does.
    /// - ensures: the code [`Self::mint_code`] mints, with the written origin;
    ///   the type is the decode of that code at the universe's level, a value
    ///   type for the value sort and a computation type for the computation
    ///   sort, with the origin marked inserted; nothing when the code did not
    ///   lower.
    /// - provides: the decode half of a value name, bare or applied, in type
    ///   position.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decode at each sort, of a bare code and of an
    ///   applied one, each asserted as the exact core type read back out of the
    ///   arena.
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    #[spec(
        ensures: |ret| match (ret, universe.sort) {
            | (Maybe::Present(Lowered::ValueType(id)), GroundSort::Value) => {
                matches!(
                    sink.arena.value_type(id),
                    Some(&gandr_core_term::ValueType::Element { .. })
                )
            },
            | (Maybe::Present(Lowered::CompType(id)), GroundSort::Computation) => {
                matches!(
                    sink.arena.comp_type(id),
                    Some(&gandr_core_term::CompType::Element { .. })
                )
            },
            | (Maybe::Absent(_), _) => true,
            | _ => false,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — decoding uses the code’s written universe when
    ///   available and marks the element node as inserted, retaining the code’s
    ///   own origin.
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    #[spec(
        ensures: |ret| match stretch(&self.operands, arguments)
            .iter()
            .find_map(|&argument| match self.value_at(argument) {
                | Maybe::Present(_) => None,
                | Maybe::Absent(reason) => Some(reason),
            }) {
            | Some(reason) => ret == Maybe::Absent(reason),
            | None => match (universe.sort, ret) {
                | (GroundSort::Value, Maybe::Present(Lowered::ValueType(id))) => {
                    sink.origins.value_type(id)
                        == Maybe::Present(origin.inserted(Insertion::Decode))
                },
                | (GroundSort::Computation, Maybe::Present(Lowered::CompType(id))) => {
                    sink.origins.comp_type(id) == Maybe::Present(origin.inserted(Insertion::Decode))
                },
                | _ => false,
            },
        },
    )]
    fn mint_decode(
        &self,
        code: Code,
        arguments: Stretch,
        universe: Universe,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let value = match self.mint_code(code, arguments, sink, origin) {
            | Maybe::Present(value) => value,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let level = Level::constant(universe.level);
        let decoded = origin.inserted(Insertion::Decode);
        match universe.sort {
            | GroundSort::Value => {
                let id = sink.arena.value_type_element(value, level);
                sink.origins.record_value_type(id, decoded);
                Maybe::Present(Lowered::ValueType(id))
            },
            | GroundSort::Computation => {
                let id = sink.arena.comp_type_element(value, level);
                sink.origins.record_comp_type(id, decoded);
                Maybe::Present(Lowered::CompType(id))
            },
        }
    }
    /// Carry out a tuple's plan: its members, as one tuple.
    ///
    /// # Specification
    /// - requires: every member is already minted or absent.
    /// - ensures: `(v1, …, vn)` mints as one tuple of `n` components in written
    ///   order, with the written origin, so a tuple inhabits the product of as
    ///   many components that one `*` chain builds; nothing is minted when a
    ///   member did not lower.
    /// - provides: the introduction of the eager product.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per entry of the finite stretch `members`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple of two and a tuple of four keep their members
    ///   in order as one node; the node records the tuple's origin.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| {
            let written = stretch(&self.operands, members);
            match written
                .iter()
                .find_map(|&member| match self.value_at(member) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                }) {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::Value(id))
                        if sink.origins.value(id) == Maybe::Present(origin)
                            && sink.arena.value(id).and_then(gandr_core_term::Value::components).is_some_and(|components| components.len() == written.len()))
                },
            }
        },
    )]
    fn mint_tuple(
        &self,
        members: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, members);
        let mut components = Vec::with_capacity(written.len());
        for &member in written {
            match self.value_at(member) {
                | Maybe::Present(component) => components.push(component),
                | Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_tuple(&components);

        Maybe::Present(sink.value(id, origin))
    }

    /// Carry out a product's plan: its components, as one product.
    ///
    /// # Specification
    /// - requires: every component is already minted or absent.
    /// - ensures: `A1 * … * An` mints as one product of `n` components in
    ///   written order, with the written origin; nothing is minted when a
    ///   component did not lower.
    /// - provides: the eager product type.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per entry of the finite stretch `components`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a product of two and a chain of four keep their
    ///   components in order as one node, which records the product's origin.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| {
            let written = stretch(&self.operands, components);
            match written
                .iter()
                .find_map(|&component| match self.value_type_at(component) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                }) {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id))
                        if sink.origins.value_type(id) == Maybe::Present(origin)
                            && sink.arena.value_type(id).is_some_and(|held| matches!(*held, ValueType::Product(ref parts) if parts.len() == written.len())))
                },
            }
        },
    )]
    fn mint_product(
        &self,
        components: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, components);
        let mut parts = Vec::with_capacity(written.len());
        for &component in written {
            match self.value_type_at(component) {
                | Maybe::Present(part) => parts.push(part),
                | Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_type_product(&parts);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Carry out a value function space's plan: the thunked arrow it is the
    /// alias of.
    ///
    /// # Specification
    /// - requires: every domain and the codomain are already minted or absent.
    /// - ensures: `(A1, …, An) => B` mints as `+U (A1 -> … -> An -> -F B)`,
    ///   every node with the written origin, so the alias and the thunked arrow
    ///   it names are one core type; nothing is minted when a domain or the
    ///   codomain did not lower.
    /// - provides: the value function space.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Both loops run once per entry of the finite stretch `domains`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one domain, a list of two, and an alias nested to the
    ///   right, each asserted as the same core node the thunked arrow it stands
    ///   for lowers to.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::ValueType(id)) => {
                matches!(
                    sink.arena.value_type(id),
                    Some(&gandr_core_term::ValueType::Thunk(_))
                )
            },
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — the value-function alias is a thunked arrow over a
    ///   returner, with domains in written order and the alias’s own origin.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| {
            let missing = stretch(&self.operands, domains)
                .iter()
                .find_map(|&domain| match self.value_type_at(domain) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                })
                .or_else(|| match self.value_type_at(codomain) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                });
            match missing {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            }
        },
    )]
    fn mint_value_function(
        &self,
        domains: Stretch,
        codomain: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, domains);
        for &domain in written {
            if let Maybe::Absent(reason) = self.value_type_at(domain) {
                return Maybe::Absent(reason);
            }
        }
        let returned = match self.value_type_at(codomain) {
            | Maybe::Present(returned) => returned,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut arrow = sink.arena.comp_type_returner(returned);
        sink.origins.record_comp_type(arrow, origin);
        for &domain in written.iter().rev() {
            let Maybe::Present(from) = self.value_type_at(domain)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            arrow = sink.arena.comp_type_arrow(from, arrow);
            sink.origins.record_comp_type(arrow, origin);
        }
        let id = sink.arena.value_type_thunk(arrow);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Carry out a type former's plan.
    ///
    /// # Specification
    /// - requires: the argument position is interpreted in this lowering run.
    /// - ensures: a thunk consumes a computation type and a returner consumes a
    ///   value type; successful nodes carry the supplied origin.
    /// - provides: the core bridge type over the already lowered argument.
    /// - fails: a missing or wrong-sort argument preserves its absence reason.
    /// - panics: none under the origin table’s ordered-identifier invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both bridge formers retain their argument type and
    ///   stay distinct from one another and from ordinary names with similar
    ///   spellings.
    /// - witness: `lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
    /// - witness: `lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    /// - witness: `lower::tests::u_and_f_are_names`
    #[spec(
        ensures: |ret| match former {
            | TypeFormer::Thunk => match self.comp_type_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            },
            | TypeFormer::Returner => match self.value_type_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::CompType(id)) if sink.origins.comp_type(id) == Maybe::Present(origin))
                },
            },
        },
    )]
    fn mint_former(
        &self,
        former: TypeFormer,
        argument: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match former {
            | TypeFormer::Thunk => self.comp_type_at(argument).map(|inner| {
                let id = sink.arena.value_type_thunk(inner);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
            | TypeFormer::Returner => self.value_type_at(argument).map(|inner| {
                let id = sink.arena.comp_type_returner(inner);
                sink.origins.record_comp_type(id, origin);
                Lowered::CompType(id)
            }),
        }
    }

    /// Carry out the plan of a former over already-minted children.
    ///
    /// # Specification
    /// - requires: child positions are interpreted in this lowering run.
    /// - ensures: each supported plan yields its own term or type family, with
    ///   the supplied origin on the new outer node.
    /// - provides: core constructors over previously lowered children.
    /// - fails: unsupported plans are Unminted; missing or wrong-sort children
    ///   preserve the first required absence.
    /// - panics: none under the origin table’s ordered-identifier invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — arrows, static products, pairs, abstraction and
    ///   computation formers retain their distinct core constructors and child
    ///   order. These witnesses cover the admitted fragment, not arbitrary
    ///   foreign identifiers.
    /// - witness: `lower::tests::an_arrow_lowers_under_a_thunk_type`
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Absent(_) => true,
            | Maybe::Present(Lowered::Value(id)) => {
                matches!(*plan, Plan::StaticLambda(_) | Plan::Thunk(_))
                    && sink.origins.value(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::Computation(id)) => {
                matches!(*plan, Plan::Return(_) | Plan::Force(_) | Plan::Lambda(_))
                    && sink.origins.computation(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::ValueType(id)) => {
                matches!(*plan, Plan::StaticPi(_, _))
                    && sink.origins.value_type(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::CompType(id)) => {
                matches!(*plan, Plan::Arrow(_, _))
                    && sink.origins.comp_type(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::Function { .. }) => false,
        },
    )]
    fn mint_over(
        &self,
        plan: &Plan,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match *plan {
            | Plan::Arrow(domain, codomain) => self.value_type_at(domain).and_then(|from| {
                self.comp_type_at(codomain).map(|to| {
                    let id = sink.arena.comp_type_arrow(from, to);
                    sink.origins.record_comp_type(id, origin);
                    Lowered::CompType(id)
                })
            }),
            | Plan::StaticPi(domain, codomain) => self.value_type_at(domain).and_then(|from| {
                self.value_type_at(codomain).map(|to| {
                    let id = sink.arena.value_type_static_pi(from, to);
                    sink.origins.record_value_type(id, origin);
                    Lowered::ValueType(id)
                })
            }),
            | Plan::StaticLambda(body) => self.value_at(body).map(|under| {
                let id = sink.arena.value_static_lambda(under);
                sink.value(id, origin)
            }),
            | Plan::Thunk(body) => self.mint_body(body, sink, origin).map(|suspended| {
                let id = sink.arena.value_thunk(suspended);
                sink.value(id, origin)
            }),
            | Plan::Return(value) => self.value_at(value).map(|returned| {
                let id = sink.arena.computation_return(returned);
                sink.computation(id, origin)
            }),
            | Plan::Force(value) => self.value_at(value).map(|forced| {
                let id = sink.arena.computation_force(forced);
                sink.computation(id, origin)
            }),
            | Plan::Lambda(body) => self.mint_body(body, sink, origin).map(|under| {
                let id = sink.arena.computation_lambda(under);
                sink.computation(id, origin)
            }),
            | Plan::Unplanned
            | Plan::ValueHole(_)
            | Plan::CompHole(_)
            | Plan::Variable(_)
            | Plan::Constant(_)
            | Plan::Primitive(_)
            | Plan::PrimitiveCall(..)
            | Plan::Unit
            | Plan::Literal(_)
            | Plan::Atom(_)
            | Plan::Universe(_)
            | Plan::Decode(..)
            | Plan::StaticApplication(..)
            | Plan::Tuple(_)
            | Plan::ValueFunction(..)
            | Plan::Former(..)
            | Plan::Transparent(_)
            | Plan::Application(..)
            | Plan::Function(_)
            | Plan::Data(..)
            | Plan::Constructor(_)
            | Plan::Case(_)
            | Plan::EmptyCase(_)
            | Plan::Product(_)
            | Plan::Block(_) => Maybe::Absent(lowered::Absent::Unminted),
        }
    }

    /// Mint a block: its statements bound over its last computation.
    ///
    /// # Specification
    /// - requires: every node the block names is already minted or absent.
    /// - ensures: `run x1 <- c1 ; … run xn <- cn ; c` mints as `bind(c1, …
    ///   bind(cn, c))`, each bind's origin its statement's `run` tile; a block
    ///   of no statements is its last computation; nothing is minted when any
    ///   computation of the block did not lower.
    /// - provides: the block half of thunks, lambdas and function tails.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — run statements wrap the final computation in source
    ///   order, each bind records its run token, and an empty statement prefix
    ///   leaves the existing final computation unchanged.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| match self.computation_at(block.last) {
            | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
            | Maybe::Present(last) => {
                let statements = stretch(&self.statements, block.statements);
                let missing = statements.iter().find_map(|statement| {
                    match (
                        self.computation_at(statement.bound),
                        self.origin_at(statement.origin),
                    ) {
                        | (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => Some(reason),
                        | (Maybe::Present(_), Maybe::Present(_)) => None,
                    }
                });
                match missing {
                    | Some(reason) => ret == Maybe::Absent(reason),
                    | None => match statements.first() {
                        | None => ret == Maybe::Present(last),
                        | Some(first) => {
                            matches!(ret, Maybe::Present(id) if matches!((sink.origins.computation(id), self.origin_at(first.origin)), (Maybe::Present(stored), Maybe::Present(expected)) if stored == expected))
                        },
                    },
                }
            },
        },
    )]
    fn mint_block(
        &self,
        block: Block,
        sink: &mut Sink<'_>,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let statements = stretch(&self.statements, block.statements);
        let mut chain = match self.computation_at(block.last) {
            | Maybe::Present(last) => last,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for statement in statements {
            if let Maybe::Absent(reason) = self.computation_at(statement.bound) {
                return Maybe::Absent(reason);
            }
            if let Maybe::Absent(reason) = self.origin_at(statement.origin) {
                return Maybe::Absent(reason);
            }
        }
        for statement in statements.iter().rev() {
            let (Maybe::Present(bound), Maybe::Present(origin)) = (
                self.computation_at(statement.bound),
                self.origin_at(statement.origin),
            )
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let split = match statement.binding {
                | StatementBinding::Named => None,
                | StatementBinding::Discarded => Some(gandr_core_term::ComponentCount::default()),
                | StatementBinding::Split(arity) => Some(arity),
            };
            if let Some(arity) = split {
                let tuple = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(tuple, origin);
                let split = sink.arena.computation_split(tuple, arity, chain);
                sink.origins.record_computation(split, origin);
                chain = split;
            }
            let id = sink.arena.computation_bind(bound, chain);
            sink.origins.record_computation(id, origin);
            if statement.rest == exits::Rest::Distributed {
                let _first = sink.distributed.insert(id, origin);
            }
            chain = id;
        }

        Maybe::Present(chain)
    }

    /// Mint an application of `head` to `arguments`, left to right.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: `c(v1, …, vn)` mints as `app(… app(c, v1) …, vn)`, every
    ///   application carrying the call's origin; a call of no arguments is its
    ///   head's own computation; nothing is minted when the head or an argument
    ///   did not lower.
    /// - provides: the curried elimination of a lambda.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — applications associate to the left, force a value
    ///   head only once when required, and preserve authored versus inserted
    ///   origins.
    /// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        captures: written = stretch(&self.operands, arguments),
        ensures: |ret| match self.computation_at(head) {
            | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
            | Maybe::Present(called) => {
                match written
                    .iter()
                    .find_map(|&argument| match self.value_at(argument) {
                        | Maybe::Present(_) => None,
                        | Maybe::Absent(reason) => Some(reason),
                    }) {
                    | Some(reason) => ret == Maybe::Absent(reason),
                    | None if written.is_empty() => {
                        ret == Maybe::Present(Lowered::Computation(called))
                    },
                    | None => {
                        matches!(ret, Maybe::Present(Lowered::Computation(id)) if sink.origins.computation(id) == Maybe::Present(origin))
                    },
                }
            },
        },
    )]
    fn mint_application(
        &self,
        head: NodeIndex,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut applied = match self.computation_at(head) {
            | Maybe::Present(called) => called,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let arguments = stretch(&self.operands, arguments);
        for &argument in arguments {
            if let Maybe::Absent(reason) = self.value_at(argument) {
                return Maybe::Absent(reason);
            }
        }
        for &argument in arguments {
            let passed = match self.value_at(argument) {
                | Maybe::Present(passed) => passed,
                | Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
            let id = sink.arena.computation_application(applied, passed);
            sink.origins.record_computation(id, origin);
            applied = id;
        }

        Maybe::Present(Lowered::Computation(applied))
    }

    /// Mint a function tail: its body, and its declared type when it states
    /// one.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: `(x1: A1, …, xn: An) -> C { b }` mints its body as `thunk (λ
    ///   … λ. b)`, one lambda per parameter with the binder tile's origin and
    ///   the thunk marked as inserted at the declaration form; a recursive tail
    ///   closes its last parameter's lambda by a fixpoint marked as inserted at
    ///   the declaration form, `thunk (λ … λ. fix. λ. b)`, claiming structural
    ///   descent when a call claims it and partial otherwise; its declared type
    ///   is `+U (A1 -> … -> An -> C)`, one arrow per parameter with the binder
    ///   tile's origin and `+U` the declaration form's, an arrow dependent
    ///   where a later type names its parameter; a tail missing a parameter or
    ///   result type mints the body alone; nothing is minted when the block did
    ///   not lower.
    /// - provides: the function tail's two halves, from one reading.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — function tails produce an inserted thunk over their
    ///   lambda chain even when a missing parameter or result type prevents a
    ///   signature.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
    /// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_last_parameter`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Absent(_) => true,
            | Maybe::Present(Lowered::Function { signature, body }) => {
                sink.origins.value(body) == Maybe::Present(origin.inserted(Insertion::Thunk))
                    && match signature {
                        | Maybe::Absent(_) => true,
                        | Maybe::Present(id) => {
                            sink.origins.value_type(id) == Maybe::Present(origin)
                        },
                    }
            },
            | Maybe::Present(_) => false,
        },
    )]
    fn mint_function(
        &self,
        function: &Function,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let parameters = stretch(&self.parameters, function.parameters);
        for parameter in parameters {
            if let Maybe::Absent(reason) = self.origin_at(parameter.binder) {
                return Maybe::Absent(reason);
            }
        }
        let mut body = match self.mint_body(function.block, sink, origin) {
            | Maybe::Present(block) => block,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut fixpoint = match self.evidence(function) {
            | Maybe::Present(evidence) => Some(evidence),
            | Maybe::Absent(_) => None,
        };
        for parameter in parameters.iter().rev() {
            let Maybe::Present(binder) = self.origin_at(parameter.binder)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = sink.arena.computation_lambda(body);
            sink.origins.record_computation(id, binder);
            body = id;
            if let Some(evidence) = fixpoint.take() {
                let closed = sink.arena.computation_fixpoint(body, evidence);
                sink.origins
                    .record_computation(closed, origin.inserted(Insertion::Fixpoint));
                body = closed;
            }
        }
        let thunk = sink.arena.value_thunk(body);
        sink.origins
            .record_value(thunk, origin.inserted(Insertion::Thunk));

        Maybe::Present(Lowered::Function {
            signature: self.mint_signature(function, parameters, sink, origin),
            body: thunk,
        })
    }

    /// Mint a function tail's declared type, `+U (A1 -> … -> An -> C)`.
    ///
    /// # Specification
    /// - requires: `parameters` are the function's own, and every type position
    ///   has been classified, so every parameter a type names is recorded as
    ///   mentioned.
    /// - ensures: the declared type, as [`Self::mint_function`] states it, with
    ///   each parameter's arrow dependent exactly when a later parameter's type
    ///   or the result names it, and plain otherwise; nothing is minted when a
    ///   type is unstated or did not lower.
    /// - provides: the signature half of [`Self::mint_function`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter a later type names beside one no type
    ///   names, each asserted as the exact arrow read back out of the arena.
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    #[spec(
        ensures: |ret| match function.result {
            | Maybe::Absent(_) => ret == Maybe::Absent(lowered::Absent::Unstated),
            | Maybe::Present(result) => match self.comp_type_at(result) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    let missing =
                        parameters
                            .iter()
                            .find_map(|parameter| match parameter.declared {
                                | Maybe::Absent(_) => Some(lowered::Absent::Unstated),
                                | Maybe::Present(written) => match self.value_type_at(written) {
                                    | Maybe::Absent(reason) => Some(reason),
                                    | Maybe::Present(_) => None,
                                },
                            });
                    match missing {
                        | Some(reason) => ret == Maybe::Absent(reason),
                        | None if parameters.iter().any(|parameter| {
                            matches!(self.origin_at(parameter.binder), Maybe::Absent(_))
                        }) =>
                        {
                            ret == Maybe::Absent(lowered::Absent::Unminted)
                        },
                        | None => {
                            matches!(ret, Maybe::Present(id) if sink.origins.value_type(id) == Maybe::Present(origin))
                        },
                    }
                },
            },
        },
    )]
    fn mint_signature(
        &self,
        function: &Function,
        parameters: &[Parameter],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let Maybe::Present(result) = function.result
        else {
            return Maybe::Absent(lowered::Absent::Unstated);
        };
        let mut declared = match self.comp_type_at(result) {
            | Maybe::Present(result) => result,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for parameter in parameters {
            let Maybe::Present(written) = parameter.declared
            else {
                return Maybe::Absent(lowered::Absent::Unstated);
            };
            if let Maybe::Absent(reason) = self.value_type_at(written) {
                return Maybe::Absent(reason);
            }
        }
        for parameter in parameters.iter().rev() {
            let (Maybe::Present(written), Maybe::Present(binder)) =
                (parameter.declared, self.origin_at(parameter.binder))
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let Maybe::Present(domain) = self.value_type_at(written)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = if bool::from(self.scope.mentioned(parameter.frame)) {
                sink.arena.comp_type_pi(domain, declared)
            }
            else {
                sink.arena.comp_type_arrow(domain, declared)
            };
            sink.origins.record_comp_type(id, binder);
            declared = id;
        }
        let id = sink.arena.value_type_thunk(declared);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(id)
    }

    /// What `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position yields its stored lowering result; a missing
    ///   position is unminted.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — independently lowered children feed their parent and
    ///   a refused declaration does not prevent its sibling from lowering.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[spec(
        ensures: |ret| {
            ret == self
                .lowered
                .get(usize::from(position))
                .copied()
                .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
        },
    )]
    fn lowered_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        self.lowered
            .get(usize::from(position))
            .copied()
            .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
    }

    /// The value `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Value(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn value_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::Value(id) => Maybe::Present(id),
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The computation `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Computation(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn computation_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::Computation(id) => Maybe::Present(id),
            | Lowered::Value(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The value type `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::ValueType(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn value_type_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::ValueType(id) => Maybe::Present(id),
            | Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The computation type `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::CompType(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn comp_type_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::CompType(id) => Maybe::Present(id),
            | Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The declared type the function tail at `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a function yields its stored signature result; an unminted
    ///   result preserves its reason and other families yield an other-sort
    ///   reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signed and unsigned function tails preserve the body
    ///   while differing in whether they supply a derived signature.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Function { signature, .. }) => signature,
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn signature_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::Function { signature, .. } => signature,
            | Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_) => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The body the function tail at `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a function yields its body id; an unminted result preserves
    ///   its reason and other families yield an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signed and unsigned function tails preserve the body
    ///   while differing in whether they supply a derived signature.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Function { body, .. }) => Maybe::Present(body),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn function_body_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::Function { body, .. } => Maybe::Present(body),
            | Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_) => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// Resolve every attribute against the registry and file it.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so an admitted payload already has
    ///   its core value.
    /// - ensures: every attribute of every declaration, refused or not, is
    ///   resolved against the registry and filed under the content identity of
    ///   the declaration form it decorates, in source order; an attribute
    ///   written twice for one declared name is refused wherever its two
    ///   spellings sit, and the earlier one is the one kept. A declaration's
    ///   lowering outcome does not gate its attributes: an expectation about a
    ///   refusal is read off the refused declaration, and an attribute's own
    ///   refusal competes with the declaration's other refusals by position.
    /// - provides: the attribute side table of the lowered module.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] abort the pass. Every other refusal
    ///   is offered to the declaration that owns the attribute rather than
    ///   raised.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — attributes are drained and filed even for a refused
    ///   declaration, while a failing schema is retained as a declaration
    ///   refusal.
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body drains every slot's attributes; the check reads each slot once"
        )
    )]
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ret| {
            self.collected.slots.len() == before
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err()
                    || self
                        .collected
                        .slots
                        .iter()
                        .all(|slot| slot.attributes.is_empty()))
        },
    )]
    fn attribute(
        &mut self,
        table: &mut AttributeTable,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut slots = core::mem::take(&mut self.collected.slots);
        let outcome = self.attribute_slots(&mut slots, table);
        self.collected.slots = slots;

        outcome
    }

    /// Resolve and file the attributes of every slot in `slots`.
    ///
    /// # Specification
    /// - requires: as [`Self::attribute`], over the slots taken out of the
    ///   collection.
    /// - ensures: as [`Self::attribute`].
    /// - provides: the slot walk of [`Self::attribute`].
    /// - fails: as [`Self::attribute`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::attribute`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each written attribute spends one step, successful
    ///   entries append under their declaration key, and schema errors do not
    ///   prevent other declarations from lowering.
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    /// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body resolves every slot's attributes; the capture counts them once"
        )
    )]
    #[spec(
        captures: before = (
            self.fuel.remaining,
            slots.iter().fold(0_usize, |count, slot| {
                count.saturating_add(slot.attributes.len())
            }),
            usize::from(table.attributed_count()),
        ),
        ensures: |ret| {
            self.fuel.remaining <= before.0
                && usize::from(table.attributed_count()) >= before.2
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err() || self.fuel.remaining == before.0.saturating_sub(before.1))
        },
    )]
    fn attribute_slots(
        &mut self,
        slots: &mut [DeclarationSlot<'source>],
        table: &mut AttributeTable,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        for slot in slots {
            let mut seen: Vec<(RegisteredAttribute, ByteSpan)> = Vec::new();
            for written in core::mem::take(&mut slot.attributes) {
                self.fuel.spend()?;
                match self.read_attribute(&written, &mut seen) {
                    | Ok(Filing::Filed(entry)) => {
                        table.file(self.key_at(written.decorates), entry);
                    },
                    | Ok(Filing::Unlowered) => {},
                    | Err(refusal) => {
                        if refusal.classify() == FailureClass::EngineFault {
                            return Err(refusal);
                        }
                        slot.refuse(written.at.node, refusal);
                    },
                }
            }
        }

        Ok(())
    }

    /// Read every declaration's documentation and check its links.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so every declaration form's key is
    ///   final.
    /// - ensures: every piece of documentation of every declaration, refused or
    ///   not, is read and filed under the content identity of the form it
    ///   documents, pieces in source order; each link to a name the module
    ///   neither declares nor recognises refuses its declaration at the link,
    ///   as a misspelt attribute does. Every slot's documentation list is
    ///   drained.
    /// - provides: the documentation table of the lowered module.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] abort the pass; every other refusal
    ///   is offered to the declaration the documentation belongs to.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both spellings file one text under one key, a link to
    ///   a later declaration resolves, and a link to a missing name refuses its
    ///   declaration at the link's span.
    /// - witness: `lower::tests::documentation_is_filed_under_the_declaration_key`
    /// - witness: `lower::tests::a_link_to_a_missing_name_is_refused_at_the_link`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body drains every slot's documentation; the check reads each slot once"
        )
    )]
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ret| {
            self.collected.slots.len() == before
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err() || self.collected.slots.iter().all(|slot| slot.docs.is_empty()))
        },
    )]
    fn document(
        &mut self
    ) -> Result<BTreeMap<NodeKey, Documentation<'source>>, LoweringRefusal<'source>>
    {
        let mut filed: BTreeMap<NodeKey, Documentation<'source>> = BTreeMap::new();
        let mut slots = core::mem::take(&mut self.collected.slots);
        let outcome = self.document_slots(&mut slots, &mut filed);
        self.collected.slots = slots;

        outcome.map(|()| filed)
    }

    /// Read and file the documentation of every slot in `slots` into `filed`.
    ///
    /// # Specification
    /// - requires: as [`Self::document`], over the slots taken out of the
    ///   collection.
    /// - ensures: as [`Self::document`]; each piece spends one step.
    /// - provides: the slot walk of [`Self::document`].
    /// - fails: as [`Self::document`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::document`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::document`].
    /// - witness: `lower::tests::documentation_is_filed_under_the_declaration_key`
    /// - witness: `lower::tests::a_link_to_a_missing_name_is_refused_at_the_link`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body drains every slot's documentation; the check reads each slot once"
        )
    )]
    #[spec(
        captures: before = self.fuel.remaining,
        ensures: |ret| self.fuel.remaining <= before
            && (ret.is_err() || slots.iter().all(|slot| slot.docs.is_empty())),
    )]
    fn document_slots(
        &mut self,
        slots: &mut [DeclarationSlot<'source>],
        filed: &mut BTreeMap<NodeKey, Documentation<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        for slot in slots.iter_mut() {
            for written in core::mem::take(&mut slot.docs) {
                self.fuel.spend()?;
                let documentation = filed.entry(self.key_at(written.documents)).or_default();
                let before = documentation.links().len();
                if let Err(refusal) = read_doc(self.pbg, self.tree, written.at.node, documentation)
                {
                    if refusal.classify() == FailureClass::EngineFault {
                        return Err(refusal);
                    }
                    slot.refuse(written.at.node, refusal);
                    continue;
                }
                for link in documentation.links().get(before ..).unwrap_or_default() {
                    let name = link.name();
                    let spelled: &str = name.as_ref();
                    let path =
                        NamePath::from(spelled.split('.').map(Segment::from).collect::<Vec<_>>());
                    let declared =
                        matches!(
                            self.recognition.resolve_path(&path),
                            PathResolution::Complete(_)
                        ) || self.collected.by_name.keys().any(|&(_, held)| held == name)
                            || self.collected.modules.keys().any(|&(_, held)| held == name)
                            || self.collected.constructors.contains_key(&name);
                    if !declared {
                        slot.refuse(written.at.node, LoweringRefusal::UnresolvedDocLink {
                            span: link.span(),
                            name,
                        });
                    }
                }
            }
        }

        Ok(())
    }

    /// Read one written attribute into an entry, or into the refusal it earns.
    ///
    /// # Specification
    /// - requires: `seen` holds the attributes already filed for this declared
    ///   name, with their spans.
    /// - ensures: a registered name whose payload its schema admits yields an
    ///   entry carrying the payload's already-minted value, and joins `seen`; a
    ///   payload whose form is not a value at all is refused before its schema
    ///   is consulted, because being no value is a different fact from being
    ///   the wrong one; nothing is filed for a payload the mint sweep left
    ///   unlowered, which is the case of a payload that itself refused.
    /// - provides: the per-attribute half of the attribute pass.
    /// - fails: yields the unknown-attribute refusal with its bounded
    ///   suggestion, the duplicate refusal naming the first spelling, the
    ///   non-value-payload refusal, the missing-payload refusal, or the
    ///   ill-typed-payload refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The attribute's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a filed entry adds exactly one recognized name and
    ///   keeps its schema, payload and span; duplicate, unknown and ill-typed
    ///   attributes leave the per-declaration seen list unchanged.
    /// - witness: `lower::tests::an_attribute_written_twice_for_one_name_is_refused`
    /// - witness: `lower::tests::an_unknown_attribute_is_refused_with_its_suggestion`
    /// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    #[spec(
        captures: before = seen.len(),
        ensures: |ret| match ret.as_ref() {
            | Ok(&Filing::Filed(ref entry)) => {
                seen.len() == before.saturating_add(1_usize)
                    && seen.last() == Some(&(entry.name(), written.span))
                    && entry.span() == written.span
                    && AttributeRegistry::lookup(written.name)
                        == Maybe::Present((entry.name(), entry.schema()))
                    && match (written.payload, entry.payload()) {
                        | (Payload::Unwritten, Maybe::Absent(payload::Absent::Marker)) => true,
                        | (Payload::Written(placed), Maybe::Present(value)) => {
                            self.value_at(placed.node) == Maybe::Present(value)
                        },
                        | _ => false,
                    }
            },
            | Ok(&Filing::Unlowered) => {
                seen.len() == before
                    && matches!(written.payload, Payload::Written(placed) if matches!(self.value_at(placed.node), Maybe::Absent(_)))
            },
            | Err(_) => seen.len() == before,
        },
    )]
    fn read_attribute(
        &self,
        written: &WrittenAttribute<'source>,
        seen: &mut Vec<(RegisteredAttribute, ByteSpan)>,
    ) -> Result<Filing, LoweringRefusal<'source>>
    {
        let Maybe::Present((name, schema)) = AttributeRegistry::lookup(written.name)
        else {
            return Err(LoweringRefusal::UnknownAttribute {
                span: written.span,
                name: written.name,
                suggestion: AttributeRegistry::suggestion(written.name),
            });
        };
        if let Some(&(_held, first)) = seen.iter().find(|&&(held, _first)| held == name) {
            return Err(LoweringRefusal::DuplicateAttribute {
                span: written.span,
                name: written.name,
                first,
            });
        }
        let form = self.payload_form_of(written, name)?;
        match payload_verdict(schema, form) {
            | PayloadVerdict::Admitted => {},
            | PayloadVerdict::Missing => {
                return Err(LoweringRefusal::MissingPayload {
                    span: written.span,
                    name,
                    expected: schema,
                });
            },
            | PayloadVerdict::IllTyped => {
                let span = match written.payload {
                    | Payload::Written(payload) => payload.span,
                    | Payload::Unwritten => written.span,
                };
                return Err(LoweringRefusal::IllTypedPayload {
                    span,
                    name,
                    expected: schema,
                    written: form,
                });
            },
        }
        let value = match written.payload {
            | Payload::Unwritten => Maybe::Absent(payload::Absent::Marker),
            | Payload::Written(placed) => {
                let Maybe::Present(value) = self.value_at(placed.node)
                else {
                    return Ok(Filing::Unlowered);
                };
                Maybe::Present(value)
            },
        };
        seen.push((name, written.span));

        Ok(Filing::Filed(AttributeEntry::new(
            name,
            schema,
            value,
            written.span,
        )))
    }

    /// The form an attribute's payload was written in.
    ///
    /// # Specification
    /// - requires: `name` is the registered name `written` resolved to.
    /// - ensures: the absent form for no payload, and the payload form of the
    ///   payload's former otherwise.
    /// - provides: the syntactic half of the payload verdict.
    /// - fails: yields the non-value-payload refusal for a payload that cannot
    ///   stand as a value, and [`LoweringRefusal::UnknownMold`] for a foreign
    ///   mold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::NonValuePayload`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an absent payload is distinguished from a non-value
    ///   form and from an admitted value of the wrong schema-specific shape.
    /// - witness: `lower::tests::a_schema_taking_a_payload_refuses_an_absent_one`
    /// - witness: `lower::tests::a_non_value_payload_is_refused`
    /// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
    #[spec(
        ensures: |ret| {
            ret == match written.payload {
                | Payload::Unwritten => Ok(PayloadForm::Absent),
                | Payload::Written(placed) => match self.payload_former(placed) {
                    | Err(refusal) => Err(refusal),
                    | Ok((Shape::Form { former, .. }, ValueForm(true))) => Ok(payload_form(former)),
                    | Ok((Shape::Form { name: form, .. }, ValueForm(false))) => {
                        Err(LoweringRefusal::NonValuePayload {
                            span: placed.span,
                            name,
                            form,
                        })
                    },
                    | Ok(_) => Ok(PayloadForm::OtherValue),
                },
            }
        },
    )]
    fn payload_form_of(
        &self,
        written: &WrittenAttribute<'source>,
        name: RegisteredAttribute,
    ) -> Result<PayloadForm, LoweringRefusal<'source>>
    {
        let Payload::Written(placed) = written.payload
        else {
            return Ok(PayloadForm::Absent);
        };
        let (shape, value) = self.payload_former(placed)?;
        let Shape::Form { name: form, former } = shape
        else {
            return Ok(PayloadForm::OtherValue);
        };
        if !value.0 {
            return Err(LoweringRefusal::NonValuePayload {
                span: placed.span,
                name,
                form,
            });
        }

        Ok(payload_form(former))
    }

    /// The cross-tree key of the node at `position`: its top-level form's
    /// digest and its rank there.
    ///
    /// # Specification
    /// - requires: positions are interpreted in this source tree.
    /// - ensures: a node with a key yields it; any other position yields the
    ///   all-zero key.
    /// - provides: declaration keys for attribute and documentation filing.
    /// - fails: the fallback does not distinguish a keyless position from an
    ///   equal key.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — filed attributes use the decorated declaration's key,
    ///   including declarations already refused for an unrelated source error.
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    #[spec(
        ensures: |ret| {
            ret == self.tree.key(position).unwrap_or_else(|| {
                NodeKey::new(NodeDigest::from([0_u8; 32_usize]), FormRank::default())
            })
        },
    )]
    fn key_at(
        &self,
        position: NodeIndex,
    ) -> NodeKey
    {
        self.tree.key(position).unwrap_or_else(|| {
            NodeKey::new(NodeDigest::from([0_u8; 32_usize]), FormRank::default())
        })
    }

    /// Mint each callable operation's type and body from its plan.
    ///
    /// # Specification
    /// - requires: the collection planned the operations.
    /// - ensures: one minted type and body per planned operation whose slot
    ///   holds no refusal, every node with the operation's origin.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a planned operation lowers to a completed declaration
    ///   the checker accepts and the machine runs.
    /// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
    /// - witness: `operation::tests::a_call_reaches_the_operation_before_a_builtin_of_its_name`
    #[spec(ensures: self.operated.keys().all(|slot| self.collected.operations.contains_key(slot)))]
    fn mint_operations(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        for (&slot, plan) in &self.collected.operations {
            let Some(entry) = self.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let origin = Origin::new(entry.named.node, entry.named.span);
            let minted = crate::operation::mint_operation(plan, sink.arena, sink.origins, origin);
            let _first = self.operated.insert(slot, minted);
        }
    }

    /// Assemble one declaration per slot, in admission order.
    ///
    /// # Specification
    /// - requires: the classification, the mint sweep and the attribute pass
    ///   have all run.
    /// - ensures: a slot holding a refusal yields the refused outcome; a slot
    ///   whose signature and definition both lowered yields the completed
    ///   outcome — a witness's definition being the member it re-states; a
    ///   signature alone yields the uncompleted outcome, which is the
    ///   obligation this module owes; a definition alone yields the bodiless
    ///   outcome. A held slot holding no refusal yields nothing, and neither
    ///   does a witness whose member refused: there is no member to state a
    ///   second type for. Each declaration keeps its container and its role,
    ///   and takes its own origin token, handed out in admission order.
    /// - provides: the declaration list a checker drives.
    /// - fails: never — a slot with neither half lowered and no refusal
    ///   contributes no declaration, which the classification makes unreachable
    ///   for every slot but a held one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — completed, one-sided and refused declarations retain
    ///   their own source metadata and appear in admission order; skipped
    ///   unminted slots do not fabricate declaration origins or change constant
    ///   coordinates.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
    /// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `modules::modules::module_members_admit_in_source_order`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body assembles a row from every slot once; the check rebuilds each row once and compares it"
        )
    )]
    #[spec(
        captures: before = usize::from(origins.declaration_count()),
        ensures: |ret| {
            usize::from(origins.declaration_count()) == before.saturating_add(ret.len())
                && ret
                    .iter()
                    .map(|row| {
                        (
                            row.name(),
                            row.container(),
                            row.role(),
                            row.constant(),
                            row.span(),
                            row.signature(),
                            row.definition(),
                            row.outcome(),
                            origins.declaration(row.origin()),
                        )
                    })
                    .eq(self.collected.slots.iter().enumerate().filter_map(
                        |(position, slot)| match self.outcome(SlotIndex::from(position), slot) {
                            | Maybe::Absent(_) => None,
                            | Maybe::Present(outcome) => Some((
                                slot.name,
                                slot.container,
                                slot.role,
                                slot.constant,
                                slot.introduced_by.span,
                                slot.signature
                                    .map(|half| self.key_at(half.declaration.node)),
                                slot.definition
                                    .map(|half| self.key_at(half.declaration.node)),
                                outcome,
                                Maybe::Present(Origin::new(
                                    slot.introduced_by.node,
                                    slot.introduced_by.span,
                                )),
                            )),
                        },
                    ))
        },
    )]
    fn assemble(
        &self,
        origins: &mut OriginTable,
    ) -> Vec<LoweredDeclaration<'source>>
    {
        let mut declarations = Vec::with_capacity(self.collected.slots.len());
        for (position, slot) in self.collected.slots.iter().enumerate() {
            let Maybe::Present(outcome) = self.outcome(SlotIndex::from(position), slot)
            else {
                continue;
            };
            let introduced = slot.introduced_by;
            let origin = origins.record_declaration(Origin::new(introduced.node, introduced.span));
            declarations.push(LoweredDeclaration::from(DeclarationParts {
                name: slot.name,
                container: slot.container,
                role: slot.role,
                constant: slot.constant,
                span: introduced.span,
                origin,
                signature: slot
                    .signature
                    .map(|half| self.key_at(half.declaration.node)),
                definition: slot
                    .definition
                    .map(|half| self.key_at(half.declaration.node)),
                outcome,
            }));
        }

        declarations
    }

    /// What the slot at `position` amounts to.
    ///
    /// # Specification
    /// - requires: the slot and its member coordinates are interpreted in this
    ///   lowering run.
    /// - ensures: a stored refusal takes precedence; a data declaration, or a
    ///   described family the decoder admitted, is the index of its minted
    ///   signature; otherwise the available signature and body select
    ///   Completed, Uncompleted or Bodied.
    /// - provides: the declaration outcome without manufacturing absent halves.
    /// - fails: a refused member witness is Unminted; if neither half exists,
    ///   the signature’s absence is preserved.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three successful half combinations remain
    ///   distinct from a stored refusal, and an ascription witness does not
    ///   resurrect a refused member. Explicit signatures keep precedence over
    ///   derived ones.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
    /// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
    /// - witness: `modules::modules::a_nonempty_ascription_checks_each_component_at_its_member`
    /// - witness: `modules::modules::member_signature_attaches_and_wins_over_derived_function_type`
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    #[spec(
        ensures: |ret| {
            if let Maybe::Present((_at, refusal)) = slot.refusal {
                ret == Maybe::Present(DeclarationOutcome::Refused(refusal))
            }
            else if let Maybe::Present(Half { operand: Operand::Data(form), .. }) = slot.definition {
                ret == self.signatures.get(&form).map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| Maybe::Present(DeclarationOutcome::Data(index)))
            }
            else if let Some(&index) = self.described.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Data(index))
            }
            else if let Maybe::Present(Half { operand: Operand::Operation, .. }) = slot.definition {
                ret == self.operated.get(&position).map_or(Maybe::Absent(lowered::Absent::Unminted), |&(declared_type, body)| Maybe::Present(DeclarationOutcome::Completed { declared_type, body }))
            }
            else if matches!(slot.definition, Maybe::Present(Half { operand: Operand::Member(target), .. }) if self.collected.slots.get(usize::from(target)).is_some_and(|member| matches!(member.refusal, Maybe::Present(_))))
            {
                ret == Maybe::Absent(lowered::Absent::Unminted)
            }
            else {
                let declared = match slot.signature {
                    | Maybe::Present(half) => match half.operand {
                        | Operand::Written(written) => self.value_type_at(written.node),
                        | Operand::Function => self.signature_at(half.declaration.node),
                        | Operand::Member(_) | Operand::Data(_) | Operand::Operation | Operand::Signature => Maybe::Absent(lowered::Absent::Unminted),
                    },
                    | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
                };
                let body = match slot.definition {
                    | Maybe::Present(half) => match half.operand {
                        | Operand::Written(written) => self.value_at(written.node),
                        | Operand::Function => self.function_body_at(half.declaration.node),
                        | Operand::Member(_) => self
                            .witnessed
                            .get(&position)
                            .copied()
                            .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                        | Operand::Data(_) | Operand::Operation | Operand::Signature => Maybe::Absent(lowered::Absent::Unminted),
                    },
                    | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
                };
                match ret {
                    | Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body: value,
                    }) => {
                        declared == Maybe::Present(declared_type) && body == Maybe::Present(value)
                    },
                    | Maybe::Present(DeclarationOutcome::Uncompleted { declared_type }) => {
                        declared == Maybe::Present(declared_type)
                            && matches!(body, Maybe::Absent(_))
                    },
                    | Maybe::Present(DeclarationOutcome::Bodied { body: value }) => {
                        matches!(declared, Maybe::Absent(_)) && body == Maybe::Present(value)
                    },
                    | Maybe::Absent(reason) => {
                        declared == Maybe::Absent(reason) && matches!(body, Maybe::Absent(_))
                    },
                    | Maybe::Present(DeclarationOutcome::Refused(_) | DeclarationOutcome::Data(_)) => false,
                }
            }
        },
    )]
    fn outcome(
        &self,
        position: SlotIndex,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<DeclarationOutcome<'source>, lowered::Absent>
    {
        if let Maybe::Present((_at, refusal)) = slot.refusal {
            return Maybe::Present(DeclarationOutcome::Refused(refusal));
        }
        if let Maybe::Present(Half {
            operand: Operand::Data(form),
            ..
        }) = slot.definition
        {
            return self
                .signatures
                .get(&form)
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| {
                    Maybe::Present(DeclarationOutcome::Data(index))
                });
        }
        if let Some(&index) = self.described.get(&position) {
            return Maybe::Present(DeclarationOutcome::Data(index));
        }
        if let Maybe::Present(Half {
            operand: Operand::Operation,
            ..
        }) = slot.definition
        {
            return self.operated.get(&position).map_or(
                Maybe::Absent(lowered::Absent::Unminted),
                |&(declared_type, body)| {
                    Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    })
                },
            );
        }
        if let Maybe::Present(Half {
            operand: Operand::Member(target),
            ..
        }) = slot.definition
            && let Some(Maybe::Present(_)) = self
                .collected
                .slots
                .get(usize::from(target))
                .map(|member| member.refusal)
        {
            return Maybe::Absent(lowered::Absent::Unminted);
        }
        let declared = match slot.signature {
            | Maybe::Present(half) => match half.operand {
                | Operand::Written(written) => self.value_type_at(written.node),
                | Operand::Function => self.signature_at(half.declaration.node),
                | Operand::Member(_)
                | Operand::Data(_)
                | Operand::Operation
                | Operand::Signature => Maybe::Absent(lowered::Absent::Unminted),
            },
            | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        let body = match slot.definition {
            | Maybe::Present(half) => match half.operand {
                | Operand::Written(written) => self.value_at(written.node),
                | Operand::Function => self.function_body_at(half.declaration.node),
                | Operand::Member(_) => self
                    .witnessed
                    .get(&position)
                    .copied()
                    .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                | Operand::Data(_) | Operand::Operation | Operand::Signature => {
                    Maybe::Absent(lowered::Absent::Unminted)
                },
            },
            | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        match (declared, body) {
            | (Maybe::Present(declared_type), Maybe::Present(body)) => {
                Maybe::Present(DeclarationOutcome::Completed {
                    declared_type,
                    body,
                })
            },
            | (Maybe::Present(declared_type), Maybe::Absent(_)) => {
                Maybe::Present(DeclarationOutcome::Uncompleted { declared_type })
            },
            | (Maybe::Absent(_), Maybe::Present(body)) => {
                Maybe::Present(DeclarationOutcome::Bodied { body })
            },
            | (Maybe::Absent(reason), Maybe::Absent(_)) => Maybe::Absent(reason),
        }
    }

    /// Carry each refused manifest type component's refusal to every
    /// declaration whose type names it.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: a declaration owning a type head that stands for a manifest
    ///   component whose type refused holds that refusal too, at the head's
    ///   position, so it keeps the lowest-positioned refusal it has; the
    ///   components are taken in signature order, so a component naming an
    ///   earlier refused one passes the refusal on.
    /// - provides: the rule that a declaration is not minted over a type that
    ///   did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of manifest aliases carries the original
    ///   located refusal into a member even when its body has independently
    ///   failed; the unrelated following declaration still lowers.
    /// - witness: `modules::modules::manifest_refusals_propagate_transitively_before_minting`
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body sorts the manifest references and visits each once; the check reads each once and its neighbour once"
        )
    )]
    #[spec(
        captures: before = (self.manifests.len(), self.collected.slots.len()),
        ensures: |_| {
            self.manifests.len() == before.0 && self.collected.slots.len() == before.1 && self.manifests.windows(2).all(|pair| match *pair { [left, right] => left.0 <= right.0, _ => false }) && self.manifests.iter().all(|&(held, head)| { if !matches!(self.collected.slots.get(usize::from(held)), Some(slot) if matches!(slot.refusal, Maybe::Present(_))) { return true; } match self.collected.owner_of(head) { Maybe::Absent(_) => true, Maybe::Present(owner) => self.collected.slots.get(usize::from(owner)).is_none_or(|slot| matches!(slot.refusal, Maybe::Present((at, _)) if at <= head)) } })
        },
    )]
    fn propagate_manifests(&mut self)
    {
        let mut named = core::mem::take(&mut self.manifests);
        named.sort_by_key(|&(held, _head)| held);
        for &(held, head) in &named {
            let Some(Maybe::Present((_at, refusal))) = self
                .collected
                .slots
                .get(usize::from(held))
                .map(|slot| slot.refusal)
            else {
                continue;
            };
            let Maybe::Present(owner) = self.collected.owner_of(head)
            else {
                continue;
            };
            if let Some(slot) = self.collected.slots.get_mut(usize::from(owner)) {
                slot.refuse(head, refusal);
            }
        }
        self.manifests = named;
    }

    /// One stratum item per module, in pre-order.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: each module's path, its form's bytes, the value components
    ///   and nested modules it exports in export order, each manifest type
    ///   component with the type it lowered to, and whether matching coerced
    ///   its body; a hidden member appears in no item.
    /// - provides: the stratum half of [`LoweredModule`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested paths retain their member names, an ascription
    ///   exports only its selected values and modules, and manifest components
    ///   keep their lowered type or their explicit Unlowered status.
    /// - witness: `modules::modules::nested_modules_lower_as_parent_members_and_project`
    /// - witness: `modules::modules::module_signature_matching_hides_extra_members`
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    #[spec(
        ensures: |ret| {
            ret.len() == self.collected.structures.len()
                && ret
                    .iter()
                    .zip(&self.collected.structures)
                    .all(|(lowered, structure)| {
                        if lowered.path().last() != Some(&structure.name)
                            || lowered.span() != structure.declared_by.span
                            || lowered.coerced() != structure.coerced
                            || lowered.types().len() != structure.types.len()
                        {
                            return false;
                        }
                        let mut values = lowered.values().iter();
                        let mut modules = lowered.modules().iter();
                        for &export in &structure.exports {
                            match export {
                                | Member::Slot(slot) => {
                                    if self.collected.slots.get(usize::from(slot)).is_some_and(
                                        |member| {
                                            !values.next().is_some_and(|value| {
                                                value.name == member.name
                                                    && value.constant == member.constant
                                            })
                                        },
                                    ) {
                                        return false;
                                    }
                                },
                                | Member::Module(nested) => {
                                    if self
                                        .collected
                                        .structures
                                        .get(usize::from(nested))
                                        .is_some_and(|member| modules.next() != Some(&member.name))
                                    {
                                        return false;
                                    }
                                },
                            }
                        }
                        values.next().is_none()
                            && modules.next().is_none()
                            && lowered.types().iter().zip(&structure.types).all(
                                |(lowered, manifest)| {
                                    lowered.name == manifest.name
                                        && lowered.defined
                                            == match self.value_type_at(manifest.defined.node) {
                                                | Maybe::Present(id) => Maybe::Present(id),
                                                | Maybe::Absent(_) => {
                                                    Maybe::Absent(manifest_type::Absent::Unlowered)
                                                },
                                            }
                                },
                            )
                    })
        },
    )]
    fn structures(&self) -> Vec<LoweredStructure<'source>>
    {
        let mut lowered = Vec::with_capacity(self.collected.structures.len());
        for (position, structure) in self.collected.structures.iter().enumerate() {
            let mut values = Vec::new();
            let mut modules = Vec::new();
            for &export in &structure.exports {
                match export {
                    | Member::Slot(slot) => {
                        if let Some(member) = self.collected.slots.get(usize::from(slot)) {
                            values.push(ValueComponent {
                                name: member.name,
                                constant: member.constant,
                            });
                        }
                    },
                    | Member::Module(nested) => {
                        if let Some(member) = self.collected.structures.get(usize::from(nested)) {
                            modules.push(member.name);
                        }
                    },
                }
            }
            let types = structure
                .types
                .iter()
                .map(|manifest| ManifestComponent {
                    name: manifest.name,
                    defined: match self.value_type_at(manifest.defined.node) {
                        | Maybe::Present(defined) => Maybe::Present(defined),
                        | Maybe::Absent(_) => Maybe::Absent(manifest_type::Absent::Unlowered),
                    },
                })
                .collect();
            lowered.push(LoweredStructure::new(
                self.collected
                    .path(Container::Module(StructureIndex::from(position))),
                structure.declared_by.span,
                values,
                modules,
                types,
                structure.coerced,
            ));
        }

        lowered
    }
}

/// What reading one attribute produced, short of a refusal.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A filed entry has passed registry and payload checks; an
///   unlowered payload contributes no entry or seen-name update.
/// - provides: The non-refusal outcome of reading one attribute.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The written attribute and seen-name list are absent;
///   `read_attribute` states the executable filing and state-update relation.
///
/// # Adequacy
/// - hypothesis: L3 — valid entries are filed under the declaration key, while
///   a refused declaration can still retain an independently valid payload.
/// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Filing
{
    /// The entry to file.
    Filed(AttributeEntry),
    /// Nothing: the payload did not lower, which only a payload that itself
    /// refused leaves behind.
    Unlowered,
}

impl Sink<'_>
{
    /// Write `bridge` over `minted`, the core node of the syntax node at
    /// `origin`.
    ///
    /// # Specification
    /// - requires: `minted` is what the node's own plan minted.
    /// - ensures: a bare node is `minted` unchanged; a forced value is minted
    ///   as a force over it, a returned value type as a returner over it, and a
    ///   quoted type as the quote of it at its own sort, each with `origin`
    ///   marked as the insertion it is; nothing when the node did not lower at
    ///   the sort its bridge leaves, which the classification makes
    ///   unreachable.
    /// - provides: the minting half of the insertions a position's sort
    ///   decides.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — forced heads, positive results and quoted types
    ///   acquire the intended inserted provenance, while an author-written
    ///   force stays written.
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| match bridge {
            | Bridge::Bare => ret == minted,
            | Bridge::Inserted(insertion) => match (minted, insertion, ret) {
                | (Maybe::Absent(reason), ..) => ret == Maybe::Absent(reason),
                | (
                    Maybe::Present(Lowered::Value(_)),
                    Insertion::Force,
                    Maybe::Present(Lowered::Computation(id)),
                ) => self.origins.computation(id) == Maybe::Present(origin.inserted(insertion)),
                | (
                    Maybe::Present(Lowered::ValueType(_)),
                    Insertion::Returner,
                    Maybe::Present(Lowered::CompType(id)),
                ) => self.origins.comp_type(id) == Maybe::Present(origin.inserted(insertion)),
                | (
                    Maybe::Present(Lowered::ValueType(_) | Lowered::CompType(_)),
                    Insertion::Quote,
                    Maybe::Present(Lowered::Value(id)),
                ) => self.origins.value(id) == Maybe::Present(origin.inserted(insertion)),
                | (Maybe::Present(Lowered::Value(_)), Insertion::Force, _)
                | (Maybe::Present(Lowered::ValueType(_)), Insertion::Returner, _)
                | (
                    Maybe::Present(Lowered::ValueType(_) | Lowered::CompType(_)),
                    Insertion::Quote,
                    _,
                ) => false,
                | _ => ret == Maybe::Absent(lowered::Absent::OtherSort),
            },
        },
    )]
    fn bridge(
        &mut self,
        minted: Maybe<Lowered, lowered::Absent>,
        bridge: Bridge,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let Bridge::Inserted(insertion) = bridge
        else {
            return minted;
        };
        let inserted = origin.inserted(insertion);
        match (minted, insertion) {
            | (Maybe::Present(Lowered::Value(forced)), Insertion::Force) => {
                let id = self.arena.computation_force(forced);
                Maybe::Present(self.computation(id, inserted))
            },
            | (Maybe::Present(Lowered::ValueType(returned)), Insertion::Returner) => {
                let id = self.arena.comp_type_returner(returned);
                self.origins.record_comp_type(id, inserted);
                Maybe::Present(Lowered::CompType(id))
            },
            | (Maybe::Present(Lowered::ValueType(quoted)), Insertion::Quote) => {
                let id = self.arena.value_quote(quoted);
                Maybe::Present(self.value(id, inserted))
            },
            | (Maybe::Present(Lowered::CompType(quoted)), Insertion::Quote) => {
                let id = self.arena.value_quote_computation(quoted);
                Maybe::Present(self.value(id, inserted))
            },
            | (
                Maybe::Present(_),
                Insertion::Force
                | Insertion::Thunk
                | Insertion::Returner
                | Insertion::Quote
                | Insertion::Decode
                | Insertion::Classifier
                | Insertion::Match
                | Insertion::Fixpoint,
            ) => Maybe::Absent(lowered::Absent::OtherSort),
            | (Maybe::Absent(reason), _) => Maybe::Absent(reason),
        }
    }

    /// Record `id`'s origin and wrap it as a lowered value.
    ///
    /// # Specification
    /// - requires: the value id follows all values already recorded in this
    ///   origin table.
    /// - ensures: the supplied origin is recorded under the value id and the
    ///   lowered result retains that id and family.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every minted value has its own source origin, and an
    ///   inserted force does not relabel the source value it consumes.
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret == Lowered::Value(id) && self.origins.value(id) == Maybe::Present(origin)
        },
    )]
    fn value(
        &mut self,
        id: ValueId,
        origin: Origin,
    ) -> Lowered
    {
        self.origins.record_value(id, origin);

        Lowered::Value(id)
    }

    /// Record `id`'s origin and wrap it as a lowered computation.
    ///
    /// # Specification
    /// - requires: the computation id follows all computations already recorded
    ///   in this origin table.
    /// - ensures: the supplied origin is recorded under the computation id and
    ///   the lowered result retains that id and family.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — written and inserted computations retain their own
    ///   source and provenance rather than borrowing an operand origin.
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret == Lowered::Computation(id)
                && self.origins.computation(id) == Maybe::Present(origin)
        },
    )]
    fn computation(
        &mut self,
        id: ComputationId,
        origin: Origin,
    ) -> Lowered
    {
        self.origins.record_computation(id, origin);

        Lowered::Computation(id)
    }

    /// Mint `atom`'s value type and record its origin.
    ///
    /// # Specification
    /// - requires: newly minted type ids follow those already recorded in the
    ///   origin table.
    /// - ensures: the selected unit, integer or text value type is minted and
    ///   receives the supplied origin.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete nullary type heads mint their own core type
    ///   and every minted type carries a source origin.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| match ret {
            | Lowered::ValueType(id) => self.origins.value_type(id) == Maybe::Present(origin) && match atom {
                TypeAtom::Boolean => self.arena.value_type(id).is_some_and(|held| matches!(*held, ValueType::Sum(ref parts) if parts.len() == 2 && parts.iter().all(|&part| self.arena.value_type(part) == Some(&ValueType::unit())))),
                TypeAtom::Unit => self.arena.value_type(id) == Some(&ValueType::unit()),
                TypeAtom::Integer => self.arena.value_type(id) == Some(&ValueType::Base(BaseType::Integer)),
                TypeAtom::Text => self.arena.value_type(id) == Some(&ValueType::Base(BaseType::String)),
                TypeAtom::Void => self.arena.value_type(id).is_some_and(|held| matches!(*held, ValueType::Sum(ref parts) if parts.is_empty())),
            },
            | _ => false,
        },
    )]
    fn atom(
        &mut self,
        atom: TypeAtom,
        origin: Origin,
    ) -> Lowered
    {
        let id = match atom {
            | TypeAtom::Boolean => {
                let unit = self.arena.value_type_unit();
                self.origins.record_value_type(unit, origin);
                self.arena.value_type_sum(&[unit, unit])
            },
            | TypeAtom::Unit => self.arena.value_type_unit(),
            | TypeAtom::Integer => self.arena.value_type_base(BaseType::Integer),
            | TypeAtom::Text => self.arena.value_type_base(BaseType::String),
            | TypeAtom::Void => self.arena.value_type_sum(&[]),
        };
        self.origins.record_value_type(id, origin);

        Lowered::ValueType(id)
    }
}

/// The parameter of a lambda: exactly one identifier between parentheses.
///
/// # Specification
/// - requires: `cursor` stands just past the lambda's `fn`.
/// - ensures: the one parameter's tile, with the cursor past the closing
///   parenthesis.
/// - provides: the binder reading of the lambda.
/// - fails: yields the unadmitted refusal for a typed parameter, the arity
///   refusal for any parameter count but one, and a misplaced-tile refusal for
///   a parameter list out of shape.
/// - panics: none.
///
/// # Errors
/// The lambda's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one and multiple binders select the documented
///   arity boundary; a successful header consumes its closing parenthesis but
///   not the following body, while typed binders remain outside this fragment.
/// - witness: `lower::tests::parameter_headers_preserve_the_body_and_locate_refusals`
/// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
#[spec(
    captures: input = cursor.clone(),
    ensures: |ret| {
        ret.as_ref().map_or(true, |binder| {
            let mut input = input.clone();
            if matches!(input.tile(TileName::PAREN_OPEN), Maybe::Absent(_)) {
                return false;
            }
            let mut seen = false;
            loop {
                match input.read() {
                    | Maybe::Present(Piece::Tile {
                        label: TileName::IDENTIFIER,
                        at,
                    }) => {
                        if seen || at != *binder {
                            return false;
                        }
                        seen = true;
                    },
                    | Maybe::Present(Piece::Tile {
                        label: TileName::COMMA,
                        ..
                    }) => {},
                    | Maybe::Present(Piece::Tile {
                        label: TileName::PAREN_CLOSE,
                        ..
                    }) => {
                        return seen
                            && cursor.peek() == input.peek()
                            && cursor.here() == input.here();
                    },
                    | _ => return false,
                }
            }
        })
    },
)]
fn parameter<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
) -> Result<Placed, LoweringRefusal<'source>>
{
    if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    let mut first: Option<Placed> = None;
    let mut count = 0_usize;
    loop {
        if let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER) {
            count = count.saturating_add(1_usize);
            first = first.or(Some(binder));
            continue;
        }
        if let Maybe::Present(_) = cursor.tile(TileName::COMMA) {
            continue;
        }
        if let Maybe::Present(_) = cursor.at(TileName::COLON) {
            return Err(site.folded(FormName::PARAMETER, FragmentBoundary::Unadmitted));
        }
        if let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE) {
            break;
        }
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    match first {
        | Some(binder) if count == 1_usize => Ok(binder),
        | Some(_) | None => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
    }
}

/// The statements a block opens with a keyword the fragment does not read, by
/// that keyword, with the form a refusal names each by; `fork` is read apart,
/// because its two statements share the keyword.
///
/// # Specification
/// - requires: lookup is by a block’s leading keyword.
/// - ensures: each listed keyword retains its distinct refused statement form;
///   `fork` is handled separately because its shared form requires lookahead.
/// - provides: the keyword-to-refusal naming table.
/// - fails: no default entry for an unlisted keyword.
/// - panics: none.
/// - executable: none — the specification attribute does not accept constant
///   items; `statement_form` checks the lookup and fork exception.
///
/// # Adequacy
/// - hypothesis: L3 — the reserved statement cases retain their own form names,
///   including the ordinary/shared fork distinction outside this table.
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
const UNREAD_STATEMENTS: [(TileName, FormName); 6_usize] = [
    (TileName::VAL, FormName::VAL_STATEMENT),
    (TileName::UNPACK, FormName::UNPACK_STATEMENT),
    (TileName::LETA, FormName::LETA_STATEMENT),
    (TileName::RECV, FormName::RECV_STATEMENT),
    (TileName::ACQUIRE, FormName::ACQUIRE_STATEMENT),
    (TileName::RELEASE, FormName::RELEASE_STATEMENT),
];

/// The statement the tile `label`, at `cursor`, opens.
///
/// # Specification
/// - requires: `cursor` stands at the tile `label`, in a block, at a place a
///   statement may start.
/// - ensures: the statement form the keyword opens — `fork` followed by `!` the
///   shared fork — and the absence for a tile that opens no statement.
/// - provides: the names a block's refused statements are written as;
///   [`statement::Absent::NotAKeyword`] for a tile no statement starts with.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the reserved statement spellings receive their own form
///   names, including the ordinary and shared fork distinction.
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
#[spec(
    captures: shared = label == TileName::FORK && {
        let mut ahead = cursor.clone();
        let _lead = ahead.read();
        matches!(ahead.at(TileName::BANG), Maybe::Present(_))
    },
    ensures: |ret| {
        ret == if label == TileName::FORK {
            Maybe::Present(if shared {
                FormName::FORK_SHARED_STATEMENT
            }
            else {
                FormName::FORK_STATEMENT
            })
        }
        else {
            UNREAD_STATEMENTS
                .iter()
                .find(|&&(keyword, _form)| keyword == label)
                .map_or(
                    Maybe::Absent(statement::Absent::NotAKeyword),
                    |&(_keyword, form)| Maybe::Present(form),
                )
        }
    },
)]
fn statement_form(
    label: TileName,
    cursor: &Cursor<'_>,
) -> Maybe<FormName, statement::Absent>
{
    if label == TileName::FORK {
        let mut ahead = cursor.clone();
        let _fork = ahead.read();
        return Maybe::Present(match ahead.at(TileName::BANG) {
            | Maybe::Present(_) => FormName::FORK_SHARED_STATEMENT,
            | Maybe::Absent(_) => FormName::FORK_STATEMENT,
        });
    }

    UNREAD_STATEMENTS
        .iter()
        .find(|&&(keyword, _form)| keyword == label)
        .map_or(
            Maybe::Absent(statement::Absent::NotAKeyword),
            |&(_keyword, form)| Maybe::Present(form),
        )
}

/// Read a parenthesised, comma-separated argument list into `written`.
///
/// # Specification
/// - requires: `cursor` stands at the list's `(`.
/// - ensures: every argument written is appended to `written`, left to right,
///   with the cursor past the closing `)` and nothing after it; empty
///   parentheses append nothing, and a comma after the last argument is
///   admitted.
/// - provides: the argument reading of calls and type applications.
/// - fails: yields the hole's own refusal for an empty or juxtaposed argument,
///   and a misplaced-tile refusal for a list out of shape; the arguments read
///   before the refusal stay appended.
/// - panics: none.
///
/// # Errors
/// The form's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — empty, multi-argument and comma-closed calls append their
///   own ordered operand range; a failure preserves the already-read prefix and
///   locates the unexpected operand or tile instead of silently accepting a
///   suffix. The predicate re-reads the list as the body did and compares it
///   with only the operands this call appended.
/// - witness: `lower::tests::argument_lists_preserve_prefixes_and_locate_the_first_fault`
/// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
#[spec(
    captures: before = (written.len(), cursor.clone()),
    ensures: |ret| {
        written.len() >= before.0
            && ret.as_ref().map_or(true, |&()| written.get(before.0 ..).is_some_and(|appended| {
                let mut input = before.1.clone();
                let mut appended = appended.iter();
                if matches!(input.tile(TileName::PAREN_OPEN), Maybe::Absent(_)) {
                    return false;
                }
                if matches!(input.tile(TileName::PAREN_CLOSE), Maybe::Present(_)) {
                    return appended.next().is_none()
                        && matches!(input.peek(), Maybe::Absent(_))
                        && cursor.peek() == input.peek();
                }
                loop {
                    match input.read() {
                        | Maybe::Present(Piece::Operand(at))
                            if appended.next() == Some(&at.node) => {},
                        | _ => return false,
                    }
                    if matches!(input.tile(TileName::PAREN_CLOSE), Maybe::Present(_)) {
                        break;
                    }
                    if matches!(input.tile(TileName::COMMA), Maybe::Absent(_)) {
                        return false;
                    }
                    if matches!(input.tile(TileName::PAREN_CLOSE), Maybe::Present(_)) {
                        break;
                    }
                }
                appended.next().is_none()
                    && matches!(input.peek(), Maybe::Absent(_))
                    && cursor.peek() == input.peek()
            }))
    },
)]
fn arguments<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    written: &mut Vec<NodeIndex>,
) -> Result<(), LoweringRefusal<'source>>
{
    if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    loop {
        let run = cursor.operands();
        let closing = cursor.tile(TileName::PAREN_CLOSE);
        if let (Run::Empty(_), Maybe::Present(_)) = (run, closing) {
            break;
        }
        let argument = site.one(run)?;
        written.push(argument.node);
        if let Maybe::Present(_) = closing {
            break;
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        }
    }

    exhausted(site, cursor)
}

/// The entries of `store` that `stretch` names.
///
/// # Specification
/// - requires: the range is interpreted against the supplied store.
/// - ensures: an ordered in-bounds range returns that borrowed slice; a
///   reversed or out-of-bounds range returns an empty slice.
/// - provides: an allocation-free view of the recorded operand, parameter or
///   statement range.
/// - fails: invalid ranges are represented by the empty view.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, interior and full ranges retain the requested
///   members; reversed and past-end ranges do not read an unrelated prefix.
/// - witness: `lower::tests::recorded_ranges_keep_valid_members_and_reject_invalid_bounds`
#[spec(
    ensures: |ret| match store.get(stretch.start .. stretch.end) {
        | Some(expected) => core::ptr::eq(&raw const *ret, &raw const *expected),
        | None => ret.is_empty(),
    },
)]
fn stretch<Entry>(
    store: &[Entry],
    stretch: Stretch,
) -> &[Entry]
{
    store.get(stretch.start .. stretch.end).unwrap_or(&[])
}

/// Read the closing tile `label`, refusing anything else in its place.
///
/// # Specification
/// - requires: the cursor describes the site’s remaining pieces.
/// - ensures: the requested tile is consumed if present; otherwise the cursor
///   is unchanged and the refusal locates its current piece or gap.
/// - provides: a checked closing tile for the form reader.
/// - fails: an absent or different tile is `MisplacedTile`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — matching and mismatched closing tiles separate
///   consumption from a located refusal, including the exhausted-cursor gap.
/// - witness: `lower::tests::closing_and_exhaustion_distinguish_tiles_operands_and_gaps`
#[spec(
    captures: before = {
        let found = cursor.at(label);
        let here = cursor.here();
        let mut next = cursor.clone();
        if matches!(found, Maybe::Present(_)) {
            let _piece = next.read();
        }
        (found, here, next.peek(), next.here())
    },
    ensures: |ret| {
        ret == match before.0 {
            | Maybe::Present(_) => Ok(()),
            | Maybe::Absent(_) => Err(site.fault(before.1, FormFault::MisplacedTile)),
        } && cursor.peek() == before.2
            && cursor.here() == before.3
    },
)]
fn closed<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    label: TileName,
) -> Result<(), LoweringRefusal<'source>>
{
    match cursor.tile(label) {
        | Maybe::Present(_) => Ok(()),
        | Maybe::Absent(_) => Err(site.fault(cursor.here(), FormFault::MisplacedTile)),
    }
}

/// Refuse a piece left after a form's last.
///
/// # Specification
/// - requires: the cursor describes the site’s remaining pieces.
/// - ensures: only an exhausted cursor succeeds; a remaining operand and a
///   remaining tile yield their distinct located refusals.
/// - provides: a check that a form reader consumed its complete input.
/// - fails: an operand is `ExtraOperand` and a tile is `MisplacedTile`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — remaining operands and tiles are distinguished from the
///   terminal gap without consuming the unexpected piece.
/// - witness: `lower::tests::closing_and_exhaustion_distinguish_tiles_operands_and_gaps`
/// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
#[spec(
    ensures: |ret| {
        ret == match cursor.peek() {
            | Maybe::Absent(_) => Ok(()),
            | Maybe::Present(Piece::Operand(at)) => {
                Err(site.fault(at.span, FormFault::ExtraOperand))
            },
            | Maybe::Present(Piece::Tile { at, .. }) => {
                Err(site.fault(at.span, FormFault::MisplacedTile))
            },
        }
    },
)]
fn exhausted<'source>(
    site: Site,
    cursor: &Cursor<'_>,
) -> Result<(), LoweringRefusal<'source>>
{
    match cursor.peek() {
        | Maybe::Absent(_) => Ok(()),
        | Maybe::Present(Piece::Operand(stray)) => {
            Err(site.fault(stray.span, FormFault::ExtraOperand))
        },
        | Maybe::Present(Piece::Tile { at, .. }) => {
            Err(site.fault(at.span, FormFault::MisplacedTile))
        },
    }
}

/// The two operands of the product `site`, `A * B`, in written order.
///
/// # Specification
/// - requires: `cursor` holds the pieces of the product at `site`.
/// - ensures: one operand, the `*` tile and one operand, nothing after them.
/// - provides: the shape check every link of a product chain shares.
/// - fails: either hole's own refusal, and a misplaced-tile or extra-operand
///   refusal for a product out of shape.
/// - panics: none.
///
/// # Errors
/// The product's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — a well-shaped product answers its operands in order.
/// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&[first, second]| first != second))]
fn halves<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
) -> Result<[NodeIndex; 2], LoweringRefusal<'source>>
{
    let first = site.one(cursor.operands())?;
    closed(site, cursor, TileName::STAR)?;
    let second = site.one(cursor.operands())?;
    exhausted(site, cursor)?;

    Ok([first.node, second.node])
}

/// Whether a form can stand where a value is expected.
///
/// # Specification
/// - requires: nothing; the function is total over the former vocabulary.
/// - ensures: exactly the value-producing formers answer affirmatively — a
///   name, a capitalised name, a number, a string, the unit, a parenthesised
///   expression and a thunk — the reserved tuple among them, since a reserved
///   form is a value the fragment declines rather than a form of another sort,
///   and keeping the two apart is what lets an attribute payload written as a
///   computation be reported as a non-value rather than as a sort error.
/// - provides: the guard the attribute payload reading takes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the vocabulary is a finite class, enumerated exhaustively
///   with each former's exact answer asserted, so promoting or demoting any
///   single former breaks one row.
/// - witness: `lower::tests::only_the_value_forms_can_stand_as_a_payload`
#[spec(
    ensures: |ret| {
        ret.0
            == matches!(
                former,
                Former::Name
                    | Former::Constructor
                    | Former::Number
                    | Former::Text
                    | Former::Parenthesized
                    | Former::Unit
                    | Former::Thunk
            )
    },
)]
const fn is_value_form(former: Former) -> ValueForm
{
    ValueForm(matches!(
        former,
        Former::Name
            | Former::Constructor
            | Former::Number
            | Former::Text
            | Former::Parenthesized
            | Former::Unit
            | Former::Thunk
    ))
}

/// Parse a literal's own text into a core literal.
///
/// # Specification
/// - requires: `text` is the literal node's whole source text.
/// - ensures: a number is the canonical non-negative magnitude of its digits,
///   so a padded spelling and its unpadded form are one literal; a string is
///   the text between its delimiting quotes with its escapes decoded — `\n`,
///   `\t`, `\r`, `\0`, `\\`, `\"` and `\'` to the character each names, a
///   backslash before a line break elided with the break, any other escaped
///   character to itself, and a trailing lone backslash dropped.
/// - provides: the only place a lexeme becomes a core literal.
/// - fails: never; the malformed absence for a number holding a non-digit or
///   nothing at all and a string missing either delimiter, and the
///   not-a-literal absence for every other former.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two decision surfaces (the magnitude guard and the
///   delimiter strip) and the escape table, separated by a padded integer, an
///   empty integer, an integer holding a letter, a quoted text, an escaped
///   text, an unterminated text, a bare quote and an unquoted text, each
///   asserted as an exact literal or absence.
/// - witness: `lower::tests::an_integer_literal_is_its_canonical_magnitude`
/// - witness: `lower::tests::a_text_literal_is_the_bytes_between_its_quotes`
/// - witness: `lower::tests::a_lexeme_of_the_wrong_shape_parses_to_nothing`
#[spec(
    ensures: |ret| {
        let spelled: &str = text.as_ref();
        match former {
            | Former::Number => {
                if spelled.is_empty() || !spelled.bytes().all(|byte| byte.is_ascii_digit()) {
                    matches!(ret, Maybe::Absent(literal::Absent::Malformed))
                }
                else {
                    let unpadded = spelled.trim_start_matches('0');
                    let expected = if unpadded.is_empty() { "0" } else { unpadded };
                    matches!(ret, Maybe::Present(Literal::Integer(ref integer)) if integer.sign() == Sign::NonNegative && integer.magnitude().as_ref() == expected)
                }
            },
            | Former::Text => match spelled
                .strip_prefix('"')
                .and_then(|opened| opened.strip_suffix('"'))
            {
                | Some(content) => match ret {
                    | Maybe::Present(Literal::Text(ref literal)) => {
                        let content: &str = content;
                        let actual: &str = literal.as_ref();
                        let mut escaped = false;
                        let mut after_cr = false;
                        actual.chars().eq(content.chars().filter_map(|character| {
                            if after_cr {
                                after_cr = false;
                                if character == '\n' {
                                    return None;
                                }
                            }
                            if escaped {
                                escaped = false;
                                match character {
                                    | 'n' => Some('\n'),
                                    | 't' => Some('\t'),
                                    | 'r' => Some('\r'),
                                    | '0' => Some('\0'),
                                    | '\r' => {
                                        after_cr = true;
                                        None
                                    },
                                    | '\n' => None,
                                    | other => Some(other),
                                }
                            }
                            else if character == '\\' {
                                escaped = true;
                                None
                            }
                            else {
                                Some(character)
                            }
                        }))
                    },
                    | _ => false,
                },
                | None => matches!(ret, Maybe::Absent(literal::Absent::Malformed)),
            },
            | _ => matches!(ret, Maybe::Absent(literal::Absent::NotALiteral)),
        }
    },
)]
pub fn parse_literal(
    former: Former,
    text: SourceFragment<'_>,
) -> Maybe<Literal, literal::Absent>
{
    let spelled: &str = text.as_ref();
    let found = match former {
        | Former::Number => Magnitude::from_decimal_text(String::from(spelled))
            .map(|magnitude| Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))),
        | Former::Text => spelled
            .strip_prefix('"')
            .and_then(|opened| opened.strip_suffix('"'))
            .map(|content| {
                Literal::Text(StringLiteral::new(decode_escapes(SourceFragment::from(
                    content,
                ))))
            }),
        | Former::Name
        | Former::Hole
        | Former::Binary
        | Former::Unary
        | Former::Constructor
        | Former::Parenthesized
        | Former::Unit
        | Former::Thunk
        | Former::Lambda
        | Former::Block
        | Former::Return
        | Former::Exit
        | Former::Become
        | Former::Force
        | Former::Call
        | Former::Case
        | Former::Instantiation
        | Former::Projection
        | Former::TypeHead
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::LazyProductType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::Unadmitted => return Maybe::Absent(literal::Absent::NotALiteral),
    };

    found.map_or(Maybe::Absent(literal::Absent::Malformed), Maybe::Present)
}

/// Decode the escapes of a string literal's or an import address's content.
///
/// # Specification
/// - requires: the input is UTF-8 content without its surrounding quote tiles.
/// - ensures: n, t, r and 0 escapes decode to their control characters; escaped
///   LF and CRLF or CR are removed; every other escaped character loses only
///   its backslash.
/// - provides: decoded literal or import-address content, preserving unescaped
///   Unicode.
/// - fails: a trailing backslash contributes no character; unknown escapes are
///   not rejected.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the named escape classes, CR/LF continuations, unknown
///   escapes, Unicode and a trailing backslash have exact decoded values.
/// - witness: `lower::tests::escape_decoding_covers_continuations_unknowns_and_unicode`
/// - witness: `lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
#[spec(
    ensures: |ret| {
        let content: &str = content.as_ref();
        let actual: &str = ret.as_str();
        let mut escaped = false;
        let mut after_cr = false;
        actual.chars().eq(content.chars().filter_map(|character| {
            if after_cr {
                after_cr = false;
                if character == '\n' {
                    return None;
                }
            }
            if escaped {
                escaped = false;
                match character {
                    | 'n' => Some('\n'),
                    | 't' => Some('\t'),
                    | 'r' => Some('\r'),
                    | '0' => Some('\0'),
                    | '\r' => {
                        after_cr = true;
                        None
                    },
                    | '\n' => None,
                    | other => Some(other),
                }
            }
            else if character == '\\' {
                escaped = true;
                None
            }
            else {
                Some(character)
            }
        }))
    },
)]
#[inline]
pub fn decode_escapes(content: SourceFragment<'_>) -> String
{
    let spelled: &str = content.as_ref();
    let mut decoded = String::with_capacity(spelled.len());
    let mut chars = spelled.chars().peekable();
    while let Some(character) = chars.next() {
        if character != '\\' {
            decoded.push(character);
            continue;
        }
        match chars.next() {
            | Some('n') => decoded.push('\n'),
            | Some('t') => decoded.push('\t'),
            | Some('r') => decoded.push('\r'),
            | Some('0') => decoded.push('\0'),
            | Some('\r') => {
                if chars.peek() == Some(&'\n') {
                    let _break = chars.next();
                }
            },
            | Some('\n') | None => {},
            | Some(other) => decoded.push(other),
        }
    }

    decoded
}

/// Whether `text` is a numeric lexeme with a fraction or an exponent.
///
/// # Specification
/// - requires: the input is interpreted as an unsigned numeric lexeme.
/// - ensures: a decimal or exponent marker is required; the whole part and each
///   present fraction or exponent contain nonempty ASCII digits, with at most
///   one exponent sign.
/// - provides: the distinction between an unadmitted fractional number and a
///   malformed integer spelling.
/// - fails: malformed, unmarked, signed-whole and non-ASCII spellings return
///   false.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — decimal and exponent boundaries distinguish unsupported
///   fractional numbers from malformed spellings, including empty fields,
///   repeated markers, exponent signs and non-ASCII digits.
/// - witness: `lower::tests::fractional_spellings_distinguish_unsupported_numbers_from_malformed_ones`
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
#[spec(
    ensures: |ret| {
        let spelled: &str = text.as_ref();
        let mut bytes = spelled.bytes().peekable();
        let digits = |bytes: &mut core::iter::Peekable<core::str::Bytes<'_>>| {
            let present = bytes.peek().is_some_and(u8::is_ascii_digit);
            while bytes.peek().is_some_and(u8::is_ascii_digit) {
                let _digit = bytes.next();
            }
            present
        };
        let whole = digits(&mut bytes);
        let fraction = bytes.next_if_eq(&b'.').is_some();
        let fraction_ok = !fraction || digits(&mut bytes);
        let exponent = bytes.next_if(|&byte| matches!(byte, b'e' | b'E')).is_some();
        let exponent_ok = !exponent || {
            let _sign = bytes.next_if(|&byte| matches!(byte, b'+' | b'-'));
            digits(&mut bytes)
        };
        ret.0
            == (whole
                && (fraction || exponent)
                && fraction_ok
                && exponent_ok
                && bytes.next().is_none())
    },
)]
fn fractional(text: SourceFragment<'_>) -> Fractional
{
    let spelled: &str = text.as_ref();
    let (mantissa, exponent) = spelled
        .split_once(['e', 'E'])
        .map_or((spelled, None), |(left, right)| (left, Some(right)));
    let (whole, fraction) = mantissa
        .split_once('.')
        .map_or((mantissa, None), |(left, right)| (left, Some(right)));
    let digits = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    let fraction_ok = fraction.is_none_or(digits);
    let exponent_ok =
        exponent.is_none_or(|part| digits(part.strip_prefix(['+', '-']).unwrap_or(part)));
    let marked = fraction.is_some() || exponent.is_some();

    Fractional(marked && digits(whole) && fraction_ok && exponent_ok)
}

#[cfg(test)]
mod tests
{

    #[test]
    fn native_boolean_results_have_the_written_classifier()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def answer : +U (-F Bool) ; def answer = thunk { become 19 < 7 } ;"),
            &mut arena,
        );
        let declared = declared_of(module.declarations()[0].outcome());
        let Some(&ValueType::Thunk(computation)) = arena.value_type(declared)
        else {
            panic!("thunk classifier");
        };
        let Some(&CompType::Returner {
            result: boolean, ..
        }) = arena.comp_type(computation)
        else {
            panic!("result classifier");
        };
        let Some(held) = arena.value_type(boolean)
        else {
            panic!("canonical boolean sum");
        };
        let ValueType::Sum(ref parts) = *held
        else {
            panic!("canonical boolean sum");
        };
        let [first, second] = **parts
        else {
            panic!("the boolean sum is binary");
        };
        assert_eq!(arena.value_type(first), Some(&ValueType::unit()));
        assert_eq!(arena.value_type(second), Some(&ValueType::unit()));
        assert!(matches!(
            module.origins().value_type(first),
            Maybe::Present(_)
        ));
    }

    #[test]
    fn native_bindings_keep_generated_origins()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def subtract = sub ;"), &mut arena);
        let value = body_of(module.declarations()[0].outcome());
        let Some(&Value::Primitive { mut body, .. }) = arena.value(value)
        else {
            panic!("native binding");
        };
        loop {
            assert!(matches!(
                module.origins().computation(body),
                Maybe::Present(_)
            ));
            match arena.computation(body) {
                | Some(&Computation::Lambda(inner)) => body = inner,
                | Some(&Computation::Primitive { ref arguments, .. }) => {
                    for &argument in arguments.iter() {
                        assert!(matches!(
                            module.origins().value(argument),
                            Maybe::Present(_)
                        ));
                    }
                    break;
                },
                | other => panic!("native closure shape: {other:?}"),
            }
        }
    }

    #[test]
    fn native_operator_plans_preserve_order()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def answer = thunk { become 19 - 7 } ;"),
            &mut arena,
        );
        let body = body_of(module.declarations()[0].outcome());
        let Some(&Value::Thunk(body)) = arena.value(body)
        else {
            panic!("thunk");
        };
        let Some(&Computation::Primitive {
            primitive,
            arguments: gandr_core_term::primitive::Arguments::Binary(arguments),
        }) = arena.computation(body)
        else {
            panic!("native subtraction");
        };
        let operands = arguments.map(|argument| match arena.value(argument) {
            | Some(&Value::Literal(Literal::Integer(ref integer))) => integer.magnitude().as_ref(),
            | _ => panic!("integer operand"),
        });
        assert_eq!(operands, ["19", "7"]);
        assert_eq!(
            primitive.operator(),
            gandr_core_term::primitive::Operator::Infix("-")
        );
    }

    use alloc::format;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_term::CompType;
    use gandr_core_term::CompTypeId;
    use gandr_core_term::Computation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Sort;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::GroutShape;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;
    use gandr_surface_syntax::SyntaxTree;
    use quenchant_shape::shape::Maybe;

    use super::Fuel;
    use super::LoweringBudget;
    use super::is_value_form;
    use super::literal;
    use super::lower_module;
    use super::parse_literal;
    use crate::attribute::AttributeRegistry;
    use crate::attribute::AttributeSchema;
    use crate::attribute::payload_form;
    use crate::classify::FailureClass;
    use crate::error::FormFault;
    use crate::error::FragmentBoundary;
    use crate::error::FragmentSort;
    use crate::error::LoweringRefusal;
    use crate::error::refusal_span;
    use crate::fixture::Handmade;
    use crate::fixture::Rule;
    use crate::fixture::Spelled;
    use crate::fixture::grammar;
    use crate::fixture::parsed;
    use crate::fixture::registered;
    use crate::fixture::repaired;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::form::Former;
    use crate::form::Repair;
    use crate::module::DeclarationOutcome;
    use crate::module::LoweredDeclaration;
    use crate::module::LoweredModule;
    use crate::namespace::Recognition;
    use crate::origin::Insertion;
    use crate::origin::OriginCount;
    use crate::origin::Provenance;
    use crate::resolve::HeadArity;
    use crate::resolve::OperandCount;
    use crate::resolve::SurfaceName;

    /// The module the parser and the lowering make of `source`, which both
    /// must accept.
    ///
    /// # Specification
    /// - requires: the source parses cleanly and fits the default lowering
    ///   allowance.
    /// - ensures: emitted declaration origins lie within the supplied source,
    ///   in admission order.
    /// - provides: a real parser-to-lowering fixture over the supplied arena.
    /// - fails: none on accepted fixtures.
    /// - panics: if parsing or the lowering engine refuses the fixture.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the listed semantic goldens — complete and one-sided
    ///   declarations retain their independently expected core structure.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
    #[spec(
        ensures: |ret| {
            let spelled: &str = source.as_ref();
            ret.declarations().iter().all(|declaration| {
                let span = declaration.span();
                usize::from(span.start()) <= usize::from(span.end())
                    && usize::from(span.end()) <= spelled.len()
            }) && ret.declarations().windows(2).all(|pair| match *pair {
                | [ref left, ref right] => left.constant() < right.constant(),
                | _ => false,
            })
        },
    )]
    fn lowered<'source>(
        source: SourceText<'source>,
        arena: &mut CoreArena,
    ) -> LoweredModule<'source>
    {
        let pbg = grammar();
        let tree = parsed(&pbg, source);

        lower_module(
            &pbg,
            &tree,
            arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap()
    }

    /// What each declaration of `module` amounts to, in admission order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one outcome per declaration, preserving admission order and
    ///   every refusal payload.
    /// - provides: the semantic outcome sequence used by lowering witnesses.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed successful and refused declarations retain
    ///   their individual outcomes rather than truncating at the first refusal.
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[spec(
        ensures: |ret| {
            ret.iter().copied().eq(module
                .declarations()
                .iter()
                .map(LoweredDeclaration::outcome))
        },
    )]
    fn outcomes<'source>(module: &LoweredModule<'source>) -> Vec<DeclarationOutcome<'source>>
    {
        module
            .declarations()
            .iter()
            .map(LoweredDeclaration::outcome)
            .collect()
    }

    /// The refusal the first declaration of `tree` carries.
    ///
    /// # Specification
    /// - requires: the engine accepts the tree and its first declaration is
    ///   refused.
    /// - ensures: the first declaration’s located refusal, rather than an
    ///   engine-wide refusal.
    /// - provides: an exact refusal witness for parsed and deliberately
    ///   malformed trees.
    /// - fails: none on a fixture meeting the precondition.
    /// - panics: if lowering fails or the first declaration is not refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — malformed lexemes and repaired declarations yield
    ///   their specific located refusal through the real lowering entry point.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    /// - witness: `lower::tests::a_malformed_text_literal_is_refused`
    /// - witness: `lower::tests::a_repaired_declaration_is_refused`
    #[spec(
        ensures: |ret| matches!(ret.span(), Maybe::Present(_)),
    )]
    fn refusal_in<'source>(
        pbg: &Pbg,
        tree: &SyntaxTree<'source>,
    ) -> LoweringRefusal<'source>
    {
        let mut arena = CoreArena::new();
        let module = lower_module(
            pbg,
            tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap();
        let Some(DeclarationOutcome::Refused(refusal)) = outcomes(&module).first().copied()
        else {
            panic!("the first declaration is refused");
        };

        refusal
    }

    /// The refusal the first declaration of `source` carries, which the
    /// parser must accept cleanly.
    ///
    /// # Specification
    /// - requires: the source parses cleanly and its first declaration is
    ///   refused.
    /// - ensures: a declaration-local refusal whose location lies within the
    ///   source.
    /// - provides: the parsed-source refusal oracle.
    /// - fails: none on a fixture meeting the precondition.
    /// - panics: if parsing or lowering fails, or the first declaration
    ///   succeeds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unresolved term and type names retain their different
    ///   refusal variants and the exact spelling’s span.
    /// - witness: `lower::tests::an_undefined_term_name_is_refused`
    /// - witness: `lower::tests::an_undefined_type_head_is_refused`
    #[spec(
        ensures: |ret| {
            let spelled: &str = source.as_ref();
            matches!(ret.span(), Maybe::Present(span) if usize::from(span.start()) <= usize::from(span.end()) && usize::from(span.end()) <= spelled.len())
        },
    )]
    fn refusal(source: SourceText<'_>) -> LoweringRefusal<'_>
    {
        let pbg = grammar();
        let tree = parsed(&pbg, source);

        refusal_in(&pbg, &tree)
    }

    /// The value `body` of `outcome`, which must lower a body.
    ///
    /// # Specification
    /// - requires: the outcome has a lowered body.
    /// - ensures: the body identifier from a completed or body-only
    ///   declaration.
    /// - provides: a checked extraction for structural core assertions.
    /// - fails: never on the required outcome variants.
    /// - panics: if the declaration has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete and body-only declarations expose their
    ///   actual literal bodies rather than substituting a signature coordinate.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
    #[spec(
        ensures: |ret| matches!(outcome, DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } if ret == body),
    )]
    fn body_of(outcome: DeclarationOutcome<'_>) -> gandr_core_term::ValueId
    {
        match outcome {
            | DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => {
                body
            },
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Refused(_) => {
                panic!("the declaration lowers a body")
            },
        }
    }

    /// The declared type of `outcome`, which must lower a signature.
    ///
    /// # Specification
    /// - requires: the outcome has a lowered signature.
    /// - ensures: the declared type from a completed or signature-only
    ///   declaration.
    /// - provides: a checked extraction for structural type assertions.
    /// - fails: never on the required outcome variants.
    /// - panics: if the declaration has no signature.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete and signature-only declarations retain the
    ///   expected type while distinguishing an absent body.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
    #[spec(
        ensures: |ret| matches!(outcome, DeclarationOutcome::Completed { declared_type, .. } | DeclarationOutcome::Uncompleted { declared_type } if ret == declared_type),
    )]
    fn declared_of(outcome: DeclarationOutcome<'_>) -> gandr_core_term::ValueTypeId
    {
        match outcome {
            | DeclarationOutcome::Completed { declared_type, .. }
            | DeclarationOutcome::Uncompleted { declared_type } => declared_type,
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Refused(_) => {
                panic!("the declaration lowers a signature")
            },
        }
    }

    /// The schema `name` is registered with.
    ///
    /// # Specification
    /// - requires: the name is registered.
    /// - ensures: the schema registered for that name.
    /// - provides: the payload policy expected by refusal witnesses.
    /// - fails: never for a registered name.
    /// - panics: if the name is not registered.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — absent and wrong-form payloads name the schema that
    ///   governs the attribute, not merely any registry entry.
    /// - witness: `lower::tests::a_schema_taking_a_payload_refuses_an_absent_one`
    /// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
    #[spec(
        ensures: |ret| matches!(AttributeRegistry::lookup(name), Maybe::Present((_entry, schema)) if ret == schema),
    )]
    fn schema_of(name: SurfaceName<'_>) -> AttributeSchema
    {
        let Maybe::Present((_entry, schema)) = AttributeRegistry::lookup(name)
        else {
            panic!("the name is registered");
        };

        schema
    }

    /// The integer literal `digits` spell.
    ///
    /// # Specification
    /// - requires: a nonempty sequence of ASCII decimal digits.
    /// - ensures: a nonnegative integer with the canonical unpadded magnitude.
    /// - provides: an independently constructed literal expected by core
    ///   witnesses.
    /// - fails: never on valid decimal text.
    /// - panics: on an empty or nondigit spelling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — padded zero and nonzero spellings distinguish
    ///   magnitude normalization from preserving the input’s padding.
    /// - witness: `lower::tests::an_integer_literal_is_its_canonical_magnitude`
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    #[spec(
        ensures: |ret| {
            let spelled: &str = digits.as_ref();
            let unpadded = spelled.trim_start_matches('0');
            let expected = if unpadded.is_empty() { "0" } else { unpadded };
            matches!(ret, Literal::Integer(ref literal) if literal.sign() == Sign::NonNegative && literal.magnitude().as_ref() == expected)
        },
    )]
    fn integer(digits: SourceFragment<'_>) -> Literal
    {
        let spelled: &str = digits.as_ref();
        let magnitude = Magnitude::from_decimal_text(String::from(spelled)).unwrap();

        Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))
    }

    /// The text literal holding `content`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the text literal contains the supplied characters without
    ///   escape decoding or delimiter stripping.
    /// - provides: the expected decoded text for literal witnesses.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — escaped source text is compared with the explicitly
    ///   decoded content, distinct from the source spelling.
    /// - witness: `lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
    /// - witness: `lower::tests::a_text_literal_is_the_bytes_between_its_quotes`
    #[spec(
        ensures: |ret| {
            let spelled: &str = content.as_ref();
            matches!(ret, Literal::Text(ref literal) if literal.as_ref() == spelled)
        },
    )]
    fn text(content: SourceFragment<'_>) -> Literal
    {
        let spelled: &str = content.as_ref();

        Literal::Text(StringLiteral::new(String::from(spelled)))
    }

    #[test]
    fn a_completed_declaration_lowers_both_halves()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x : Integer ; def x = 3 ;"),
            &mut arena,
        );
        let [
            DeclarationOutcome::Completed {
                declared_type,
                body,
            },
        ] = outcomes(&module)[..]
        else {
            panic!("a signature and its definition pair into one completed declaration");
        };

        assert_eq!(
            arena.value_type(declared_type),
            Some(&ValueType::Base(BaseType::Integer)),
            "the signature lowers to the declared type"
        );
        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the definition lowers to the body"
        );
    }

    #[test]
    fn an_uncompleted_signature_is_the_obligation_producer()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x : Integer ;"), &mut arena);
        let [DeclarationOutcome::Uncompleted { declared_type }] = outcomes(&module)[..]
        else {
            panic!("a signature alone is an uncompleted declaration");
        };

        assert_eq!(
            arena.value_type(declared_type),
            Some(&ValueType::Base(BaseType::Integer)),
            "the obligation carries the declared type"
        );
    }

    #[test]
    fn source_holes_keep_their_families_and_distinct_occurrences()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(r#"def a = ?; def b = ?named; def c() { ?pending }"#),
            &mut arena,
        );
        let [
            DeclarationOutcome::Bodied { body: a },
            DeclarationOutcome::Bodied { body: b },
            DeclarationOutcome::Bodied { body: c },
        ] = outcomes(&module)[..]
        else {
            panic!("each unfinished definition lowers");
        };
        let Some(&Value::Hole(first)) = arena.value(a)
        else {
            panic!("anonymous value hole")
        };
        let Some(&Value::Hole(second)) = arena.value(b)
        else {
            panic!("named value hole")
        };
        assert_ne!(first, second);
        let Some(&Value::Thunk(body)) = arena.value(c)
        else {
            panic!("function thunk")
        };
        assert!(matches!(
            arena.computation(body),
            Some(&Computation::Hole(_))
        ));
    }

    #[test]
    fn a_bodiless_definition_lowers_its_body_alone()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x = 3 ;"), &mut arena);
        let [DeclarationOutcome::Bodied { body }] = outcomes(&module)[..]
        else {
            panic!("a definition alone is a bodiless declaration");
        };

        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the body lowers alone"
        );
    }

    #[test]
    fn the_thunk_and_returner_heads_lower_to_their_formers()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x : +U (-F Integer) ;"), &mut arena);
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
        else {
            panic!("`+U` lowers to the thunk type");
        };
        let Some(&CompType::Returner {
            result: returned, ..
        }) = arena.comp_type(suspended)
        else {
            panic!("`-F` lowers to the returner type");
        };

        assert_eq!(
            arena.value_type(returned),
            Some(&ValueType::Base(BaseType::Integer)),
            "the returner carries its value type"
        );
    }

    #[test]
    fn the_bridge_tokens_are_compound_and_sum_is_unaffected()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let sum = |start: usize, end: usize| LoweringRefusal::OutOfFragment {
            span: at(start, end),
            form: FormName::from(NamedKind("sum_type")),
            sort: FragmentSort::ValueType,
            boundary: FragmentBoundary::Unadmitted,
        };

        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x : +U(-F Integer) ;"), &mut arena);
        assert!(
            matches!(
                arena.value_type(declared_of(outcomes(&module)[0])),
                Some(&ValueType::Thunk(_))
            ),
            "`+U` against a bracket is the bridge"
        );
        assert_eq!(
            refusal(SourceText::from("def s : Integer + Unit ;")),
            sum(8_usize, 22_usize),
            "`A + B` is the sum"
        );
        assert_eq!(
            refusal(SourceText::from("def s : Integer +Unit ;")),
            sum(8_usize, 21_usize),
            "a sign against a word that begins with the bridge letter is still the sum"
        );
        for source in [
            "def x : Integer +U Integer ;",
            "def x : Integer -F Integer ;",
        ] {
            assert_eq!(
                refusal(SourceText::from(source)),
                LoweringRefusal::MalformedForm {
                    span: at(16_usize, 26_usize),
                    form: FormName::DECLARATION,
                    fault: FormFault::ExtraOperand,
                },
                "a bridge after an operand is no sum, and `{source}` is refused"
            );
        }
    }

    #[test]
    fn an_arrow_lowers_under_a_thunk_type()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g : +U (Integer -> -F Integer) ;"),
            &mut arena,
        );
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
        else {
            panic!("`+U` lowers to the thunk type");
        };
        let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(suspended)
        else {
            panic!("the arrow lowers to the function type");
        };

        assert_eq!(
            arena.value_type(domain),
            Some(&ValueType::Base(BaseType::Integer)),
            "the domain is a value type"
        );
        assert!(
            matches!(arena.comp_type(codomain), Some(&CompType::Returner { .. })),
            "the codomain is a computation type"
        );
    }

    #[test]
    fn every_type_atom_lowers_to_its_core_type()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def u : Unit ; def i : Integer ; def s : String ;"),
            &mut arena,
        );
        let lowered: Vec<_> = outcomes(&module)
            .into_iter()
            .map(|outcome| arena.value_type(declared_of(outcome)).cloned())
            .collect();

        assert_eq!(
            lowered,
            [
                Some(ValueType::unit()),
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::String)),
            ],
            "each atom lowers to its own core type"
        );
    }

    #[test]
    fn every_universe_spelling_lowers_to_its_universe()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a : Type ; def b : Type[+] ; def c : Type[-] ; def d : Type[+, 3] ; def e : \
                 Type[-, 1] ;",
            ),
            &mut arena,
        );
        let universe = |sort: GroundSort, level: u64| {
            Some(ValueType::Universe {
                sort: Sort::Ground(sort),
                level: Level::constant(LevelConstant::from(level)),
            })
        };
        let lowered: Vec<_> = outcomes(&module)
            .into_iter()
            .map(|outcome| arena.value_type(declared_of(outcome)).cloned())
            .collect();

        assert_eq!(
            lowered,
            [
                universe(GroundSort::Value, 0),
                universe(GroundSort::Value, 0),
                universe(GroundSort::Computation, 0),
                universe(GroundSort::Value, 3),
                universe(GroundSort::Computation, 1),
            ],
            "a universe is the sort and the level written, the value sort and level zero for \
             whichever is left off"
        );
    }

    #[test]
    fn u_and_f_are_names()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (source, name, arity) in [
            ("def x : U ;", "U", HeadArity::Nullary),
            ("def x : F ;", "F", HeadArity::Nullary),
            ("def x : U(Integer) ;", "U", HeadArity::Unary),
            ("def x : F(Integer) ;", "F", HeadArity::Unary),
        ] {
            assert_eq!(
                refusal(SourceText::from(source)),
                LoweringRefusal::UnresolvedTypeHead {
                    span: at(8_usize, 9_usize),
                    name: SurfaceName::from(name),
                    arity,
                },
                "the bridges are `+U` and `-F`, so `{source}` names a type nothing declares"
            );
        }
    }

    #[test]
    fn a_bare_type_binder_is_positive_at_the_fuss_free_level()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def id(a : Type, x : a) -> -F a { return x }"),
            &mut arena,
        );
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&CompType::Pi {
            domain: universe,
            codomain,
        }) = arena.comp_type(suspended)
        else {
            panic!("`a`, which a later type names, binds a dependent arrow");
        };
        let Some(&CompType::Arrow {
            domain,
            codomain: result,
        }) = arena.comp_type(codomain)
        else {
            panic!("`x`, which no type names, binds a plain arrow");
        };
        let Some(&CompType::Returner {
            result: returned, ..
        }) = arena.comp_type(result)
        else {
            panic!("the result is a returner");
        };
        let decoded = |id| match arena.value_type(id) {
            | Some(&ValueType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            | _ => (None, None),
        };
        let fuss_free = Level::constant(LevelConstant::ZERO);
        let innermost = Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        };

        assert_eq!(
            arena.value_type(universe),
            Some(&ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                level: fuss_free.clone(),
            }),
            "a bare `Type` is the value universe at the fuss-free level"
        );
        assert_eq!(
            decoded(domain),
            (Some(innermost.clone()), Some(fuss_free.clone())),
            "`x : a` decodes `a` out of the universe it was bound at"
        );
        assert_eq!(
            decoded(returned),
            (Some(innermost), Some(fuss_free)),
            "the plain arrow binds nothing, so the result names `a` at the same index"
        );
        assert_eq!(
            module
                .origins()
                .value_type(domain)
                .map(|origin| origin.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Decode)),
            "the decode is the lowering's, not the source's"
        );
    }

    #[test]
    fn a_decode_reads_the_universe_its_code_was_written_at()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def small : Type[+, 1] ; def n : small ; def k(c : (Type[-, 2]), t : +U c) -> c \
                 { become force t }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let decoded = |id| match arena.value_type(id) {
            | Some(&ValueType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            | _ => (None, None),
        };
        assert_eq!(
            decoded(declared_of(lowered[1])),
            (
                Some(Value::Constant(ConstantIndex::from(0_usize))),
                Some(Level::constant(LevelConstant::from(1_u64)))
            ),
            "a declaration signed at a universe decodes at that universe's level"
        );

        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_of(lowered[2]))
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&CompType::Pi { codomain, .. }) = arena.comp_type(suspended)
        else {
            panic!("`c`, which later types name, binds a dependent arrow");
        };
        let Some(&CompType::Arrow {
            domain,
            codomain: result,
        }) = arena.comp_type(codomain)
        else {
            panic!("`t`, which no type names, binds a plain arrow");
        };
        let Some(&ValueType::Thunk(thunked)) = arena.value_type(domain)
        else {
            panic!("`+U c` is a thunk type");
        };
        let comp_decoded = |id| match arena.comp_type(id) {
            | Some(&CompType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            | _ => (None, None),
        };
        let code = (
            Some(Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
            Some(Level::constant(LevelConstant::from(2_u64))),
        );
        assert_eq!(
            comp_decoded(thunked),
            code,
            "a binder written at the computation universe, through a grouping, decodes a \
             computation type at its level"
        );
        assert_eq!(
            comp_decoded(result),
            code,
            "and a result naming it is that computation type, with no returner"
        );
    }

    #[test]
    fn a_type_where_a_value_is_read_is_quoted()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a = Integer ; def b = -F Integer ; def c = Type ; def d = +U (-F Integer) ;",
            ),
            &mut arena,
        );
        let quoted = |declaration: usize| {
            let body = body_of(outcomes(&module)[declaration]);
            let provenance = module
                .origins()
                .value(body)
                .map(|origin| origin.provenance());
            match arena.value(body) {
                | Some(&Value::Quote(inner)) => {
                    (arena.value_type(inner).cloned(), None, provenance)
                },
                | Some(&Value::QuoteComputation(inner)) => {
                    (None, arena.comp_type(inner).cloned(), provenance)
                },
                | _ => (None, None, provenance),
            }
        };
        let inserted = Maybe::Present(Provenance::Inserted(Insertion::Quote));

        assert_eq!(
            quoted(0_usize),
            (Some(ValueType::Base(BaseType::Integer)), None, inserted),
            "a type atom where a value is read is its code"
        );
        assert!(
            matches!(quoted(1_usize), (None, Some(CompType::Returner { .. }), _)),
            "a computation type is quoted at its own sort"
        );
        assert_eq!(
            quoted(2_usize).0,
            Some(ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                level: Level::constant(LevelConstant::ZERO),
            }),
            "`Type` where a value is read is the code of the fuss-free universe"
        );
        assert!(
            matches!(quoted(3_usize), (Some(ValueType::Thunk(_)), None, _)),
            "a bridge where a value is read is the code of its thunk type"
        );
    }

    #[test]
    fn the_producer_does_not_admit_a_graded_bridge()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a : +U[ω] (-F Integer) ; def b : +U (-F Integer) ;"),
            &mut arena,
        );
        let lowered: Vec<_> = outcomes(&module)
            .into_iter()
            .map(|outcome| {
                let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_of(outcome))
                else {
                    panic!("the bridge lowers to the thunk type");
                };
                let Some(&CompType::Returner {
                    result: returned, ..
                }) = arena.comp_type(suspended)
                else {
                    panic!("the bridged computation is the returner");
                };
                arena.value_type(returned).cloned()
            })
            .collect();
        assert_eq!(
            lowered,
            [
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::Integer)),
            ],
            "the default grade `ω` is the bridge the core carries, the same as none written"
        );
        assert!(
            matches!(
                refusal(SourceText::from("def c : +U[1] (-F Integer) ;")),
                LoweringRefusal::GradedBridge { .. }
            ),
            "any other grade mints no thunk type"
        );
    }

    #[test]
    fn a_graded_bridge_is_refused_by_name()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (source, grade) in [
            ("def c : +U[1] (-F Integer) ;", "1"),
            ("def c : +U[r] (-F Integer) ;", "r"),
        ] {
            let refused = refusal(SourceText::from(source));
            assert_eq!(
                refused,
                LoweringRefusal::GradedBridge {
                    span: at(11_usize, 12_usize),
                    grade: SurfaceName::from(grade),
                },
                "`{source}` is refused at its grade, naming it"
            );
            assert_eq!(
                refused.classify(),
                FailureClass::Unrepresentable,
                "a grade is a form the fragment does not represent"
            );
        }
    }

    #[test]
    fn a_lambda_body_binds_its_own_de_bruijn_index()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x = thunk { fn (y) { return y } } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[0]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Lambda(under)) = arena.computation(suspended)
        else {
            panic!("the lambda lowers to a lambda");
        };
        let Some(&Computation::Return(returned)) = arena.computation(under)
        else {
            panic!("the lambda's body lowers to a returner");
        };

        assert_eq!(
            arena.value(returned),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
            "the parameter is the innermost binder"
        );
    }

    #[test]
    fn an_earlier_declaration_resolves_as_a_constant()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def a = 3 ; def b = a ;"), &mut arena);
        let body = body_of(outcomes(&module)[1]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "a name declared earlier resolves to its admission position"
        );
    }

    #[test]
    fn the_unit_keyword_lowers_to_the_unit_value()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x : Unit ; def x = unit ;"),
            &mut arena,
        );
        let lowered = outcomes(&module);

        assert_eq!(
            arena.value(body_of(lowered[0])),
            Some(&Value::unit()),
            "`unit` is the unit value"
        );
        assert_eq!(
            spine(&arena, declared_of(lowered[0])),
            ["Unit"],
            "and `Unit` its type"
        );
        let matched = refusal(SourceText::from(
            "def g(x : Unit) -> -F Integer { case x { unit => return 1 } }",
        ));
        assert!(
            matches!(matched, LoweringRefusal::OutOfFragment {
                form: FormName::UNIT,
                boundary: FragmentBoundary::Unadmitted,
                ..
            }),
            "the unit pattern molds, and a match does not admit it yet: {matched:?}"
        );
    }

    #[test]
    fn the_empty_parentheses_are_never_the_unit()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def x = () ;"));

        assert_eq!(
            refused,
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 10_usize),
                form: FormName::UNIT,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::EmptyList,
            },
            "`()` as a value is an empty list"
        );
        assert!(
            alloc::format!("{refused}").contains("`Unit`"),
            "and the refusal names the unit value and its type: {refused}"
        );
        let typed = refusal(SourceText::from("def y : () ;"));
        assert!(
            matches!(typed, LoweringRefusal::OutOfFragment {
                form: FormName::UNIT,
                boundary: FragmentBoundary::EmptyList,
                ..
            }),
            "`()` as a type is the same empty list: {typed:?}"
        );
        assert!(
            alloc::format!("{typed}").contains("`Unit`"),
            "and the refusal names the unit type: {typed}"
        );
    }

    #[test]
    fn a_grouping_lowers_to_what_it_wraps()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x = ( 3 ) ;"), &mut arena);
        let body = body_of(outcomes(&module)[0]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the grouping mints nothing of its own"
        );
        assert_eq!(
            module.origins().value(body).map(|origin| origin.span()),
            Maybe::Present(at(10_usize, 11_usize)),
            "the value's origin is the wrapped form, not the parentheses"
        );
    }

    #[test]
    fn a_text_literal_lowers_with_its_escapes_decoded()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def s = \"a\\nb\" ;"), &mut arena);
        let body = body_of(outcomes(&module)[0]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(text(SourceFragment::from("a\nb")))),
            "the escape is decoded into the character it names"
        );
    }

    #[test]
    fn force_and_application_lower_over_their_children()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = 3 ; def a = thunk { become (force g)(3) } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[1]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Application(head, argument)) = arena.computation(suspended)
        else {
            panic!("the call lowers to an application");
        };
        let Some(&Computation::Force(forced)) = arena.computation(head)
        else {
            panic!("the grouped force lowers to a force");
        };

        assert_eq!(
            arena.value(forced),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "the forced value is the earlier declaration"
        );
        assert_eq!(
            arena.value(argument),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the argument is a value"
        );
    }

    #[test]
    fn an_exit_lowers_where_a_path_passes_and_nowhere_else()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def g = 3 ; def a = thunk { return g } ; def b = thunk { become (force a) } ; \
                 def c = thunk { { return 4 } } ; def d = thunk { return 5 ; } ; \
                 def e = thunk { become return 6 } ;",
            ),
            &mut arena,
        );
        let suspended = |index: usize| {
            let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[index]))
            else {
                panic!("the thunk lowers to a thunk value");
            };
            suspended
        };
        let Some(&Computation::Return(returned)) = arena.computation(suspended(1_usize))
        else {
            panic!("`return` ending a thunk's body lowers to the returner");
        };
        assert_eq!(
            arena.value(returned),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "the returned value is the earlier declaration"
        );
        assert!(
            matches!(
                arena.computation(suspended(2_usize)),
                Some(&Computation::Force(_))
            ),
            "`become` adopts the computation it runs, minting no frame of its own"
        );
        assert!(
            matches!(
                arena.computation(suspended(3_usize)),
                Some(&Computation::Return(_))
            ),
            "tail position reaches through a block"
        );
        assert!(
            matches!(
                arena.computation(suspended(4_usize)),
                Some(&Computation::Return(_))
            ),
            "an exit written as the block's closing statement ends the body"
        );
        assert!(
            matches!(
                arena.computation(suspended(5_usize)),
                Some(&Computation::Return(_))
            ),
            "`become` passes its body's end to the exit it runs"
        );
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def a = thunk { become (return 1)(2) } ;"));
        assert!(
            matches!(
                refused,
                LoweringRefusal::OutOfFragment { span, form, boundary: FragmentBoundary::NotInTail, .. }
                    if span == at(24, 32) && form == FormName::from(NamedKind("return_expression"))
            ),
            "an exit at a call's head, where no path passes, is refused at itself: {refused:?}"
        );
        for (source, start, end) in [
            (
                "def a = thunk { run y <- return 1 ; return y } ;",
                36_usize,
                44_usize,
            ),
            (
                "def a = thunk { run y <- become pure 1 ; return y } ;",
                41_usize,
                49_usize,
            ),
        ] {
            let refused = refusal(SourceText::from(source));
            assert_eq!(
                refused,
                LoweringRefusal::Unreachable {
                    span: at(start, end)
                },
                "the rest of a block after a statement that always exits is unreachable: \
                 `{source}`"
            );
        }
    }

    #[test]
    fn a_function_tail_lowers_to_a_thunked_lambda_chain()
    {
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def f(x: Integer, y: String) -> -F Integer { run z <- pure y ; return x }",
            ),
            &mut arena,
        );
        let [ref declaration] = *module.declarations()
        else {
            panic!("the tail declares one name");
        };
        let DeclarationOutcome::Completed {
            declared_type,
            body,
        } = declaration.outcome()
        else {
            panic!("a tail typing every parameter and its result writes both halves");
        };
        assert!(
            matches!(declaration.signature(), Maybe::Present(_))
                && declaration.signature() == declaration.definition(),
            "both halves are the one declaration form"
        );

        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_type)
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&CompType::Arrow {
            domain: first,
            codomain: rest,
        }) = arena.comp_type(suspended)
        else {
            panic!("the first parameter is the outer arrow");
        };
        let Some(&CompType::Arrow {
            domain: second,
            codomain: result,
        }) = arena.comp_type(rest)
        else {
            panic!("the second parameter is the inner arrow");
        };
        let Some(&CompType::Returner {
            result: returned, ..
        }) = arena.comp_type(result)
        else {
            panic!("the result is the written returner");
        };
        assert_eq!(
            [first, second, returned].map(|id| arena.value_type(id).cloned()),
            [
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::String)),
                Some(ValueType::Base(BaseType::Integer)),
            ],
            "the declared type is `+U (Integer -> String -> -F Integer)`"
        );

        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the body is a thunk");
        };
        let Some(&Computation::Lambda(outer)) = arena.computation(suspended)
        else {
            panic!("the first parameter is the outer lambda");
        };
        let Some(&Computation::Lambda(inner)) = arena.computation(outer)
        else {
            panic!("the second parameter is the inner lambda");
        };
        let Some(&Computation::Bind(bound, rest)) = arena.computation(inner)
        else {
            panic!("the statement is a bind");
        };
        let (Some(&Computation::Return(read)), Some(&Computation::Return(last))) =
            (arena.computation(bound), arena.computation(rest))
        else {
            panic!("the bound and the last computation are returners");
        };
        assert_eq!(
            [read, last].map(|id| arena.value(id).cloned()),
            [Some(variable(0_u32)), Some(variable(2_u32))],
            "`y` is innermost before the statement, and `x` sits under `y` and `z` after it"
        );
        assert_eq!(
            module
                .origins()
                .value(body)
                .map(|origin| origin.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Thunk)),
            "the body's thunk is the lowering's, not the source's"
        );
        assert_eq!(
            module
                .origins()
                .value_type(declared_type)
                .map(|origin| origin.provenance()),
            Maybe::Present(Provenance::Written),
            "the declared type is the function form's own"
        );
    }

    #[test]
    fn an_empty_parameter_list_lowers_to_a_thunked_computation()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def main() -> -F Integer { return 3 }"),
            &mut arena,
        );
        let [
            DeclarationOutcome::Completed {
                declared_type,
                body,
            },
        ] = outcomes(&module)[..]
        else {
            panic!("a tail of no parameters writes both halves");
        };
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_type)
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&Value::Thunk(computation)) = arena.value(body)
        else {
            panic!("the body is a thunk");
        };

        assert!(
            matches!(arena.comp_type(suspended), Some(&CompType::Returner { .. })),
            "no arrow stands between `+U` and the result"
        );
        assert!(
            matches!(
                arena.computation(computation),
                Some(&Computation::Return(_))
            ),
            "no lambda stands between the thunk and the block"
        );
    }

    #[test]
    fn a_tail_missing_a_type_writes_its_definition_alone()
    {
        for source in [
            "def f(x: Integer) { return x }",
            "def f(x, y: Integer) -> -F Integer { return y }",
        ] {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            let [ref declaration] = *module.declarations()
            else {
                panic!("`{source}` declares one name");
            };

            assert!(
                matches!(declaration.outcome(), DeclarationOutcome::Bodied { .. }),
                "`{source}` lowers its body alone"
            );
            assert!(
                matches!(declaration.signature(), Maybe::Absent(_)),
                "`{source}` writes no signature"
            );
        }
    }

    #[test]
    fn a_block_binds_each_statement_over_the_next()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run x <- pure 1 ; run y <- pure x ; return x } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[0]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(first, rest)) = arena.computation(suspended)
        else {
            panic!("the first statement is the outer bind");
        };
        let Some(&Computation::Bind(second, last)) = arena.computation(rest)
        else {
            panic!("the second statement binds over the rest of the block");
        };
        let returned = |id| match arena.computation(id) {
            | Some(&Computation::Return(value)) => arena.value(value).cloned(),
            | _ => None,
        };

        assert_eq!(
            [returned(first), returned(second), returned(last)],
            [
                Some(Value::Literal(integer(SourceFragment::from("1")))),
                Some(variable(0_u32)),
                Some(variable(1_u32)),
            ],
            "each statement's name binds over everything after it"
        );
        assert_eq!(
            module
                .origins()
                .computation(suspended)
                .map(|origin| origin.span()),
            Maybe::Present(at(16_usize, 19_usize)),
            "a bind's origin is its statement's `run`"
        );
    }

    /// `c ;` binds its value under a binder no name reaches and splits it as
    /// the unit, so a name bound before it is read one index further out
    /// after it, and the bind's origin is the discarded computation.
    #[test]
    fn a_discarded_statement_splits_its_unit()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run x <- pure 1 ; pure 2 ; return x } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(_, rest)) = arena.computation(suspended)
        else {
            panic!("the named statement is the outer bind");
        };
        let Some(&Computation::Bind(discarded, split)) = arena.computation(rest)
        else {
            panic!("the discarded statement binds over the rest of the block");
        };
        let Some(&Computation::Split {
            scrutinee,
            arity,
            body,
        }) = arena.computation(split)
        else {
            panic!("the discarded value is split");
        };
        assert_eq!(arity, gandr_core_term::ComponentCount::default());
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        assert_eq!(arena.value(scrutinee), Some(&variable(0_u32)));
        let returned = |id| match arena.computation(id) {
            | Some(&Computation::Return(value)) => arena.value(value).cloned(),
            | _ => None,
        };
        assert_eq!(
            [returned(discarded), returned(body)],
            [
                Some(Value::Literal(integer(SourceFragment::from("2")))),
                Some(variable(1_u32)),
            ],
            "the name bound before the discard is read past its binder"
        );
        assert_eq!(
            module
                .origins()
                .computation(rest)
                .map(|origin| origin.span()),
            Maybe::Present(at(34_usize, 40_usize)),
            "a discarded statement's bind has its computation's origin"
        );
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run x <- pure 1 ; run _ <- pure 2 ; return x } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(_, rest)) = arena.computation(suspended)
        else {
            panic!("the named statement is the outer bind");
        };
        let Some(&Computation::Bind(_, last)) = arena.computation(rest)
        else {
            panic!("the wildcard statement binds over the rest of the block");
        };
        assert!(
            matches!(arena.computation(last), Some(&Computation::Return(value)) if arena.value(value) == Some(&variable(1_u32))),
            "a wildcard binds at any type, with no split, and a name before it is read past it"
        );
    }

    /// `run (q, r) <- c ;` binds the tuple under a binder no name reaches and
    /// splits it, the first component outermost, so `q` is read one index
    /// further out than `r`.
    #[test]
    fn a_tuple_binder_splits_the_returned_tuple_in_order()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run (q, r) <- pure (1, 2) ; return (r, q) } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(_, split)) = arena.computation(suspended)
        else {
            panic!("the statement binds over the rest of the block");
        };
        let Some(&Computation::Split {
            scrutinee,
            arity,
            body,
        }) = arena.computation(split)
        else {
            panic!("the bound tuple is split");
        };
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        assert_eq!(arity, gandr_core_term::ComponentCount::from(2_usize));
        assert_eq!(arena.value(scrutinee), Some(&variable(0_u32)));
        let Some(&Computation::Return(returned)) = arena.computation(body)
        else {
            panic!("the block's last computation returns");
        };
        let Some(returned) = arena.value(returned)
        else {
            panic!("the returned value is minted");
        };
        let Value::Tuple(ref components) = *returned
        else {
            panic!("a pair is returned");
        };
        assert_eq!(
            components
                .iter()
                .map(|&component| arena.value(component).cloned())
                .collect::<Vec<_>>(),
            [Some(variable(0_u32)), Some(variable(1_u32))],
            "`r` is the innermost binder and `q` the one outside it"
        );
    }

    #[test]
    fn a_block_standing_as_a_computation_binds_its_statements()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { { run x <- pure 1 ; return x } } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(first, last)) = arena.computation(suspended)
        else {
            panic!("the inner block's statement binds over its last computation");
        };
        assert!(
            matches!(arena.computation(first), Some(&Computation::Return(value)) if arena.value(value) == Some(&Value::Literal(integer(SourceFragment::from("1"))))),
            "the statement runs first"
        );
        assert!(
            matches!(arena.computation(last), Some(&Computation::Return(value)) if arena.value(value) == Some(&Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) })),
            "the last computation reads the statement's binder"
        );
        assert_eq!(
            refusal(SourceText::from("def b = thunk { return { pure 1 } } ;")),
            LoweringRefusal::OutOfFragment {
                span: at(23_usize, 33_usize),
                form: FormName::BLOCK,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::WrongSort,
            },
            "a block is a computation, refused where a value is read"
        );
    }

    #[test]
    fn a_call_applies_its_arguments_left_to_right()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def g = thunk { fn (x) { fn (y) { return x } } } ; def h = thunk { become g(1, 2) } ; \
                 def k = thunk { become g() } ;",
            ),
            &mut arena,
        );
        let called = |declaration: usize| {
            let Some(&Value::Thunk(suspended)) =
                arena.value(body_of(outcomes(&module)[declaration]))
            else {
                panic!("the thunk lowers to a thunk value");
            };
            suspended
        };
        let Some(&Computation::Application(inner, second)) = arena.computation(called(1_usize))
        else {
            panic!("the last argument is the outer application");
        };
        let Some(&Computation::Application(head, first)) = arena.computation(inner)
        else {
            panic!("the first argument is the inner application");
        };

        assert_eq!(
            [first, second].map(|id| arena.value(id).cloned()),
            [
                Some(Value::Literal(integer(SourceFragment::from("1")))),
                Some(Value::Literal(integer(SourceFragment::from("2")))),
            ],
            "the arguments apply left to right"
        );
        assert!(
            matches!(arena.computation(head), Some(&Computation::Force(_))),
            "the head is applied to the first argument"
        );
        assert!(
            matches!(
                arena.computation(called(2_usize)),
                Some(&Computation::Force(_))
            ),
            "a call of no arguments is its head"
        );
    }

    #[test]
    fn a_value_head_is_forced_and_marked_inserted()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def g = thunk { fn (x) { return x } } ; def h = thunk { become g(1) } ;",
            ),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[1]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Application(head, _argument)) = arena.computation(suspended)
        else {
            panic!("the call lowers to an application");
        };
        let Some(&Computation::Force(forced)) = arena.computation(head)
        else {
            panic!("the value head is forced");
        };
        let origin = module.origins().computation(head);

        assert_eq!(
            arena.value(forced),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "the force is over the name the source wrote"
        );
        assert_eq!(
            origin.map(|inserted| inserted.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Force)),
            "the force is the lowering's, not the source's"
        );
        assert_eq!(
            origin.map(|inserted| inserted.span()),
            Maybe::Present(at(63_usize, 64_usize)),
            "the inserted force names the head whose position demanded it"
        );
    }

    #[test]
    fn an_author_written_force_is_not_marked_inserted()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = 3 ; def a = thunk { become (force g)(3) } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[1]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Application(head, _argument)) = arena.computation(suspended)
        else {
            panic!("the call lowers to an application");
        };
        let Some(&Computation::Force(forced)) = arena.computation(head)
        else {
            panic!("the written force is the head");
        };

        assert!(
            matches!(arena.value(forced), Some(&Value::Constant(_))),
            "a computation head gains no second force"
        );
        assert_eq!(
            module
                .origins()
                .computation(head)
                .map(|written| written.provenance()),
            Maybe::Present(Provenance::Written),
            "the force the source wrote is the source's"
        );
    }

    #[test]
    fn a_positive_result_gains_a_returner_once()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def f(x: Integer) -> Integer { return x } def g(x: Integer) -> -F Integer { return x }",
            ),
            &mut arena,
        );
        let result = |declaration: usize| {
            let declared = declared_of(outcomes(&module)[declaration]);
            let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
            else {
                panic!("the declared type is a thunk type");
            };
            let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(suspended)
            else {
                panic!("the parameter is an arrow");
            };
            let Some(&CompType::Returner {
                result: returned, ..
            }) = arena.comp_type(codomain)
            else {
                panic!("the result is a returner");
            };
            (
                arena.value_type(returned).cloned(),
                module
                    .origins()
                    .comp_type(codomain)
                    .map(|origin| origin.provenance()),
            )
        };

        assert_eq!(
            result(0_usize),
            (
                Some(ValueType::Base(BaseType::Integer)),
                Maybe::Present(Provenance::Inserted(Insertion::Returner))
            ),
            "a value type at the result gains the lowering's returner"
        );
        assert_eq!(
            result(1_usize),
            (
                Some(ValueType::Base(BaseType::Integer)),
                Maybe::Present(Provenance::Written)
            ),
            "a written returner is the only one, and the source's"
        );
    }

    #[test]
    fn a_self_reference_is_unresolved()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a = a ;")),
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 9_usize),
                name: SurfaceName::from("a"),
            },
            "a declaration is not in scope in its own body"
        );
    }

    #[test]
    fn an_undefined_term_name_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a = b ;")),
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 9_usize),
                name: SurfaceName::from("b"),
            },
            "a name nothing declares is refused where it stands"
        );
    }

    #[test]
    fn an_undefined_type_head_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def a : Intgr ;"));

        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 13_usize),
                name: SurfaceName::from("Intgr"),
                arity: HeadArity::Nullary,
            },
            "a misspelt head is a mistake, not a new nominal type"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an unresolved head is the author's mistake"
        );
    }

    #[test]
    fn an_applied_nullary_head_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Unit Integer ;")),
            LoweringRefusal::MalformedForm {
                span: at(13_usize, 20_usize),
                form: FormName::DECLARATION,
                fault: FormFault::ExtraOperand,
            },
            "juxtaposition is not application: the second head is an operand too many"
        );
    }

    #[test]
    fn an_applied_head_no_former_answers_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Foo(Integer) ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 11_usize),
                name: SurfaceName::from("Foo"),
                arity: HeadArity::Unary,
            },
            "a head applied to one argument is looked up among the unary formers"
        );
        assert_eq!(
            refusal(SourceText::from("def a : Foo(Integer, String) ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 11_usize),
                name: SurfaceName::from("Foo"),
                arity: HeadArity::Polyadic(OperandCount::from(2_usize)),
            },
            "no former takes two arguments, and the refusal says how many were written"
        );
    }

    /// One node of a core type, as [`spine`] walks it.
    ///
    /// # Specification
    /// - requires: identifiers are interpreted in the supplied arena.
    /// - ensures: the pending work retains whether the next node is a value or
    ///   computation type.
    /// - provides: a family-tagged traversal stack for the supported type
    ///   fragment.
    /// - fails: none as a data value.
    /// - panics: none.
    /// - executable: none — the arena and traversal stack are absent; `spine`
    ///   checks the root token and its witnesses observe the ordered structure.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the named semantic goldens — thunk, returner and
    ///   arrow nodes are traversed across both type families.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
    #[derive(Clone, Copy)]
    enum TypeNode
    {
        /// A value type.
        Value(ValueTypeId),
        /// A computation type.
        Computation(CompTypeId),
    }

    /// The type at `root`, in pre-order, one token per former, so two types
    /// minted at different arena positions compare by structure.
    ///
    /// # Specification
    /// - requires: an acyclic type graph rooted in the supplied arena.
    /// - ensures: preorder tokens preserve the supported thunk, returner, arrow
    ///   and product structure; unsupported or absent nodes are terminal
    ///   diagnostic tokens.
    /// - provides: an arena-coordinate-independent comparison for the supported
    ///   type fragment.
    /// - fails: never; this is not a complete serialization of every core type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the supported fragment only — explicit
    ///   thunk/returner and arrow/product spellings yield pinned semantic
    ///   preorder tokens; unsupported nodes are not claimed to have a
    ///   structural encoding.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
    #[spec(
        ensures: |ret| match arena.value_type(root) {
            | Some(&ValueType::Thunk(_)) => ret.first().is_some_and(|token| token == "U"),
            | Some(&ValueType::Product(ref parts)) if parts.is_empty() => ret.first().is_some_and(|token| token == "Unit"),
            | Some(&ValueType::Product(_)) => ret.first().is_some_and(|token| token == "*"),
            | _ => true,
        },
    )]
    fn spine(
        arena: &CoreArena,
        root: ValueTypeId,
    ) -> Vec<String>
    {
        let mut pending = vec![TypeNode::Value(root)];
        let mut tokens = Vec::new();
        while let Some(next) = pending.pop() {
            match next {
                | TypeNode::Value(at) => match arena.value_type(at) {
                    | Some(&ValueType::Base(base)) => tokens.push(format!("{base:?}")),
                    | Some(&ValueType::Product(ref parts)) if parts.is_empty() => {
                        tokens.push(String::from("Unit"));
                    },
                    | Some(&ValueType::Thunk(inner)) => {
                        tokens.push(String::from("U"));
                        pending.push(TypeNode::Computation(inner));
                    },
                    | Some(&ValueType::Product(ref parts)) => {
                        tokens.push(String::from("*"));
                        pending.extend(parts.iter().rev().map(|&part| TypeNode::Value(part)));
                    },
                    | other => tokens.push(format!("{other:?}")),
                },
                | TypeNode::Computation(at) => match arena.comp_type(at) {
                    | Some(&CompType::Returner { result: inner, .. }) => {
                        tokens.push(String::from("F"));
                        pending.push(TypeNode::Value(inner));
                    },
                    | Some(&CompType::Arrow { domain, codomain }) => {
                        tokens.push(String::from("->"));
                        pending.push(TypeNode::Computation(codomain));
                        pending.push(TypeNode::Value(domain));
                    },
                    | other => tokens.push(format!("{other:?}")),
                },
            }
        }

        tokens
    }

    #[test]
    fn the_alias_is_the_thunked_arrow()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a : Integer => String ; def b : +U (Integer -> -F String) ; def c : \
                 (Integer, String) => Unit ; def d : +U (Integer -> String -> -F Unit) ; def e \
                 : Integer => Integer => String ; def f : +U (Integer -> -F (+U (Integer -> -F \
                 String))) ; def g : () => String ; def h : +U (-F String) ; def i : Unit => \
                 String ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let declared = |at: usize| spine(&arena, declared_of(lowered[at]));

        assert_eq!(
            declared(0_usize),
            ["U", "->", "Integer", "F", "String"],
            "`A => B` lowers to the thunked arrow into the returner"
        );
        assert_eq!(
            declared(0_usize),
            declared(1_usize),
            "and is the same core type the thunked arrow spells"
        );
        assert_eq!(
            declared(2_usize),
            declared(3_usize),
            "a domain list curries left to right under one thunk"
        );
        assert_eq!(
            declared(4_usize),
            declared(5_usize),
            "the alias nests to the right, each level its own thunk"
        );
        assert_eq!(
            declared(6_usize),
            ["U", "F", "String"],
            "`() => C` takes no argument"
        );
        assert_eq!(
            declared(6_usize),
            declared(7_usize),
            "and is the thunked returner itself"
        );
        assert_eq!(
            declared(8_usize),
            ["U", "->", "Unit", "F", "String"],
            "`Unit => C` takes the unit value, a type of its own"
        );
        assert_eq!(
            refusal(SourceText::from("def z : (Integer, String) ;")),
            LoweringRefusal::MalformedForm {
                span: at(16_usize, 17_usize),
                form: FormName::from(NamedKind("parenthesized_type")),
                fault: FormFault::MisplacedTile,
            },
            "a type list anywhere but before `=>` is refused at its first comma"
        );
    }

    #[test]
    fn an_arrow_where_a_value_type_is_read_is_a_static_pi()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def t : (Type -> Type[-]) -> Type -> Type ;"),
            &mut arena,
        );
        let universe = |id, sort| {
            arena.value_type(id)
                == Some(&ValueType::Universe {
                    sort: Sort::Ground(sort),
                    level: Level::constant(LevelConstant::ZERO),
                })
        };
        let pi = |id| match arena.value_type(id) {
            | Some(&ValueType::StaticPi { domain, codomain }) => Some((domain, codomain)),
            | _ => None,
        };
        let Some((family, rest)) = pi(declared_of(outcomes(&module)[0]))
        else {
            panic!("an arrow where a value type is read is a static Pi");
        };
        let Some((family_domain, family_codomain)) = pi(family)
        else {
            panic!("the grouped domain is a static Pi of its own");
        };
        let Some((carrier, result)) = pi(rest)
        else {
            panic!("the codomain nests to the right");
        };
        assert!(
            universe(family_domain, GroundSort::Value)
                && universe(family_codomain, GroundSort::Computation)
                && universe(carrier, GroundSort::Value)
                && universe(result, GroundSort::Value),
            "every operand is the universe it spells"
        );
    }

    #[test]
    fn the_reserved_lazy_product_is_declined()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def a : -F Integer & -F Integer ;"));

        assert_eq!(
            refused,
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 31_usize),
                form: FormName::from(NamedKind("lazy_product_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::Reserved,
            },
            "the lazy product parses and is declined by name"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::Unrepresentable,
            "a reserved form is outside the fragment, not the author's mistake"
        );
    }

    #[test]
    fn a_computation_codomain_of_a_static_pi_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Integer -> -F Integer ;")),
            LoweringRefusal::OutOfFragment {
                span: at(19_usize, 29_usize),
                form: FormName::from(NamedKind("f_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            },
            "an arrow in a declaration's type is a static Pi, whose codomain is a value type"
        );
    }

    #[test]
    fn the_eager_product_and_pair_lower_to_their_formers()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def p : Integer * String ; def q = (1, \"a\") ; def r : Integer * Unit * String ; \
                 def s = (1, unit, \"a\") ; def l : (Integer * Unit) * String ; def m : Integer \
                 * (Unit * String) ; def o = (1,) ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let one = Value::Literal(integer(SourceFragment::from("1")));
        let letter = Value::Literal(text(SourceFragment::from("a")));
        let members = |id| {
            arena
                .value(id)
                .and_then(Value::components)
                .map(|components| {
                    components
                        .iter()
                        .map(|&component| arena.value(component))
                        .collect::<Vec<_>>()
                })
        };
        let parts = |id| match arena.value_type(id) {
            | Some(&ValueType::Product(ref parts)) => Some(parts.to_vec()),
            | _ => None,
        };
        let spines = |id| {
            parts(id)
                .unwrap_or_default()
                .into_iter()
                .map(|part| spine(&arena, part).join(" "))
                .collect::<Vec<_>>()
        };

        assert_eq!(
            spines(declared_of(lowered[0])),
            ["Integer", "String"],
            "`A * B` lowers to the product of its operands"
        );
        assert_eq!(
            members(body_of(lowered[1])),
            Some(vec![Some(&one), Some(&letter)]),
            "a comma list where a value is read is one tuple holding its members in order"
        );
        assert_eq!(
            spines(declared_of(lowered[2])),
            ["Integer", "Unit", "String"],
            "an unparenthesized chain is one product of three components"
        );
        assert_eq!(
            members(body_of(lowered[3])),
            Some(vec![Some(&one), Some(&Value::unit()), Some(&letter)]),
            "a tuple of three is one node, each member at its place"
        );
        assert_eq!(
            spines(declared_of(lowered[4])),
            ["* Integer Unit", "String"],
            "a parenthesized product on the left stays one component"
        );
        assert_eq!(
            spines(declared_of(lowered[5])),
            ["Integer", "* Unit String"],
            "a parenthesized product on the right stays one component"
        );
        assert_eq!(
            members(body_of(lowered[6])),
            Some(vec![Some(&one)]),
            "`(v,)` is the tuple of one component, not `v`"
        );
        assert_eq!(
            refusal(SourceText::from("def t : +U (Integer * Integer) ;")),
            LoweringRefusal::OutOfFragment {
                span: at(12_usize, 29_usize),
                form: FormName::from(NamedKind("product_type")),
                sort: FragmentSort::CompType,
                boundary: FragmentBoundary::WrongSort,
            },
            "a product is a value type, not a computation type"
        );
        assert_eq!(
            refusal(SourceText::from("def u = thunk { (1, 2) } ;")),
            LoweringRefusal::OutOfFragment {
                span: at(16_usize, 22_usize),
                form: FormName::TUPLE,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::WrongSort,
            },
            "a pair is a value, not a computation"
        );
    }

    #[test]
    fn a_static_abstraction_binds_its_name_over_a_quoted_body()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def k = \\A. \\B. A * B ;"), &mut arena);
        let lambda = |id| match arena.value(id) {
            | Some(&Value::StaticLambda(body)) => Some(body),
            | _ => None,
        };
        let decoded = |id| match arena.value_type(id) {
            | Some(&ValueType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            | _ => (None, None),
        };
        let variable = |index: u32| {
            (
                Some(Value::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(index),
                }),
                Some(Level::constant(LevelConstant::ZERO)),
            )
        };

        let Some(inner) = lambda(body_of(outcomes(&module)[0])).and_then(lambda)
        else {
            panic!("each backslash is one static lambda");
        };
        let Some(&Value::Quote(quoted)) = arena.value(inner)
        else {
            panic!("a type written as the body is quoted");
        };
        let Some(held) = arena.value_type(quoted)
        else {
            panic!("the body is the product it spells");
        };
        let ValueType::Product(ref parts) = *held
        else {
            panic!("the body is the product it spells");
        };
        let [first, second] = **parts
        else {
            panic!("the spelled product is binary");
        };
        assert_eq!(
            (decoded(first), decoded(second)),
            (variable(1_u32), variable(0_u32)),
            "each binder decodes at its own index, the fuss-free universe where a value type \
             is read"
        );
        assert_eq!(
            refusal(SourceText::from("def m : \\A. A ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 13_usize),
                form: FormName::from(NamedKind("static_abstraction")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            },
            "a static abstraction is a value, not a type"
        );
    }

    #[test]
    fn a_static_application_decodes_where_its_operator_says_or_where_it_stands()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def t : Type -> Type[-, 1] ; def a : +U (t(Integer)) ; def w = \\X. t(X) ; def k \
                 = \\G. \\A. +U (G(A)) * A ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let constant = Value::Constant(ConstantIndex::from(0_usize));
        let applied = |id| match arena.value(id) {
            | Some(&Value::StaticApplication(head, argument)) => {
                Some((arena.value(head).cloned(), arena.value(argument).cloned()))
            },
            | _ => None,
        };
        let decoded = |id| match arena.comp_type(id) {
            | Some(&CompType::Element { code, ref target }) => Some((code, target.clone())),
            | _ => None,
        };
        let lambda = |id| match arena.value(id) {
            | Some(&Value::StaticLambda(body)) => Some(body),
            | _ => None,
        };

        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_of(lowered[1]))
        else {
            panic!("`+U` is a thunk type");
        };
        let Some((code, target)) = decoded(suspended)
        else {
            panic!("an operator applied where a computation type is read decodes");
        };
        assert_eq!(
            target,
            Level::constant(LevelConstant::from(1_u64)),
            "at the level of the universe its operator's codomain spells"
        );
        let Some((Some(head), Some(Value::Quote(argument)))) = applied(code)
        else {
            panic!("the code is the operator applied to the quoted argument");
        };
        assert_eq!(
            (head, arena.value_type(argument).cloned()),
            (constant.clone(), Some(ValueType::Base(BaseType::Integer))),
            "the operator is the declaration, and the argument a type's code"
        );

        assert_eq!(
            lambda(body_of(lowered[2])).and_then(applied),
            Some((Some(constant), Some(variable(0_u32)))),
            "where a value is read the application stands as itself, its binder unquoted"
        );

        let Some(inner) = lambda(body_of(lowered[3])).and_then(lambda)
        else {
            panic!("two static lambdas");
        };
        let Some(&Value::Quote(quoted)) = arena.value(inner)
        else {
            panic!("a quoted body");
        };
        let Some(held) = arena.value_type(quoted)
        else {
            panic!("a product body");
        };
        let ValueType::Product(ref parts) = *held
        else {
            panic!("a product body");
        };
        let [left, right] = **parts
        else {
            panic!("the product body is binary");
        };
        let Some(&ValueType::Thunk(family)) = arena.value_type(left)
        else {
            panic!("a thunk type on the left");
        };
        let Some((family_code, family_level)) = decoded(family)
        else {
            panic!("an untyped operator applied where a computation type is read decodes there");
        };
        assert_eq!(
            (applied(family_code), family_level),
            (
                Some((Some(variable(1_u32)), Some(variable(0_u32)))),
                Level::constant(LevelConstant::ZERO)
            ),
            "at the computation types and the fuss-free level"
        );
        assert!(
            matches!(
                arena.value_type(right),
                Some(&ValueType::Element { code, .. })
                    if arena.value(code) == Some(&variable(0_u32))
            ),
            "and an untyped binder where a value type is read decodes at the value types"
        );
    }

    #[test]
    fn a_lambda_in_value_position_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a = fn (y) { return y } ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 27_usize),
                form: FormName::from(NamedKind("lambda_expression")),
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::WrongSort,
            },
            "a lambda is a computation and must be suspended to stand as a value"
        );
    }

    #[test]
    fn forms_outside_the_fragment_are_unadmitted()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let unadmitted = |start: usize, end: usize, form: FormName, sort: FragmentSort| {
            LoweringRefusal::OutOfFragment {
                span: at(start, end),
                form,
                sort,
                boundary: FragmentBoundary::Unadmitted,
            }
        };
        let rows = [
            (
                "def a = 1.5 ;",
                unadmitted(
                    8_usize,
                    11_usize,
                    FormName::from(NamedKind("number")),
                    FragmentSort::Value,
                ),
            ),
            (
                "def a = thunk { val y = 3; return y } ;",
                unadmitted(
                    16_usize,
                    19_usize,
                    FormName::VAL_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { fork (x : Integer) { pure 1 } as y ; return 2 } ;",
                unadmitted(
                    16_usize,
                    20_usize,
                    FormName::FORK_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { pure 1 ; } ;",
                unadmitted(
                    16_usize,
                    24_usize,
                    FormName::EXPRESSION_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { run y : -F Integer <- pure 1; return y } ;",
                unadmitted(
                    22_usize,
                    23_usize,
                    FormName::ANNOTATION,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def f @[a : Type] (x) { return x }",
                unadmitted(
                    0_usize,
                    34_usize,
                    FormName::PARAMETERS,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def rec f() { return 1 }",
                unadmitted(
                    0_usize,
                    24_usize,
                    FormName::RECURSIVE,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def f(A) { return 1 }",
                unadmitted(
                    6_usize,
                    7_usize,
                    FormName::PARAMETER,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def a = (3 : Integer) ;",
                unadmitted(8_usize, 21_usize, FormName::ANNOTATION, FragmentSort::Value),
            ),
            (
                "def a = \"a${b}\" ;",
                unadmitted(
                    8_usize,
                    15_usize,
                    FormName::INTERPOLATION,
                    FragmentSort::Value,
                ),
            ),
        ];
        for (source, expected) in rows {
            let refused = refusal(SourceText::from(source));
            assert_eq!(refused, expected, "`{source}` is outside the fragment");
            assert_eq!(
                refused.classify(),
                FailureClass::Unrepresentable,
                "`{source}` is unrepresentable, not malformed"
            );
        }
    }

    #[test]
    fn a_form_offered_the_wrong_operand_count_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let arity = |start: usize, end: usize, form: FormName, count: usize| {
            LoweringRefusal::OutOfFragment {
                span: at(start, end),
                form,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::Arity(OperandCount::from(count)),
            }
        };
        let rows = [
            (
                "def a = thunk { fn (x, y) { return x } } ;",
                arity(
                    16_usize,
                    38_usize,
                    FormName::from(NamedKind("lambda_expression")),
                    2_usize,
                ),
            ),
            (
                "def a = thunk {} ;",
                arity(14_usize, 16_usize, FormName::BLOCK, 0_usize),
            ),
            (
                "def a = thunk { run x <- pure 1; } ;",
                arity(14_usize, 34_usize, FormName::BLOCK, 0_usize),
            ),
        ];
        for (source, expected) in rows {
            assert_eq!(
                refusal(SourceText::from(source)),
                expected,
                "`{source}` offers its form the wrong number of operands"
            );
        }
    }

    #[test]
    fn a_malformed_integer_literal_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def a = 3x ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("number.expression"),
            Spelled("number"),
            at(8_usize, 10_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(11_usize, 12_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 12_usize), &[
            keyword, name, equals, body, close,
        ]);
        let tree = made.module(at(0_usize, 12_usize), &[declaration]);
        let refused = refusal_in(&pbg, &tree);

        assert_eq!(
            refused,
            LoweringRefusal::MalformedLiteral {
                span: at(8_usize, 10_usize),
                form: FormName::from(NamedKind("number")),
            },
            "a number whose text is not digits is refused"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a malformed literal is the author's mistake"
        );
    }

    #[test]
    fn a_malformed_text_literal_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def a = \"abc ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("string.expression"),
            Spelled("\""),
            at(8_usize, 12_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(13_usize, 14_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 14_usize), &[
            keyword, name, equals, body, close,
        ]);
        let tree = made.module(at(0_usize, 14_usize), &[declaration]);

        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedLiteral {
                span: at(8_usize, 12_usize),
                form: FormName::from(NamedKind("string")),
            },
            "a string missing its closing quote is refused"
        );
    }

    #[test]
    fn a_repaired_declaration_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(&pbg, SourceText::from("def x ;"));
        let refused = refusal_in(&pbg, &tree);

        assert_eq!(
            refused,
            LoweringRefusal::MalformedForm {
                span: at(5_usize, 5_usize),
                form: FormName::DECLARATION,
                fault: FormFault::Repaired(Repair::Grout(GroutShape::Postfix)),
            },
            "the grout the parser inserted is reported where it stands"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a repaired form is the author's mistake"
        );
    }

    #[test]
    fn a_missing_close_is_reported_at_the_innermost_form()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(
            &pbg,
            SourceText::from(
                "def rank() -> -F Integer {\n  case (Green : Color) {\n    Red => return 0,\n",
            ),
        );
        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(72_usize, 72_usize),
                form: FormName::CASE,
                fault: FormFault::Repaired(Repair::GhostClose(
                    gandr_surface_syntax::ClosingClass::Brace,
                )),
            },
            "the source ends with both the case and the definition open; the refusal names \
             the case at the end of its last arm, not the definition at its opening brace"
        );
    }

    #[test]
    fn a_juxtaposed_operand_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        let refused = refusal(SourceText::from("def a = thunk { return 1 2 } ;"));

        assert_eq!(
            refused,
            LoweringRefusal::MalformedForm {
                span: at(25_usize, 26_usize),
                form: FormName::from(NamedKind("thunk_expression")),
                fault: FormFault::ExtraOperand,
            },
            "a thunk's block holds one computation, and a second juxtaposed beside it is \
             refused where it stands"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a juxtaposition is the author's mistake"
        );
        assert_eq!(
            refusal(SourceText::from("def f(x: Integer Integer) { return x }")),
            LoweringRefusal::MalformedForm {
                span: at(17_usize, 24_usize),
                form: FormName::FUNCTION,
                fault: FormFault::ExtraOperand,
            },
            "a parameter's type is one form, and a second juxtaposed beside it is refused as \
             the function's"
        );
    }

    #[test]
    fn a_tile_out_of_place_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def x ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(6_usize, 7_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 7_usize), &[
            keyword, name, close,
        ]);
        let tree = made.module(at(0_usize, 7_usize), &[declaration]);

        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(6_usize, 7_usize),
                form: FormName::DECLARATION,
                fault: FormFault::MisplacedTile,
            },
            "a declaration with no tail closes where its tail should open"
        );
    }

    #[test]
    fn a_root_that_is_not_a_module_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def a = 3 ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("number.expression"),
            Spelled("number"),
            at(8_usize, 9_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(10_usize, 11_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 11_usize), &[
            keyword, name, equals, body, close,
        ]);
        let tree = made.finish(declaration);
        let mut arena = CoreArena::new();

        assert_eq!(
            lower_module(
                &pbg,
                &tree,
                &mut arena,
                LoweringBudget::DEFAULT,
                Recognition::default()
            ),
            Err(LoweringRefusal::OutOfFragment {
                span: at(0_usize, 11_usize),
                form: FormName::DECLARATION,
                sort: FragmentSort::Module,
                boundary: FragmentBoundary::WrongSort,
            }),
            "a tree rooted at a declaration is not a module"
        );
    }

    #[test]
    fn a_tree_of_another_grammar_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let foreign = GrammarFingerprint::from(0_u64);
        let mut made = Handmade::under(&pbg, SourceText::from("x"), foreign);
        let name = made.tile(
            Rule("identifier.expression"),
            Spelled("identifier"),
            at(0_usize, 1_usize),
        );
        let tree = made.module(at(0_usize, 1_usize), &[name]);
        let mut arena = CoreArena::new();
        let refused = lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap_err();

        assert_eq!(
            refused,
            LoweringRefusal::GrammarMismatch {
                tree: foreign,
                grammar: pbg.fingerprint(),
            },
            "a tree molded under another grammar is refused before any mold is read"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::EngineFault,
            "the caller paired the wrong tree and grammar"
        );
        assert_eq!(
            refused.span(),
            Maybe::Absent(refusal_span::Absent::Run),
            "the refusal is about the run, not a position in the source"
        );
    }

    #[test]
    fn a_mold_the_grammar_does_not_hold_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let foreign = MoldId::from(u32::MAX);
        let mut made = Handmade::new(&pbg, SourceText::from("x"));
        let stray = made.raw(NodeLabel::Tile(foreign), at(0_usize, 1_usize), &[]);
        let tree = made.module(at(0_usize, 1_usize), &[stray]);
        let mut arena = CoreArena::new();
        let refused = lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap_err();

        assert_eq!(
            refused,
            LoweringRefusal::UnknownMold {
                span: at(0_usize, 1_usize),
                mold: foreign,
            },
            "a mold outside the grammar's table is refused where it stands"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::EngineFault,
            "a foreign mold is the engine's fault, not the author's"
        );
    }

    #[test]
    fn an_unknown_attribute_is_refused_with_its_suggestion()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ check ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::UnknownAttribute {
                span: at(3_usize, 8_usize),
                name: SurfaceName::from("check"),
                suggestion: Maybe::Present(registered(SurfaceName::from("checks"))),
            },
            "a near miss is refused with the registered name it nearly spells"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an unknown attribute is the author's mistake"
        );
    }

    #[test]
    fn an_attribute_written_twice_for_one_name_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ checks ] @[ checks ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::DuplicateAttribute {
                span: at(15_usize, 21_usize),
                name: SurfaceName::from("checks"),
                first: at(3_usize, 9_usize),
            },
            "the second spelling is refused, naming the first"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a duplicate attribute is the author's mistake"
        );
    }

    #[test]
    fn a_schema_taking_a_payload_refuses_an_absent_one()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ owes ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::MissingPayload {
                span: at(3_usize, 7_usize),
                name: registered(SurfaceName::from("owes")),
                expected: schema_of(SurfaceName::from("owes")),
            },
            "an attribute whose schema takes a payload is refused without one"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a missing payload is the author's mistake"
        );
    }

    #[test]
    fn a_non_value_payload_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ owes(pure 1) ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::NonValuePayload {
                span: at(8_usize, 14_usize),
                name: registered(SurfaceName::from("owes")),
                form: FormName::from(NamedKind("pure_expression")),
            },
            "a computation cannot stand as a payload"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a non-value payload is the author's mistake"
        );
    }

    #[test]
    fn a_payload_of_the_wrong_form_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ owes(\"one\") ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::IllTypedPayload {
                span: at(8_usize, 13_usize),
                name: registered(SurfaceName::from("owes")),
                expected: schema_of(SurfaceName::from("owes")),
                written: payload_form(Former::Text),
            },
            "a payload whose form the schema does not admit is refused at the payload"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an ill-typed payload is the author's mistake"
        );
    }

    #[test]
    fn a_marker_given_a_payload_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("@[ checks(1) ] def a = 3 ;")),
            LoweringRefusal::IllTypedPayload {
                span: at(10_usize, 11_usize),
                name: registered(SurfaceName::from("checks")),
                expected: AttributeSchema::Marker,
                written: payload_form(Former::Number),
            },
            "a marker takes no payload, and one written is refused at the payload"
        );
    }

    #[test]
    fn an_attribute_is_filed_under_its_declaration_key()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("@[ owes(1) ] def a : Integer ;"),
            &mut arena,
        );
        let [ref declaration] = *module.declarations()
        else {
            panic!("one name is declared");
        };
        let Maybe::Present(key) = declaration.signature()
        else {
            panic!("the name has a signature");
        };
        let [ref entry] = *module.attributes().entries(key)
        else {
            panic!("one attribute is filed under the signature");
        };

        assert_eq!(
            (entry.name(), entry.span()),
            (registered(SurfaceName::from("owes")), at(3_usize, 10_usize)),
            "the entry names the attribute and where it was written"
        );
        let Maybe::Present(payload) = entry.payload()
        else {
            panic!("the entry carries its payload");
        };
        assert_eq!(
            arena.value(payload),
            Some(&Value::Literal(integer(SourceFragment::from("1")))),
            "the payload is the lowered value"
        );
    }

    #[test]
    fn documentation_is_filed_under_the_declaration_key()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "/// Squares, as [cube] cubes.\n/// Twice.\ndef square = 1 ;\n@[ doc(\"Cubes.\") ] def cube = 2 ;\n/// A colour.\ndata Color : Type { Red : Color; }\ndef plain = 3 ;",
            ),
            &mut arena,
        );
        let [ref square, ref cube, ref color, ref plain] = *module.declarations()
        else {
            panic!("four names are declared");
        };
        let key = |declaration: &crate::module::LoweredDeclaration<'_>| {
            let Maybe::Present(key) = declaration.definition()
            else {
                panic!("the name has a definition");
            };
            key
        };
        let text = |key| match module.documentation(key) {
            | Maybe::Present(found) => Some(String::from(found.text().as_ref())),
            | Maybe::Absent(_) => None,
        };

        assert_eq!(
            text(key(square)).as_deref(),
            Some("Squares, as [cube] cubes.\nTwice."),
            "a `///` run is one text, its link to a later declaration resolving"
        );
        assert!(!matches!(square.outcome(), DeclarationOutcome::Refused(_)));
        assert_eq!(text(key(cube)).as_deref(), Some("Cubes."));
        assert_eq!(text(key(color)).as_deref(), Some("A colour."));
        assert_eq!(text(key(plain)), None, "an undocumented form has none");
        let mut bare_arena = CoreArena::new();
        let bare = lowered(SourceText::from("def square = 1 ;"), &mut bare_arena);
        let [ref undocumented] = *bare.declarations()
        else {
            panic!("one name is declared");
        };
        assert_eq!(
            key(undocumented),
            key(square),
            "documentation leaves the declaration's identity alone"
        );
    }

    #[test]
    fn a_link_to_a_missing_name_is_refused_at_the_link()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("/// See [gone].\ndef a = 1 ;\n@[ doc(\"Or [`a`].\") ] def b = 2 ;"),
            &mut arena,
        );
        let [ref stale, ref linked] = *module.declarations()
        else {
            panic!("two names are declared");
        };

        assert_eq!(
            stale.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedDocLink {
                span: at(9_usize, 13_usize),
                name: SurfaceName::from("gone"),
            }),
            "the refusal stands at the link's name"
        );
        assert!(
            !matches!(linked.outcome(), DeclarationOutcome::Refused(_)),
            "a link to a declared name resolves"
        );
    }

    #[test]
    fn a_refused_declarations_attributes_are_filed_under_its_key()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                r#"@[ refuses("UnresolvedName") ] def a = b ; @[ owes(1) ] def c : Intgr ;"#,
            ),
            &mut arena,
        );
        let [ref defined, ref signed] = *module.declarations()
        else {
            panic!("two names are declared");
        };

        assert_eq!(
            (defined.outcome(), signed.outcome()),
            (
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName {
                    span: at(39_usize, 40_usize),
                    name: SurfaceName::from("b"),
                }),
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedTypeHead {
                    span: at(64_usize, 69_usize),
                    name: SurfaceName::from("Intgr"),
                    arity: HeadArity::Nullary,
                }),
            ),
            "both declarations are refused by their operands"
        );
        let (Maybe::Present(definition), Maybe::Present(signature)) =
            (defined.definition(), signed.signature())
        else {
            panic!("each refused name keeps the key of the form it wrote");
        };
        let [ref refuses] = *module.attributes().entries(definition)
        else {
            panic!("one attribute is filed under the refused definition");
        };
        let [ref owes] = *module.attributes().entries(signature)
        else {
            panic!("one attribute is filed under the refused signature");
        };
        assert_eq!(
            ((refuses.name(), refuses.span()), (owes.name(), owes.span())),
            (
                (
                    registered(SurfaceName::from("refuses")),
                    at(3_usize, 28_usize)
                ),
                (
                    registered(SurfaceName::from("owes")),
                    at(46_usize, 53_usize)
                ),
            ),
            "each entry names its attribute and where it was written"
        );
        let (Maybe::Present(named), Maybe::Present(counted)) = (refuses.payload(), owes.payload())
        else {
            panic!("each entry carries its payload");
        };
        assert_eq!(
            (arena.value(named), arena.value(counted)),
            (
                Some(&Value::Literal(text(SourceFragment::from(
                    "UnresolvedName"
                )))),
                Some(&Value::Literal(integer(SourceFragment::from("1")))),
            ),
            "a refused declaration's payloads are lowered all the same"
        );
    }

    #[test]
    fn the_attribute_diagnostics_fire_on_a_refused_declaration()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let owes = registered(SurfaceName::from("owes"));
        let rows = [
            (
                r#"@[ check ] def a = b ;"#,
                LoweringRefusal::UnknownAttribute {
                    span: at(3_usize, 8_usize),
                    name: SurfaceName::from("check"),
                    suggestion: Maybe::Present(registered(SurfaceName::from("checks"))),
                },
            ),
            (
                r#"@[ checks ] @[ checks ] def a = b ;"#,
                LoweringRefusal::DuplicateAttribute {
                    span: at(15_usize, 21_usize),
                    name: SurfaceName::from("checks"),
                    first: at(3_usize, 9_usize),
                },
            ),
            (
                r#"@[ owes ] def a = b ;"#,
                LoweringRefusal::MissingPayload {
                    span: at(3_usize, 7_usize),
                    name: owes,
                    expected: schema_of(SurfaceName::from("owes")),
                },
            ),
            (
                r#"@[ owes(pure 1) ] def a = b ;"#,
                LoweringRefusal::NonValuePayload {
                    span: at(8_usize, 14_usize),
                    name: owes,
                    form: FormName::from(NamedKind("pure_expression")),
                },
            ),
            (
                r#"@[ owes("one") ] def a = b ;"#,
                LoweringRefusal::IllTypedPayload {
                    span: at(8_usize, 13_usize),
                    name: owes,
                    expected: schema_of(SurfaceName::from("owes")),
                    written: payload_form(Former::Text),
                },
            ),
        ];

        for (source, expected) in rows {
            assert_eq!(
                refusal(SourceText::from(source)),
                expected,
                "the attribute's refusal sits before the body's in `{source}` and is the one kept"
            );
        }
    }

    #[test]
    fn every_minted_node_has_an_origin()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x : Integer ; def x = 3 ;"),
            &mut arena,
        );
        let [ref declaration] = *module.declarations()
        else {
            panic!("one name is declared");
        };
        let origins = module.origins();

        assert_eq!(
            origins
                .value_type(declared_of(declaration.outcome()))
                .map(|origin| origin.span()),
            Maybe::Present(at(8_usize, 15_usize)),
            "the declared type's origin is the type it was written as"
        );
        assert_eq!(
            origins
                .value(body_of(declaration.outcome()))
                .map(|origin| origin.span()),
            Maybe::Present(at(26_usize, 27_usize)),
            "the body's origin is the value it was written as"
        );
        assert_eq!(
            origins
                .declaration(declaration.origin())
                .map(|origin| origin.span()),
            Maybe::Present(at(0_usize, 17_usize)),
            "the declaration's origin is the form that introduced the name"
        );
        assert_eq!(
            origins.recorded_count(),
            OriginCount::from(2_usize),
            "exactly the two minted nodes have origins"
        );
    }

    #[test]
    fn a_refused_declaration_leaves_the_others_lowered()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def a = b ; def c = 3 ;"), &mut arena);
        let [
            DeclarationOutcome::Refused(refused),
            DeclarationOutcome::Bodied { body },
        ] = outcomes(&module)[..]
        else {
            panic!("the first declaration refuses and the second lowers");
        };

        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 9_usize),
                name: SurfaceName::from("b"),
            },
            "the first declaration carries its own refusal"
        );
        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the second declaration lowers regardless"
        );
    }

    #[test]
    fn a_module_past_the_allowance_is_refused()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def a = 3 ;"));
        let mut arena = CoreArena::new();
        let budget = LoweringBudget::from(1_usize);
        let refused =
            lower_module(&pbg, &tree, &mut arena, budget, Recognition::default()).unwrap_err();

        assert_eq!(
            refused,
            LoweringRefusal::BudgetExceeded { budget },
            "a module costing more than the allowance is refused"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::EngineFault,
            "running out of allowance is the engine's fault, not the author's"
        );
    }

    #[test]
    fn only_the_value_forms_can_stand_as_a_payload()
    {
        let values = [
            Former::Name,
            Former::Constructor,
            Former::Number,
            Former::Text,
            Former::Parenthesized,
            Former::Unit,
            Former::Thunk,
        ];
        for former in Former::ALL {
            assert_eq!(
                is_value_form(former).0,
                values.contains(&former),
                "{former:?} can stand as a value exactly when it produces one"
            );
        }
    }

    #[test]
    fn an_integer_literal_is_its_canonical_magnitude()
    {
        assert_eq!(
            parse_literal(Former::Number, SourceFragment::from("007")),
            Maybe::Present(integer(SourceFragment::from("7"))),
            "a padded spelling is the unpadded literal"
        );
        assert_eq!(
            parse_literal(Former::Number, SourceFragment::from("0")),
            Maybe::Present(integer(SourceFragment::from("0"))),
            "zero is a literal"
        );
    }

    #[test]
    fn a_text_literal_is_the_bytes_between_its_quotes()
    {
        let rows = [
            ("\"abc\"", "abc"),
            ("\"\"", ""),
            ("\"a\\tb\\\\c\\q\"", "a\tb\\cq"),
            ("\"a\\\"b\\'c\\0\\r\"", "a\"b'c\0\r"),
            ("\"a\\\nb\"", "ab"),
            ("\"a\\\r\nb\"", "ab"),
            ("\"ab\\\"", "ab"),
        ];
        for (spelled, content) in rows {
            assert_eq!(
                parse_literal(Former::Text, SourceFragment::from(spelled)),
                Maybe::Present(text(SourceFragment::from(content))),
                "`{spelled}` decodes to its content"
            );
        }
    }

    #[test]
    fn a_lexeme_of_the_wrong_shape_parses_to_nothing()
    {
        let rows = [
            (Former::Number, "", literal::Absent::Malformed),
            (Former::Number, "3x", literal::Absent::Malformed),
            (Former::Text, "\"abc", literal::Absent::Malformed),
            (Former::Text, "\"", literal::Absent::Malformed),
            (Former::Text, "abc", literal::Absent::Malformed),
            (Former::Name, "abc", literal::Absent::NotALiteral),
        ];
        for (former, spelled, reason) in rows {
            assert_eq!(
                parse_literal(former, SourceFragment::from(spelled)),
                Maybe::Absent(reason),
                "`{spelled}` is not a {former:?} literal"
            );
        }
    }

    #[test]
    fn the_last_step_of_an_allowance_is_spendable()
    {
        let mut fuel = Fuel::new(LoweringBudget::from(1_usize));

        assert_eq!(fuel.spend(), Ok(()), "an allowance of one admits one step");
    }

    #[test]
    fn a_step_past_the_allowance_is_refused()
    {
        let budget = LoweringBudget::from(1_usize);
        let mut fuel = Fuel::new(budget);
        let _first = fuel.spend();

        assert_eq!(
            fuel.spend(),
            Err(LoweringRefusal::BudgetExceeded { budget }),
            "the step past the allowance is refused, naming the allowance"
        );
    }

    /// Escape classes and continuations preserve their specified characters.
    #[test]
    fn escape_decoding_covers_continuations_unknowns_and_unicode()
    {
        for (written, expected) in [
            ("plain λ", "plain λ"),
            ("\\n\\t\\r\\0", "\n\t\r\0"),
            ("a\\\nb", "ab"),
            ("a\\\r\nb", "ab"),
            ("a\\\rb", "ab"),
            ("a\\q\\λ", "aqλ"),
            ("a\\", "a"),
            ("a\r\nb", "a\r\nb"),
            ("\\\\", "\\"),
            ("\\\r\\n", "\n"),
        ] {
            assert_eq!(
                super::decode_escapes(SourceFragment::from(written)),
                expected
            );
        }
    }

    /// Only complete unsigned decimal or exponent spellings are fractional.
    #[test]
    fn fractional_spellings_distinguish_unsupported_numbers_from_malformed_ones()
    {
        for (written, expected) in [
            ("0.0", true),
            ("01e+2", true),
            ("1e-2", true),
            ("1E0", true),
            ("1.2e3", true),
            ("", false),
            ("3", false),
            (".1", false),
            ("1.", false),
            ("1e", false),
            ("1e+", false),
            ("1e--2", false),
            ("1.2.3", false),
            ("1e2e3", false),
            ("-1.0", false),
            ("١.0", false),
            ("1.٢", false),
            ("1.0 ", false),
        ] {
            assert_eq!(super::fractional(SourceFragment::from(written)).0, expected);
        }
    }

    /// Range boundaries keep selected members and never substitute a prefix.
    #[test]
    fn recorded_ranges_keep_valid_members_and_reject_invalid_bounds()
    {
        let entries = [11_u8, 22_u8, 33_u8];
        for (start, end, expected) in [
            (0_usize, 0_usize, [].as_slice()),
            (0_usize, 3_usize, [11_u8, 22_u8, 33_u8].as_slice()),
            (1_usize, 3_usize, [22_u8, 33_u8].as_slice()),
            (2_usize, 1_usize, [].as_slice()),
            (0_usize, 4_usize, [].as_slice()),
            (4_usize, 4_usize, [].as_slice()),
        ] {
            assert_eq!(
                super::stretch(&entries, super::Stretch { start, end }),
                expected
            );
        }
    }

    /// Closing and exhaustion retain the first unexpected position.
    #[test]
    fn closing_and_exhaustion_distinguish_tiles_operands_and_gaps()
    {
        let placed = |index: usize, start: usize, end: usize| super::Placed {
            node: super::NodeIndex::from(index),
            span: span(ByteOffset::from(start), ByteOffset::from(end)),
        };
        let close = placed(1_usize, 2_usize, 3_usize);
        let operand = placed(2_usize, 5_usize, 6_usize);
        let site = super::Site {
            at: placed(0_usize, 0_usize, 8_usize),
            name: FormName::FUNCTION,
            reading: super::Reading::Function,
        };
        let pieces = [
            super::Piece::Tile {
                label: super::TileName::PAREN_CLOSE,
                at: close,
            },
            super::Piece::Operand(operand),
        ];
        let mut cursor = super::Cursor::new(&pieces, site.at.span);
        let misplaced = LoweringRefusal::MalformedForm {
            span: close.span,
            form: FormName::FUNCTION,
            fault: FormFault::MisplacedTile,
        };
        assert_eq!(super::exhausted(site, &cursor), Err(misplaced));
        assert_eq!(
            super::closed(site, &mut cursor, super::TileName::BRACE_CLOSE),
            Err(misplaced)
        );
        assert_eq!(cursor.peek(), Maybe::Present(pieces[0_usize]));
        assert_eq!(
            super::closed(site, &mut cursor, super::TileName::PAREN_CLOSE),
            Ok(())
        );
        assert_eq!(
            super::exhausted(site, &cursor),
            Err(LoweringRefusal::MalformedForm {
                span: operand.span,
                form: FormName::FUNCTION,
                fault: FormFault::ExtraOperand,
            })
        );
        assert_eq!(
            cursor.read(),
            Maybe::Present(super::Piece::Operand(operand))
        );
        assert_eq!(super::exhausted(site, &cursor), Ok(()));
        assert_eq!(
            super::closed(site, &mut cursor, super::TileName::PAREN_CLOSE),
            Err(LoweringRefusal::MalformedForm {
                span: span(ByteOffset::from(6_usize), ByteOffset::from(6_usize)),
                form: FormName::FUNCTION,
                fault: FormFault::MisplacedTile,
            })
        );
    }

    /// Parameter arities consume the header but preserve the following body.
    #[test]
    fn parameter_headers_preserve_the_body_and_locate_refusals()
    {
        let placed = |index: usize, start: usize, end: usize| super::Placed {
            node: super::NodeIndex::from(index),
            span: span(ByteOffset::from(start), ByteOffset::from(end)),
        };
        let lead = super::Piece::Tile {
            label: super::TileName::FN,
            at: placed(1_usize, 0_usize, 2_usize),
        };
        let open = super::Piece::Tile {
            label: super::TileName::PAREN_OPEN,
            at: placed(2_usize, 3_usize, 4_usize),
        };
        let first = placed(3_usize, 4_usize, 5_usize);
        let identifier = super::Piece::Tile {
            label: super::TileName::IDENTIFIER,
            at: first,
        };
        let comma = super::Piece::Tile {
            label: super::TileName::COMMA,
            at: placed(4_usize, 5_usize, 6_usize),
        };
        let second = super::Piece::Tile {
            label: super::TileName::IDENTIFIER,
            at: placed(5_usize, 6_usize, 7_usize),
        };
        let close = super::Piece::Tile {
            label: super::TileName::PAREN_CLOSE,
            at: placed(6_usize, 7_usize, 8_usize),
        };
        let body = super::Piece::Operand(placed(7_usize, 9_usize, 12_usize));
        let colon = super::Piece::Tile {
            label: super::TileName::COLON,
            at: placed(4_usize, 5_usize, 6_usize),
        };
        let form = FormName::from(NamedKind("lambda_expression"));
        let site = super::Site {
            at: placed(0_usize, 0_usize, 12_usize),
            name: form,
            reading: super::Reading::Computation(super::Frame::Outermost),
        };
        for (pieces, expected, next) in [
            (
                [lead, open, identifier, close, body].as_slice(),
                Ok(first),
                body,
            ),
            (
                [lead, open, close, body].as_slice(),
                Err(LoweringRefusal::OutOfFragment {
                    span: site.at.span,
                    form,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::Arity(OperandCount::from(0_usize)),
                }),
                body,
            ),
            (
                [lead, open, identifier, comma, second, close, body].as_slice(),
                Err(LoweringRefusal::OutOfFragment {
                    span: site.at.span,
                    form,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::Arity(OperandCount::from(2_usize)),
                }),
                body,
            ),
            (
                [lead, open, identifier, colon, body].as_slice(),
                Err(LoweringRefusal::OutOfFragment {
                    span: site.at.span,
                    form: FormName::PARAMETER,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::Unadmitted,
                }),
                colon,
            ),
            (
                [lead, identifier, close, body].as_slice(),
                Err(LoweringRefusal::MalformedForm {
                    span: first.span,
                    form,
                    fault: FormFault::MisplacedTile,
                }),
                identifier,
            ),
        ] {
            let mut cursor = super::Cursor::new(pieces, site.at.span);
            let _lead = cursor.tile(super::TileName::FN);
            assert_eq!(super::parameter(site, &mut cursor), expected);
            assert_eq!(cursor.peek(), Maybe::Present(next));
        }
    }

    /// Argument failures retain appended operands and identify the first fault.
    #[test]
    fn argument_lists_preserve_prefixes_and_locate_the_first_fault()
    {
        let placed = |index: usize, start: usize, end: usize| super::Placed {
            node: super::NodeIndex::from(index),
            span: span(ByteOffset::from(start), ByteOffset::from(end)),
        };
        let open = super::Piece::Tile {
            label: super::TileName::PAREN_OPEN,
            at: placed(1_usize, 1_usize, 2_usize),
        };
        let first = placed(2_usize, 2_usize, 3_usize);
        let second = placed(4_usize, 4_usize, 5_usize);
        let comma = super::Piece::Tile {
            label: super::TileName::COMMA,
            at: placed(3_usize, 3_usize, 4_usize),
        };
        let close = super::Piece::Tile {
            label: super::TileName::PAREN_CLOSE,
            at: placed(5_usize, 5_usize, 6_usize),
        };
        let stray = placed(6_usize, 7_usize, 8_usize);
        let site = super::Site {
            at: placed(0_usize, 0_usize, 8_usize),
            name: FormName::FUNCTION,
            reading: super::Reading::Function,
        };
        let previous = super::NodeIndex::from(99_usize);
        let trailing = super::Piece::Tile {
            label: super::TileName::COMMA,
            at: stray,
        };
        for (pieces, expected, appended) in [
            ([open, close].as_slice(), Ok(()), [].as_slice()),
            (
                [
                    open,
                    super::Piece::Operand(first),
                    comma,
                    super::Piece::Operand(second),
                    close,
                ]
                .as_slice(),
                Ok(()),
                [first.node, second.node].as_slice(),
            ),
            (
                [open, super::Piece::Operand(first), comma, close].as_slice(),
                Ok(()),
                [first.node].as_slice(),
            ),
            (
                [
                    open,
                    super::Piece::Operand(first),
                    close,
                    super::Piece::Operand(stray),
                ]
                .as_slice(),
                Err(LoweringRefusal::MalformedForm {
                    span: stray.span,
                    form: FormName::FUNCTION,
                    fault: FormFault::ExtraOperand,
                }),
                [first.node].as_slice(),
            ),
            (
                [open, super::Piece::Operand(first), close, trailing].as_slice(),
                Err(LoweringRefusal::MalformedForm {
                    span: stray.span,
                    form: FormName::FUNCTION,
                    fault: FormFault::MisplacedTile,
                }),
                [first.node].as_slice(),
            ),
        ] {
            let mut cursor = super::Cursor::new(pieces, site.at.span);
            let mut written = vec![previous];
            assert_eq!(super::arguments(site, &mut cursor, &mut written), expected);
            assert_eq!(written.first(), Some(&previous));
            assert!(written.iter().skip(1_usize).eq(appended.iter()));
        }
    }
}
