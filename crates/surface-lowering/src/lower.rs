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
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::ops::ControlFlow;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
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
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
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
                    | Former::Number
                    | Former::Text
                    | Former::Parenthesized
                    | Former::Thunk
                    | Former::Lambda
                    | Former::Return
                    | Former::Force
                    | Former::Call
                    | Former::Projection,
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
        | Former::Number
        | Former::Text
        | Former::Parenthesized
        | Former::Thunk
        | Former::Lambda
        | Former::Return
        | Former::Force
        | Former::Call
        | Former::Projection => Family::Term,
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

/// One `run x <- c ;` statement of a block.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The run position supplies the bind’s origin while the bound
///   position supplies its computation.
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
/// - witness: `lower::tests::every_minted_node_has_an_origin`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Statement
{
    /// The `run` tile, the origin of the bind.
    run: NodeIndex,
    /// The computation whose returned value the statement binds.
    bound: NodeIndex,
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
///   separately so an incomplete signature does not discard the body.
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
    /// A variable at this index.
    Variable(DeBruijnIndex),
    /// A constant at this admission position.
    Constant(ConstantIndex),
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
    /// The eager product of two value types.
    Product(NodeIndex, NodeIndex),
    /// The values in the lowerer's operand store, paired to the right.
    Pair(Stretch),
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
    /// An application of its head to its arguments, left to right, in the
    /// lowerer's operand store.
    Application(NodeIndex, Stretch),
    /// A function tail's declared type and body.
    Function(Function),
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
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
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
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
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
}

/// Where the mint sweep writes: the arena and the origin table.
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
struct Sink<'run>
{
    /// The arena the core nodes are minted into.
    arena: &'run mut CoreArena,
    /// The table every minted node's origin is recorded in.
    origins: &'run mut OriginTable,
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
/// - witness: `lower::tests::the_empty_parentheses_lower_to_the_unit_value`
/// - witness: `lower::tests::an_identifier_spelled_unit_is_an_ordinary_name`
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
/// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_digest`
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
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
                                    && tree
                                        .node(origin.node())
                                        .is_some_and(|node| node.digest() == origin.digest())
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
    lowerer.classify()?;
    lowerer.propagate_manifests();
    let mut origins = OriginTable::new();
    lowerer.mint(&mut Sink {
        arena,
        origins: &mut origins,
    })?;
    let mut attributes = AttributeTable::new();
    lowerer.attribute(&mut attributes)?;
    let declarations = lowerer.assemble(&mut origins);
    let structures = lowerer.structures();
    let Lowerer {
        collected,
        recognition,
        ..
    } = lowerer;

    Ok(LoweredModule::new(
        declarations,
        structures,
        attributes,
        origins,
        collected.imports,
        recognition,
    ))
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
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
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
    ///   module, each path asserted as the exact resolution.
    /// - witness: `recognition::recognition::a_shadowed_builtin_is_reported_as_a_warning`
    /// - witness: `recognition::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
    /// - witness: `recognition::recognition::user_shadowing_is_the_only_observable_delta`
    /// - witness: `modules::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `modules::modules::a_hidden_member_is_admitted_and_absent_from_the_namespace`
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
    ///   own paths.
    /// - witness: `modules::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `modules::modules::a_hidden_member_is_admitted_and_absent_from_the_namespace`
    #[spec(
        captures: before = (self.exported.len(), self.collected.slots.len()),
        ensures: |_| {
            self.exported.len() >= before.0
                && self.collected.slots.len() >= before.1
                && self.collected.slots.len() <= before.1.saturating_add(1)
                && self.exported.values().all(|slot| {
                    self.collected
                        .slots
                        .get(usize::from(*slot))
                        .is_some_and(|entry| entry.role == Role::Declared)
                })
                && self.collected.slots.iter().skip(before.1).all(|slot| {
                    slot.role == Role::Held
                        && matches!(
                            slot.refusal,
                            Maybe::Present((_, LoweringRefusal::ShadowedBuiltin { .. }))
                        )
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
    ///   manifest type component's type as a value type, and an attribute's
    ///   payload as a value when its form can stand as one; a witness's body, a
    ///   member rather than a form, is read nowhere. Every other node stays
    ///   unread. Every written payload is marked as one, whatever its form, and
    ///   every signature type's root with the manifest components it sees.
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
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
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
                    | Operand::Member(_) => {},
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
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_digest`
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
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
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
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
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
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
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
    /// - ensures: a repair refuses the form; a former of the wrong family for
    ///   the position refuses as the wrong sort, except a type standing where a
    ///   value is read, which is quoted; every other former is handed to its
    ///   own reader, a declaration form to the function reader, the one reading
    ///   of the family that seeds one.
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
    #[spec(
        ensures: |ret| {
            if let Maybe::Present(repaired) = pieces.repair {
                ret == Err(site.fault(repaired.span, FormFault::Repaired(repaired.repair)))
            }
            else if family_of(former) != site.reading.family()
                && !(family_of(former) == Family::Type && matches!(site.reading, Reading::Value(_)))
            {
                ret == Err(site.out(FragmentBoundary::WrongSort))
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
            return Err(site.fault(repaired.span, FormFault::Repaired(repaired.repair)));
        }
        let family = family_of(former);
        let quoted = family == Family::Type && matches!(site.reading, Reading::Value(_));
        if family != site.reading.family() && !quoted {
            return Err(site.out(FragmentBoundary::WrongSort));
        }
        let cursor = Cursor::new(&pieces.pieces, site.at.span);
        match former {
            | Former::Name => self.name(site),
            | Former::Constructor => self.constructor(site),
            | Former::Number => self.number(site),
            | Former::Text => self.text(site, pieces),
            | Former::Parenthesized => self.parenthesized(site, cursor),
            | Former::Thunk => self.thunk(site, cursor),
            | Former::Lambda => self.lambda(site, cursor),
            | Former::Return => self.keyed(site, cursor, TileName::RET),
            | Former::Force => self.keyed(site, cursor, TileName::FORCE),
            | Former::Call => self.call(site, cursor),
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
            | Former::Declaration | Former::Module => self.function(site, cursor),
            | Former::AttributeBlock | Former::Import | Former::Unadmitted => {
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
    /// the one `site` belongs to, searched from that declaration's own module
    /// outward to the top level.
    ///
    /// # Specification
    /// - requires: `site` is the name's own node.
    /// - ensures: the binder with its index and its written type; else the
    ///   first module, innermost first, whose body declares the name: its
    ///   member when that member's admission position is strictly earlier, and
    ///   the forward-member refusal when it is not; else a top-level
    ///   declaration strictly earlier, with its admission position and its
    ///   signature's written type; the unresolved absence when nothing answers.
    /// - provides: the one resolution term names, capitalised names and type
    ///   heads share.
    /// - fails: [`LoweringRefusal::ForwardMemberReference`] for a member of an
    ///   enclosing module declared at or after the referring declaration;
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
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
    /// - witness: `lower::tests::an_earlier_declaration_resolves_as_a_constant`
    #[spec(
        captures: before = self.fuel.remaining,
        ensures: |ret| {
            self.fuel.remaining <= before
                && match ret {
                    | Ok(Maybe::Present(Resolved::Declaration { constant, declared })) => {
                        matches!(self.collected.owner_of(site.at.node), Maybe::Present(own) if usize::from(constant) < usize::from(own) && self.collected.slots.get(usize::from(constant)).is_some_and(|entry| entry.name == name && entry.constant == constant && declared == match entry.signature { Maybe::Present(Half { operand: Operand::Written(written), .. }) => Maybe::Present(written.node), _ => Maybe::Absent(binder_type::Absent::Untyped) }))
                    },
                    | Err(LoweringRefusal::ForwardMemberReference {
                        span,
                        name: refused,
                        ..
                    }) => span == site.at.span && refused == name,
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
                if target < own {
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
                    Some(&(Plan::Variable(_) | Plan::Constant(_)))
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
            | Maybe::Absent(_) => Err(LoweringRefusal::UnresolvedName {
                span: site.at.span,
                name,
            }),
        }
    }

    /// Classify a capitalised name in term position.
    ///
    /// # Specification
    /// - requires: `site` is a constructor in term position.
    /// - ensures: a name a binder or an earlier declaration answers stands as
    ///   the value it resolved to; otherwise a type atom, or `Type` for the
    ///   value universe at the fuss-free level, stands as a type, which a value
    ///   position quotes.
    /// - provides: the term-position spelling of a type, and of a declaration
    ///   named with a capital.
    /// - fails: yields the wrong-sort refusal for a resolved name or a type
    ///   where its position reads neither; a name nothing answers is a
    ///   constructor, which the fragment does not admit.
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
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(
                        &(Plan::Variable(_)
                            | Plan::Constant(_)
                            | Plan::Atom(_)
                            | Plan::Universe(_))
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
        if let Maybe::Present(resolved) = self.resolve_name(site, site.reading.frame(), name)? {
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

    /// Classify a parenthesised expression: the unit, a grouping, a pair or
    /// an annotation.
    ///
    /// # Specification
    /// - requires: `site` is a parenthesised expression in term position.
    /// - ensures: `()` standing as a value is planned as the unit; `(e)` reads
    ///   its operand at its own reading and adopts it; a comma list is read as
    ///   a pair.
    /// - provides: the reading of every form the grammar folds into
    ///   parentheses.
    /// - fails: yields the pair's own refusal, the unadmitted refusal for an
    ///   annotation, the wrong-sort refusal for a unit outside value position,
    ///   and the extra-operand refusal for a juxtaposition.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — grouping preserves its operand while a
    ///   comma-separated tuple plans an eager pair rather than treating the
    ///   commas as grouping.
    /// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Unit | Plan::Transparent(_) | Plan::Pair(_)))
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
            return Err(site.folded(FormName::ANNOTATION, FragmentBoundary::Unadmitted));
        }
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        if let Run::Empty(_) = run {
            let unit = Site {
                name: FormName::UNIT,
                ..site
            };
            let _frame = self.require(unit, Produced::Value)?;
            self.plan(site, Plan::Unit);
            return Ok(());
        }
        let inner = site.one(run)?;
        self.read(inner.node, site.reading);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// Classify a pair, `(v1, …, vn)`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the `(` of a parenthesised expression
    ///   whose first member a comma follows.
    /// - ensures: the pair stands as a value, reads every member as a value
    ///   under its own frame, and is planned over them, paired to the right as
    ///   the product associates.
    /// - provides: the introduction of the eager product.
    /// - fails: yields the wrong-sort refusal where no value is read, and the
    ///   list's refusal for a member out of shape, both naming the tuple.
    /// - panics: none.
    ///
    /// # Errors
    /// The pair's refusal.
    ///
    /// # Termination
    /// The member loop runs once per entry of the finite member stretch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pair of two, a tuple of four, and a pair where a
    ///   computation is read, each asserted as the exact core node read back
    ///   out of the arena or the exact refusal.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Pair(members)) if members.end.saturating_sub(members.start) >= 2_usize
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

        self.plan(site, Plan::Pair(members));

        Ok(())
    }

    /// Classify a thunk, `thunk { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a thunk in term position.
    /// - ensures: a thunk standing as a value reads its block in its own frame
    ///   and is planned over it.
    /// - provides: the value former that suspends a computation.
    /// - fails: yields the wrong-sort refusal outside value position, the
    ///   unadmitted refusal for a grade, and the block's own refusal.
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

        self.plan(site, Plan::Thunk(body));

        Ok(())
    }

    /// Classify a lambda, `fn (x) { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a lambda in term position.
    /// - ensures: a lambda standing as a computation binds its one parameter in
    ///   a frame extending its own, reads its block under that frame, and is
    ///   planned over it.
    /// - provides: the binder of the fragment.
    /// - fails: yields the wrong-sort refusal outside computation position; the
    ///   unadmitted refusal for a type abstraction or a typed parameter; the
    ///   arity refusal for any parameter count but one; the block's own
    ///   refusal.
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

        self.plan(site, Plan::Lambda(body));

        Ok(())
    }

    /// Classify a function tail, `def f(x: A, …) -> B { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a declaration form read as a function, whose tail
    ///   opens on `(`.
    /// - ensures: each parameter binds in a frame extending the one before it,
    ///   left to right, with its type, when written, read as a value type under
    ///   the frame before it and recorded on the binder; the result, when
    ///   written, is read at the result position under the last parameter's
    ///   frame, as the block is; the form is planned as the function's declared
    ///   type and body.
    /// - provides: the function tail, lowered once at the declaration form for
    ///   both halves it writes.
    /// - fails: yields the unadmitted refusal for a parameter spelled as a type
    ///   or a type variable; a fault naming the function form for a parameter
    ///   list, a type or a result out of shape; and the block's own refusal.
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
        let _name = cursor.tile(TileName::IDENTIFIER);
        closed(function, &mut cursor, TileName::PAREN_OPEN)?;
        let start = self.parameters.len();
        let mut frame = Frame::Outermost;
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

        self.plan(
            site,
            Plan::Function(Function {
                parameters,
                result,
                block,
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
    ///   extending that one; the last computation reads under the frame every
    ///   statement extended; the statements and the last computation are
    ///   returned, with the cursor past the closing `}` and nothing after it.
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
                        return Err(LoweringRefusal::OutOfFragment {
                            span: first.join(semicolon.span),
                            form: FormName::EXPRESSION_STATEMENT,
                            sort: FragmentSort::Computation,
                            boundary: FragmentBoundary::Unadmitted,
                        });
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

    /// Read one `run x <- c ;` statement, its `run` tile already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's `run` tile `run`;
    ///   `frame` is the frame the statement reads under.
    /// - ensures: the statement's computation is read under `frame` and the
    ///   statement recorded with its `run` tile; the frame binding the
    ///   statement's name over `frame`, which the rest of the block reads
    ///   under, is returned.
    /// - provides: the one statement the fragment reads.
    /// - fails: yields the unadmitted refusal for an annotated binder and for a
    ///   binder pattern other than a name, and a fault naming the bind
    ///   statement for a hole or a tile out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each run statement reads its bound computation in the
    ///   previous frame and introduces its name only for subsequent
    ///   computations.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    #[spec(
        captures: before = self.statements.len(),
        ensures: |ret| match ret {
            | Ok(Frame::Inner(_)) => {
                self.statements.len() == before.saturating_add(1_usize)
                    && self.statements.last().is_some_and(|last| {
                        last.run == run.node
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
        let name = self.binder_name(statement, binder)?;
        self.note_binder(binder, name)?;
        self.read(bound.node, Reading::Computation(frame));
        self.statements.push(Statement {
            run: run.node,
            bound: bound.node,
        });

        Ok(Frame::Inner(self.scope.extend(frame, name)))
    }

    /// The name a `run` statement's pattern binds.
    ///
    /// # Specification
    /// - requires: `binder` is the pattern operand of the statement at
    ///   `statement`.
    /// - ensures: the name an identifier pattern spells.
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
    /// - hypothesis: L3 — ordinary run binders introduce the spelled name;
    ///   wildcard and annotated patterns are refused rather than becoming
    ///   ordinary names.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |name| {
                *name == self.name_at(binder)
                    && self.tree.node(binder.node).is_some_and(|node| {
                        matches!(
                            shape_of(self.pbg, node),
                            Ok(Shape::Form {
                                former: Former::Name,
                                ..
                            })
                        )
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

    /// Classify a keyword form of one value operand: `ret v` or `force v`.
    ///
    /// # Specification
    /// - requires: `site` is a returner or a force in term position, whose
    ///   keyword tile is `keyword`.
    /// - ensures: the form standing as a computation reads its one operand as a
    ///   value in its own frame and is planned over it.
    /// - provides: the two computation formers over a value.
    /// - fails: yields the wrong-sort refusal outside computation position, and
    ///   the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — force and return plan their own former over a value
    ///   operand, and an author-written force is not marked as inserted.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
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

    /// Classify an application, `c(v, …)`.
    ///
    /// # Specification
    /// - requires: `site` is a call in term position.
    /// - ensures: a call standing as a computation reads its head at the head
    ///   position and each argument as a value, all in its own frame, and is
    ///   planned as the head applied to the arguments left to right; a call of
    ///   no arguments is its head.
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
    ///   arena.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    #[spec(
        captures: start = self.operands.len(),
        ensures: |ret| {
            ret.is_err()
                || match self.plans.get(usize::from(site.at.node)) {
                    | Some(&Plan::Application(head, arguments)) => {
                        arguments.start == start
                            && arguments.end == self.operands.len()
                            && self.reading(head) == Reading::Head(site.reading.frame())
                            && self.operands.iter().skip(start).all(|&argument| {
                                self.reading(argument) == Reading::Value(site.reading.frame())
                            })
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
        let frame = self.require(site, Produced::Computation)?;
        let head = site.one(cursor.operands())?;
        let start = self.operands.len();
        arguments(site, &mut cursor, &mut self.operands)?;
        let written = Stretch {
            start,
            end: self.operands.len(),
        };
        self.read(head.node, Reading::Head(frame));
        for position in written.start .. written.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(site, Plan::Application(head.node, written));

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
                    Some(&Plan::Constant(_))
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
                        return Err(site.fault(repaired.span, FormFault::Repaired(repaired.repair)));
                    }
                    let (inner, selected) = Self::link(site, &chain.pieces, target.span)?;
                    links.push((inner, selected));
                    target = inner;
                },
                | Shape::Form {
                    former: Former::Constructor,
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
                                | Plan::StaticApplication(_, _))
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
                    Some(&(Plan::Former(..) | Plan::Decode(..) | Plan::StaticApplication(..)))
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
    /// - ensures: where a value is read, the application stands as itself;
    ///   where a type is read, it stands as the decode of the application, in
    ///   the universe the code's written type reaches after one arrow per
    ///   argument, and else in the universe the position reads — the
    ///   computation types where only a computation type is read, the value
    ///   types everywhere else, at the fuss-free level. Every argument is read
    ///   as a value under the site's frame, and a binder so named is recorded
    ///   as mentioned.
    /// - provides: the one reading of a type operator's use, bare or applied,
    ///   as a value or as the type it denotes.
    /// - fails: yields the wrong-sort refusal where the position reads neither
    ///   a value nor the sort of the decode's universe; propagates
    ///   [`LoweringRefusal::BudgetExceeded`] from the walk of the code's type.
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

    /// Classify an eager product type, `A * B`.
    ///
    /// # Specification
    /// - requires: `site` is a product in type position, or in value position
    ///   where a type is quoted.
    /// - ensures: the product stands as a value type, reads both operands as
    ///   value types under its own frame, and is planned over them.
    /// - provides: the eager product of the fragment.
    /// - fails: yields the wrong-sort refusal where no value type is read, and
    ///   either hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The product's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a product of atoms, a chain of three, and a product
    ///   where a computation type is read, each asserted as the exact core node
    ///   read back out of the arena or the exact refusal.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Product(..))
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
        let first = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::STAR)?;
        let second = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(first.node, Reading::ValueType(frame));
        self.read(second.node, Reading::ValueType(frame));

        self.plan(site, Plan::Product(first.node, second.node));

        Ok(())
    }

    /// Classify a value function space, `A => B` or `(A1, …, An) => B`.
    ///
    /// # Specification
    /// - requires: `site` is a value function space in type position, or in
    ///   value position where a type is quoted.
    /// - ensures: the alias stands as a value type; its domains — each member
    ///   of a parenthesised list written before `=>`, else the one operand
    ///   there — and its codomain are each read as value types under its own
    ///   frame, and it is planned as the thunked arrow over them.
    /// - provides: the value function space, the alias of `+U (A1 -> … -> An ->
    ///   -F B)`.
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
    /// - hypothesis: L3 — one domain, a list of two, and an alias nested to the
    ///   right, each asserted as the same core node the thunked arrow it stands
    ///   for lowers to.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::ValueFunction(domains, _)) if domains.start < domains.end
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
    /// - ensures: each member of an unrepaired parenthesised list of more than
    ///   one, left to right; else `domain` itself, whose own reading groups,
    ///   reports a repair or refuses an empty list.
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
    /// - hypothesis: L3 — one domain and a list of two, each asserted through
    ///   the alias it lowers.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        captures: before = self.operands.len(),
        ensures: |ret| ret.is_err() || self.operands.len() > before,
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
            if commas && let Maybe::Absent(_) = scratch.repair {
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
    /// - fails: yields the hole's own refusal, and a misplaced-tile fault at
    ///   the first comma of a list, which only a value function space's domain
    ///   reads.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — parenthesized type operands keep the surrounding
    ///   reading and lower to the wrapped type rather than introducing a core
    ///   constructor.
    /// - witness: `lower::tests::an_arrow_lowers_under_a_thunk_type`
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
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
        let inner = site.one(cursor.operands())?;
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
    ///   wherever it sits. Every other planned node is then minted, with its
    ///   children already minted because the level-order layout puts them at
    ///   strictly higher positions; every minted node gets an origin naming the
    ///   syntax node that produced it, terms and types alike, while an adopted
    ///   child keeps its own. A node whose position bridges its sort has the
    ///   bridge minted over its own core node, with the same syntax node's
    ///   origin marked as inserted. A node under a declaration that refused is
    ///   not minted, and neither is any node above it, unless it lies inside an
    ///   attribute payload: the side table files a payload whatever its
    ///   declaration's outcome, so an expectation about a refused declaration
    ///   stays readable. Last, the body of every witness whose member and own
    ///   type are unrefused is minted as that member's constant, its origin the
    ///   form that stated the second type.
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
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
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
        if let Some(held) = self.lowered.get_mut(usize::from(position)) {
            *held = bridged;
        }
    }

    /// The origin of a core node the syntax node at `position` wrote.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live syntax node yields its own position, digest and span
    ///   as written provenance; a missing node is unminted.
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
                    Maybe::Present(Origin::new(position, node.digest(), node.span()))
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
                Maybe::Present(Origin::new(position, node.digest(), node.span()))
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
                | Plan::Constant(_)
                | Plan::Unit
                | Plan::Literal(_)
                | Plan::StaticApplication(..)
                | Plan::Pair(_)
                | Plan::StaticLambda(_)
                | Plan::Thunk(_) => Some(Produced::Value),
                | Plan::Return(_) | Plan::Force(_) | Plan::Lambda(_) | Plan::Application(..) => {
                    Some(Produced::Computation)
                },
                | Plan::Atom(_)
                | Plan::Universe(_)
                | Plan::ValueFunction(..)
                | Plan::StaticPi(..)
                | Plan::Product(..)
                | Plan::Former(TypeFormer::Thunk, _) => Some(Produced::ValueType),
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
            | Plan::Pair(members) => self.mint_pair(members, sink, origin),
            | Plan::ValueFunction(domains, codomain) => {
                self.mint_value_function(domains, codomain, sink, origin)
            },
            | Plan::Transparent(child) => self.lowered_at(child),
            | Plan::Former(former, argument) => self.mint_former(former, argument, sink, origin),
            | Plan::Application(head, arguments) => {
                self.mint_application(head, arguments, sink, origin)
            },
            | Plan::Function(function) => self.mint_function(&function, sink, origin),
            | Plan::Arrow(..)
            | Plan::StaticPi(..)
            | Plan::Product(..)
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

    /// Carry out a pair's plan: its members, paired to the right.
    ///
    /// # Specification
    /// - requires: every member is already minted or absent.
    /// - ensures: `(v1, …, vn)` mints as `pair(v1, … pair(vn-1, vn))`, every
    ///   pair with the written origin, so a tuple inhabits the product chain
    ///   `*` builds; nothing is minted when a member did not lower or fewer
    ///   than two were written.
    /// - provides: the introduction of the eager product.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Both loops run once per entry of the finite stretch `members`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pair of two and a tuple of four, each asserted as
    ///   the exact core value read back out of the arena.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Value(id)) => {
                matches!(
                    sink.arena.value(id),
                    Some(&gandr_core_term::Value::Pair(..))
                )
            },
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — eager pairs associate to the right and preserve the
    ///   order of their member values; their new pair nodes record the pair’s
    ///   origin.
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
                | None if written.len() < 2 => ret == Maybe::Absent(lowered::Absent::Unminted),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::Value(id)) if sink.origins.value(id) == Maybe::Present(origin))
                },
            }
        },
    )]
    fn mint_pair(
        &self,
        members: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, members);
        for &member in written {
            if let Maybe::Absent(reason) = self.value_at(member) {
                return Maybe::Absent(reason);
            }
        }
        let Some((&last, before)) = written.split_last()
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        if before.is_empty() {
            return Maybe::Absent(lowered::Absent::Unminted);
        }
        let Maybe::Present(mut paired) = self.value_at(last)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        for &member in before.iter().rev() {
            let Maybe::Present(first) = self.value_at(member)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            paired = sink.arena.value_pair(first, paired);
            sink.origins.record_value(paired, origin);
        }

        Maybe::Present(Lowered::Value(paired))
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
                matches!(*plan, Plan::StaticPi(_, _) | Plan::Product(_, _))
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
            | Plan::Product(first, second) => self.value_type_at(first).and_then(|left| {
                self.value_type_at(second).map(|right| {
                    let id = sink.arena.value_type_product(left, right);
                    sink.origins.record_value_type(id, origin);
                    Lowered::ValueType(id)
                })
            }),
            | Plan::StaticLambda(body) => self.value_at(body).map(|under| {
                let id = sink.arena.value_static_lambda(under);
                sink.value(id, origin)
            }),
            | Plan::Thunk(body) => self.mint_block(body, sink).map(|suspended| {
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
            | Plan::Lambda(body) => self.mint_block(body, sink).map(|under| {
                let id = sink.arena.computation_lambda(under);
                sink.computation(id, origin)
            }),
            | Plan::Unplanned
            | Plan::Variable(_)
            | Plan::Constant(_)
            | Plan::Unit
            | Plan::Literal(_)
            | Plan::Atom(_)
            | Plan::Universe(_)
            | Plan::Decode(..)
            | Plan::StaticApplication(..)
            | Plan::Pair(_)
            | Plan::ValueFunction(..)
            | Plan::Former(..)
            | Plan::Transparent(_)
            | Plan::Application(..)
            | Plan::Function(_) => Maybe::Absent(lowered::Absent::Unminted),
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
                        self.origin_at(statement.run),
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
                            matches!(ret, Maybe::Present(id) if matches!((sink.origins.computation(id), self.origin_at(first.run)), (Maybe::Present(stored), Maybe::Present(expected)) if stored == expected))
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
            if let Maybe::Absent(reason) = self.origin_at(statement.run) {
                return Maybe::Absent(reason);
            }
        }
        for statement in statements.iter().rev() {
            let (Maybe::Present(bound), Maybe::Present(origin)) = (
                self.computation_at(statement.bound),
                self.origin_at(statement.run),
            )
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = sink.arena.computation_bind(bound, chain);
            sink.origins.record_computation(id, origin);
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
    ///   the thunk marked as inserted at the declaration form, and its declared
    ///   type as `+U (A1 -> … -> An -> C)`, one arrow per parameter with the
    ///   binder tile's origin and `+U` the declaration form's, an arrow
    ///   dependent where a later type names its parameter; a tail missing a
    ///   parameter or result type mints the body alone; nothing is minted when
    ///   the block did not lower.
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
        let mut body = match self.mint_block(function.block, sink) {
            | Maybe::Present(block) => block,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for parameter in parameters.iter().rev() {
            let Maybe::Present(binder) = self.origin_at(parameter.binder)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = sink.arena.computation_lambda(body);
            sink.origins.record_computation(id, binder);
            body = id;
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
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
    /// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
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
    ///   entries append under their declaration digest, and schema errors do
    ///   not prevent other declarations from lowering.
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_digest`
    /// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
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
                        table.file(self.digest_at(written.decorates), entry);
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
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_digest`
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

    /// The content identity of the node at `position`.
    ///
    /// # Specification
    /// - requires: positions are interpreted in this source tree.
    /// - ensures: a live node yields its digest; an absent node yields the
    ///   all-zero digest.
    /// - provides: declaration keys for attribute filing and origin records.
    /// - fails: the fallback does not distinguish absence from an equal digest.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — filed attributes use the decorated declaration
    ///   digest, including declarations already refused for an unrelated source
    ///   error.
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_digest`
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
    #[spec(
        ensures: |ret| {
            ret == self
                .tree
                .node(position)
                .map_or_else(|| NodeDigest::from([0_u8; 32_usize]), Node::digest)
        },
    )]
    fn digest_at(
        &self,
        position: NodeIndex,
    ) -> NodeDigest
    {
        self.tree
            .node(position)
            .map_or_else(|| NodeDigest::from([0_u8; 32_usize]), Node::digest)
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
                                    .map(|half| self.digest_at(half.declaration.node)),
                                slot.definition
                                    .map(|half| self.digest_at(half.declaration.node)),
                                outcome,
                                Maybe::Present(Origin::new(
                                    slot.introduced_by.node,
                                    self.digest_at(slot.introduced_by.node),
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
            let origin = origins.record_declaration(Origin::new(
                introduced.node,
                self.digest_at(introduced.node),
                introduced.span,
            ));
            declarations.push(LoweredDeclaration::from(DeclarationParts {
                name: slot.name,
                container: slot.container,
                role: slot.role,
                constant: slot.constant,
                span: introduced.span,
                origin,
                signature: slot
                    .signature
                    .map(|half| self.digest_at(half.declaration.node)),
                definition: slot
                    .definition
                    .map(|half| self.digest_at(half.declaration.node)),
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
    /// - ensures: a stored refusal takes precedence; otherwise the available
    ///   signature and body select Completed, Uncompleted or Bodied.
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
    #[spec(
        ensures: |ret| {
            if let Maybe::Present((_at, refusal)) = slot.refusal {
                ret == Maybe::Present(DeclarationOutcome::Refused(refusal))
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
                        | Operand::Member(_) => Maybe::Absent(lowered::Absent::Unminted),
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
                    | Maybe::Present(DeclarationOutcome::Refused(_)) => false,
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
                | Operand::Member(_) => Maybe::Absent(lowered::Absent::Unminted),
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
/// - hypothesis: L3 — valid entries are filed under the declaration digest,
///   while a refused declaration can still retain an independently valid
///   payload.
/// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_digest`
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
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
                | Insertion::Decode,
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
            | Lowered::ValueType(id) => {
                self.origins.value_type(id) == Maybe::Present(origin)
                    && self.arena.value_type(id)
                        == Some(&match atom {
                            | TypeAtom::Unit => ValueType::Unit,
                            | TypeAtom::Integer => ValueType::Base(BaseType::Integer),
                            | TypeAtom::Text => ValueType::Base(BaseType::String),
                        })
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
            | TypeAtom::Unit => self.arena.value_type_unit(),
            | TypeAtom::Integer => self.arena.value_type_base(BaseType::Integer),
            | TypeAtom::Text => self.arena.value_type_base(BaseType::String),
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
    (TileName::VAL, FormName::LET_STATEMENT),
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
///   parentheses append nothing.
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
/// - hypothesis: L3 — empty and multi-argument calls append their own ordered
///   operand range; a failure preserves the already-read prefix and locates the
///   unexpected operand or tile instead of silently accepting a suffix.
/// - witness: `lower::tests::argument_lists_preserve_prefixes_and_locate_the_first_fault`
/// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
#[spec(
    captures: before = (written.len(), cursor.clone()),
    ensures: |ret| {
        written.len() >= before.0
            && ret.as_ref().map_or(true, |&()| {
                let mut input = before.1.clone();
                let mut appended = written.iter().skip(before.0);
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
                }
                appended.next().is_none()
                    && matches!(input.peek(), Maybe::Absent(_))
                    && cursor.peek() == input.peek()
            })
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
    let start = written.len();
    loop {
        let run = cursor.operands();
        let closing = cursor.tile(TileName::PAREN_CLOSE);
        if let (Run::Empty(_), Maybe::Present(_)) = (run, closing)
            && written.len() == start
        {
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

/// Whether a form can stand where a value is expected.
///
/// # Specification
/// - requires: nothing; the function is total over the former vocabulary.
/// - ensures: exactly the value-producing formers answer affirmatively — a
///   name, a capitalised name, a number, a string, a parenthesised expression
///   and a thunk — the reserved tuple among them, since a reserved form is a
///   value the fragment declines rather than a form of another sort, and
///   keeping the two apart is what lets an attribute payload written as a
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
fn parse_literal(
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
        | Former::Constructor
        | Former::Parenthesized
        | Former::Thunk
        | Former::Lambda
        | Former::Return
        | Former::Force
        | Former::Call
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
            | DeclarationOutcome::Uncompleted { .. } | DeclarationOutcome::Refused(_) => {
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
            | DeclarationOutcome::Bodied { .. } | DeclarationOutcome::Refused(_) => {
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
        let Some(&CompType::Returner(returned)) = arena.comp_type(suspended)
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
            matches!(arena.comp_type(codomain), Some(&CompType::Returner(_))),
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
                Some(ValueType::Unit),
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
            SourceText::from("def id(a : Type, x : a) -> -F a { ret x }"),
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
        let Some(&CompType::Returner(returned)) = arena.comp_type(result)
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
                 { force t }",
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
            matches!(quoted(1_usize), (None, Some(CompType::Returner(_)), _)),
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
                let Some(&CompType::Returner(returned)) = arena.comp_type(suspended)
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
            SourceText::from("def x = thunk { fn (y) { ret y } } ;"),
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
    fn the_empty_parentheses_lower_to_the_unit_value()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x = () ;"), &mut arena);
        let body = body_of(outcomes(&module)[0]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Unit),
            "`()` is the unit value"
        );
    }

    #[test]
    fn an_identifier_spelled_unit_is_an_ordinary_name()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def x = unit ;"));

        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 12_usize),
                name: SurfaceName::from("unit"),
            },
            "`unit` is resolved like any other name, and nothing answers it"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an unresolved name is the author's mistake"
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
            SourceText::from("def g = 3 ; def a = thunk { (force g)(3) } ;"),
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
    fn a_function_tail_lowers_to_a_thunked_lambda_chain()
    {
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def f(x: Integer, y: String) -> -F Integer { run z <- ret y ; ret x }",
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
        let Some(&CompType::Returner(returned)) = arena.comp_type(result)
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
            SourceText::from("def main() -> -F Integer { ret 3 }"),
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
            matches!(arena.comp_type(suspended), Some(&CompType::Returner(_))),
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
            "def f(x: Integer) { ret x }",
            "def f(x, y: Integer) -> -F Integer { ret y }",
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
            SourceText::from("def a = thunk { run x <- ret 1 ; run y <- ret x ; ret x } ;"),
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

    #[test]
    fn a_call_applies_its_arguments_left_to_right()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def g = thunk { fn (x) { fn (y) { ret x } } } ; def h = thunk { g(1, 2) } ; \
                 def k = thunk { g() } ;",
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
            SourceText::from("def g = thunk { fn (x) { ret x } } ; def h = thunk { g(1) } ;"),
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
            Maybe::Present(at(53_usize, 54_usize)),
            "the inserted force names the head whose position demanded it"
        );
    }

    #[test]
    fn an_author_written_force_is_not_marked_inserted()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = 3 ; def a = thunk { (force g)(3) } ;"),
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
                "def f(x: Integer) -> Integer { ret x } def g(x: Integer) -> -F Integer { ret x }",
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
            let Some(&CompType::Returner(returned)) = arena.comp_type(codomain)
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
            | Some(&ValueType::Product(..)) => ret.first().is_some_and(|token| token == "*"),
            | Some(&ValueType::Unit) => ret.first().is_some_and(|token| token == "Unit"),
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
                    | Some(&ValueType::Unit) => tokens.push(String::from("Unit")),
                    | Some(&ValueType::Thunk(inner)) => {
                        tokens.push(String::from("U"));
                        pending.push(TypeNode::Computation(inner));
                    },
                    | Some(&ValueType::Product(first, second)) => {
                        tokens.push(String::from("*"));
                        pending.push(TypeNode::Value(second));
                        pending.push(TypeNode::Value(first));
                    },
                    | other => tokens.push(format!("{other:?}")),
                },
                | TypeNode::Computation(at) => match arena.comp_type(at) {
                    | Some(&CompType::Returner(inner)) => {
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
                 String))) ;",
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
            refusal(SourceText::from("def g : (Integer, String) ;")),
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
                 def s = (1, (), \"a\") ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let one = Value::Literal(integer(SourceFragment::from("1")));
        let letter = Value::Literal(text(SourceFragment::from("a")));
        let pair = |id| match arena.value(id) {
            | Some(&Value::Pair(first, second)) => Some((first, second)),
            | _ => None,
        };

        assert_eq!(
            spine(&arena, declared_of(lowered[0])),
            ["*", "Integer", "String"],
            "`A * B` lowers to the product of its operands"
        );
        let Some((first, second)) = pair(body_of(lowered[1]))
        else {
            panic!("a comma list where a value is read is a pair");
        };
        assert_eq!(
            (arena.value(first), arena.value(second)),
            (Some(&one), Some(&letter)),
            "the pair holds its members in order"
        );
        assert_eq!(
            spine(&arena, declared_of(lowered[2])),
            ["*", "Integer", "*", "Unit", "String"],
            "a product chain nests to the right"
        );
        let Some((head, tail)) = pair(body_of(lowered[3]))
        else {
            panic!("a tuple is a pair");
        };
        let Some((middle, last)) = pair(tail)
        else {
            panic!("a tuple pairs to the right, as the product chain nests");
        };
        assert_eq!(
            (arena.value(head), arena.value(middle), arena.value(last)),
            (Some(&one), Some(&Value::Unit), Some(&letter)),
            "each member stands at its place in the chain"
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
        let Some(&ValueType::Product(first, second)) = arena.value_type(quoted)
        else {
            panic!("the body is the product it spells");
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
        let Some(&ValueType::Product(left, right)) = arena.value_type(quoted)
        else {
            panic!("a product body");
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
            refusal(SourceText::from("def a = fn (y) { ret y } ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 24_usize),
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
                "def a = thunk { val y = 3; ret y } ;",
                unadmitted(
                    16_usize,
                    19_usize,
                    FormName::LET_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { fork (x : Integer) { ret 1 } as y ; ret 2 } ;",
                unadmitted(
                    16_usize,
                    20_usize,
                    FormName::FORK_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { ret 1; ret 2 } ;",
                unadmitted(
                    16_usize,
                    22_usize,
                    FormName::EXPRESSION_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { run _ <- ret 1; ret 2 } ;",
                unadmitted(
                    20_usize,
                    21_usize,
                    FormName::from(NamedKind("wildcard")),
                    FragmentSort::Pattern,
                ),
            ),
            (
                "def a = thunk { run y : -F Integer <- ret 1; ret y } ;",
                unadmitted(
                    22_usize,
                    23_usize,
                    FormName::ANNOTATION,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def f @[a : Type] (x) { ret x }",
                unadmitted(
                    0_usize,
                    31_usize,
                    FormName::PARAMETERS,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def rec f(x) { ret x }",
                unadmitted(
                    0_usize,
                    22_usize,
                    FormName::RECURSIVE,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def f(A) { ret 1 }",
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
                "def a = thunk { fn (x, y) { ret x } } ;",
                arity(
                    16_usize,
                    35_usize,
                    FormName::from(NamedKind("lambda_expression")),
                    2_usize,
                ),
            ),
            (
                "def a = thunk {} ;",
                arity(14_usize, 16_usize, FormName::BLOCK, 0_usize),
            ),
            (
                "def a = thunk { run x <- ret 1; } ;",
                arity(14_usize, 33_usize, FormName::BLOCK, 0_usize),
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
    fn a_juxtaposed_operand_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        let refused = refusal(SourceText::from("def a = thunk { ret 1 2 } ;"));

        assert_eq!(
            refused,
            LoweringRefusal::MalformedForm {
                span: at(22_usize, 23_usize),
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
            refusal(SourceText::from("def f(x: Integer Integer) { ret x }")),
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
        let refused = refusal(SourceText::from("@[ owes(ret 1) ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::NonValuePayload {
                span: at(8_usize, 13_usize),
                name: registered(SurfaceName::from("owes")),
                form: FormName::from(NamedKind("ret_expression")),
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
    fn an_attribute_is_filed_under_its_declaration_digest()
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
    fn a_refused_declarations_attributes_are_filed_under_its_digest()
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
            panic!("each refused name keeps the digest of the form it wrote");
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
                r#"@[ owes(ret 1) ] def a = b ;"#,
                LoweringRefusal::NonValuePayload {
                    span: at(8_usize, 13_usize),
                    name: owes,
                    form: FormName::from(NamedKind("ret_expression")),
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
