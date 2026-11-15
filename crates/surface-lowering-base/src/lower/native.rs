//! The records of the native data, the matches and the recursion that the
//! lowering's context holds.
//!
//! The classification reads a constructor, its classifier, a match compiled
//! to its decision tree, a field read off a data value and a recursive call
//! into these records. The mint sweep reads them back, and
//! `gandr-surface-lowering` names each one at its old path.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Carried;
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::TermId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::Literal;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Sink;
use super::Site;
use super::arity::Dependent;
use super::exits;
use super::lowered;
use crate::by_form::FormPlace;
use crate::by_form::FormStretch;
use crate::form::Former;
use crate::form::Placed;
use crate::module::SlotIndex;
use crate::origin::CaseOrigin;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
use crate::resolve::ScopeId;

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
    /// Why an answer is read at no arm of an enclosing match.
    pub mod passed {
        /// No match passed the answer into one of its arms on its way here,
        /// or none that did reads its scrutinee at a constructor.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The answer is stated here, or reaches here through no arm.
            Unpassed,
            /// Every arm the answer was passed into reads its scrutinee as
            /// written.
            Unsettled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an arm reads its match's scrutinee at no constructor over the
    /// arm's own variables.
    pub mod settled {
        /// The arm's body reads the scrutinee as the source writes it.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The tree's root is no data switch on the scrutinee over a bare
            /// family.
            Unswitched,
            /// The scrutinee is no name the case's frame binds
            /// intuitionistically.
            Unbound,
            /// The arm's leaves stand under no one branch of the root, or a
            /// field of that branch is settled by no variable of the arm.
            Unnamed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a data switch names no classifier for the constructors it splits
    /// into.
    pub mod bare {
        /// The switch reads no family the bare family type classifies.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The family has parameters, or is the presentation's own, so a
            /// constructor needs a written classifier the switch does not hold.
            Parameterised,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a data switch names no declaration whose constructors it splits
    /// into.
    pub mod eliminated {
        /// The switch's constructors are named by no declaration it records.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The family holds no slot the switch reads: the presentation
            /// code in a module that mints no `Theory`, or a declaration the
            /// collection filed no slot for.
            Unslotted,
            /// The switch has no branch to name: a match of no arms over a
            /// family the bare family type does not classify.
            Armless,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a constant is a word of no words.
    pub mod worded {
        /// The constant names no words.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The constant is neither a loop nor the words a loop is a
            /// letter of.
            Unworded,
        }
    }
}

/// How many tree binders stand above a node of a match's decision tree; as a
/// variable's index, how many binders stand between the variable and its
/// binder.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Depth(pub usize);

/// A value a match's decision tree scrutinises: level zero is the scrutinee
/// itself, and the binder a node under `depth` tree binders introduces for
/// its field `field` is level `depth + field + 1`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TreeLevel(pub usize);

/// A node of a decision tree, by its position in the tree's node list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TestAt(pub usize);

/// An arm of a match, by its position in source order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArmAt(pub usize);

/// A match, by its form and its place among the form's matches in the
/// lowering's match store.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CaseIndex(FormPlace);

/// A match's constructor arm, by its form and its place among the form's
/// arms in the lowering's store of the arms an answer is passed into.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArmIndex(FormPlace);

/// A field read off a data value by name, by its form and its place among
/// the form's fields in the lowering's store of them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProjectedIndex(FormPlace);

/// Read a store coordinate as each index of a flat store, and back.
macro_rules! form_keyed {
    ($($index:ident),* $(,)?) => {$(
        impl From<FormPlace> for $index
        {
            /// Read a store coordinate as the index.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(at: FormPlace) -> Self
            {
                Self(at)
            }
        }

        impl From<$index> for FormPlace
        {
            /// Read the index as its store coordinate.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(index: $index) -> Self
            {
                index.0
            }
        }
    )*};
}

form_keyed!(CaseIndex, ArmIndex, ProjectedIndex);

/// Whether a recursive call claims descent.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Claimed(pub bool);

/// A recursive function's parameter, by its position in the function's
/// parameter list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParameterAt(pub usize);

/// A recursive function's own name, which the frame of its fixpoint binds.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: the function's parameters, the ones before the fixpoint that
///   every recursive call passes unchanged, the staged one, whether a call
///   claims descent and the tile writing the name stay together under the frame
///   binding the name.
/// - provides: what a descent claim checks its call against, the evidence the
///   fixpoint carries, and the name its binder is read by.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the scope and the parameter store are not retained;
///   `function`, `instantiation` and `mint_function` interpret the record.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive function over one parameter, over a uniform
///   leading parameter and over a varying later one each close their fixpoint
///   over the parameter their matches scrutinise, with descent evidence exactly
///   when a call claims it.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_definition_descends_on_the_parameter_its_cases_scrutinise`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Recursion
{
    /// Every parameter, in the lowerer's parameter store.
    pub parameters: FormStretch,
    /// The parameters before the fixpoint, in the lowerer's parameter store:
    /// the ones every recursive call passes unchanged.
    pub uniform: FormStretch,
    /// The parameter the fixpoint stages, counted from the function's first:
    /// at or past the uniform ones.
    pub staged: ParameterAt,
    /// Whether a call claims descent, which makes the fixpoint's evidence
    /// structural rather than partial.
    pub claimed: Claimed,
    /// The tile writing the function's own name: where its fixpoint's binder
    /// is named.
    pub named: NodeIndex,
}

/// A recursive function's parameter as a match on it reads it: the frame
/// naming the function and the parameter's position in its list.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: the recursion and the position stay together.
/// - provides: what an arm under a match on a parameter hands down to the
///   claims inside it.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — `match` records it and `claim` reads it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Recursion`].
/// - witness: `gandr-surface-lowering::lower::native::tests::claims_under_cases_on_two_parameters_are_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Scrutiny
{
    /// The frame binding the recursive function's own name.
    pub recursion: ScopeId,
    /// The parameter's position in the function's list.
    pub position: ParameterAt,
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
/// - witness: `gandr-surface-lowering::lower::native::tests::a_recursive_call_passes_its_leading_parameters_unchanged`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Descent
{
    /// The call form.
    pub call: Site,
    /// Every argument the call wrote, in the lowerer's operand store.
    pub arguments: FormStretch,
}

/// A recursive call through a joint fixpoint to a sibling member, held until
/// every member's parameters are read.
///
/// # Specification
/// - requires: built by `Lowerer::instantiation` for a call whose summand is
///   not its caller's own.
/// - ensures: the call, the member it stands in, the member it calls and the
///   count of arguments it passes, together.
/// - provides: what `Lowerer::refuse_sibling_arities` holds to the called
///   member's parameters.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the record has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::refuse_sibling_arities`.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_mutual_block_member_takes_later_parameters_its_sibling_does_not_5036`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SiblingCall
{
    /// The descent call.
    pub call: Site,
    /// The member the call stands in.
    pub caller: SlotIndex,
    /// The member it calls.
    pub called: SlotIndex,
    /// The arguments it passes.
    pub arguments: OperandCount,
}

/// The computation type that a position answers.
///
/// A function's result or a match's answer states it. The record holds the
/// frame that the type was read under, and the innermost match arm that the
/// answer passed into on its way to the position.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the node is read where a result is read, under `frame`; `arm`
///   names an arm whose frame stands between `frame` and the position.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — an answer written on the match and one taken from the
///   function result each become the motive of the same tree, and one passed
///   into an arm is read at the constructor the arm matched.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_match_takes_its_answer_from_the_function_result`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Answer
{
    /// The type's syntax node.
    pub node: NodeIndex,
    /// The frame the type was read under.
    pub frame: Frame,
    /// What the position answers of the type the node writes.
    pub over: Over,
    /// The innermost arm the answer was passed into, whose reading of its
    /// match's scrutinee the answer is read under.
    pub arm: Maybe<ArmIndex, passed::Absent>,
}

/// What a position answers of the type its answer's node writes.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a loop arm's frame binds the answer at the loop's point
///   innermost.
/// - executable: none — the frame is a coordinate.
///
/// # Adequacy
/// - hypothesis: L3 — `loop => Path.back(loop)` takes its endpoints from the
///   path over the loop, and a written answer from itself.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Over
{
    /// The written type itself.
    Written,
    /// The path over a loop of a case answering the written type `B`:
    /// `Path[.A = B](y, y)`, `y` the case's answer at the loop's point, which
    /// the arm's frame `arm` binds innermost. Once the case is minted the
    /// lowering substitutes for `y` the answer
    /// [`gandr_core_term::identity::answer_at`] reads at the point.
    Loop
    {
        /// The arm's frame.
        arm: Frame,
    },
    /// The returner over the written value type, `-F B`: the answer of a
    /// thunk's body whose signature writes the box `() -> B`.
    Returning,
    /// The arrows the box `(A1, …, An) -> B` the node writes stands for, past
    /// its first `taken` domains: `Aₜ₊₁ -> … -> An -> -F B`. The answer of a
    /// thunk's body whose signature writes the box, and of each lambda under
    /// it but the last, which answers `B` returning.
    Valued
    {
        /// How many domains the lambdas around the position took.
        taken: usize,
    },
}

/// Where a constructor takes its whole classifier from.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a written classifier is a type node read under the constructor's
///   frame; an answered one names the frame the constructor stands under; a
///   slot names a data family's form, the argument's place among its parameters
///   and the stretch of the operand store the application's arguments occupy.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — an annotated constructor, one at the tail of a body a
///   signature answers, a field of either, one written as a data family's
///   argument, and a family without parameters.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_parameterized_constructor_needs_its_classifier`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Classifier
{
    /// A type the source wrote for the constructor: its annotation, the
    /// signature of the definition it is, or, for a field, the argument the
    /// classifier of the constructor around it writes at the parameter the
    /// field is typed by.
    Written(NodeIndex),
    /// The value type the answer of the position returns, the answer read
    /// under its own frame and carried to `frame`, the constructor's.
    Answered
    {
        /// The answer the position states.
        answer: Answer,
        /// The frame the constructor stands under.
        frame: Frame,
    },
    /// The constructor is written as an argument of a data family: the
    /// family's parameter at its place, under the arguments before it.
    Slot(Argued),
    /// The constructor is written as an argument of a call naming a
    /// declaration: the type the declaration writes for the parameter at its
    /// place, under the parameters before it, with those replaced by the
    /// arguments written for them.
    Parameter(CalledAt),
    /// The constructor is written in a field of another: the field's declared
    /// type, read under the family's parameters and the fields before it, with
    /// those replaced by the arguments of the other's classifier and the fields
    /// it is written with.
    Field(FieldOf),
    /// The constructor is written as an index a generator's result states:
    /// the family's index type at its place, read under the family's
    /// parameters and the indices before it, with those replaced by the
    /// generator's own parameters and the indices it states before it (#4027).
    Stated(StatedIndex),
    /// The constructor is bound by a `let` with no type, and its family takes
    /// indices and no parameters: the family at the indices its generator's
    /// result states, with the fields replaced by the values the constructor
    /// is written with (#5050).
    Resulted(ResultOf),
    /// The family's one classifier, which the lowering inserts: the family
    /// has no parameters.
    Inserted,
}

/// A field of a written constructor, as [`Classifier::Field`] reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `around` is the constructor's node and `declared` the field's
///   declared type, read under the family's `parameters` and the `index` fields
///   before it.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Classifier::Field`].
/// - witness: `gandr-surface-lowering::lower::native::tests::a_field_classifies_the_constructor_written_in_it_1171`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct FieldOf
{
    /// The constructor the field belongs to.
    pub around: NodeIndex,
    /// The field's declared type.
    pub declared: NodeIndex,
    /// How many parameters the family declares.
    pub parameters: usize,
    /// The field's place among its constructor's fields.
    pub index: usize,
}

/// Where the mint names the wildcards of the classifier it inserts for a
/// constructor written in a field, when the constructor around reads as no
/// family's application (#6113).
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `form` is the hole form of the form that writes the constructor,
///   `family` the slot of the constructor's family, and `written` the family's
///   position in the collection's data list.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::fielded_classifier`.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_pair_in_a_field_at_a_computed_pair_type_takes_its_family_over_wildcards_6113`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Fielded
{
    /// The hole form the wildcards' names hold.
    pub form: gandr_core_term::hole::HoleForm,
    /// The family's slot.
    pub family: SlotIndex,
    /// The family's position in the collection's data list.
    pub written: usize,
}

/// A generator's result read as its constructor's classifier, as
/// [`Classifier::Resulted`] reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `form` is the family's position in the collection's data list,
///   and `generator` the constructor's tag among its generators.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Classifier::Resulted`].
/// - witness: `gandr-surface-lowering::lower::native::tests::an_untyped_let_reads_its_constructor_s_classifier_off_its_result_5050`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ResultOf
{
    /// The family's position in the collection's data list.
    pub form: usize,
    /// The generator's place among the family's generators.
    pub generator: usize,
}

/// An index a generator's result states, as [`Classifier::Stated`] reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `form` is the family's position in the collection's data list,
///   `generator` the generator's among its generators, and `place` the index's
///   among the indices the generator states.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Classifier::Stated`].
/// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_at_a_family_s_index_takes_the_index_s_type_4027`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct StatedIndex
{
    /// The family's position in the collection's data list.
    pub form: usize,
    /// The generator's place among the family's generators.
    pub generator: usize,
    /// The index's place among the indices the generator states.
    pub place: usize,
}

/// The place a value argument takes in a data family's application.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `form` is the family's position in the collection's data list,
///   `place` the argument's among the family's parameters, and `applied` the
///   operand stretch of the application's arguments, `place` within it.
/// - executable: none — the plan holds no store to check its stretch against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Classifier`]'s slot row.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Argued
{
    /// The family's position in the collection's data list.
    pub form: usize,
    /// The argument's place among the family's parameters.
    pub place: usize,
    /// The application's arguments, in the operand store.
    pub applied: FormStretch,
}

/// The parameter a value argument stands at in a call naming a declaration.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `typed` is the type the declaration at `slot` writes for the
///   parameter, read under the parameters before it, and `applied` the operand
///   stretch of the call's arguments, one per explicit parameter from the
///   first.
/// - executable: none — the plan holds no store to check its stretch against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Classifier`]'s parameter row.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_argument_reads_the_arguments_before_it_1876`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CalledAt
{
    /// The type the declaration writes for the parameter.
    pub typed: Placed,
    /// The declaration's slot.
    pub slot: SlotIndex,
    /// The call's arguments, in the operand store.
    pub applied: FormStretch,
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
/// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_applies_to_its_fields`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Constructed
{
    /// The family's admission position.
    pub family: ConstantIndex,
    /// The constructor's tag.
    pub tag: ConstructorTag,
    /// The fields, in the operand store.
    pub fields: FormStretch,
    /// Where its classifier comes from.
    pub classifier: Classifier,
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
/// - witness: `gandr-surface-lowering::lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `gandr-surface-lowering::lower::native::tests::literal_patterns_compare_and_branch`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
/// - witness: `gandr-surface-lowering::lower::native::tests::telescope_patterns_split_and_project`
/// - witness: `gandr-surface-lowering::lower::native::tests::sum_patterns_case_on_the_stated_arity`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Test
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
    /// Run arm `arm` when its guard holds, its variables settled as a leaf's:
    /// the guard bound and cased on, `yes` the arm's leaf and `no` the rows
    /// after it, each under the guard's binder and its case's.
    Guard
    {
        /// The guarded arm.
        arm: ArmAt,
        /// The tree binders above the guard.
        depth: Depth,
        /// The level that settled each arm variable.
        bindings: Vec<TreeLevel>,
        /// The child where the guard holds: the arm's leaf.
        yes: TestAt,
        /// The child where it fails: the rows after the arm's.
        no: TestAt,
    },
    /// The hole that decides whether the first surviving row matches.
    Stuck(HoleId),
    /// A branch whose constructor no row admits: the case of no branches on
    /// one of its equations, which the checker admits when the constructor's
    /// index there is apart from the scrutinee's. The equation is named by its
    /// binder, counted from the innermost.
    Absurd(Depth),
    /// Switch on the native data value at `level`: one child per
    /// constructor, with the constructor's arity.
    Data
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the switch.
        depth: Depth,
        /// The family, when the family over no arguments classifies its
        /// constructors.
        family: Maybe<ConstantIndex, bare::Absent>,
        /// The data declaration whose constructors the branches are, by
        /// which a printer names them.
        eliminated: Maybe<ConstantIndex, eliminated::Absent>,
        /// The equations each branch binds past its fields, one per index of
        /// the family; its child stands under both.
        equations: usize,
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
    /// Split the tuple at `level` into its `arity` components, component
    /// zero outermost.
    Split
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the split.
        depth: Depth,
        /// How many components it binds.
        arity: usize,
        /// Whether the split reads its motive at the scrutinee.
        dependent: Dependent,
        /// The label of each component some row leaves unwritten under a
        /// label pattern, or that holds the rest of a dependent record from
        /// that label's field on, by component, ascending.
        unwritten: Vec<(usize, FieldLabel)>,
        /// The child under them.
        child: TestAt,
    },
    /// Project each of `labels` off the record at `level`, binding them in
    /// order.
    Record
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the projections.
        depth: Depth,
        /// The labels projected, in order.
        labels: Vec<FieldLabel>,
        /// The child under them.
        child: TestAt,
    },
    /// Switch on the summand of the sum at `level`: one child per summand,
    /// under its payload's binder.
    Sum
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the switch.
        depth: Depth,
        /// Each summand's child.
        branches: Vec<TestAt>,
    },
    /// Case on the native list at `level`: the empty list's child under no
    /// binder, and the cell's under its head's and its tail's, the head
    /// outermost.
    List
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the case.
        depth: Depth,
        /// The child for the empty list.
        nil: TestAt,
        /// The child for a cell.
        cell: TestAt,
    },
}

/// What a decision tree's root stands over.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a match's root reads its scrutinee at level zero; clauses' root
///   stands under one binder per column, the column at place `k` read at level
///   `k + 1`.
/// - executable: none — a plain tag its producer establishes.
///
/// # Adequacy
/// - hypothesis: L3 — a function's clauses and a matching lambda's lower under
///   one lambda per column.
/// - witness: `gandr-surface-lowering::lower::native::tests::clauses_match_one_column_per_arrow`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_matching_lambda_binds_one_lambda_per_column`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Roots
{
    /// A match's scrutinee, at level zero.
    Scrutinee,
    /// A function's clauses, under its parameters' lambdas, which the
    /// function mints.
    Parameters(Depth),
    /// A matching lambda's clauses, under lambdas the tree mints itself.
    Lambdas(Depth),
}

impl Roots
{
    /// The tree binders the root stands under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn columns(self) -> Depth
    {
        match self {
            Self::Scrutinee => Depth(0),
            Self::Parameters(columns) | Self::Lambdas(columns) => columns,
        }
    }
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
/// - witness: `gandr-surface-lowering::lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaseForm
{
    /// The scrutinee's syntax node; for clauses, a node standing for their
    /// columns, which no value is written at.
    pub scrutinee: NodeIndex,
    /// What the tree's root stands over.
    pub roots: Roots,
    /// The frame the match is read under.
    pub frame: Frame,
    /// The answer the motive is read from.
    pub answer: Maybe<Answer, answered::Absent>,
    /// The answer written on the match itself, `match e -> C { … }`, which
    /// the tree's root is ascribed; absent where only its position states
    /// one.
    pub ascribed: Maybe<Answer, answered::Absent>,
    /// Each constructor arm's body.
    pub bodies: Vec<NodeIndex>,
    /// Each guarded clause's guard, `| p if g => c`.
    pub guards: BTreeMap<ArmAt, NodeIndex>,
    /// The decision tree.
    pub tests: Vec<Test>,
    /// The loop arms, one per loop of the root's sort in the order its loop
    /// branches follow its constructors' branches, or none.
    pub loops: Vec<LoopArm>,
    /// What the origin table keeps of the arms.
    pub origin: CaseOrigin,
    /// Each constructor arm's variables, in the order its leaves settle
    /// them.
    pub variables: Vec<Vec<Placed>>,
}

/// What one constructor arm of a match reads the match's scrutinee as, for
/// the answer the match passes the arm's body.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `outer` names an arm stored before this one.
/// - executable: none — the reading names binders of the lowering's scope and
///   an arm of its store, which the record cannot reach.
///
/// # Adequacy
/// - hypothesis: L3 — a match in an arm, on the variable naming the arm's
///   field, reads the answer and the outer scrutinee at the arm's constructor;
///   one in an arm that leaves a field unnamed reads them as written.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `gandr-surface-lowering::lower::native::tests::an_arm_leaving_a_field_unnamed_passes_the_answer_as_written_2994`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArmReading
{
    /// The constructor the arm reads the scrutinee at.
    pub settled: Maybe<Settled, settled::Absent>,
    /// The arm the match's own answer was passed into.
    pub outer: Maybe<ArmIndex, passed::Absent>,
}

/// The constructor an arm reads its match's scrutinee at, over what it
/// reads each field at.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `scrutinee` is the binder the case's frame reads the scrutinee
///   by, intuitionistic; `read` spells one term in prefix order, a constructor
///   first.
/// - executable: none — the binders are coordinates of the lowering's scope.
///
/// # Adequacy
/// - hypothesis: L3 — as [`ArmReading`].
/// - witness: `gandr-surface-lowering::lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `gandr-surface-lowering::lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Settled
{
    /// The scrutinee's binder.
    pub scrutinee: ScopeId,
    /// What the arm reads the scrutinee at, in prefix order.
    pub read: Vec<Built>,
}

/// One node of what an arm reads a level of its match's tree at.
///
/// The nodes are in prefix order. A node is the binder of the arm variable
/// that the level settles, or the constructor that a switch above the arm's
/// leaf matched there. The readings of the constructor's fields follow it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a constructor's `arity` is its field count, and `family` the bare
///   family that classifies it.
/// - executable: none — the binders are coordinates of the lowering's scope.
///
/// # Adequacy
/// - hypothesis: L3 — as [`ArmReading`].
/// - witness: `gandr-surface-lowering::lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `gandr-surface-lowering::lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Built
{
    /// The arm variable's binder.
    Bound(ScopeId),
    /// A constructor, its fields' readings after it.
    Constructed
    {
        /// The bare family the switch eliminates.
        family: ConstantIndex,
        /// The branch's constructor.
        tag: ConstructorTag,
        /// The constructor's field count.
        arity: usize,
    },
}

/// A field read off a data value by its name, `e.l`: the case over `e` whose
/// branch for each constructor returns that constructor's field `l`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `branches` holds, per constructor in tag order, its field count
///   and the position of its field `l`, which is below that count; the subject
///   is read as a value under `frame`.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::data_field`.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_data_field_is_the_case_returning_it_1106`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Projected
{
    /// The data value's syntax node, a name.
    pub subject: NodeIndex,
    /// The frame the projection is read under.
    pub frame: Frame,
    /// The family the case eliminates.
    pub family: ConstantIndex,
    /// Per constructor, its field count and the position of the field read.
    pub branches: Vec<(usize, usize)>,
    /// Where the type the projection returns is read from.
    pub typed: Typed,
}

/// Where the type a field projection returns is read from.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: an answer is the projection's position's; a field names its first
///   constructor's field, whose type names no field before it.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::data_field`.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_data_field_is_the_case_returning_it_1106`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Typed
{
    /// The answer the projection's position states.
    Answered(Answer),
    /// The field's declared type, with the family's parameters replaced by the
    /// arguments of the type the subject is stated at.
    Field
    {
        /// The subject's stated type's syntax node.
        stated: NodeIndex,
        /// The field's declared type's syntax node.
        declared: NodeIndex,
        /// How many fields come before it in its constructor.
        earlier: usize,
        /// How many parameters the family takes.
        parameters: usize,
    },
}

impl Projected
{
    /// The nodes a projection typed by its field reads its type off: its
    /// subject, the subject's stated type and the field's declared type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present exactly when the projection is typed by its field,
    ///   with the subject first.
    /// - provides: the types the mint sweep lowers before the projection.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field read in an operand, where no answer is
    ///   stated, is typed by its declaration.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_data_field_is_the_case_returning_it_1106`
    #[spec(ensures: |ret| ret.is_some() == matches!(self.typed, Typed::Field { .. }))]
    #[inline]
    #[must_use]
    pub const fn typed_by(&self) -> Option<(NodeIndex, NodeIndex, NodeIndex)>
    {
        match self.typed {
            Typed::Field {
                stated, declared, ..
            } => Some((self.subject, stated, declared)),
            Typed::Answered(_) => None,
        }
    }
}

/// One loop arm of a match, `loop => e`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `words` and `generator` name a loop the lowering collected.
/// - executable: none — the indices name collected words.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::loop_arms`.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoopArm
{
    /// The words the loop is a letter of, by their position among the
    /// collected words.
    pub words: usize,
    /// The loop's position among its words' cells.
    pub generator: usize,
    /// The arm's body.
    pub body: NodeIndex,
    /// The arm's pattern, the loop's name.
    pub named: Placed,
}

/// What a place inside a type holds, by the type the place states: a code,
/// or a value that is no code. A telescope type written at a place that holds
/// a value reads as a tuple (#5208, #5500).
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `Code` for a place whose type is a universe, or that states no
///   type the walk reads; `Value` for any other place, with the type the place
///   writes when it writes one.
/// - executable: none — the record holds no place to check against.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::held_at`.
/// - witness: `gandr-surface-lowering::lower::tests::a_parenthesised_or_nested_telescope_reads_by_its_place_5500`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Holds
{
    /// A code: the place's type is a universe.
    Code,
    /// A value that is no code, of the written type when the place writes
    /// one.
    Value(Option<NodeIndex>),
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
/// - witness: `gandr-surface-lowering::lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
#[spec(ensures: sink.arena.values_since(mark).all(|id| sink.origins.value(id) == Maybe::Present(origin))
    && sink.arena.computations_since(mark).all(|id| match root {
        | Maybe::Present((held, written)) if held == id => sink.origins.computation(id) == Maybe::Present(written),
        | _ => sink.origins.computation(id) == Maybe::Present(origin),
    }))]
#[inline]
pub fn record_since(
    sink: &mut Sink<'_>,
    mark: gandr_core_term::ArenaWatermark,
    origin: Origin,
    root: Maybe<(ComputationId, Origin), rooted::Absent>,
)
{
    record_copied_since(sink, mark, origin, root, &[]);
}

/// Record, for every copy a match's leaves made of a written variable, the
/// binder the variable was written against.
///
/// A leaf places an arm's body under the binders its tests opened, so each
/// written use in the body stands in the tree as the copy the substitution
/// minted for it. The copy keeps the use's binder, which is what names the
/// binders a split opens for its components: a type the copy's judgement
/// spells, a dependent split's answer at its components say, reads them by
/// the names the arm wrote. A pattern variable that binds the whole scrutinee
/// stands for the scrutinee's own node, which the leaf did not mint; that
/// node keeps the binding it was written with.
///
/// A rewrite can copy a copy: an arm that writes a call inside another form
/// reports the use's first copy as the source of a second. The copies are
/// recorded in ascending order and each source is read as the loop reaches
/// it, so the second copy finds the binder its source took earlier in the
/// same pass; reading every source before recording any left it unbound.
///
/// # Specification
/// - requires: `carried` is what the rewrites since `floor` reported, and no
///   variable the origin table records a binding for was minted after it.
/// - ensures: every value minted after `floor` that `carried` maps a recorded
///   use to holds that use's binder, recorded once, in ascending order of the
///   copies; a value from before `floor` keeps what it held.
/// - provides: what keeps a match leaf's copy of a use naming its binder.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a leaf's copy of an arm returning its two pattern
///   variables swapped names each at the variable that binds it, and a variable
///   binding the whole scrutinee leaves the scrutinee bound at its parameter; a
///   copy left without its binding, bound at the other component, or a
///   scrutinee rebound at the pattern fails the witness. A copy the same
///   rewrite made of a copy names the use's binder too; reading every source
///   before recording any leaves it unbound and fails the second witness.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_leaf_copy_keeps_each_use_naming_its_pattern_variable`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_leaf_copy_of_a_copy_keeps_the_use_naming_its_binder_451`
#[spec(
    requires: sink.arena.values_since(floor).next().is_none_or(|first| {
        sink.origins.bindings().last().is_none_or(|&(held, _)| held < first)
    }),
    ensures: carried.iter().all(|pair| match *pair {
        Carried::Value(held, written) => sink.arena.values_since(floor).next().is_none_or(|first| written < first)
            || matches!(sink.origins.binding(held), Maybe::Absent(_))
            || matches!(sink.origins.binding(written), Maybe::Present(_)),
        Carried::Computation(..) | Carried::ValueType(..) | Carried::CompType(..) => true,
    }),
)]
fn carry_bindings(
    sink: &mut Sink<'_>,
    carried: &[Carried],
    floor: gandr_core_term::ArenaWatermark,
)
{
    let Some(first) = sink.arena.values_since(floor).next()
    else {
        return;
    };
    let mut copies: Vec<(ValueId, ValueId)> = carried
        .iter()
        .filter_map(|pair| match *pair {
            Carried::Value(held, written) if first <= written => Some((written, held)),
            Carried::Value(..)
            | Carried::Computation(..)
            | Carried::ValueType(..)
            | Carried::CompType(..) => None,
        })
        .collect();
    copies.sort_by_key(|&(written, _)| written);
    let mut recorded = None;
    for (written, held) in copies {
        if recorded == Some(written) {
            continue;
        }
        if let Maybe::Present(binder) = sink.origins.binding(held) {
            sink.origins.record_binding(written, binder);
            recorded = Some(written);
        }
    }
}

/// [`record_since`], each node `carried` reports as a copy at the origin of
/// the node it was copied from, and each copy of a written use at the use's
/// binder.
///
/// # Specification
/// - requires: nothing has been recorded for a node minted since `mark`, and
///   `carried` reports the rewrites that minted the copies among them.
/// - ensures: every node minted since `mark` carries an origin, in ascending
///   order in each family: the root its own; a node `carried` reports as a copy
///   the origin of the node it was copied from, a copy of a match's root that
///   match's record too; every other node `origin`. Each written variable the
///   rewrite replaced by a node answering elsewhere is labelled with it, and a
///   copy of a written use holds the use's binder, as [`carry_bindings`]
///   states.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every node of a compiled tree has an origin, and a leaf's
///   copy of its arm's body answers at the body's bytes.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_leaf_keeps_its_arm_body_written`
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_leaf_copy_keeps_each_use_naming_its_pattern_variable`
#[spec(ensures: sink.arena.values_since(mark).all(|id| matches!(sink.origins.value(id), Maybe::Present(_)))
    && sink.arena.computations_since(mark).all(|id| match root {
        | Maybe::Present((held, written)) if held == id => sink.origins.computation(id) == Maybe::Present(written),
        | _ => matches!(sink.origins.computation(id), Maybe::Present(_)),
    }))]
#[inline]
pub fn record_copied_since(
    sink: &mut Sink<'_>,
    mark: gandr_core_term::ArenaWatermark,
    origin: Origin,
    root: Maybe<(ComputationId, Origin), rooted::Absent>,
    carried: &[Carried],
)
{
    let sources = gandr_core_term::Sources::of(carried);
    for id in sink.arena.values_since(mark) {
        let recorded = exits::value_origin(sink, &sources, id, origin);
        sink.origins.record_value(id, recorded);
    }
    for id in sink.arena.computations_since(mark) {
        match root {
            Maybe::Present((held, written)) if held == id => {
                sink.origins.record_computation(id, written);
            },
            Maybe::Present(_) | Maybe::Absent(_) => {
                let recorded = exits::computation_origin(sink, &sources, id, origin);
                sink.origins.record_computation(id, recorded);
                exits::keep_case(sink, &sources, id);
            },
        }
    }
    for id in sink.arena.value_types_since(mark) {
        let recorded = exits::value_type_origin(sink, &sources, id, origin);
        sink.origins.record_value_type(id, recorded);
    }
    for id in sink.arena.comp_types_since(mark) {
        let recorded = exits::comp_type_origin(sink, &sources, id, origin);
        sink.origins.record_comp_type(id, recorded);
    }
    exits::label_replaced(sink, carried);
    carry_bindings(sink, carried, mark);
}

quenchant_shape::reason_enum! {
    /// Why a written type gives a field no classifier.
    pub mod inherited {
        /// The field's type is neither its family over its own parameters nor
        /// a parameter a written classifier gives an argument for.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No classifier is read off the type.
            Unclassified,
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
            /// The name stands at a place its data family declares a universe,
            /// where it names a type.
            TypePlace,
            /// More than one family the site sees declares a constructor so
            /// named, so the bare name selects none.
            Several,
            /// Two imports bind the name to two constructors.
            Shadowed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a constant has no body a decode of it reads through.
    pub mod unfolding {
        /// The constant stands for itself where a type decodes it.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The constant is no top-level definition written as one form,
            /// or its declaration refused.
            Opaque,
            /// The definition's body did not lower.
            Unlowered,
        }
    }
}

/// A form with its parentheses stripped, as `Lowerer::unwrapped` reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the operands keep source order.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::unwrapped`.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unwrapped
{
    /// The form's node.
    pub node: NodeIndex,
    /// Its former.
    pub former: Former,
    /// The first tile it is written with.
    pub keyword: Option<Placed>,
    /// Its operands, left to right.
    pub operands: Vec<NodeIndex>,
}

/// `declared` quoted, its binders replaced by `environment`, the innermost
/// first, and read back as a type, each node the substitution carries pushed
/// onto `carried` when one is given.
///
/// # Specification
/// - requires: `environment` holds one value per binder `declared` reads, the
///   innermost first.
/// - ensures: the type the substituted quote holds; nothing when the
///   substitution leaves no quoted type. With `carried`, each node the
///   substitution carried, as
///   [`gandr_core_term::substitute_environment_traced`] records it; the caller
///   records their origins.
/// - provides: the one reading of a declared type at the arguments it is
///   applied to.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a constructor's classifier, a projected field's type and
///   a called parameter's type, each over its arguments.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_data_field_is_the_case_returning_it_1106`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_at_a_family_s_index_takes_the_index_s_type_4027`
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_call_s_lambda_argument_reads_its_parameter_s_domain_3921`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if arena.value_type(id).is_some()))]
#[inline]
pub fn substituted_type(
    declared: ValueTypeId,
    environment: &[ValueId],
    arena: &mut gandr_core_term::CoreArena,
    carried: Option<&mut Vec<Carried>>,
) -> Maybe<ValueTypeId, lowered::Absent>
{
    let code = TermId::Value(arena.value_quote(declared));
    let substituted = match carried {
        Some(carried) => {
            gandr_core_term::substitute_environment_traced(arena, code, environment, carried)
        },
        None => gandr_core_term::substitute_environment(arena, code, environment),
    };
    let TermId::Value(substituted) = substituted
    else {
        return Maybe::Absent(lowered::Absent::Unminted);
    };
    match arena.value(substituted) {
        Some(&Value::Quote(ty)) => Maybe::Present(ty),
        Some(_) | None => Maybe::Absent(lowered::Absent::Unminted),
    }
}

/// `(carrier, point)` wrapped `reflexivities` times in its reflexivity.
///
/// # Specification
/// - requires: `point` is a value of `carrier`.
/// - ensures: `(carrier, point)` for no wrapping; otherwise `(Path[.A = c](p,
///   p), here(p))` over the pair `(c, p)` for one wrapping fewer.
/// - provides: the path a word above dimension one stands at, the sphere's
///   `Path[.A = Path[.A = S2](Base, Base)](here(Base), here(Base))`.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the wrappings, not recursion.
/// - measure: the wrappings left.
///
/// # Adequacy
/// - hypothesis: L3 — the sphere's 2-cell binds at the path at the reflexivity
///   of its point.
/// - witness: `gandr-surface-lowering::lower::native::tests::a_loop_mints_the_words_at_its_point`
#[spec(captures: before = (carrier, point), ensures: |ret| reflexivities != gandr_kernel_term::Reflexivities::NONE || ret == before)]
#[inline]
pub fn wrapped_point(
    arena: &mut CoreArena,
    (carrier, point): (ValueTypeId, ValueId),
    reflexivities: gandr_kernel_term::Reflexivities,
) -> (ValueTypeId, ValueId)
{
    let (mut carrier, mut point) = (carrier, point);
    for _ in 0 .. usize::from(reflexivities) {
        carrier = arena.value_type_path(carrier, point, point);
        point = arena.value_here(point);
    }
    (carrier, point)
}
