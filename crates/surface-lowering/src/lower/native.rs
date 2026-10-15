//! Native data in the lowering: a data family where a type is read, a
//! constructor applied to its fields, a data declaration's signature, and a
//! match compiled to native eliminations.
//!
//! # A constructor carries its whole classifier
//!
//! The core's constructor value names the nominal type it builds, arguments
//! and all, so the lowering has to know them where the constructor is
//! written. A family without parameters has one classifier, which the
//! lowering inserts. A family with parameters takes it from the type the
//! constructor's position states: an annotation `(C(…) : T(…))`; the
//! signature of the definition it is, `def x : T(…) ; def x = C(…) ;`; the
//! answer of the body it ends, `+U (-F T(…))`, `() => T(…)` or a function's
//! stated result, through a tail, a `pure` there or a `return`; its parent's
//! classifier, for a field typed by the family itself or by one of its
//! parameters; and, where it is written as an argument of a data family, that
//! family's parameter at its place with the parameters before it replaced by
//! the arguments written for them: `Inl(a)` in `Tagged(Integer, String,
//! Inl(a))`, whose third parameter is `s : SumOb(l, r)`, is a
//! `SumOb(Integer, String)`. The arguments before the place are its
//! siblings, which the mint sweep reaches after it, so the application mints
//! such a constructor before itself. A constructor no position types is
//! refused as unannotated.
//!
//! The alternative was the checker's check mode: a constructor synthesised
//! against its expected type, which needs the certificate to carry a
//! classifier the checker fills in, a kernel change. Every type the lowering
//! reads here is written in the source and closed at the position it is read
//! from, or closed by the arguments written beside it, so the lowering
//! carries it. Reversal: a checker that elaborates a constructor against an
//! expected type makes the classifier the checker's, and this reading is
//! deleted.
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
//! # The motive is the answer the source states
//!
//! A data case checks against a motive under one scrutinee binder. The
//! lowering reads it from the match's own answer, `case e -> T { … }`, or
//! from the result type of the function whose body ends in the match,
//! relocated into the match's context; a match with neither is refused as
//! unannotated when its tree eliminates native data. Reversal: a checker that
//! takes the motive from the checking direction makes the answer optional.
//!
//! A pattern at a scrutinee written with a dependent record (`lower::arity`)
//! splits each link of its nesting: a link the type binds by a dependent
//! split, whose motive is the answer with the split's scrutinee abstracted,
//! and a product link by a split of two. The answers are read from the root
//! down: a data case passes its answer to its branches under their fields,
//! a dependent split's arm answers the motive at the pair of its two
//! binders, and every other test passes its answer under the binders it
//! opens. A scrutinee that is a variable is abstracted wherever the answer
//! reads it, so an arm's answer reads the pair it matched; any other
//! scrutinee gives the motive that ignores its binder. A match with a
//! dependent split and no answer is refused as unannotated.
//!
//! - Alternatives: projections in place of the split, which leave the arm's
//!   answer reading the scrutinee rather than its components; a motive left for
//!   the checker to infer, which is higher-order unification.
//! - Reversal: a checker that infers the motive from the checking direction
//!   makes the abstraction here unnecessary.
//!
//! A data case over a variable is the dependent eliminator the same way: its
//! motive is the answer with the scrutinee abstracted, and each branch
//! answers the motive at its constructor over the branch's fields. A
//! recursive call at a field, `f[<](x)`, then answers the motive at `x`, and
//! the `Loop(x)` arm the motive at `Loop(x)`; a leaf under such a root reads
//! the scrutinee's variable as the constructor its branch matched, over the
//! root's fields. A parameterless family is refined so, and so are the words
//! over a looped point: a case over `p : Path(Circle, Base, Base)` answers
//! its motive at `here(Base)`, `loop ∷ q` and `back(loop) ∷ q`, each the
//! words' own constructor, which both checkers read at the path type. A
//! family with parameters and the presentation's own keep the answer as
//! written under the fields, and an answer that does not read the scrutinee
//! is unchanged, its motive ignoring its binder.
//!
//! - Alternatives: a motive clause written on the case, a second spelling of
//!   what the result type already states.
//! - Reversal: a motive that is not the answer with the scrutinee abstracted —
//!   one reading an index of the scrutinee's type — needs the clause.
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
//! The core's fixpoint `fix x. λy. M` binds its own thunk, and the checker
//! and the kernel type it by stages: `y` stands at a fresh stage, a case on it
//! binds its constructor's recursive fields one stage below, and every self
//! call `(force x) a` takes `a` strictly below the stage `y` stands at
//! (`gandr-core-checker`'s crate documentation, § Recursion).
//! `def rec f(p₁, …, pₖ, y) -> C { b }` therefore lowers to `thunk (λp₁ …
//! λpₖ. fix f. λy. b)`, and a call `f[<](p₁, …, pₖ, a)` to `(force f) a`. The
//! parameters before the last are the uniform parameters of an inductive
//! definition (Coquand and Paulin, *Inductively defined types*, COLOG 1988):
//! bound outside the fixpoint, so every recursive call must pass them as
//! themselves, and a call passing anything else is refused as non-uniform.
//! The last parameter is the one the fixpoint recurses on, its evidence's
//! staged position the fixpoint's first, and whether `a` stands below its
//! stage is the checkers' to judge, which a call at anything else fails as
//! `StageNotBelow`; the lowering neither searches for a decreasing argument
//! nor duplicates the check.
//!
//! `<` is the claim. A fixpoint carries structural evidence when one of its
//! calls writes it and partial evidence when none does, so the checker and
//! the kernel type every recursion the source claims and none it does not.
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
//! member its projection, with partial evidence until a stage typing spans
//! the bundle; this needs the members collected as declarations from
//! inside one form, and is its own unit.
//!
//! `def rec f(p₁, …, pₖ, y) -> C { b }` lowers to `thunk (λp₁ … λpₖ. fix f. λy.
//! b)`: the core fixpoint binds its own thunk, and its structural evidence
//! stages the parameter the fixpoint takes first, which is the last one the
//! source writes. A recursive call is written `f[<](p₁, …, pₖ, a)` and lowers
//! to `(force f) a`. `<` is the claim: a fixpoint carries `StructuralDescent`
//! evidence when one of its calls writes it and `Partial` evidence when none
//! does, so the checker and the kernel type every recursion the source claims
//! and none it does not, and a call at an argument not below the stage fails
//! as `StageNotBelow`. The lowering neither searches for a decreasing argument
//! nor duplicates the check. The fixpoint is marked `Insertion::Fixpoint` at
//! the function form's origin, since the source writes no `fix`.
//!
//! The function's own name is bound by one frame between the last parameter and
//! the ones before it, typed by the declaration form so no signature telescope
//! counts it, and it resolves only as the head of a claim: written bare, it is
//! `UnmarkedSelfReference`, whose message spells the claim. A parameter of the
//! same name shadows it. The parameters before the last are uniform (Coquand
//! and Paulin): bound outside the fixpoint, so a recursive call must pass each
//! as itself, and a call passing anything else is `OutOfFragment` with the
//! `NonUniform` boundary, at the argument. A function with no parameter has
//! nothing to recurse on and is declined. Every resident of the instantiation
//! other than a lone `<` — `>` for productivity, a measure, a size, a cost — is
//! reserved until its termination rung lands. A block stands as a match arm, so
//! the four programs the corpus carries in
//! `fixture/model/data/data-recursive.gandr` — `plus`, `length`, `append` and
//! `map` — are written in the surface's intended spelling.
//!
//! The alternative was the recursive argument first, with every later parameter
//! pushed into the case's motive and re-bound under each branch's fields, as an
//! eliminator's methods take them (`McBride`); it admits a recursive call that
//! varies them, an accumulator, at the cost of re-indexing every branch.
//! Reversal: a recursive definition that must vary an earlier parameter.
//!
//! The mutual block `rec { def …; def … }` is declined. The grammar parses it
//! as one item whose members are inline tiles of the block, so the module reads
//! no declaration in it and refuses the whole source at the block's form.
//! Reversal: one fixpoint over a bundle of the members' thunks, each member its
//! projection, with partial evidence until a descent judgment spans the bundle.
//! That needs the members collected as declarations from inside one form, and
//! is its own unit.
//!
//! # Native data and the match
//!
//! `lower::native` lowers a `data` declaration at the root to the core's native
//! `DataSignature`, a constructor to a native constructor value carrying its
//! whole classifier, a `case` to a decision tree of native eliminations, and a
//! `def rec` function to one fixpoint over its last parameter, recursive calls
//! written with the descent claim `f[<](…)`.
//!
//! `data T(a : A) : Type { C : (x : X) --> T(a); … }` at the root lowers to the
//! core's native `DataSignature`: the parameters as a telescope, each
//! generator's fields as one constructor, in source order. A field may name the
//! family it belongs to, applied to its own parameters, which is how `List(a)`
//! holds its tail; whether every such occurrence is strictly positive is the
//! checker's judgment, not the lowering's. `DeclarationOutcome::Data` carries a
//! `DataIndex` into `LoweredModule::data`, so the outcome stays `Copy` and the
//! signature is shared, not cloned, with the checker's declaration. A generator
//! whose result applies the family to anything but its own parameters is an
//! indexed family and is declined as `OutOfFragment` with the `Indexed`
//! boundary; the constructor-block spelling and a field's attributes or grade
//! are declined by name
//! (`tests::members_outside_the_fragment_are_declined_by_name`); a constructor
//! named twice is `DuplicateDefinition`. Each of these is decided while the
//! declaration is collected, so the declaration records no half and its
//! attributes are not filed: a corpus source holding one stays pending.
//! Operation and rule members, `oper`, `op` and `rule`, are passed over: the
//! description route (the `description` module) reads them and holds any
//! refusal among them at the member, so the family keeps its generators.
//! Reversal: the indexed boundary lifts when the core's data former carries
//! indices.
//!
//! A constructor `C(e, …)` is a native constructor value, which names its whole
//! classifier, taken from the type its position states as the opening section
//! reads it.
//!
//! `case e -> T? { p => c, … }` compiles to a decision tree of native
//! eliminations by the pattern-matrix construction of Maranget's _Compiling
//! Pattern Matching to Good Decision Trees_ (ML 2008): a data case per
//! constructor column, a sum case per boolean column, and the prelude's integer
//! equality cased on per integer literal. Patterns nest: constructors,
//! variables, `_`, integer and boolean literals, or-patterns binding nothing,
//! and a pattern hole `?` or `?name` in any position, which leaves the leaf it
//! reaches stuck on a hole whose identity is the pattern's syntax node. The
//! scrutinee is never bound; each leaf substitutes its arm body's variables by
//! the tree binders that settled them, so an arm reached twice is copied, not
//! joined through a thunk whose type the checker would have to know. The data
//! case's motive is the written answer or the result of the function whose body
//! ends in the match, and a match that eliminates native data with neither is
//! unannotated. Rows exhausted before a leaf are `NonExhaustiveMatch`, classed
//! as malformed source; string patterns, as-patterns, an or-pattern binding a
//! variable and the view `with e` are declined by name. Reversal: a join point
//! earns its thunk once duplication costs more than binding the answer type at
//! every join.
//!
//! A match of no arms, `case e {}`, names no family to compile against, so it
//! reads its scrutinee's stated type, as a sum pattern reads its arity. Over a
//! data type with no constructor it lowers to that type's data case of no
//! branch; over a path type, to a data case of no branch whose admission the
//! checker decides by apartness (`gandr-core-checker`'s `former` § Apartness);
//! over a data type with a constructor it is `NonExhaustiveMatch`; over
//! anything else, `Void` among them, it is the case of no branches, the empty
//! sum's eliminator, which checks at any answer. The data case reads its
//! answer as any match does, `case e -> T {}` or the enclosing result type;
//! the empty sum's case takes none written, since no branch would answer it.
//!
//! **Choice.** The empty match read by its scrutinee's written type, so `data
//! Empty : Type {}` and a path between apart terms each have an eliminator.
//! **Alternatives.** One reading of `case e {}`, the empty sum's eliminator,
//! which leaves every empty nominal family without one; a reading by the
//! checked type, which the lowering does not compute. **Reversal.** A
//! scrutinee with no written type — a nested expression — takes the reading
//! once the lowering learns synthesized types.
//!
//! The tree forgets its patterns, so `OriginTable::case` keeps them: per match,
//! the `gandr_core_term` pattern table the arms are written in, one `ArmOrigin`
//! per arm alternative, and the syntax nodes of the scrutinee and of each
//! pattern and body, keyed by the tree's root. A live match and a hole report
//! read that one seam rather than parsing the tree back.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Carried;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::Value;
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
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use super::FormName;
use super::Former;
use super::Function;
use super::LabelRead;
use super::LabelSite;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Sink;
use super::Site;
use super::Stretch;
use super::arity;
use super::arity::Dependent;
use super::closed;
use super::exhausted;
use super::exits;
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
use crate::module::Generators;
use crate::module::Half;
use crate::module::Operand;
use crate::module::SlotIndex;
use crate::module::WordsForm;
use crate::module::closed_term;
use crate::origin::ArmOrigin;
use crate::origin::CaseOrigin;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::origin::PatternReading;
use crate::origin::PatternSpan;
use crate::origin::scrutinised;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;
use crate::resolve::TypeFormer;
use crate::resolve::binder_site;
use crate::resolve::binder_type;
use crate::resolve::type_former;

#[cfg(test)]
pub(super) mod tests;

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
    /// Why a match of no arms switches on no data.
    pub mod switched {
        /// Its scrutinee states no data type and no path type.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The scrutinee is no name written with a type.
            Untyped,
            /// The stated type is another former: the empty sum among them.
            Otherwise,
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
    /// What the position answers of the type the node writes.
    pub over: Over,
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
/// - hypothesis: L3 — `loop => back(loop)` takes its endpoints from the path
///   over the loop, and a written answer from itself.
/// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Over
{
    /// The written type itself.
    Written,
    /// The path over a loop of a case answering the written type `B`:
    /// `Path(B, y, y)`, `y` the case's answer at the loop's point, which the
    /// arm's frame `arm` binds innermost. Once the case is minted the lowering
    /// substitutes for `y` the answer [`gandr_core_term::identity::answer_at`]
    /// reads at the point.
    Loop
    {
        /// The arm's frame.
        arm: Frame,
    },
    /// The returner over the written value type, `-F B`: the answer of a
    /// thunk's body whose signature writes the alias `() => B`.
    Returning,
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
/// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
/// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers`
/// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Classifier
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
    /// The family's one classifier, which the lowering inserts: the family
    /// has no parameters.
    Inserted,
}

/// A form with its parentheses stripped, as [`Lowerer::unwrapped`] reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the operands keep source order.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::unwrapped`].
/// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Unwrapped
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
/// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Argued
{
    /// The family's position in the collection's data list.
    pub form: usize,
    /// The argument's place among the family's parameters.
    pub place: usize,
    /// The application's arguments, in the operand store.
    pub applied: Stretch,
}

/// One field of one generator of a written data family.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `form` is the family's position in the collection's data list,
///   `tag` the generator's among the family's, and `index` the field's among
///   the generator's.
/// - executable: none — the coordinates hold no collection to check them
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::field_classifier`].
/// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FieldAt
{
    /// The family's position in the collection's data list.
    form: usize,
    /// The generator's tag.
    tag: usize,
    /// The field's position among the generator's.
    index: usize,
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
    /// Where its classifier comes from.
    pub classifier: Classifier,
}

/// One pattern, as the match compiler reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a constructor's, a tuple's and a record's fields are a stretch of
///   the match's part store, a record's labels one per field; a binder numbers
///   its arm variable.
/// - executable: none — the pattern holds no store to check its stretch
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses compile every shape into the tree they
///   assert.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::telescope_patterns_split_and_project`
/// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Matcher
{
    /// `_`: matches anything, binds nothing.
    Wild,
    /// A name: matches anything and binds the arm variable numbered here.
    Binder(VariableAt),
    /// `?`: a pattern the author has not written.
    Hole(HoleId),
    /// A constructor of the family `form` reads its generators from, with its
    /// fields.
    Constructor
    {
        /// Where the family's generators are read from.
        form: Generators,
        /// The constructor's tag.
        tag: usize,
        /// The field patterns, in the part store.
        fields: Stretch,
    },
    /// `true` or `false`.
    Boolean(bool),
    /// An integer literal.
    Integer(Literal),
    /// A positional telescope `#{p, …}` or a tuple `(p, …)`: its components,
    /// in index order.
    Tuple
    {
        /// The component patterns, in the part store.
        fields: Stretch,
        /// Whether its split reads the motive at the scrutinee: a link of a
        /// dependent record whose label a later entry names.
        dependent: Dependent,
    },
    /// A labelled telescope `#{.l = p, …}`: the fields it names.
    Record
    {
        /// The labels, one per field.
        labels: Vec<FieldLabel>,
        /// The field patterns, in the part store.
        fields: Stretch,
    },
    /// An injection `+{ .l = p }` into the summand `summand` of a sum of
    /// `arity` summands.
    Injection
    {
        /// The summand's index.
        summand: usize,
        /// How many summands the sum has.
        arity: usize,
        /// The payload's pattern.
        field: PatternAt,
    },
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
/// - witness: `lower::native::tests::telescope_patterns_split_and_project`
/// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
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
        /// The family, when the family over no arguments classifies its
        /// constructors.
        family: Maybe<ConstantIndex, bare::Absent>,
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
    /// Each constructor arm's body.
    bodies: Vec<NodeIndex>,
    /// The decision tree.
    tests: Vec<Test>,
    /// The loop arms, one per loop of the root's sort in the order its loop
    /// branches follow its constructors' branches, or none.
    loops: Vec<LoopArm>,
    /// What the origin table keeps of the arms.
    origin: CaseOrigin,
    /// Each constructor arm's variables, in the order its leaves settle
    /// them.
    variables: Vec<Vec<Placed>>,
}

/// One loop arm of a match, `loop => e`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `words` and `generator` name a loop the lowering collected.
/// - executable: none — the indices name collected words.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::loop_arms`].
/// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LoopArm
{
    /// The words the loop is a letter of, by their position among the
    /// collected words.
    words: usize,
    /// The loop's position among its words' cells.
    generator: usize,
    /// The arm's body.
    body: NodeIndex,
    /// The arm's pattern, the loop's name.
    named: Placed,
}

/// The loop an arm's whole pattern names.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `words` and `generator` name a loop the lowering collected.
/// - executable: none — the indices name collected words.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::loop_named`].
/// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NamedLoop
{
    /// The words the loop is a letter of, by their position among the
    /// collected words.
    words: usize,
    /// The loop's position among its words' cells.
    generator: gandr_kernel_term::CellIndex,
}

/// What a pattern's name is to the modules enclosing it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Declared
{
    /// Some enclosing module binds the name to a loop.
    Loop,
    /// None does: the name binds a pattern variable.
    Binder,
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
    /// The spans inside a pattern that answer apart from its own: the name a
    /// constructor pattern applies, a word pattern's letter, a sum pattern's
    /// key, an or-pattern.
    spelled: Vec<(PatternAt, ByteSpan, PatternReading)>,
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
    /// A constructor of the family whose generators are read from here.
    Data(Generators),
    /// A boolean.
    Boolean,
    /// This integer.
    Integer(Literal),
    /// A tuple of this many components, split dependently or not.
    Tuple(usize, Dependent),
    /// A record.
    Record,
    /// An injection into a sum of this many summands.
    Sum(usize),
}

/// Whether a queued pattern is the label tile a punned telescope entry binds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Punned(bool);

/// Whether a word's letter is a loop's inverse rather than the loop.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Inverse(bool);

/// How many components a split binds, or how many summands a sum switch
/// cases on.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Width(usize);

/// A pattern the reader has allocated and not yet read.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the slot is the pattern's place in the match's store.
/// - executable: none — the record holds no store.
///
/// # Adequacy
/// - hypothesis: L3 — a sum pattern nested in a telescope pattern reads its
///   arity from the component type its scrutinee's type states.
/// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Queued
{
    /// The pattern's syntax: a form, or the label tile a pun binds.
    at: Placed,
    /// The slot it fills.
    slot: PatternAt,
    /// The type its position states, when the source wrote one.
    stated: Maybe<NodeIndex, binder_type::Absent>,
    /// Whether `at` is a punned label.
    punned: Punned,
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
                let bound = self.scope.extend_typed(
                    frame,
                    name,
                    parameter.classifier.node,
                    Maybe::Present(parameter.named.span),
                );
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
            (Some(&found), Maybe::Present(own)) if found.family < own => Maybe::Present(found),
            _ => Maybe::Absent(constructed::Absent::Unnamed),
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
    ///   under the site's frame. Its classifier is the annotation the site
    ///   stands under, or the signature of the definition it is; else, for a
    ///   family with parameters, the value type the answer of its position
    ///   returns — a tail's, or a `pure`'s or `return`'s operand's — else its
    ///   place in the data family application it is an argument of, the
    ///   constructor then awaiting that application's mint; else the one the
    ///   constructor around it gives the field it stands in; else, for a family
    ///   without, the one the lowering inserts. A field typed by the family
    ///   over its own parameters takes the constructor's classifier, and one
    ///   typed by a parameter the argument a written classifier gives it.
    /// - provides: constructor application, bare and called.
    /// - fails: yields the arity refusal for a field count other than the
    ///   constructor's; the wrong-sort refusal outside value position; the
    ///   unannotated refusal for a constructor of a family with parameters
    ///   whose position states no type and that stands at no data family's
    ///   argument place.
    /// - panics: none.
    ///
    /// # Errors
    /// The constructor's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nullary, unary and three-field constructors, a wrong
    ///   field count and a parameterised family without its annotation, each
    ///   asserted as the exact plan's core node or refusal; a parameterised
    ///   family at a signed thunk's tail, under a `run` and as a definition,
    ///   its recursive field and its parameter field classified with it; and
    ///   one written as a data family's argument, classified by its place.
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers`
    /// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument`
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
        let parameters = match constructor.form {
            Generators::Written(form) => self
                .collected
                .data
                .get(form)
                .map_or(0_usize, |written| written.parameters.len()),
            Generators::Presentation | Generators::Words(_) => 0_usize,
        };
        // A constructor standing where a body ends is the value the body
        // returns, of the type the body answers.
        let answered = self
            .answers
            .get(&site.at.node)
            .filter(|_| self.exits.contains(&site.at.node));
        let classifier = match (
            self.classifiers.get(&site.at.node),
            answered,
            self.argued.get(&site.at.node),
            self.inherited.get(&site.at.node),
        ) {
            (Some(&written), ..) => Classifier::Written(written),
            (None, ..) if parameters == 0 => Classifier::Inserted,
            (None, Some(&answer), ..) => Classifier::Answered { answer, frame },
            (None, None, Some(&argued), _) => {
                let _first = self.awaiting.insert(site.at.node);
                Classifier::Slot(argued)
            },
            (None, None, None, Some(&inherited)) => inherited,
            (None, None, None, None) => return Err(site.out(FragmentBoundary::Unannotated)),
        };
        let family = self
            .collected
            .slots
            .get(usize::from(constructor.family))
            .map_or_else(|| ConstantIndex::from(0_usize), |slot| slot.constant);
        for (index, position) in (fields.start .. fields.end).enumerate() {
            if let Some(&field) = self.operands.get(position) {
                self.read(field, Reading::Value(frame));
                if let Generators::Written(form) = constructor.form
                    && classifier != Classifier::Inserted
                    && let Maybe::Present(inherited) = self.field_classifier(
                        FieldAt {
                            form,
                            tag: constructor.tag,
                            index,
                        },
                        classifier,
                    )?
                {
                    let _first = self.inherited.insert(field, inherited);
                }
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

    /// The classifier the field `at` names takes from its constructor's,
    /// `classifier`.
    ///
    /// # Specification
    /// - requires: `at.form` and `at.tag` name a generator the collection read.
    /// - ensures: `classifier` itself when the field's written type, its
    ///   parentheses stripped, is the family applied to its own parameters in
    ///   order, or the family bare when it has none; the argument a written
    ///   classifier, an application of the family, gives the parameter when the
    ///   field's type is that parameter; the unclassified absence otherwise.
    /// - provides: the classifier a constructor written in a field takes.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance; the refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list's tail and head, written and answered.
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(found)) => found == classifier || matches!(found, Classifier::Written(_)),
        | Ok(Maybe::Absent(_)) | Err(_) => true,
    })]
    fn field_classifier(
        &mut self,
        at: FieldAt,
        classifier: Classifier,
    ) -> Result<Maybe<Classifier, inherited::Absent>, LoweringRefusal<'source>>
    {
        let unclassified = Maybe::Absent(inherited::Absent::Unclassified);
        let Some(data) = self.collected.data.get(at.form)
        else {
            return Ok(unclassified);
        };
        let Some(field) = data
            .generators
            .get(at.tag)
            .and_then(|generator| generator.fields.get(at.index))
        else {
            return Ok(unclassified);
        };
        let named: Vec<SurfaceName<'source>> = data
            .parameters
            .iter()
            .map(|parameter| self.name_at(parameter.named))
            .collect();
        let family = self
            .collected
            .slots
            .get(usize::from(data.slot))
            .map(|slot| slot.name);
        let Maybe::Present(typed) = self.unwrapped(field.node)?
        else {
            return Ok(unclassified);
        };
        let spelled = |lowerer: &Self, node: NodeIndex| {
            SurfaceName::from(
                lowerer
                    .tree
                    .fragment(node)
                    .unwrap_or_else(|| SourceFragment::from("")),
            )
        };
        let head = typed.keyword.map(|at| self.name_at(at));
        let own = spelled(self, typed.node);
        let uniform = if typed.former == Former::TypeApplication {
            head.is_some()
                && head == family
                && typed
                    .operands
                    .iter()
                    .map(|&node| spelled(self, node))
                    .eq(named.iter().copied())
        }
        else {
            typed.former == Former::TypeHead && named.is_empty() && Some(own) == family
        };
        if uniform {
            return Ok(Maybe::Present(classifier));
        }
        let Some(parameter) = named.iter().position(|name| *name == own)
        else {
            return Ok(unclassified);
        };
        let Classifier::Written(written) = classifier
        else {
            return Ok(unclassified);
        };
        let Maybe::Present(applied) = self.unwrapped(written)?
        else {
            return Ok(unclassified);
        };
        Ok(match applied.operands.get(parameter) {
            Some(&argument) if applied.former == Former::TypeApplication => {
                Maybe::Present(Classifier::Written(argument))
            },
            Some(_) | None => unclassified,
        })
    }

    /// Give each definition its signature as the type its constructors are
    /// checked against: a thunk's body the answer the signature states, and
    /// any other definition the signature itself.
    ///
    /// # Specification
    /// - requires: the collection has read every slot.
    /// - ensures: for each slot whose signature and definition are both written
    ///   types and terms: a signature `+U C`, its parentheses stripped, answers
    ///   the definition's thunk body with `C`, and the alias `() => B` with `-F
    ///   B`, each read under the outermost frame; any other signature
    ///   classifies the definition.
    /// - provides: the expected type a constructor takes its classifier from
    ///   where the source states one only in the signature.
    /// - fails: as [`Self::unwrapped`].
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk signed `+U (-F T)` and `() => T`, and a
    ///   definition signed `T`, each over a parameterised family's constructor.
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers`
    #[spec(
        captures: before = (self.inherited.len(), self.thunked.len()),
        ensures: |ret| ret.is_err() || (self.inherited.len() >= before.0 && self.thunked.len() >= before.1),
    )]
    pub(super) fn sign_definitions(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        let signed: Vec<(NodeIndex, NodeIndex)> = self
            .collected
            .slots
            .iter()
            .filter_map(|slot| {
                if let (
                    Maybe::Present(Half {
                        operand: Operand::Written(signature),
                        ..
                    }),
                    Maybe::Present(Half {
                        operand: Operand::Written(definition),
                        ..
                    }),
                ) = (slot.signature, slot.definition)
                {
                    Some((definition.node, signature.node))
                }
                else {
                    None
                }
            })
            .collect();
        for (definition, signature) in signed {
            let Maybe::Present(written) = self.unwrapped(signature)?
            else {
                continue;
            };
            let thunked = matches!(written.former, Former::ThunkType | Former::ReturnerType)
                && written.keyword.is_some_and(|at| {
                    type_former(self.name_at(at)) == Maybe::Present(TypeFormer::Thunk)
                });
            let answer = match *written.operands.as_slice() {
                [body] if thunked => Some(Answer {
                    node: body,
                    frame: Frame::Outermost,
                    over: Over::Written,
                }),
                [domain, codomain] if written.former == Former::ValueFunctionType => {
                    match self.unwrapped(domain)? {
                        Maybe::Present(Unwrapped {
                            former: Former::ParenthesizedType,
                            ref operands,
                            ..
                        }) if operands.is_empty() => Some(Answer {
                            node: codomain,
                            frame: Frame::Outermost,
                            over: Over::Returning,
                        }),
                        Maybe::Present(_) | Maybe::Absent(_) => None,
                    }
                },
                _ => None,
            };
            if let Some(answer) = answer {
                let _first = self.thunked.insert(definition, answer);
            }
            else {
                let _first = self
                    .inherited
                    .insert(definition, Classifier::Written(signature));
            }
        }
        Ok(())
    }

    /// The form `node` writes once its parentheses are stripped: its former,
    /// the first tile it is written with and its operands.
    ///
    /// # Specification
    /// - requires: nothing; a node the tree does not hold has no form.
    /// - ensures: a parenthesised type around one operand read through to the
    ///   operand; the form's former, first tile and operands, left to right;
    ///   the unformed absence for a node that is no form.
    /// - provides: the syntactic reading a signature and a field type are read
    ///   by.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance; the refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Termination
    /// Every turn spends one unit of the lowerer's allowance and steps to the
    /// operand of the node it read, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parenthesised application and a bare head.
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers`
    #[spec(captures: before = self.fuel.remaining, ensures: self.fuel.remaining <= before)]
    pub(super) fn unwrapped(
        &mut self,
        mut node: NodeIndex,
    ) -> Result<Maybe<Unwrapped, inherited::Absent>, LoweringRefusal<'source>>
    {
        loop {
            self.fuel.spend()?;
            let Some(tree_node) = self.tree.node(node)
            else {
                return Ok(Maybe::Absent(inherited::Absent::Unclassified));
            };
            let Shape::Form { former, .. } = shape_of(self.pbg, tree_node)?
            else {
                return Ok(Maybe::Absent(inherited::Absent::Unclassified));
            };
            let mut scratch = core::mem::take(&mut self.scratch);
            let read = read_pieces(self.pbg, self.tree, node, &mut scratch);
            let operands: Vec<NodeIndex> = scratch
                .pieces
                .iter()
                .filter_map(|piece| match *piece {
                    Piece::Operand(operand) => Some(operand.node),
                    Piece::Tile { .. } => None,
                })
                .collect();
            let keyword = scratch.pieces.iter().find_map(|piece| match *piece {
                Piece::Tile { at, .. } => Some(at),
                Piece::Operand(_) => None,
            });
            self.scratch = scratch;
            read?;
            if former == Former::ParenthesizedType
                && let [inner] = *operands.as_slice()
            {
                node = inner;
                continue;
            }
            return Ok(Maybe::Present(Unwrapped {
                node,
                former,
                keyword,
                operands,
            }));
        }
    }

    /// Classify the word `letter ∷ rest`, written at `site`.
    ///
    /// # Specification
    /// - requires: `letter` and `rest` are the cons's operands, in order.
    /// - ensures: the constructor of the words `letter` names, as
    ///   [`Self::written_letter`] reads it, applied to `rest`, as
    ///   [`Self::construct`] plans it; the letter, and the name inside an
    ///   inverse letter, recorded with its words so each answers at the path
    ///   type at their point.
    /// - fails: the unadmitted refusal at the cons for a left operand that is
    ///   no loop and no loop's inverse; [`Self::construct`]'s refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The cons's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a letter and an inverse cons onto a word, each letter
    ///   and the name inside the inverse labelled at the path type, and a left
    ///   operand that is no loop is refused.
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Constructor(_))))]
    pub(super) fn cons(
        &mut self,
        site: Site,
        letter: Placed,
        rest: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(constructor) = self.written_letter(site, letter)?
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        if let Generators::Words(words) = constructor.form {
            self.lettered.push((letter.span, words));
            if constructor.named.span != letter.span {
                self.lettered.push((constructor.named.span, words));
            }
        }
        let start = self.operands.len();
        self.operands.push(rest.node);
        let fields = Stretch {
            start,
            end: self.operands.len(),
        };
        self.construct(site, constructor, fields)
    }

    /// The letter a cons's left operand `at`, written under `site`, spells: a
    /// loop's name its letter, and `back(g)`, `g` a loop's name, its inverse.
    ///
    /// # Specification
    /// - requires: `at` is a cons's left operand.
    /// - ensures: as [`Self::loop_letter`], for the name `at` is or the one
    ///   `back` applies to; `back` is read by its spelling, whatever a
    ///   declaration of that name binds, since only a letter conses. The
    ///   unnamed absence for any other form.
    /// - fails: [`Self::loop_letter`]'s refusals;
    ///   [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::cons`].
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    #[spec(ensures: |ret| match ret {
        Ok(Maybe::Present(constructor)) => constructor.arity == 1 && matches!(constructor.form, Generators::Words(_)),
        _ => true,
    })]
    fn written_letter(
        &mut self,
        site: Site,
        at: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let unnamed = Ok(Maybe::Absent(constructed::Absent::Unnamed));
        let Some(node) = self.tree.node(at.node)
        else {
            return unnamed;
        };
        let (cell, inverse) = match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::Name,
                ..
            } => (at, false),
            Shape::Form {
                former: Former::Call,
                ..
            } => {
                let mut pieces = core::mem::take(&mut self.scratch);
                let read = read_pieces(self.pbg, self.tree, at.node, &mut pieces);
                let mut operands = pieces.pieces.iter().filter_map(|piece| match *piece {
                    Piece::Operand(operand) => Some(operand),
                    Piece::Tile { .. } => None,
                });
                let written = (operands.next(), operands.next(), operands.next());
                self.scratch = pieces;
                read?;
                let (Some(head), Some(cell), None) = written
                else {
                    return unnamed;
                };
                if self.text_at(head).as_ref() != super::identity::BACK
                    || !matches!(self.form_at(cell)?, Some((_, Former::Name)))
                {
                    return unnamed;
                }
                (cell, true)
            },
            Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                return unnamed;
            },
        };
        self.loop_letter(site, cell, Inverse(inverse))
    }

    /// The letter of the loop `cell` names, written under `site`, or its
    /// inverse when `inverse` holds.
    ///
    /// # Specification
    /// - requires: `cell` is a name's own node or tile inside the form at
    ///   `site`, which the name is resolved under: a name inside a letter is
    ///   owned by no declaration until the form around it is read.
    /// - ensures: when the name resolves to a loop's binding, the constructor
    ///   of the loop's words whose tag is the loop's letter, or its inverse,
    ///   with one field, the rest of the word; the unnamed absence for a name
    ///   that resolves to anything else or to nothing.
    /// - fails: the name's resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::cons`].
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    #[spec(ensures: |ret| match ret {
        Ok(Maybe::Present(constructor)) => constructor.arity == 1 && constructor.named == cell,
        _ => true,
    })]
    fn loop_letter(
        &mut self,
        site: Site,
        cell: Placed,
        inverse: Inverse,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let named = Site {
            at: Placed {
                node: site.at.node,
                span: cell.span,
            },
            ..site
        };
        let name = self.name_at(cell);
        let Maybe::Present(super::Resolved::Declaration { constant, .. }) =
            self.resolve_name(named, site.reading.frame(), name)?
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };
        let Some(Maybe::Present(Half {
            operand: Operand::Loop { words, generator },
            ..
        })) = self
            .collected
            .slots
            .get(usize::from(constant))
            .map(|slot| slot.definition)
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };
        let Some(family) = self.collected.words.get(words).map(|written| written.slot)
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };
        let tag = if inverse.0 {
            gandr_core_term::FreeCells::inverse(gandr_core_term::CellIndex::from(generator))
        }
        else {
            gandr_core_term::FreeCells::letter(gandr_core_term::CellIndex::from(generator))
        };

        Ok(Maybe::Present(Constructor {
            family,
            form: Generators::Words(words),
            tag: usize::from(tag),
            arity: 1,
            named: cell,
        }))
    }

    /// The empty word `here(point)` is, when `point` spells the point a
    /// family's loops are at.
    ///
    /// # Specification
    /// - requires: `point` is the operand of a `here` call.
    /// - ensures: the empty word of the first words whose point `point` spells
    ///   as a closed term over their family's constructors, each written node
    ///   of the point recorded with the words so it answers at their family;
    ///   the unnamed absence when no words are at it, and `here(point)` stays
    ///   reflexivity.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `here` at a looped point is the empty word, its point
    ///   labelled at the family, and at any other point reflexivity.
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    #[spec(
        captures: before = self.pointed.len(),
        ensures: |ret| match ret {
            Ok(Maybe::Present(constructor)) => constructor.arity == 0 && constructor.tag == 0
                && matches!(constructor.form, Generators::Words(_)) && self.pointed.len() > before,
            _ => self.pointed.len() == before,
        },
    )]
    pub(super) fn looped_point(
        &mut self,
        point: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let mut found = None;
        for (index, words) in self.collected.words.iter().enumerate() {
            let family = Generators::Written(words.family);
            let tag_of = |name: SourceFragment<'source>| {
                self.collected
                    .constructors
                    .get(&SurfaceName::from(name))
                    .filter(|constructor| constructor.form == family)
                    .map(|constructor| (constructor.tag, constructor.arity))
            };
            if let Maybe::Present(term) = closed_term(self.pbg, self.tree, point, &tag_of)?
                && term.nodes == words.point
            {
                found = Some((index, words.slot, term.written));
                break;
            }
        }
        let Some((index, family, written)) = found
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };
        self.pointed
            .extend(written.iter().map(|node| (node.span, index)));

        Ok(Maybe::Present(Constructor {
            family,
            form: Generators::Words(index),
            tag: 0,
            arity: 0,
            named: point,
        }))
    }

    /// Classify `(e : T)`, its `(` and `e` read, the cursor at its `:`.
    ///
    /// # Specification
    /// - requires: `run` is the parenthesised expression's first hole and
    ///   `cursor` stands at its `:`.
    /// - ensures: an annotation over a constructor standing as a value reads
    ///   `T` as a value type under the same frame, records it as the
    ///   constructor's classifier, and adopts the constructor; an annotation
    ///   over an injection does the same, the injection reading its summand's
    ///   label among the sum `T` states. An annotation standing at a tail,
    ///   where a path through a body ends, is a value there and takes the
    ///   `return` its polarity names.
    /// - fails: the unadmitted annotation refusal for any other annotation; the
    ///   hole's and the tiles' own faults.
    /// - panics: none.
    ///
    /// # Errors
    /// The annotation's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an annotated parameterised constructor lowers over
    ///   the annotation's type, at a value position and at a tail, and an
    ///   annotated name is refused.
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    /// - witness: `lower::arity::tests::an_injection_takes_its_index_from_its_label`
    /// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Transparent(_))))]
    pub(super) fn annotated(
        &mut self,
        site: Site,
        run: Run,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let declined = site.folded(FormName::ANNOTATION, FragmentBoundary::Unadmitted);
        let Run::One(inner) = run
        else {
            return Err(declined);
        };
        let frame = match site.reading {
            Reading::Value(frame) => frame,
            Reading::Computation(_)
                if self.exits.contains(&site.at.node) || self.results.contains(&site.at.node) =>
            {
                self.require(site, Produced::Value)?
            },
            Reading::Unread
            | Reading::ValueType(_)
            | Reading::CompType(_)
            | Reading::Computation(_)
            | Reading::Head(_)
            | Reading::Result(_)
            | Reading::Function => return Err(declined),
        };
        let injected = matches!(self.form_at(inner)?, Some((_, Former::Injection)));
        if !injected && let Maybe::Absent(_) = self.applied_constructor(site, inner)? {
            return Err(declined);
        }
        let _colon = cursor.tile(TileName::COLON);
        let classifier = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        exhausted(site, &cursor)?;
        self.read(classifier.node, Reading::ValueType(frame));
        self.read(inner.node, Reading::Value(frame));
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
                    Some(&Piece::Operand(head)) => Some(head),
                    Some(&Piece::Tile { .. }) | None => None,
                }
            });
        self.scratch = scratch;
        head?.map_or(Ok(bare), |head| self.constructor_head(site, head))
    }

    /// The number of parameters of the data family declared at `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the parameter count of the data declaration whose slot takes
    ///   `constant`, and none for `Sig`; the undeclared absence for any other
    ///   declaration.
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
            Some(Maybe::Present(Half {
                operand: Operand::Data(form),
                ..
            })) => self
                .collected
                .data
                .get(form)
                .map_or(Maybe::Absent(family::Absent::Undeclared), |written| {
                    Maybe::Present(OperandCount::from(written.parameters.len()))
                }),
            Some(Maybe::Present(Half {
                operand: Operand::Code,
                ..
            })) => Maybe::Present(OperandCount::from(0_usize)),
            _ => Maybe::Absent(family::Absent::Undeclared),
        }
    }

    /// Classify the data family at `constant`, of `arity` parameters,
    /// applied to the arguments `applied` holds in the operand store.
    ///
    /// # Specification
    /// - ensures: the family stands as a value type over its arguments, each
    ///   read as a value under the site's frame and recorded at its place among
    ///   the family's parameters.
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
        let form = self.collected.data.iter().position(|form| {
            self.collected
                .slots
                .get(usize::from(form.slot))
                .is_some_and(|slot| slot.constant == constant)
        });
        for (place, position) in (applied.start .. applied.end).enumerate() {
            if let Some(&argument) = self.operands.get(position) {
                if let Some(form) = form {
                    let _first = self.argued.insert(argument, Argued {
                        form,
                        place,
                        applied,
                    });
                }
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
    /// - ensures: a match of no arms, `case e {}`, is planned as
    ///   [`Self::empty_case`] plans it: the data switch of no branches over a
    ///   scrutinee stated at a data type or a path type, and else the case of
    ///   no branches, the eliminator of the empty sum `Void`; otherwise the
    ///   match stands as a computation, its arms' patterns read and compiled to
    ///   a decision tree over the scrutinee, read as a value under the site's
    ///   frame; the written answer is read where a result is read, and else the
    ///   answer the position states is taken; each arm body is read as a
    ///   computation under the case's frame, the tree's anonymous binders and
    ///   its own variables, answers what the match does, and takes the paths
    ///   through the match's position.
    /// - provides: the reading of `case`.
    /// - fails: the wrong-sort refusal outside computation position; the view
    ///   form `case … with` by the view's name; a match of no arms as
    ///   [`Self::empty_case`] refuses it; a written answer on a match whose
    ///   arms continue a block as joining it; a pattern the fragment does not
    ///   read by its own name; a pattern of the wrong kind for its column as
    ///   the wrong sort; a variable bound twice in one pattern; a
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
    /// - witness: `lower::native::tests::a_match_of_no_arms_eliminates_the_empty_sum`
    /// - witness: `lower::exits::tests::a_match_continuing_its_block_answers_what_the_block_does`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&(Plan::Case(_) | Plan::EmptyCase(_)))))]
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
            Maybe::Present(_) => Maybe::Present(site.one(cursor.operands())?),
            Maybe::Absent(_) => Maybe::Absent(answered::Absent::Unstated),
        };
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let mut arms: Vec<(Placed, Placed)> = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let _bar = cursor.tile(TileName::BAR);
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
            return self.empty_case(site, frame, scrutinee, written);
        }
        if self.joined.contains(&site.at.node)
            && let Maybe::Present(stated) = written
        {
            return Err(LoweringRefusal::OutOfFragment {
                span: stated.span,
                form: FormName::CASE,
                sort: site.reading.sort(),
                boundary: FragmentBoundary::JoinsBlock,
            });
        }
        // A loop's name as an arm's whole pattern names the loop's arm, never
        // a variable, and answers as the loop does; the other arms compile to
        // the tree.
        let mut looped = Vec::new();
        let mut constructed = Vec::with_capacity(arms.len());
        for &(pattern, body) in &arms {
            match self.loop_named(site, pattern)? {
                Maybe::Present(NamedLoop { words, generator }) => {
                    self.lettered.push((pattern.span, words));
                    looped.push(LoopArm {
                        words,
                        generator: usize::from(generator),
                        body: body.node,
                        named: pattern,
                    });
                },
                Maybe::Absent(_) => constructed.push((pattern, body)),
            }
        }
        let arms = constructed;
        let mut patterns = Written::default();
        let mut rows = Vec::new();
        let mut variables: Vec<Vec<Placed>> = Vec::with_capacity(arms.len());
        let mut kept = CaseOrigin {
            written: site.at.node,
            scrutinee: scrutinee.node,
            scrutinised: Maybe::Absent(scrutinised::Absent::Unminted),
            patterns: Patterns::new(),
            arms: Vec::new(),
            spans: Vec::new(),
        };
        let stated = self.scrutinee_type(frame, scrutinee)?;
        let mut roots = Vec::new();
        for (arm, &(pattern, body)) in arms.iter().enumerate() {
            let arm = ArmAt(arm);
            let alternatives = self.alternatives(pattern)?;
            let several = alternatives.len() > 1;
            let mut bound = Vec::new();
            for (place, alternative) in alternatives.into_iter().enumerate() {
                let mut named = Vec::new();
                let root = self.pattern(site, alternative, stated, &mut patterns, &mut named)?;
                if several && !named.is_empty() {
                    return Err(LoweringRefusal::OutOfFragment {
                        span: pattern.span,
                        form: FormName::OR_PATTERN,
                        sort: site.reading.sort(),
                        boundary: FragmentBoundary::Unadmitted,
                    });
                }
                bound = named;
                if several && place == 0_usize {
                    patterns
                        .spelled
                        .push((root, pattern.span, PatternReading::Matched));
                }
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
        let loops = self.loop_arms(site, &tests, looped)?;
        let eliminates = tests.iter().any(|test| {
            matches!(
                *test,
                Test::Data { .. }
                    | Test::Split {
                        dependent: Dependent(true),
                        ..
                    }
            )
        });
        let answer = match written {
            Maybe::Present(node) => Maybe::Present(Answer {
                node: node.node,
                frame,
                over: Over::Written,
            }),
            Maybe::Absent(reason) => self
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
                inner = Frame::Inner(self.scope.extend(inner, name, Maybe::Present(binder.span)));
            }
            self.read(body.node, Reading::Computation(inner));
            if let Maybe::Present(stated) = answer {
                let _first = self.answers.insert(body.node, stated);
            }
            self.pass_paths(site.at.node, body.node);
        }
        // A loop arm reads the case's answer at its loop's point as a binder,
        // which the minted case replaces by that answer.
        for arm in &loops {
            let inner = Frame::Inner(self.scope.extend(
                frame,
                SurfaceName::from(""),
                Maybe::Absent(binder_site::Absent::Unwritten),
            ));
            self.read(arm.body, Reading::Computation(inner));
            if let Maybe::Present(stated) = answer {
                let _first = self.answers.insert(arm.body, Answer {
                    over: Over::Loop { arm: inner },
                    ..stated
                });
            }
            self.pass_paths(site.at.node, arm.body);
        }
        let index = CaseIndex(self.cases.len());
        self.cases.push(CaseForm {
            scrutinee: scrutinee.node,
            frame,
            answer,
            bodies: arms.iter().map(|&(_pattern, body)| body.node).collect(),
            tests,
            loops,
            origin: kept,
            variables,
        });
        self.plan(site, Plan::Case(index));

        Ok(())
    }

    /// Classify a match of no arms, `case e -> T? {}`, over `scrutinee` under
    /// `frame`, with the answer `written` when one is written.
    ///
    /// # Specification
    /// - requires: `site` is a match of no arms in term position, read under
    ///   `frame`.
    /// - ensures: over a scrutinee [`Self::empty_switch`] reads a data switch
    ///   for, the match is planned as that switch with no branch, its answer
    ///   the written one and else the one its position states, the written
    ///   answer read where a result is read; over any other scrutinee it is
    ///   planned as the case of no branches, the eliminator of the empty sum
    ///   `Void`. The scrutinee is read as a value under `frame` either way.
    /// - provides: the empty match: a data type with no constructor, and a path
    ///   the checker decides has no inhabitant, are eliminated by their own
    ///   switch, exhaustive with no branch, at any answer.
    /// - fails: as [`Self::empty_switch`] refuses the scrutinee's type; a
    ///   written answer on the case of no branches, which checks at any type; a
    ///   data switch whose answer neither the match nor its position states, as
    ///   unannotated.
    /// - panics: none.
    ///
    /// # Errors
    /// The match's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match of no arms over `Void`, over a data type with
    ///   no constructor, over a path and over a data type with a constructor
    ///   separate the empty sum's case, the data switch and the refusal.
    /// - witness: `lower::native::tests::a_match_of_no_arms_eliminates_the_empty_sum`
    /// - witness: `lower::native::tests::a_match_of_no_arms_switches_on_empty_data_and_on_a_path`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&(Plan::Case(_) | Plan::EmptyCase(_)))))]
    fn empty_case(
        &mut self,
        site: Site,
        frame: Frame,
        scrutinee: Placed,
        written: Maybe<Placed, answered::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let stated = self.scrutinee_type(frame, scrutinee)?;
        let Maybe::Present(family) = self.empty_switch(site, frame, stated)?
        else {
            if let Maybe::Present(stated) = written {
                return Err(LoweringRefusal::OutOfFragment {
                    span: stated.span,
                    form: FormName::CASE,
                    sort: site.reading.sort(),
                    boundary: FragmentBoundary::Unadmitted,
                });
            }
            self.read(scrutinee.node, Reading::Value(frame));
            self.plan(site, Plan::EmptyCase(scrutinee.node));
            return Ok(());
        };
        let answer = match written {
            Maybe::Present(node) => Maybe::Present(Answer {
                node: node.node,
                frame,
                over: Over::Written,
            }),
            Maybe::Absent(reason) => self
                .answers
                .get(&site.at.node)
                .copied()
                .map_or(Maybe::Absent(reason), Maybe::Present),
        };
        if let Maybe::Absent(_) = answer {
            return Err(site.out(FragmentBoundary::Unannotated));
        }
        self.read(scrutinee.node, Reading::Value(frame));
        if let Maybe::Present(node) = written {
            self.read(node.node, Reading::Result(frame));
        }
        let index = CaseIndex(self.cases.len());
        self.cases.push(CaseForm {
            scrutinee: scrutinee.node,
            frame,
            answer,
            bodies: Vec::new(),
            tests: Vec::from([Test::Data {
                level: TreeLevel::default(),
                depth: Depth::default(),
                family,
                branches: Vec::new(),
            }]),
            loops: Vec::new(),
            origin: CaseOrigin {
                written: site.at.node,
                scrutinee: scrutinee.node,
                scrutinised: Maybe::Absent(scrutinised::Absent::Unminted),
                patterns: Patterns::new(),
                arms: Vec::new(),
                spans: Vec::new(),
            },
            variables: Vec::new(),
        });
        self.plan(site, Plan::Case(index));

        Ok(())
    }

    /// The family of the data switch a match of no arms eliminates its
    /// scrutinee by, the scrutinee stated at `stated`.
    ///
    /// # Specification
    /// - requires: `site` is a match of no arms under `frame`; `stated` is its
    ///   scrutinee's written type, as [`Self::scrutinee_type`] reads it.
    /// - ensures: read through parentheses, a path type answers a switch over
    ///   no bare family, whose emptiness the checker decides; a type head, bare
    ///   or applied, naming a data declaration with no constructor answers a
    ///   switch over that family, bare when it takes no parameter. Any other
    ///   stated type, the empty sum among them, answers
    ///   [`switched::Absent::Otherwise`], and an unstated one
    ///   [`switched::Absent::Untyped`].
    /// - fails: [`LoweringRefusal::NonExhaustiveMatch`] at the match for a head
    ///   naming a data declaration with a constructor, which no arm covers; the
    ///   head's own resolution refusals; the allowance, one step per form read.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Termination
    /// Every round reads one form and descends only into the type its
    /// parentheses hold, a strict subtree, spending one step of the
    /// allowance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::empty_case`].
    /// - witness: `lower::native::tests::a_match_of_no_arms_switches_on_empty_data_and_on_a_path`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::NonExhaustiveMatch { span }) if span == site.at.span) || !matches!(ret, Err(LoweringRefusal::NonExhaustiveMatch { .. })))]
    fn empty_switch(
        &mut self,
        site: Site,
        frame: Frame,
        stated: Maybe<NodeIndex, binder_type::Absent>,
    ) -> Result<Maybe<Maybe<ConstantIndex, bare::Absent>, switched::Absent>, LoweringRefusal<'source>>
    {
        let otherwise = Ok(Maybe::Absent(switched::Absent::Otherwise));
        let Maybe::Present(mut at) = stated
        else {
            return Ok(Maybe::Absent(switched::Absent::Untyped));
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = loop {
            if let Err(refusal) = self.fuel.spend() {
                break Err(refusal);
            }
            let Some(tree) = self.tree.node(at)
            else {
                break Ok(None);
            };
            let placed = Placed::of(at, tree);
            let former = match self.form_at(placed) {
                Ok(Some((_name, former))) => former,
                Ok(None) => break Ok(None),
                Err(refusal) => break Err(refusal),
            };
            if former == Former::PathType {
                break Ok(Some(Maybe::Absent(bare::Absent::Parameterised)));
            }
            if former == Former::TypeHead {
                break Ok(Some(Maybe::Present(placed)));
            }
            if former != Former::ParenthesizedType && former != Former::TypeApplication {
                break Ok(None);
            }
            if let Err(refusal) = read_pieces(self.pbg, self.tree, at, &mut scratch) {
                break Err(refusal);
            }
            if former == Former::TypeApplication {
                break Ok(scratch.pieces.first().and_then(|piece| match *piece {
                    Piece::Tile { at: head, .. } => Some(Maybe::Present(head)),
                    Piece::Operand(_) => None,
                }));
            }
            let mut operands = scratch.pieces.iter().filter_map(|piece| match *piece {
                Piece::Operand(inner) => Some(inner),
                Piece::Tile { .. } => None,
            });
            match (operands.next(), operands.next()) {
                (Some(inner), None) => at = inner.node,
                (Some(_) | None, _) => break Ok(None),
            }
        };
        self.scratch = scratch;
        let head = match read? {
            Some(Maybe::Present(head)) => head,
            Some(Maybe::Absent(path)) => return Ok(Maybe::Present(Maybe::Absent(path))),
            None => return otherwise,
        };
        let named = Site {
            at: head,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let name = self.name_at(head);
        let Maybe::Present(super::Resolved::Declaration { constant, .. }) =
            self.resolve_name(named, frame, name)?
        else {
            return otherwise;
        };
        let Some(Maybe::Present(Half {
            operand: Operand::Data(form),
            ..
        })) = self
            .collected
            .slots
            .get(usize::from(constant))
            .map(|slot| slot.definition)
        else {
            return otherwise;
        };
        let Some(written) = self.collected.data.get(form)
        else {
            return otherwise;
        };
        if !written.generators.is_empty() {
            return Err(LoweringRefusal::NonExhaustiveMatch { span: site.at.span });
        }

        Ok(Maybe::Present(if written.parameters.is_empty() {
            Maybe::Present(constant)
        }
        else {
            Maybe::Absent(bare::Absent::Parameterised)
        }))
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

    /// The loop an arm's whole pattern names, when it is a name a loop binds.
    ///
    /// # Specification
    /// - requires: `pattern` is an arm's pattern of the match at `site`.
    /// - ensures: the position of the loop's words among the collected words
    ///   and the loop's position among its words' cells exactly when the
    ///   pattern is a name that resolves to a loop's binding; the unnamed
    ///   absence otherwise. A name no loop of the enclosing modules declares is
    ///   a binder and is never resolved, so a pattern variable spelled as a
    ///   later member or a recursive binder binds as it always has.
    /// - fails: the name's resolution refusals, for a name a loop declares, and
    ///   the tree's molds'.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `loop` names the circle's loop, and `x` binds.
    /// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| matches!(found, Maybe::Absent(_)) || !self.collected.words.is_empty()))]
    fn loop_named(
        &mut self,
        site: Site,
        pattern: Placed,
    ) -> Result<Maybe<NamedLoop, constructed::Absent>, LoweringRefusal<'source>>
    {
        if !matches!(self.form_at(pattern)?, Some((name, _)) if name == FormName::IDENTIFIER)
            || self.declares_a_loop(pattern, self.name_at(pattern))? == Declared::Binder
        {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        }
        Ok(match self.loop_letter(site, pattern, Inverse(false))? {
            Maybe::Present(Constructor {
                form: Generators::Words(words),
                tag,
                ..
            }) => gandr_core_term::FreeCells::generator(gandr_core_term::ConstructorTag::from(tag))
                .map_or(Maybe::Absent(constructed::Absent::Unnamed), |generator| {
                    Maybe::Present(NamedLoop { words, generator })
                }),
            Maybe::Present(_) => Maybe::Absent(constructed::Absent::Unnamed),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        })
    }

    /// Whether a loop named `name` is declared in a module enclosing the
    /// declaration that owns `at`, read off the collected names without
    /// resolving: a source with no loop answers at once.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Declared::Loop`] exactly when some module on the chain from
    ///   the owner's container out to the top level binds `name` to a loop's
    ///   slot.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk out spends
    ///   the fuel.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: the `loop` steps out one module per iteration, each step
    ///   spending fuel, never recursing.
    /// - measure: the modules between the owner and the top level.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `loop` names the circle's loop at the top level and
    ///   inside a module, while `kept` and `later` bind as pattern variables
    ///   beside a later member of the same name; a name read as a loop there
    ///   refuses a punned pattern.
    /// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
    #[spec(ensures: |ret| ret.as_ref().ok() != Some(&Declared::Loop) || !self.collected.words.is_empty())]
    fn declares_a_loop(
        &mut self,
        at: Placed,
        name: SurfaceName<'source>,
    ) -> Result<Declared, LoweringRefusal<'source>>
    {
        if self.collected.words.is_empty() {
            return Ok(Declared::Binder);
        }
        let Maybe::Present(own) = self.collected.owner_of(at.node)
        else {
            return Ok(Declared::Binder);
        };
        let mut container = self
            .collected
            .slots
            .get(usize::from(own))
            .map_or(crate::module::Container::TopLevel, |slot| slot.container);
        loop {
            self.fuel.spend()?;
            if let Some(&target) = self.collected.by_name.get(&(container, name))
                && let Some(Maybe::Present(Half {
                    operand: Operand::Loop { .. },
                    ..
                })) = self
                    .collected
                    .slots
                    .get(usize::from(target))
                    .map(|slot| slot.definition)
            {
                return Ok(Declared::Loop);
            }
            let crate::module::Container::Module(module) = container
            else {
                return Ok(Declared::Binder);
            };
            container = self
                .collected
                .structures
                .get(usize::from(module))
                .map_or(crate::module::Container::TopLevel, |structure| {
                    structure.container
                });
        }
    }

    /// The loop arms `written` of the match at `site`, in the order the loop
    /// branches of the tree `tests`' root follow its constructors' branches.
    ///
    /// # Specification
    /// - requires: `tests` is the match's compiled tree and `written` its loop
    ///   arms, in source order.
    /// - ensures: none for no loop arm; otherwise one arm per loop of the root
    ///   switch's sort, words by their position among the collected words and
    ///   loops in written order.
    /// - fails: [`LoweringRefusal::NonExhaustiveMatch`] when the root is no
    ///   switch on the scrutinee's constructors or a loop of its sort has no
    ///   arm; [`LoweringRefusal::DuplicateDefinition`] at a loop's second arm;
    ///   the wrong-sort refusal at an arm for a loop of another sort.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's loop arm follows its point's branch, and
    ///   a loop arm over a case with no loop arm owed is refused.
    /// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
    #[spec(captures: count = written.len(), ensures: |ret| ret.as_ref().map_or(true, |ordered| ordered.len() <= count))]
    fn loop_arms(
        &self,
        site: Site,
        tests: &[Test],
        written: Vec<LoopArm>,
    ) -> Result<Vec<LoopArm>, LoweringRefusal<'source>>
    {
        if written.is_empty() {
            return Ok(written);
        }
        let uncovered = LoweringRefusal::NonExhaustiveMatch { span: site.at.span };
        let Some(&Test::Data {
            level,
            family: Maybe::Present(family),
            ..
        }) = tests.first()
        else {
            return Err(uncovered);
        };
        if level != TreeLevel::default() {
            return Err(uncovered);
        }
        let mut owed = Vec::new();
        for (index, words) in self.collected.words.iter().enumerate() {
            let sort = self
                .collected
                .data
                .get(words.family)
                .and_then(|form| self.collected.slots.get(usize::from(form.slot)))
                .map(|slot| slot.constant);
            if sort == Some(family) {
                owed.extend((0 .. words.loops.len()).map(|generator| (index, generator)));
            }
        }
        if let Some(stray) = written
            .iter()
            .find(|arm| !owed.contains(&(arm.words, arm.generator)))
        {
            return Err(LoweringRefusal::OutOfFragment {
                span: stray.named.span,
                form: FormName::CASE,
                sort: site.reading.sort(),
                boundary: FragmentBoundary::WrongSort,
            });
        }
        let mut ordered = Vec::with_capacity(owed.len());
        for &(words, generator) in &owed {
            let mut matching = written
                .iter()
                .filter(|arm| arm.words == words && arm.generator == generator);
            let Some(&arm) = matching.next()
            else {
                return Err(uncovered);
            };
            if let Some(again) = matching.next() {
                return Err(LoweringRefusal::DuplicateDefinition {
                    span: again.named.span,
                    name: SurfaceName::from(self.text_at(again.named)),
                    first: arm.named.span,
                });
            }
            ordered.push(arm);
        }

        Ok(ordered)
    }

    /// Read the or-free pattern `root` of the match at `site` into
    /// `patterns`, numbering its variables into `named`; `stated` is the type
    /// the scrutinee's position states.
    ///
    /// # Specification
    /// - requires: `root` is an alternative of an arm of the match at `site`.
    /// - ensures: the root's position in `patterns`; every part after the
    ///   pattern holding it; each name bound once, numbered in source order.
    /// - fails: a pattern the fragment does not read, by its own name; a
    ///   constructor no earlier family declares, as unresolved; a constructor
    ///   applied to other than its arity; a sum pattern whose position states
    ///   no sum, as unannotated; a variable bound twice; a repair;
    ///   [`LoweringRefusal::WithoutK`] for `here`, reflexivity as a pattern.
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
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    /// - witness: `lower::identity::tests::matching_reflexivity_is_refused_as_k`
    #[spec(
        captures: before = patterns.shapes.len(),
        ensures: |ret| ret.as_ref().map_or(true, |&root| root == PatternAt(before) && patterns.shapes.len() > before),
    )]
    fn pattern(
        &mut self,
        site: Site,
        root: Placed,
        stated: Maybe<NodeIndex, binder_type::Absent>,
        patterns: &mut Written,
        named: &mut Vec<Placed>,
    ) -> Result<PatternAt, LoweringRefusal<'source>>
    {
        let first = PatternAt(patterns.shapes.len());
        patterns.shapes.push((root, Matcher::Wild));
        let mut work = Vec::from([Queued {
            at: root,
            slot: first,
            stated,
            punned: Punned(false),
        }]);
        let mut pieces = Pieces::new();
        while let Some(queued) = work.pop() {
            self.fuel.spend()?;
            let shape = if queued.punned.0 {
                self.binder(queued.at, named)?
            }
            else {
                self.pattern_shape(site, queued, &mut pieces, patterns, named, &mut work)?
            };
            if let Some(held) = patterns.shapes.get_mut(queued.slot.0) {
                held.1 = shape;
            }
        }

        Ok(first)
    }

    /// The binder the name written at `at` makes, numbered into `named`.
    ///
    /// # Specification
    /// - requires: `at` is a pattern name or a punned label of one pattern.
    /// - ensures: the binder of the next arm variable.
    /// - fails: [`LoweringRefusal::DuplicateDefinition`] for a name already
    ///   bound in the pattern.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::DuplicateDefinition`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name and a punned label each bind once.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    #[spec(captures: before = named.len(), ensures: |ret| ret.is_err() || (named.len() == before.saturating_add(1) && matches!(ret, Ok(Matcher::Binder(variable)) if variable.0 == before)))]
    fn binder(
        &self,
        at: Placed,
        named: &mut Vec<Placed>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
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

        Ok(Matcher::Binder(VariableAt(named.len().saturating_sub(1))))
    }

    /// The shape of the queued pattern, its field patterns allocated and
    /// queued on `work`.
    ///
    /// # Specification
    /// - requires: as [`Self::pattern`]; `pieces` is scratch.
    /// - ensures: as [`Self::pattern`], for one pattern; a telescope or tuple
    ///   pattern's components and a sum pattern's payload are queued with the
    ///   component's or summand's type the queued pattern's stated type writes,
    ///   when it writes one.
    /// - fails: as [`Self::pattern`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::pattern`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pattern`].
    /// - witness: `lower::native::tests::patterns_outside_the_fragment_are_declined_by_name`
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    #[spec(captures: before = patterns.shapes.len(), ensures: patterns.shapes.len() >= before)]
    fn pattern_shape(
        &mut self,
        site: Site,
        queued: Queued,
        pieces: &mut Pieces,
        patterns: &mut Written,
        named: &mut Vec<Placed>,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let at = queued.at;
        let Some(node) = self.tree.node(at.node)
        else {
            return Ok(Matcher::Wild);
        };
        let name = match shape_of(self.pbg, node)? {
            Shape::Form { name, .. } => name,
            Shape::Repair(repair) => {
                return Err(LoweringRefusal::MalformedForm {
                    span: at.span,
                    form: FormName::CASE,
                    fault: FormFault::Repaired(repair),
                });
            },
            Shape::Root | Shape::Layout => return Ok(Matcher::Wild),
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
            if self.text_at(at).as_ref() == super::identity::HERE {
                return match self.collected.words.len() {
                    0_usize => Err(LoweringRefusal::WithoutK { span: at.span }),
                    1_usize => Ok(Matcher::Constructor {
                        form: Generators::Words(0),
                        tag: 0,
                        fields: allocated(patterns, work, &[]),
                    }),
                    _ => Err(here.out(FragmentBoundary::Unannotated)),
                };
            }
            // A loop's name in a pattern names the loop, never a variable; a
            // loop is matched only as an arm's whole pattern.
            if let Maybe::Present(_) = self.loop_named(site, at)? {
                return Err(here.out(FragmentBoundary::Unadmitted));
            }
            return self.binder(at, named);
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
        if name == FormName::CONS_PATTERN {
            return self.cons_pattern(site, here, queued.slot, pieces, patterns, work);
        }
        if name == FormName::LITERAL_PATTERN {
            return match pieces.pieces.first() {
                Some(&Piece::Tile { label, at: tile }) if label == TileName::NUMBER => {
                    integer(here, self.text_at(tile))
                },
                Some(&Piece::Tile { label, .. }) if label == TileName::TRUE => {
                    Ok(Matcher::Boolean(true))
                },
                Some(&Piece::Tile { label, .. }) if label == TileName::FALSE => {
                    Ok(Matcher::Boolean(false))
                },
                _ => Err(here.out(FragmentBoundary::Unadmitted)),
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
            let shape = self.constructor_pattern(site, here, head, &fields, patterns, work)?;
            patterns
                .spelled
                .push((queued.slot, head.span, PatternReading::Constructor));
            return Ok(shape);
        }
        if name == FormName::TUPLE_PATTERN {
            let mut cursor = Cursor::new(&pieces.pieces, at.span);
            closed(here, &mut cursor, TileName::PAREN_OPEN)?;
            let entries = Self::tuple_entries(here, &mut cursor)?;
            return self.components(here, queued.stated, &entries, patterns, work);
        }
        if name == FormName::TELESCOPE_PATTERN {
            let mut cursor = Cursor::new(&pieces.pieces, at.span);
            closed(here, &mut cursor, TileName::RECORD)?;
            let entries = self.pattern_entries(here, &mut cursor)?;
            return self.components(here, queued.stated, &entries, patterns, work);
        }
        if name == FormName::LABELLED_SUM_PATTERN {
            let mut cursor = Cursor::new(&pieces.pieces, at.span);
            closed(here, &mut cursor, TileName::PLUS)?;
            closed(here, &mut cursor, TileName::BRACE_OPEN)?;
            let key = self.dotted(here, &mut cursor)?;
            closed(here, &mut cursor, TileName::EQUALS)?;
            let payload = here.one(cursor.operands())?;
            closed(here, &mut cursor, TileName::BRACE_CLOSE)?;
            exhausted(here, &cursor)?;
            return self.injected(here, queued.stated, key, payload, patterns, work);
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
        work: &mut Vec<Queued>,
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
        let queued: Vec<Queued> = fields
            .iter()
            .map(|&field| Queued {
                at: field,
                slot: UNWRITTEN,
                stated: Maybe::Absent(binder_type::Absent::Untyped),
                punned: Punned(false),
            })
            .collect();

        Ok(Matcher::Constructor {
            form: constructor.form,
            tag: constructor.tag,
            fields: allocated(patterns, work, &queued),
        })
    }

    /// The shape of the word pattern `g ∷ p` or `back(g) ∷ p` at `here`, the
    /// pattern at `slot`, read from `pieces`, its rest pattern `p` allocated
    /// and queued.
    ///
    /// # Specification
    /// - requires: `here` is a cons pattern of the match at `site`, `slot` its
    ///   place in `patterns` and `pieces` its reading.
    /// - ensures: the constructor of the words of the loop `g` names whose tag
    ///   is its letter, or its inverse under `back`, as [`Self::loop_letter`]
    ///   reads it, its one field the rest queued on `work`; the letter `g`, and
    ///   the name `back` that inverts it, spelled at `slot` as a word of one
    ///   letter, so the parentheses around `g`, tiles of the pattern, answer
    ///   the pattern as a constructor pattern's do.
    /// - fails: the unadmitted refusal for a head other than `back` applied to
    ///   a name; the unresolved-name refusal for a name that is no loop; a tile
    ///   out of place.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a letter and an inverse match their constructors, and
    ///   a name that is no loop is refused.
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    /// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
    #[spec(captures: before = work.len(), ensures: |ret| ret.is_err() || work.len() == before.saturating_add(1))]
    fn cons_pattern(
        &mut self,
        site: Site,
        here: Site,
        slot: PatternAt,
        pieces: &Pieces,
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, here.at.span);
        let Maybe::Present(head) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let (cell, inverse) = if let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN) {
            let Maybe::Present(cell) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
            };
            let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE)
            else {
                return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
            };
            if self.text_at(head).as_ref() != super::identity::BACK {
                return Err(here.out(FragmentBoundary::Unadmitted));
            }
            patterns
                .spelled
                .push((slot, head.span, PatternReading::Matched));
            (cell, Inverse(true))
        }
        else {
            (head, Inverse(false))
        };
        patterns
            .spelled
            .push((slot, cell.span, PatternReading::Matched));
        closed(here, &mut cursor, TileName::CONS)?;
        let rest = here.one(cursor.operands())?;
        exhausted(here, &cursor)?;
        let Maybe::Present(constructor) = self.loop_letter(site, cell, inverse)?
        else {
            return Err(LoweringRefusal::UnresolvedName {
                span: cell.span,
                name: self.name_at(cell),
            });
        };
        let queued = [Queued {
            at: rest,
            slot: UNWRITTEN,
            stated: Maybe::Absent(binder_type::Absent::Untyped),
            punned: Punned(false),
        }];

        Ok(Matcher::Constructor {
            form: constructor.form,
            tag: constructor.tag,
            fields: allocated(patterns, work, &queued),
        })
    }

    /// The tuple or record shape of a telescope or tuple pattern's
    /// `entries`, each component queued with the type `stated` writes for
    /// it.
    ///
    /// # Specification
    /// - requires: `entries` are the entries of the pattern at `here`.
    /// - ensures: at a scrutinee written with a dependent record, labelled
    ///   entries and positional ones of its arity are its nested pairs, as
    ///   [`Self::dependent_components`] reads them; otherwise positional
    ///   entries, in index order, make a tuple and labelled ones a record of
    ///   their labels; each component queued with the positional type of the
    ///   same place, or the labelled type of the same label, of the telescope
    ///   type `stated` writes, when it writes one.
    /// - fails: the entries' arrangement refusals; the stated type's own
    ///   malformation; the unresolved-name refusal for a label the dependent
    ///   record lacks.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — positional, reordered and labelled telescope
    ///   patterns, a tuple pattern, and patterns at a dependent record.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    /// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |shape| matches!(*shape, Matcher::Tuple { .. } | Matcher::Record { .. })))]
    fn components(
        &mut self,
        here: Site,
        stated: Maybe<NodeIndex, binder_type::Absent>,
        entries: &[arity::Entry<'source>],
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let form = match stated {
            Maybe::Present(node) => {
                self.stated_form(here, node, Former::TelescopeType, arity::Thunked(false))?
            },
            Maybe::Absent(_) => Maybe::Absent(arity::stated_labels::Absent::Otherwise),
        };
        let arranged = arity::arrange(here, entries.to_vec())?;
        let links = match form {
            Maybe::Present((_, ref typed)) => self.dependent_links(typed)?,
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        if let Maybe::Present((_, ref typed)) = form
            && let Maybe::Present(ref links) = links
            && match arranged {
                arity::Arranged::Positional(ref entries) => entries.len() == typed.len(),
                arity::Arranged::Labelled(_) => true,
            }
        {
            return Self::dependent_components(here, typed, links, arranged, patterns, work);
        }
        let typed = form.map(|(_node, typed)| typed);
        let untyped = Maybe::Absent(binder_type::Absent::Untyped);
        let queue = |entry: &arity::Entry<'source>, stated| Queued {
            at: entry.held.at(),
            slot: UNWRITTEN,
            stated,
            punned: Punned(matches!(entry.held, arity::Held::Punned(_))),
        };
        match arranged {
            arity::Arranged::Positional(entries) => {
                let queued: Vec<Queued> = match typed {
                    Maybe::Present(ref typed)
                        if typed.len() == entries.len()
                            && typed
                                .iter()
                                .all(|entry| matches!(entry.key, arity::Key::Positional)) =>
                    {
                        entries
                            .iter()
                            .zip(typed)
                            .map(|(entry, component)| {
                                queue(entry, Maybe::Present(component.held.at().node))
                            })
                            .collect()
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => {
                        entries.iter().map(|entry| queue(entry, untyped)).collect()
                    },
                };
                Ok(Matcher::Tuple {
                    fields: allocated(patterns, work, &queued),
                    dependent: Dependent(false),
                })
            },
            arity::Arranged::Labelled(entries) => {
                let mut labels = Vec::with_capacity(entries.len());
                let mut queued = Vec::with_capacity(entries.len());
                for entry in &entries {
                    let arity::Key::Label(name, _) = entry.key
                    else {
                        continue;
                    };
                    let component = match typed {
                        | Maybe::Present(ref typed) => typed
                            .iter()
                            .find(|held| matches!(held.key, arity::Key::Label(label, _) if label == name))
                            .map_or(untyped, |held| Maybe::Present(held.held.at().node)),
                        | Maybe::Absent(_) => untyped,
                    };
                    labels.push(FieldLabel::from(String::from(name.as_ref())));
                    queued.push(queue(entry, component));
                }
                Ok(Matcher::Record {
                    labels,
                    fields: allocated(patterns, work, &queued),
                })
            },
        }
    }

    /// The nested pairs a pattern at a dependent record matches: its
    /// entries placed by the record's written order, the links nested to the
    /// right.
    ///
    /// # Specification
    /// - requires: `typed` are the entries of the dependent record the
    ///   scrutinee's position states, `links` whether each but the last binds
    ///   the ones after it, and `arranged` the pattern's entries: positional
    ///   ones of the record's arity, or labelled ones.
    /// - ensures: one tuple of two per link, the outermost returned and each
    ///   inner one a part after its parent: the link's entry, then the next
    ///   link or the last entry; a split of a link that binds is dependent; a
    ///   place no entry names is a wildcard; each written entry queued with its
    ///   place's type, in written order.
    /// - fails: the unresolved-name refusal for a label the record lacks.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnresolvedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a positional and a labelled pattern at a dependent
    ///   record of two, and a labelled one at a record of three naming two of
    ///   its labels.
    /// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |shape| matches!(*shape, Matcher::Tuple { fields, .. } if fields.end.saturating_sub(fields.start) == 2_usize)))]
    fn dependent_components(
        here: Site,
        typed: &[arity::Entry<'source>],
        links: &[Dependent],
        arranged: arity::Arranged<'source>,
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let mut placed: Vec<Option<(usize, arity::Entry<'source>)>> =
            alloc::vec![None; typed.len()];
        match arranged {
            arity::Arranged::Positional(entries) => {
                for (written, (slot, entry)) in placed.iter_mut().zip(entries).enumerate() {
                    *slot = Some((written, entry));
                }
            },
            arity::Arranged::Labelled(entries) => {
                for (written, entry) in entries.into_iter().enumerate() {
                    let arity::Key::Label(name, key) = entry.key
                    else {
                        continue;
                    };
                    let (arity::Place(place), _) = Self::labelled_in(typed, name, key)?;
                    if let Some(slot) = placed.get_mut(place) {
                        *slot = Some((written, entry));
                    }
                }
            },
        }
        let mut queued: Vec<(usize, Queued)> = Vec::with_capacity(typed.len());
        let mut part = |patterns: &mut Written, place: usize| -> PatternAt {
            let slot = PatternAt(patterns.shapes.len());
            let entry = placed.get(place).copied().flatten();
            patterns.shapes.push((
                entry.map_or(here.at, |(_, entry)| entry.held.at()),
                Matcher::Wild,
            ));
            if let Some((written, entry)) = entry {
                queued.push((written, Queued {
                    at: entry.held.at(),
                    slot,
                    stated: typed
                        .get(place)
                        .map_or(Maybe::Absent(binder_type::Absent::Untyped), |component| {
                            Maybe::Present(component.held.at().node)
                        }),
                    punned: Punned(matches!(entry.held, arity::Held::Punned(_))),
                }));
            }
            slot
        };
        let mut outer = None;
        let mut pending: Option<PatternAt> = None;
        for (link, &dependent) in links.iter().enumerate() {
            let first = part(patterns, link);
            let second = if link.saturating_add(2) >= typed.len() {
                part(patterns, link.saturating_add(1))
            }
            else {
                let slot = PatternAt(patterns.shapes.len());
                patterns.shapes.push((here.at, Matcher::Wild));
                slot
            };
            let start = patterns.parts.len();
            patterns.parts.extend([first, second]);
            let matcher = Matcher::Tuple {
                fields: Stretch {
                    start,
                    end: patterns.parts.len(),
                },
                dependent,
            };
            match pending {
                Some(slot) => {
                    if let Some(held) = patterns.shapes.get_mut(slot.0) {
                        held.1 = matcher;
                    }
                },
                None => outer = Some(matcher),
            }
            pending = Some(second);
        }
        queued.sort_by_key(|&(written, _)| core::cmp::Reverse(written));
        work.extend(queued.into_iter().map(|(_, each)| each));

        outer.ok_or_else(|| LoweringRefusal::OutOfFragment {
            span: here.at.span,
            form: here.name,
            sort: here.reading.sort(),
            boundary: FragmentBoundary::WrongSort,
        })
    }

    /// The injection shape of a sum pattern `+{ key = payload }` whose
    /// position states the type `stated`.
    ///
    /// # Specification
    /// - requires: `key` and `payload` are the sum pattern's at `here`.
    /// - ensures: the injection into the summand the key's index names, or its
    ///   label names among the stated sum's entries, of as many summands as the
    ///   stated sum has; the payload queued with the summand's type, and the
    ///   key spelled at the payload, which it names.
    /// - fails: the unannotated refusal where the position states no sum; a
    ///   misplaced tile at an index past the sum; the unresolved-name refusal
    ///   for a label the sum lacks.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — labelled and indexed sum patterns under a stated sum,
    ///   nested in a telescope pattern, and with no stated sum.
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |shape| matches!(*shape, Matcher::Injection { summand, arity, .. } if summand < arity)))]
    fn injected(
        &mut self,
        here: Site,
        stated: Maybe<NodeIndex, binder_type::Absent>,
        key: arity::Key<'source>,
        payload: Placed,
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let summands = match stated {
            Maybe::Present(node) => {
                self.stated_entries(here, node, Former::LabelledSumType, arity::Thunked(false))?
            },
            Maybe::Absent(_) => Maybe::Absent(arity::stated_labels::Absent::Otherwise),
        };
        let Maybe::Present(summands) = summands
        else {
            return Err(here.out(FragmentBoundary::Unannotated));
        };
        let (summand, entry, keyed) = match key {
            arity::Key::Index(index, _, written) => {
                let Some(&entry) = summands.get(index)
                else {
                    return Err(here.fault(written.span, FormFault::MisplacedTile));
                };
                (index, entry, written.span)
            },
            arity::Key::Label(name, written) => {
                let (arity::Place(index), entry) = Self::labelled_in(&summands, name, written)?;
                (index, entry, written.span)
            },
            arity::Key::Positional => {
                return Err(here.fault(payload.span, FormFault::MisplacedTile));
            },
        };
        let queued = [Queued {
            at: payload,
            slot: UNWRITTEN,
            stated: Maybe::Present(entry.held.at().node),
            punned: Punned(false),
        }];
        let fields = allocated(patterns, work, &queued);
        let field = patterns
            .parts
            .get(fields.start)
            .copied()
            .unwrap_or(UNWRITTEN);
        patterns
            .spelled
            .push((field, keyed, PatternReading::Matched));

        Ok(Matcher::Injection {
            summand,
            arity: summands.len(),
            field,
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
                    Matcher::Wild | Matcher::Binder(_) => return None,
                    Matcher::Hole(hole) => Head::Hole(hole),
                    Matcher::Constructor { form, .. } => Head::Data(form),
                    Matcher::Boolean(_) => Head::Boolean,
                    Matcher::Integer(ref literal) => Head::Integer(literal.clone()),
                    Matcher::Tuple { fields, dependent } => {
                        Head::Tuple(fields.end.saturating_sub(fields.start), dependent)
                    },
                    Matcher::Record { .. } => Head::Record,
                    Matcher::Injection { arity, .. } => Head::Sum(arity),
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
            Head::Hole(hole) => Ok(Test::Stuck(hole)),
            Head::Data(form) => self.switch_data(patterns, item, switch, form, tree),
            Head::Boolean => self.switch_boolean(patterns, item, switch, tree),
            Head::Integer(literal) => self.switch_integer(patterns, item, switch, literal, tree),
            Head::Tuple(arity, dependent) => {
                self.switch_tuple(patterns, item, switch, Width(arity), dependent, tree)
            },
            Head::Record => self.switch_record(patterns, item, switch, tree),
            Head::Sum(arity) => self.switch_sum(patterns, item, switch, Width(arity), tree),
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
        form: Generators,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let arities: Vec<usize> = match form {
            Generators::Written(position) => self
                .collected
                .data
                .get(position)
                .map(|written| {
                    written
                        .generators
                        .iter()
                        .map(|generator| generator.fields.len())
                        .collect()
                })
                .unwrap_or_default(),
            Generators::Presentation => match self.collected.sig {
                Maybe::Present(ref sig) => sig.arities.clone(),
                Maybe::Absent(_) => Vec::new(),
            },
            Generators::Words(words) => {
                let loops = self
                    .collected
                    .words
                    .get(words)
                    .map_or(0_usize, |written| written.loops.len());
                let mut arities = Vec::from([0_usize]);
                arities.resize(loops.saturating_mul(2).saturating_add(1), 1_usize);
                arities
            },
        };
        let family = match form {
            Generators::Written(position) => match self.collected.data.get(position) {
                Some(written) if written.parameters.is_empty() => self
                    .collected
                    .slots
                    .get(usize::from(written.slot))
                    .map_or(Maybe::Absent(bare::Absent::Parameterised), |slot| {
                        Maybe::Present(slot.constant)
                    }),
                _ => Maybe::Absent(bare::Absent::Parameterised),
            },
            Generators::Presentation => Maybe::Absent(bare::Absent::Parameterised),
            Generators::Words(words) => self
                .collected
                .words
                .get(words)
                .and_then(|written| self.collected.slots.get(usize::from(written.slot)))
                .map_or(Maybe::Absent(bare::Absent::Parameterised), |slot| {
                    Maybe::Present(slot.constant)
                }),
        };
        let mut branches = Vec::with_capacity(arities.len());
        for (tag, &arity) in arities.iter().enumerate() {
            let mut specialised = Vec::new();
            for row in &item.rows {
                self.fuel.spend()?;
                let mut next = row.clone();
                let held = patterns.entry(row, switch.column);
                let replacement = match *held {
                    Matcher::Constructor {
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
                    Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                        through(&mut next, held, switch.level);
                        alloc::vec![UNWRITTEN; arity]
                    },
                    Matcher::Boolean(_)
                    | Matcher::Integer(_)
                    | Matcher::Tuple { .. }
                    | Matcher::Record { .. }
                    | Matcher::Injection { .. } => return Err(switch.wrong),
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
            family,
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
    ///   column is a constructor, an integer, a tuple, a record or an
    ///   injection; [`LoweringRefusal::BudgetExceeded`].
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
                Matcher::Boolean(true) => left.push(next),
                Matcher::Boolean(false) => right.push(next),
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut next, held, switch.level);
                    left.push(next.clone());
                    right.push(next);
                },
                Matcher::Constructor { .. }
                | Matcher::Integer(_)
                | Matcher::Tuple { .. }
                | Matcher::Record { .. }
                | Matcher::Injection { .. } => return Err(switch.wrong),
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
    ///   column is a constructor, a boolean, a tuple, a record or an injection;
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
                Matcher::Integer(ref written) if *written == literal => equal.push(matched),
                Matcher::Integer(_) => other.push(row.clone()),
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut matched, held, switch.level);
                    equal.push(matched);
                    other.push(row.clone());
                },
                Matcher::Constructor { .. }
                | Matcher::Boolean(_)
                | Matcher::Tuple { .. }
                | Matcher::Record { .. }
                | Matcher::Injection { .. } => return Err(switch.wrong),
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

    /// Split the tuple in `switch`'s column into its `arity` components.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds a tuple of `arity` components in the
    ///   item's first row, split dependently as `dependent` says.
    /// - ensures: a split, dependent as the column's tuple is, whose child
    ///   holds every row, the column replaced by the components a tuple pattern
    ///   writes or by wildcards for a pattern matching anything, under `arity`
    ///   more binders, component zero outermost.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is a tuple of another arity or of another kind;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a positional telescope pattern of three binders, a
    ///   tuple pattern and a pattern at a dependent record each reach their arm
    ///   at the component's level.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    /// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Split { arity: held, dependent: split, .. } if held == width.0 && split == dependent)))]
    fn switch_tuple(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch<'source>,
        width: Width,
        dependent: Dependent,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let Width(arity) = width;
        let mut specialised = Vec::with_capacity(item.rows.len());
        for row in &item.rows {
            self.fuel.spend()?;
            let mut next = row.clone();
            let held = patterns.entry(row, switch.column);
            let replacement = match *held {
                Matcher::Tuple { fields, .. }
                    if fields.end.saturating_sub(fields.start) == arity =>
                {
                    patterns
                        .parts
                        .get(fields.start .. fields.end)
                        .map(<[PatternAt]>::to_vec)
                        .unwrap_or_default()
                },
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut next, held, switch.level);
                    alloc::vec![UNWRITTEN; arity]
                },
                Matcher::Tuple { .. }
                | Matcher::Constructor { .. }
                | Matcher::Boolean(_)
                | Matcher::Integer(_)
                | Matcher::Record { .. }
                | Matcher::Injection { .. } => return Err(switch.wrong),
            };
            next.columns = splice(&row.columns, switch.column, &replacement);
            specialised.push(next);
        }
        let child = tree.queue(
            Depth(item.depth.0.saturating_add(arity)),
            splice(&item.levels, switch.column, &fresh(item.depth, width)),
            specialised,
        );

        Ok(Test::Split {
            level: switch.level,
            depth: item.depth,
            arity,
            dependent,
            child,
        })
    }

    /// Project the fields every row's record pattern in `switch`'s column
    /// names.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds a record in the item's first row.
    /// - ensures: the projections of every label any row names, in label order,
    ///   whose child holds every row, the column replaced by the field each
    ///   label's pattern writes, a wildcard for a label the row does not name
    ///   or a pattern matching anything, under one more binder per label.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is of another kind; [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two record arms naming different labels each reach
    ///   their arm with the fields they name.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Record { ref labels, .. } if labels.is_sorted())))]
    fn switch_record(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch<'source>,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let mut named = BTreeSet::new();
        for row in &item.rows {
            match *patterns.entry(row, switch.column) {
                Matcher::Record { ref labels, .. } => named.extend(labels.iter().cloned()),
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {},
                Matcher::Constructor { .. }
                | Matcher::Boolean(_)
                | Matcher::Integer(_)
                | Matcher::Tuple { .. }
                | Matcher::Injection { .. } => return Err(switch.wrong),
            }
        }
        let labels: Vec<FieldLabel> = named.into_iter().collect();
        let mut specialised = Vec::with_capacity(item.rows.len());
        for row in &item.rows {
            self.fuel.spend()?;
            let mut next = row.clone();
            let held = patterns.entry(row, switch.column);
            let replacement: Vec<PatternAt> = match *held {
                Matcher::Record {
                    labels: ref written,
                    fields,
                } => {
                    let parts = patterns
                        .parts
                        .get(fields.start .. fields.end)
                        .unwrap_or_default();
                    labels
                        .iter()
                        .map(|label| {
                            written
                                .iter()
                                .zip(parts)
                                .find_map(|(each, &part)| (each == label).then_some(part))
                                .unwrap_or(UNWRITTEN)
                        })
                        .collect()
                },
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut next, held, switch.level);
                    alloc::vec![UNWRITTEN; labels.len()]
                },
                Matcher::Constructor { .. }
                | Matcher::Boolean(_)
                | Matcher::Integer(_)
                | Matcher::Tuple { .. }
                | Matcher::Injection { .. } => return Err(switch.wrong),
            };
            next.columns = splice(&row.columns, switch.column, &replacement);
            specialised.push(next);
        }
        let child = tree.queue(
            Depth(item.depth.0.saturating_add(labels.len())),
            splice(
                &item.levels,
                switch.column,
                &fresh(item.depth, Width(labels.len())),
            ),
            specialised,
        );

        Ok(Test::Record {
            level: switch.level,
            depth: item.depth,
            labels,
            child,
        })
    }

    /// Switch on the summand of the sum of `arity` summands in `switch`'s
    /// column.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds an injection into a sum of `arity`
    ///   summands in the item's first row.
    /// - ensures: a sum switch with one child per summand, holding the rows
    ///   that admit it, the column replaced by the injection's payload or by a
    ///   wildcard for a pattern matching anything, under the payload's one
    ///   binder.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is an injection into a sum of another arity or of another kind;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a three-summand match with a catch-all reaches each
    ///   summand's arm, the catch-all filling the rest.
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Sum { ref branches, .. } if branches.len() == width.0)))]
    fn switch_sum(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch<'source>,
        width: Width,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let Width(arity) = width;
        let mut branches = Vec::with_capacity(arity);
        for summand in 0 .. arity {
            let mut specialised = Vec::new();
            for row in &item.rows {
                self.fuel.spend()?;
                let mut next = row.clone();
                let held = patterns.entry(row, switch.column);
                let replacement = match *held {
                    Matcher::Injection {
                        summand: written,
                        arity: of,
                        field,
                    } => {
                        if of != arity {
                            return Err(switch.wrong);
                        }
                        if written != summand {
                            continue;
                        }
                        field
                    },
                    Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                        through(&mut next, held, switch.level);
                        UNWRITTEN
                    },
                    Matcher::Constructor { .. }
                    | Matcher::Boolean(_)
                    | Matcher::Integer(_)
                    | Matcher::Tuple { .. }
                    | Matcher::Record { .. } => return Err(switch.wrong),
                };
                next.columns = splice(&row.columns, switch.column, &[replacement]);
                specialised.push(next);
            }
            branches.push(tree.queue(
                Depth(item.depth.0.saturating_add(1)),
                splice(&item.levels, switch.column, &fresh(item.depth, Width(1))),
                specialised,
            ));
        }

        Ok(Test::Sum {
            level: switch.level,
            depth: item.depth,
            branches,
        })
    }

    /// Mint `patterns` into `kept`'s core pattern table and record one arm
    /// alternative per entry of `roots`.
    ///
    /// # Specification
    /// - requires: every root of `roots` names a pattern of `patterns`.
    /// - ensures: each pattern minted after its parts, in the core's shapes: a
    ///   binder, a wildcard, a hole, a constructor over its fields, a literal,
    ///   a boolean as an injection over the unit, a tuple of no component as
    ///   the unit and of two as a pair, and an injection into a sum of two as
    ///   the injection on its side; any other tuple and a record as a
    ///   constructor of tag zero over its parts, and any other injection as the
    ///   constructor tagged with its summand over its payload, which the core's
    ///   coverage reads as outside its fragment; one arm record per root, in
    ///   order; each pattern's own span, then each span `patterns` spells
    ///   inside one, recorded against the pattern minted for it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match over nested constructors, a binder, a hole
    ///   and an or-pattern keeps each alternative's shape; a pair pattern keeps
    ///   a pair and a two-summand injection its side.
    /// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    #[spec(captures: before = kept.arms.len(), ensures: kept.arms.len() == before.saturating_add(roots.len()) && kept.spans.len() >= patterns.shapes.len())]
    fn keep(
        patterns: &Written,
        roots: &[(ArmAt, PatternAt, NodeIndex, NodeIndex)],
        kept: &mut CaseOrigin,
    )
    {
        let mut minted: Vec<Option<PatternId>> =
            Vec::from_iter(patterns.shapes.iter().map(|_shape| None));
        for (position, &(_at, ref shape)) in patterns.shapes.iter().enumerate().rev() {
            let parts = |fields: Stretch| -> Vec<PatternId> {
                patterns
                    .parts
                    .get(fields.start .. fields.end)
                    .unwrap_or_default()
                    .iter()
                    .filter_map(|&part| minted.get(part.0).copied().flatten())
                    .collect()
            };
            let pattern = match *shape {
                Matcher::Wild => Pattern::Wildcard,
                Matcher::Binder(_) => Pattern::Binder,
                Matcher::Hole(hole) => Pattern::Hole(hole),
                Matcher::Integer(ref literal) => Pattern::Literal(literal.clone()),
                Matcher::Boolean(value) => {
                    let unit = kept.patterns.mint(Pattern::Unit);
                    Pattern::Injection(if value { Side::Left } else { Side::Right }, unit)
                },
                Matcher::Constructor { tag, fields, .. } => Pattern::Constructor {
                    tag: ConstructorTag::from(tag),
                    fields: parts(fields),
                },
                Matcher::Tuple { fields, .. } => match *parts(fields).as_slice() {
                    [] => Pattern::Unit,
                    [first, second] => Pattern::Pair(first, second),
                    ref several => Pattern::Constructor {
                        tag: ConstructorTag::from(0_usize),
                        fields: several.to_vec(),
                    },
                },
                Matcher::Record { fields, .. } => Pattern::Constructor {
                    tag: ConstructorTag::from(0_usize),
                    fields: parts(fields),
                },
                Matcher::Injection {
                    summand,
                    arity,
                    field,
                } => {
                    let body = minted.get(field.0).copied().flatten();
                    match (arity, summand, body) {
                        (2_usize, 0_usize, Some(body)) => Pattern::Injection(Side::Left, body),
                        (2_usize, 1_usize, Some(body)) => Pattern::Injection(Side::Right, body),
                        _ => Pattern::Constructor {
                            tag: ConstructorTag::from(summand),
                            fields: body.into_iter().collect(),
                        },
                    }
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
        let spelled = patterns
            .spelled
            .iter()
            .map(|&(slot, span, reading)| (slot.0, span, reading));
        let own = patterns
            .shapes
            .iter()
            .enumerate()
            .map(|(position, &(at, _))| (position, at.span, PatternReading::Matched));
        for (position, span, reading) in own.chain(spelled) {
            if let Some(&Some(pattern)) = minted.get(position) {
                kept.spans.push(PatternSpan {
                    pattern,
                    span,
                    reading,
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
    ///   level when none is written, its origin the declaration form — and the
    ///   rules of its presented reading ([`Self::presentation`]), pushed onto
    ///   the module's list, its index recorded by the declaration's position in
    ///   the collection's data list.
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
                        Maybe::Present(id) => Some(id),
                        Maybe::Absent(_) => None,
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
                Maybe::Present(written) => self.value_type_at(written.node),
                Maybe::Absent(_) => match self.origin_at(form.declaration.node) {
                    Maybe::Present(origin) => {
                        let id = sink.arena.value_type_universe(
                            Sort::Ground(GroundSort::Value),
                            Level::constant(super::Universe::FUSS_FREE.level),
                        );
                        sink.origins.record_value_type(id, origin);
                        Maybe::Present(id)
                    },
                    Maybe::Absent(reason) => Maybe::Absent(reason),
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
            let signature = DataSignature::new(parameters, constructors, kind)
                .presented(self.presentation(form));
            self.data.push(Arc::new(signature));
            self.constructors.push(
                form.generators
                    .iter()
                    .map(|generator| String::from(<&str>::from(self.text_at(generator.named))))
                    .collect(),
            );
            let _first = self.signatures.insert(position, index);
        }
        self.mint_words(sink);
    }

    /// Mint the words of every family's loops at their point, and each
    /// loop's binding, for the families [`Self::mint_data`] minted.
    ///
    /// # Specification
    /// - requires: the family signatures are minted.
    /// - ensures: per words entry over a minted family, a signature without
    ///   parameters at the family's universe whose constructors are the empty
    ///   word, then each loop's letter and its inverse, each a cons onto a
    ///   word, presented as the words of the loops at their point — the two
    ///   cancellations per loop the presentation mints — its index recorded by
    ///   the entry's position; each loop's binding the path type at the point
    ///   and the word of its one letter. Each letter a cons wrote, and each
    ///   loop's name where its cell declares it, is labelled at the path type,
    ///   and each node of a point an empty word or a cell's side wrote at the
    ///   family, since no core node holds them.
    /// - provides: the
    ///   [`DeclarationOutcome::Data`](crate::DeclarationOutcome::Data) outcome
    ///   of a words slot and the completed outcome of a loop.
    /// - fails: never; words over a family that did not mint mint nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block with one loop mints its words with three
    ///   constructors and two rules, and binds the loop at its path type; a
    ///   word's letters and its empty word's point are labelled.
    /// - witness: `lower::native::tests::a_loop_mints_the_words_at_its_point`
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    #[spec(captures: before = self.data.len(), ensures: self.data.len() >= before && self.worded.len() <= self.collected.words.len())]
    fn mint_words(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        for (index, words) in self.collected.words.iter().enumerate() {
            let (Some(&minted), Some(form)) = (
                self.signatures.get(&words.family),
                self.collected.data.get(words.family),
            )
            else {
                continue;
            };
            let constant = |slot: SlotIndex| {
                self.collected
                    .slots
                    .get(usize::from(slot))
                    .map(|entry| entry.constant)
            };
            let (Some(family), Some(own), Some(kind), Maybe::Present(origin)) = (
                constant(form.slot),
                constant(words.slot),
                self.data
                    .get(usize::from(minted))
                    .map(|signature| signature.kind()),
                self.origin_at(form.declaration.node),
            )
            else {
                continue;
            };
            let word = sink.arena.value_type_data(own, Vec::new());
            sink.origins.record_value_type(word, origin);
            let mut constructors =
                Vec::with_capacity(words.loops.len().saturating_mul(2).saturating_add(1));
            let mut names = Vec::with_capacity(constructors.capacity());
            constructors.push(Vec::new());
            names.push(String::from(super::identity::HERE));
            for &bound in &words.loops {
                let letter = self
                    .collected
                    .slots
                    .get(usize::from(bound))
                    .map_or("", |entry| entry.name.as_ref());
                constructors.extend([Vec::from([word]), Vec::from([word])]);
                names.extend([String::from(letter), alloc::format!("back({letter})")]);
            }
            let cells = words
                .loops
                .iter()
                .map(|_bound| {
                    gandr_core_term::FreeCell::new(words.point.clone(), words.point.clone())
                })
                .collect();
            let presentation = gandr_core_term::Presentation::words(
                gandr_core_term::FreeCells::new(family, cells),
            );
            let data = DataIndex::from(self.data.len());
            self.data.push(Arc::new(
                DataSignature::new(Vec::new(), constructors, kind).presented(presentation),
            ));
            self.constructors.push(names);
            let _first = self.worded.insert(index, data);
            let mark = sink.arena.watermark();
            let pointed_at = self.words_point(sink.arena, words);
            record_since(sink, mark, origin, Maybe::Absent(rooted::Absent::Unminted));
            let Maybe::Present((carrier, point)) = pointed_at
            else {
                continue;
            };
            let path = sink.arena.value_type_path(carrier, point, point);
            sink.origins.record_value_type(path, origin);
            let lettered = self
                .lettered
                .iter()
                .filter(|&&(_, at)| at == index)
                .map(|&(span, _)| (span, path));
            let pointed = self
                .pointed
                .iter()
                .filter(|&&(_, at)| at == index)
                .map(|&(span, _)| (span, carrier));
            let at_point = || form.cells.iter().filter(|cell| cell.point == words.point);
            let named = at_point().map(|cell| (cell.named.span, path));
            let sides = at_point().flat_map(|cell| cell.sides.iter().map(|&span| (span, carrier)));
            for (span, ty) in lettered.chain(pointed).chain(named).chain(sides) {
                sink.origins.record_label(crate::origin::Label {
                    span,
                    labelled: crate::origin::Labelled::ValueType {
                        ty,
                        context: Vec::new(),
                    },
                });
            }
            let nil =
                sink.arena
                    .value_constructor(word, gandr_core_term::FreeCells::nil(), Vec::new());
            sink.origins.record_value(nil, origin);
            for (generator, &bound) in words.loops.iter().enumerate() {
                let letter = sink.arena.value_constructor(
                    word,
                    gandr_core_term::FreeCells::letter(gandr_core_term::CellIndex::from(generator)),
                    Vec::from([nil]),
                );
                sink.origins.record_value(letter, origin);
                let _first = self.looped.insert(bound, (path, letter));
            }
        }
    }

    /// The carrier and the point of `words`: the family's type, and the closed
    /// term the point spells over it.
    ///
    /// # Specification
    /// - requires: `words` is an entry of the collection's words list.
    /// - ensures: the family's type without arguments, and the point as
    ///   [`spelled_point`] mints it over that type.
    /// - provides: the path type `Path(carrier, point, point)` a word at that
    ///   point stands at, for the words' own binding and for a derived
    ///   operation reading its path's type.
    /// - fails: the unminted absence for words over a family the collection
    ///   does not hold, or a point that spells nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_words`], and a derived operation over
    ///   a word.
    /// - witness: `lower::native::tests::a_loop_mints_the_words_at_its_point`
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present((carrier, point)) => arena.value_type(carrier).is_some() && arena.value(point).is_some(),
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn words_point(
        &self,
        arena: &mut CoreArena,
        words: &WordsForm,
    ) -> Maybe<(ValueTypeId, ValueId), lowered::Absent>
    {
        let Some(form) = self.collected.data.get(words.family)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let Some(family) = self.collected.slots.get(usize::from(form.slot))
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let carrier = arena.value_type_data(family.constant, Vec::new());
        let arities: Vec<gandr_kernel_term::FieldCount> = form
            .generators
            .iter()
            .map(|generator| gandr_kernel_term::FieldCount::from(generator.fields.len()))
            .collect();
        let mut minted = Vec::new();

        spelled_point(arena, carrier, (&words.point, &arities), &mut minted)
            .map(|point| (carrier, point))
    }

    /// The words a constant is a word of: a loop's, or the words' own.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entry of the collection's words list whose slot or one of
    ///   whose loops' slots `constant` is.
    /// - fails: [`worded::Absent::Unworded`] for any other constant.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the loop and the empty word read at their words, and
    ///   a function at none.
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(
        self.collected.slots.get(usize::from(constant)).map(|slot| slot.definition),
        Some(Maybe::Present(Half { operand: Operand::Loop { .. } | Operand::Words(_), .. }))
    ))]
    pub(super) fn words_at(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<&WordsForm, worded::Absent>
    {
        let Some(Maybe::Present(Half {
            operand: Operand::Loop { words, .. } | Operand::Words(words),
            ..
        })) = self
            .collected
            .slots
            .get(usize::from(constant))
            .map(|slot| slot.definition)
        else {
            return Maybe::Absent(worded::Absent::Unworded);
        };
        self.collected
            .words
            .get(words)
            .map_or(Maybe::Absent(worded::Absent::Unworded), Maybe::Present)
    }

    /// The rules a data declaration's presented reading writes over its own
    /// constructors, as the checkers read a presented type: each side in
    /// pre-order, a constructor by its tag and a variable by the order its
    /// first occurrence on the left takes.
    ///
    /// # Specification
    /// - requires: the description route has read the declaration's cells.
    /// - ensures: one rule per face of the presented reading, in rule order,
    ///   whose left side is headed by a constructor, whose two sides apply only
    ///   the declaration's own constructors and whose right side names only
    ///   variables the left binds; the empty presentation when the declaration
    ///   has no presented reading. A face applying an operation rewrites a
    ///   call, not the type's terms, and is left to its operation.
    /// - provides: the rules [`DataSignature::presented`] carries to both
    ///   checkers, which validate them against the constructor table.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's two cancellations lower to the rules
    ///   both checkers rewrite its words by, and a family without rules lowers
    ///   to the free signature.
    /// - witness: `lower::native::tests::a_presented_family_lowers_its_rules`
    #[spec(ensures: |ret| ret.rules().len() <= self.collected.descriptions.get(&form.declaration.node)
        .map_or(0, |described| described.description.rules.len()))]
    fn presentation(
        &self,
        form: &crate::module::DataForm,
    ) -> gandr_core_term::Presentation
    {
        let Some(described) = self.collected.descriptions.get(&form.declaration.node)
        else {
            return gandr_core_term::Presentation::default();
        };
        let Some(cells) = self
            .collected
            .cells
            .declarations
            .iter()
            .find(|cells| cells.at.node == form.declaration.node)
        else {
            return gandr_core_term::Presentation::default();
        };
        let Maybe::Present(ref presented) = cells.presented
        else {
            return gandr_core_term::Presentation::default();
        };
        let names: Vec<SourceFragment<'source>> = form
            .generators
            .iter()
            .map(|generator| self.text_at(generator.named))
            .collect();
        let mut rules = Vec::new();
        let faces = if cells.oriented.is_empty() {
            described.description.rules.as_ref()
        }
        else {
            cells.oriented.as_slice()
        };
        for &(index, _cell) in &presented.faces {
            let Some(face) = faces.get(usize::from(index))
            else {
                continue;
            };
            let mut variables = Vec::new();
            let (Maybe::Present(left), Maybe::Present(right)) = (
                rule_side(&face.lhs, &names, &mut variables, Binding::Binds),
                rule_side(&face.rhs, &names, &mut variables, Binding::Reads),
            )
            else {
                continue;
            };
            if matches!(
                left.first(),
                Some(gandr_core_term::RuleNode::Constructor(_))
            ) {
                rules.push(gandr_core_term::PresentedRule::new(left, right));
            }
        }
        gandr_core_term::Presentation::new(rules)
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
                Maybe::Present(value) => passed.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_type_data(constant, passed);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Mint a constructor over its fields and its classifier.
    ///
    /// # Specification
    /// - requires: every field, the annotation's type and the answer's are
    ///   already minted or absent; for a slot, the family's parameter type and
    ///   every argument before the constructor's are too.
    /// - ensures: the constructor value over its fields, its classifier the
    ///   annotation's type — or the type a family's argument quotes — carried
    ///   into the term's binders; the value type the answer's returner returns
    ///   carried from the answer's frame to the constructor's; for a slot, the
    ///   family's parameter at the constructor's place with the parameters
    ///   before it replaced by the arguments written for them; or the family
    ///   over no arguments; the classifier's origin inserted and the written
    ///   origin on the value; nothing when a field, the annotation, the answer
    ///   or a slot's type or argument did not lower, or the answer is no
    ///   returner.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::construct`].
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument`
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
                Maybe::Present(value) => fields.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let classified = origin.inserted(Insertion::Classifier);
        let classifier = match constructed.classifier {
            Classifier::Written(written) => {
                // A type written as a family's argument is read as its code;
                // the classifier is the type it quotes.
                let quoted = if let Maybe::Present(code) = self.value_at(written)
                    && let Some(&gandr_core_term::Value::Quote(quoted)) = sink.arena.value(code)
                {
                    Some(quoted)
                }
                else {
                    None
                };
                let id = match (self.value_type_at(written), quoted) {
                    (Maybe::Present(id), _) => id,
                    (Maybe::Absent(_), Some(quoted)) => quoted,
                    (Maybe::Absent(_), None) => return Maybe::Absent(lowered::Absent::Unminted),
                };
                let frame = self.reading(written).frame();
                self.relocate_value_type(id, frame, sink, classified)
            },
            Classifier::Slot(argued) => match self.slot_type(argued, sink, classified) {
                Maybe::Present(id) => id,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Classifier::Answered { answer, frame } => {
                let mark = sink.arena.watermark();
                let written = self.answered_type(answer, sink);
                let Maybe::Present(written) = written
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let gap = self
                    .scope
                    .telescope_binders(frame)
                    .count()
                    .saturating_sub(self.scope.telescope_binders(answer.frame).count());
                let lift = Binders::from(u32::try_from(gap).unwrap_or(u32::MAX));
                let mut copies = Vec::new();
                let carried =
                    self.relocate(sink.arena, written, answer.frame, lift, Some(&mut copies));
                record_copied_since(
                    sink,
                    mark,
                    origin.inserted(Insertion::Classifier),
                    Maybe::Absent(rooted::Absent::Classifier),
                    &copies,
                );
                let Some(&CompType::Returner { result, .. }) = sink.arena.comp_type(carried)
                else {
                    return Maybe::Absent(lowered::Absent::OtherSort);
                };
                result
            },
            Classifier::Inserted => {
                let id = sink.arena.value_type_data(constructed.family, Vec::new());
                sink.origins.record_value_type(id, classified);
                id
            },
        };
        let id = sink
            .arena
            .value_constructor(classifier, constructed.tag, fields);

        Maybe::Present(sink.value(id, origin))
    }

    /// The type a data family's application gives the argument at `argued`'s
    /// place.
    ///
    /// # Specification
    /// - requires: the family's parameter types and the arguments before the
    ///   place are minted or absent.
    /// - ensures: the family's parameter at the place, read under the
    ///   parameters before it, with each of those replaced by the argument
    ///   written for it, every node the substitution mints recorded at
    ///   `origin`; nothing when the parameter's type or an argument did not
    ///   lower.
    /// - provides: the classifier of a constructor written as a family's
    ///   argument (#421).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Inl(a)` written for the third parameter `s :
    ///   SumOb(l, r)` of a family applied to `Integer` and `String` is
    ///   classified `SumOb(Integer, String)`.
    /// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value_type(id).is_some()))]
    fn slot_type(
        &self,
        argued: Argued,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let Some(parameter) = self
            .collected
            .data
            .get(argued.form)
            .and_then(|form| form.parameters.get(argued.place))
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let declared = match self.value_type_at(parameter.classifier.node) {
            Maybe::Present(declared) => declared,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut environment = Vec::with_capacity(argued.place);
        for &argument in stretch(&self.operands, argued.applied)
            .iter()
            .take(argued.place)
        {
            match self.value_at(argument) {
                Maybe::Present(value) => environment.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        // The innermost parameter is the last before the place.
        environment.reverse();
        let mark = sink.arena.watermark();
        let code = sink.arena.value_quote(declared);
        let mut carried = Vec::new();
        let substituted = gandr_core_term::substitute_environment_traced(
            sink.arena,
            TermId::Value(code),
            &environment,
            &mut carried,
        );
        exits::record_copies(sink, mark, &carried, origin);
        let TermId::Value(substituted) = substituted
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let Some(&Value::Quote(ty)) = sink.arena.value(substituted)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };

        Maybe::Present(ty)
    }

    /// `ty`, a value type read under `frame` in a type's telescope, carried
    /// into the term context of the same frame.
    ///
    /// # Specification
    /// - requires: `ty` is minted under `frame`, counting only the frames that
    ///   bind in a telescope.
    /// - ensures: `ty` itself when every frame binds; otherwise `ty` with a
    ///   binder inserted for each frame that does not, each node the rewrite
    ///   copies recorded at the origin of the node it copies and every other
    ///   node it mints with `origin`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed annotation is carried unchanged, and one
    ///   under a match's binders keeps each of its nodes at its bytes.
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    /// - witness: `lower::native::tests::a_relocated_annotation_keeps_its_bytes`
    #[spec(ensures: |ret| sink.arena.value_type(ret).is_some() || ret == ty)]
    pub(super) fn relocate_value_type(
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
        let mut copies = Vec::new();
        let carried = self.relocate(
            sink.arena,
            wrapped,
            frame,
            Binders::default(),
            Some(&mut copies),
        );
        let result = match sink.arena.comp_type(carried) {
            Some(&CompType::Returner { result: inner, .. }) => inner,
            _ => ty,
        };
        record_copied_since(
            sink,
            mark,
            origin,
            Maybe::Absent(rooted::Absent::Classifier),
            &copies,
        );

        result
    }

    /// The computation type `answer` states, read under its own frame: the
    /// written computation type, or the returner over a written value type
    /// the position returns.
    ///
    /// # Specification
    /// - requires: the answer's node is already minted or absent.
    /// - ensures: the node's computation type for a written answer and a loop
    ///   arm's, and a returner newly minted over the node's value type for a
    ///   returning one; the node's absence when it did not lower.
    /// - provides: the one reading every consumer of an answer mints it by.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function result and a thunk signed `() => T`, each
    ///   answering a constructor's classifier.
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.comp_type(id).is_some()))]
    pub(super) fn answered_type(
        &self,
        answer: Answer,
        sink: &mut Sink<'_>,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        match answer.over {
            Over::Written | Over::Loop { .. } => self.comp_type_at(answer.node),
            Over::Returning => match self.value_type_at(answer.node) {
                Maybe::Present(result) => Maybe::Present(sink.arena.comp_type_returner(result)),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            },
        }
    }

    /// `ty`, a computation type read under `from` in a type's telescope,
    /// carried into the term context of `from` and then under `lift` more
    /// binders, each node it rewrote reported into `copies` when given.
    ///
    /// # Specification
    /// - requires: `ty` is minted under `from`, counting only the frames that
    ///   bind in a telescope.
    /// - ensures: a binder inserted at each frame of `from`'s chain that does
    ///   not bind in a telescope, then every free index raised by `lift`;
    ///   `copies`, when given, gains each node a shift rewrote beside its
    ///   source.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function result and a written answer become the
    ///   motive of a nested tree; a dependent transport's motive answers where
    ///   its endpoints are written.
    /// - witness: `lower::native::tests::a_match_takes_its_answer_from_the_function_result`
    /// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
    #[spec(ensures: |ret| arena.comp_type(ret).is_some() || ret == ty)]
    pub(super) fn relocate(
        &self,
        arena: &mut CoreArena,
        ty: CompTypeId,
        from: Frame,
        lift: Binders,
        mut copies: Option<&mut Vec<Carried>>,
    ) -> CompTypeId
    {
        let mut shift = |arena: &mut CoreArena, subject, scope, amount| match copies.as_deref_mut()
        {
            Some(copies) => {
                gandr_core_term::shift_comp_type_under_traced(arena, subject, scope, amount, copies)
            },
            None => gandr_core_term::shift_comp_type_under(arena, subject, scope, amount),
        };
        let mut carried = ty;
        for (position, binds) in self.scope.telescope_binders(from).enumerate() {
            if !binds {
                let scope = Binders::from(u32::try_from(position).unwrap_or(u32::MAX));
                carried = shift(arena, carried, scope, Binders::ONE);
            }
        }
        shift(arena, carried, Binders::NONE, lift)
    }

    /// Mint the match at `case`: its scrutinee bound once over its decision
    /// tree.
    ///
    /// # Specification
    /// - requires: the scrutinee, every arm body and the answer are already
    ///   minted or absent.
    /// - ensures: the tree, every node minted descending: a data case over the
    ///   scrutinised level with the motive [`tracked_motives`] reads, each
    ///   branch a lambda per field; a sum case for a boolean; an integer
    ///   comparison bound and cased on; a hole for a stuck node; and a leaf as
    ///   its arm's body with each variable replaced by the level that settled
    ///   it and the case's context carried under the tree's binders, the
    ///   scrutinee's variable read at the root's constructor where
    ///   [`refinements`] refines it. Level zero is the scrutinee itself,
    ///   carried under the binders above its use, so no binding of it is
    ///   minted. The root carries the written origin, a leaf's copy of its
    ///   arm's body the origin of what it copies, every other node the inserted
    ///   match origin, and the arms are recorded beside the root with the
    ///   scrutinee's value; a match whose first arm matches anything is that
    ///   arm's body. Nothing when the scrutinee, a reached body or a needed
    ///   answer did not lower.
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
            Maybe::Present(answer) => match self.answered_type(answer, sink) {
                Maybe::Present(written) => {
                    let gap = Depth(
                        self.scope
                            .telescope_binders(form.frame)
                            .count()
                            .saturating_sub(self.scope.telescope_binders(answer.frame).count()),
                    );
                    let base =
                        self.relocate(sink.arena, written, answer.frame, Binders::default(), None);
                    Maybe::Present((base, gap))
                },
                Maybe::Absent(reason) => Maybe::Absent(reason),
            },
            Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        let scrutinised = Scrutinised {
            scrutinee,
            outer: Depth(self.scope.telescope_binders(form.frame).count()),
        };
        let tracked = match motive {
            Maybe::Present((base, gap))
                if form.tests.iter().any(|test| {
                    matches!(
                        *test,
                        Test::Data { .. }
                            | Test::Split {
                                dependent: Dependent(true),
                                ..
                            }
                    )
                }) =>
            {
                tracked_motives(&form.tests, base, gap, scrutinised, sink.arena)
            },
            Maybe::Present(_) | Maybe::Absent(_) => Vec::new(),
        };
        let refined = refinements(&form.tests, &tracked, scrutinised, sink.arena);
        let mut minted: Vec<Maybe<ComputationId, lowered::Absent>> = Vec::from_iter(
            form.tests
                .iter()
                .map(|_test| Maybe::Absent(lowered::Absent::Unminted)),
        );
        let mut copies = Vec::new();
        for (position, test) in form.tests.iter().enumerate().rev() {
            let read = tracked
                .get(position)
                .copied()
                .unwrap_or(Maybe::Absent(lowered::Absent::Unminted));
            let at = refined
                .get(position)
                .copied()
                .unwrap_or(Maybe::Absent(refined::Absent::Unswitched));
            let id = mint_test(
                test,
                scrutinised,
                &bodies,
                &minted,
                (read, at),
                sink,
                &mut copies,
            );
            if let Some(held) = minted.get_mut(position) {
                *held = id;
            }
        }
        self.name_fields(form, &minted, sink);
        let inserted = origin.inserted(Insertion::Match);
        let minted_root = match minted.first() {
            Some(&Maybe::Present(root)) if form.loops.is_empty() => Maybe::Present(root),
            Some(&Maybe::Present(root)) => self.with_loops(form, root, sink, &mut copies),
            Some(&Maybe::Absent(_)) | None => Maybe::Absent(lowered::Absent::Unminted),
        };
        let Maybe::Present(root) = minted_root
        else {
            record_copied_since(
                sink,
                mark,
                inserted,
                Maybe::Absent(rooted::Absent::Unminted),
                &copies,
            );
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        if sink.arena.computations_since(mark).all(|id| id != root) {
            record_copied_since(
                sink,
                mark,
                inserted,
                Maybe::Absent(rooted::Absent::Adopted),
                &copies,
            );
            return Maybe::Present(Lowered::Computation(root));
        }
        record_copied_since(
            sink,
            mark,
            inserted,
            Maybe::Present((root, origin)),
            &copies,
        );
        let mut kept = form.origin.clone();
        kept.scrutinised = Maybe::Present(scrutinee);
        sink.origins.record_case(root, kept);

        Maybe::Present(Lowered::Computation(root))
    }

    /// Records, for each field binder a data switch of `form`'s tree opens,
    /// the arm variable every arm reached through it binds there, when they
    /// agree on its name.
    ///
    /// # Specification
    /// - requires: `minted` holds the tree's nodes as [`mint_test`] minted
    ///   them, position for position.
    /// - ensures: each lambda a minted data switch's branch opens for its field
    ///   `f` under `d` tree binders is recorded as written at the arm variable
    ///   that the leaves under that branch settle at level `d + f + 1`, when at
    ///   least one leaf settles a variable there and every one that does writes
    ///   the same name; any other binder keeps no name.
    /// - provides: the source's name for a pattern variable, which a type
    ///   printed inside an arm reads its field binder by.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the origins it records live in the sink's table,
    ///   which a predicate over the lowerer cannot read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field a single arm names, and one two arms name
    ///   alike, each answer under the written name.
    /// - witness: `lower::native::tests::a_pattern_variable_names_its_field_binder`
    fn name_fields(
        &self,
        form: &CaseForm,
        minted: &[Maybe<ComputationId, lowered::Absent>],
        sink: &mut Sink<'_>,
    )
    {
        for (test, &held) in form.tests.iter().zip(minted) {
            let (
                &Test::Data {
                    depth,
                    ref branches,
                    ..
                },
                Maybe::Present(switch),
            ) = (test, held)
            else {
                continue;
            };
            let Some(&gandr_core_term::Computation::DataCase {
                branches: ref lowered,
                ..
            }) = sink.arena.computation(switch)
            else {
                continue;
            };
            let lowered = lowered.clone();
            for (&(arity, at), &branch) in branches.iter().zip(&lowered) {
                let mut lambda = branch;
                for field in 0 .. arity {
                    let level = TreeLevel(depth.0.saturating_add(field).saturating_add(1));
                    if let Some(origin) = self.field_name(form, at, level) {
                        sink.origins.place_binder(lambda, origin);
                    }
                    let Some(&gandr_core_term::Computation::Lambda(body)) =
                        sink.arena.computation(lambda)
                    else {
                        break;
                    };
                    lambda = body;
                }
            }
        }
    }

    /// The origin of the arm variable every leaf under `at` settles at
    /// `level`, when at least one does and all write one name.
    ///
    /// # Specification
    /// - requires: `at` is a node of `form`'s tree.
    /// - ensures: the first such variable's origin when the leaves under `at`
    ///   that settle a variable at `level` all write the same name; none when
    ///   no leaf does, two write different names, or the variable has no
    ///   origin.
    /// - provides: the name [`Self::name_fields`] records.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the subtree on an explicit stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::name_fields`].
    /// - witness: `lower::native::tests::a_pattern_variable_names_its_field_binder`
    #[spec(ensures: |ret| ret.is_none() || form.tests.get(at.0).is_some())]
    fn field_name(
        &self,
        form: &CaseForm,
        at: TestAt,
        level: TreeLevel,
    ) -> Option<Origin>
    {
        let mut named: Option<Placed> = None;
        let mut pending = Vec::from([at]);
        while let Some(TestAt(position)) = pending.pop() {
            match form.tests.get(position) {
                Some(&Test::Leaf {
                    arm, ref bindings, ..
                }) => {
                    let variables = form.variables.get(arm.0).map_or(&[][..], Vec::as_slice);
                    for (&settled, &variable) in bindings.iter().zip(variables) {
                        if settled != level {
                            continue;
                        }
                        match named {
                            Some(first) if self.text_at(first) != self.text_at(variable) => {
                                return None;
                            },
                            Some(_) => {},
                            None => named = Some(variable),
                        }
                    }
                },
                Some(&Test::Data { ref branches, .. }) => {
                    pending.extend(branches.iter().map(|&(_arity, child)| child));
                },
                Some(&Test::Sum { ref branches, .. }) => pending.extend(branches.iter().copied()),
                Some(&(Test::Boolean { yes, no, .. } | Test::Integer { yes, no, .. })) => {
                    pending.extend([yes, no]);
                },
                Some(&(Test::Split { child, .. } | Test::Record { child, .. })) => {
                    pending.push(child);
                },
                Some(&(Test::Pending | Test::Stuck(_))) | None => {},
            }
        }
        let variable = named?;
        match self.origin_at(variable.node) {
            Maybe::Present(origin) => Some(origin),
            Maybe::Absent(_) => None,
        }
    }

    /// The root data case `root` of the match `form` with a loop branch per
    /// loop arm after its constructors' branches.
    ///
    /// # Specification
    /// - requires: `root` is the minted root of `form`'s tree, and `form`
    ///   carries loop arms.
    /// - ensures: the data case over the root's scrutinee and motive whose
    ///   branches are the root's, then each loop arm's body in `form`'s order
    ///   with the binder its arm reads replaced by `b`, the root's answer at
    ///   the arm's loop's point over the root's branches as
    ///   [`gandr_core_term::identity::answer_at`] reads it, which the checker
    ///   reads alike; every node the replacement rewrote reported in `copies`
    ///   beside its original. The unminted absence when the root is no data
    ///   case, a body did not lower or a point does not spell.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's loop arm follows its point's branch and
    ///   reads `Base`, the value that branch returns, for its answer.
    /// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if matches!(sink.arena.computation(id), Some(gandr_core_term::Computation::DataCase { .. }))))]
    fn with_loops(
        &self,
        form: &CaseForm,
        root: ComputationId,
        sink: &mut Sink<'_>,
        copies: &mut Vec<Carried>,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let Some(&gandr_core_term::Computation::DataCase {
            scrutinee,
            motive,
            ref branches,
        }) = sink.arena.computation(root)
        else {
            return unminted;
        };
        let branches = branches.clone();
        let mut all = branches.clone();
        for arm in &form.loops {
            let Maybe::Present(body) = self.computation_at(arm.body)
            else {
                return unminted;
            };
            let Some((carrier, point, arities)) =
                self.collected.words.get(arm.words).and_then(|words| {
                    let data = self.collected.data.get(words.family)?;
                    let family = self.collected.slots.get(usize::from(data.slot))?.constant;
                    let arities: Vec<gandr_kernel_term::FieldCount> = data
                        .generators
                        .iter()
                        .map(|generator| {
                            gandr_kernel_term::FieldCount::from(generator.fields.len())
                        })
                        .collect();
                    Some((family, &words.point, arities))
                })
            else {
                return unminted;
            };
            let classifier = sink.arena.value_type_data(carrier, Vec::new());
            let Maybe::Present(at) =
                spelled_point(sink.arena, classifier, (point, &arities), &mut Vec::new())
            else {
                return unminted;
            };
            let carried = gandr_core_term::identity::answer_at(sink.arena, at, motive, &branches);
            let mut rewritten = Vec::new();
            let instantiated = gandr_core_term::instantiate_computation_traced(
                sink.arena,
                body,
                carried,
                &mut rewritten,
            );
            exits::mark_copies(sink, &rewritten);
            copies.extend_from_slice(&rewritten);
            all.push(instantiated);
        }
        Maybe::Present(sink.arena.computation_data_case(scrutinee, motive, all))
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

quenchant_shape::reason_enum! {
    /// Why a node of a match's tree reads its scrutinee as itself.
    pub mod refined {
        /// No switch above the node refines the scrutinee to a constructor.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node is the root, or the root is no data switch on the
            /// scrutinee over a bare family.
            Unswitched,
            /// The scrutinee is no variable of the case's frame.
            Unbound,
            /// The root's motive does not read its scrutinee.
            Independent,
        }
    }
}

/// The constructor a leaf reads a match's scrutinee at: the root switch's
/// branch the leaf descends from, over the root's fields.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `held` is the scrutinee's index in the case's frame, `family` the
///   bare family that classifies the root's constructors, `tag` and `arity` the
///   branch's constructor and its field count.
/// - executable: none — the record holds no tree to check its branch against.
///
/// # Adequacy
/// - hypothesis: L3 — a leaf under a dependent root reads the scrutinee at its
///   branch's constructor, and one under an independent root reads it as
///   itself.
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Refined
{
    /// The scrutinee's index in the case's frame.
    held: usize,
    /// The family the bare family type names.
    family: ConstantIndex,
    /// The branch's constructor.
    tag: ConstructorTag,
    /// The constructor's field count.
    arity: usize,
}

/// The motive of every data case and dependent split of a tree, read from the
/// root down.
///
/// # Specification
/// - requires: `tests` is a compiled tree, every child after its parent; `base`
///   is the answer in the term context of its own frame, `gap` the binders the
///   case's frame adds to it.
/// - ensures: one entry per node. The root answers `base` under `gap` more
///   binders; a data case's and a dependent split's motive is its answer with
///   its scrutinee abstracted, as [`abstracted`] reads it. A data case's
///   branches answer its motive at the constructor over their fields when the
///   motive reads its binder and the bare family classifies the constructor,
///   and its answer under their fields otherwise; a dependent split's child
///   answers its motive at the pair of its two components; every other node
///   passes its answer to its children under the binders it opens. Nodes other
///   than data cases and dependent splits answer nothing.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a split whose answer names its scrutinee reads it back at
///   the pair of its components, and one whose answer does not keeps it; a data
///   case whose answer names its scrutinee reads it back at each constructor.
/// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
#[spec(ensures: |ret| ret.len() == tests.len())]
fn tracked_motives(
    tests: &[Test],
    base: CompTypeId,
    gap: Depth,
    scrutinised: Scrutinised,
    arena: &mut CoreArena,
) -> Vec<Maybe<CompTypeId, lowered::Absent>>
{
    let binders = |count: usize| Binders::from(u32::try_from(count).unwrap_or(u32::MAX));
    let mut expected: Vec<Option<CompTypeId>> = alloc::vec![None; tests.len()];
    let mut motives = alloc::vec![Maybe::Absent(lowered::Absent::Unminted); tests.len()];
    if let Some(root) = expected.first_mut() {
        *root = Some(gandr_core_term::shift_comp_type(
            arena,
            base,
            binders(gap.0),
        ));
    }
    for (position, test) in tests.iter().enumerate() {
        let Some(here) = expected.get(position).copied().flatten()
        else {
            continue;
        };
        let mut answers: Vec<(TestAt, CompTypeId)> = Vec::new();
        let mut under = |arena: &mut CoreArena, at: TestAt, count: usize| {
            answers.push((
                at,
                gandr_core_term::shift_comp_type(arena, here, binders(count)),
            ));
        };
        match *test {
            Test::Pending | Test::Stuck(_) | Test::Leaf { .. } => {},
            Test::Data {
                level,
                depth,
                family,
                ref branches,
            } => {
                let scrutinee = level_value(arena, scrutinised, depth, level);
                let context = Depth(scrutinised.outer.0.saturating_add(depth.0));
                let motive = abstracted(arena, here, scrutinee, context);
                if let Some(slot) = motives.get_mut(position) {
                    *slot = Maybe::Present(motive);
                }
                let reads = matches!(
                    gandr_core_term::strengthen_comp_type(arena, motive),
                    Maybe::Absent(_)
                );
                for (tag, &(arity, at)) in branches.iter().enumerate() {
                    let answer = match family {
                        Maybe::Present(family) if reads => {
                            let lifted = gandr_core_term::shift_comp_type_under(
                                arena,
                                motive,
                                Binders::ONE,
                                binders(arity),
                            );
                            let fields = (0 .. arity)
                                .rev()
                                .map(|field| variable(arena, Depth(field)))
                                .collect();
                            let at_constructor =
                                constructed(arena, family, ConstructorTag::from(tag), fields);
                            gandr_core_term::instantiate_comp_type(arena, lifted, at_constructor)
                        },
                        Maybe::Present(_) | Maybe::Absent(_) => {
                            gandr_core_term::shift_comp_type(arena, here, binders(arity))
                        },
                    };
                    answers.push((at, answer));
                }
            },
            Test::Boolean { yes, no, .. } => {
                under(arena, yes, 1_usize);
                under(arena, no, 1_usize);
            },
            Test::Integer { yes, no, .. } => {
                under(arena, yes, 2_usize);
                under(arena, no, 2_usize);
            },
            Test::Split {
                arity,
                dependent: Dependent(false),
                child,
                ..
            } => under(arena, child, arity),
            Test::Split {
                level,
                depth,
                dependent: Dependent(true),
                child,
                ..
            } => {
                let scrutinee = level_value(arena, scrutinised, depth, level);
                let context = Depth(scrutinised.outer.0.saturating_add(depth.0));
                let motive = abstracted(arena, here, scrutinee, context);
                if let Some(slot) = motives.get_mut(position) {
                    *slot = Maybe::Present(motive);
                }
                let lifted = gandr_core_term::shift_comp_type_under(
                    arena,
                    motive,
                    Binders::ONE,
                    binders(2_usize),
                );
                let first = variable(arena, Depth(1_usize));
                let second = variable(arena, Depth::default());
                let pair = arena.value_tuple(&[first, second]);
                answers.push((
                    child,
                    gandr_core_term::instantiate_comp_type(arena, lifted, pair),
                ));
            },
            Test::Record {
                ref labels, child, ..
            } => under(arena, child, labels.len()),
            Test::Sum { ref branches, .. } => {
                for &at in branches {
                    under(arena, at, 1_usize);
                }
            },
        }
        for (at, answer) in answers {
            if let Some(slot) = expected.get_mut(at.0) {
                *slot = Some(answer);
            }
        }
    }

    motives
}

/// The constructor each node of a match's tree reads the scrutinee at.
///
/// # Specification
/// - requires: `tests` is a compiled tree, every child after its parent;
///   `tracked` holds the motive [`tracked_motives`] read for each node, or
///   nothing.
/// - ensures: one entry per node. When the root is a data switch on level zero
///   over a bare family, the scrutinee is an intuitionistic variable of the
///   case's frame and the root's motive reads its binder, every node below a
///   root branch reads the scrutinee at that branch's constructor and the root
///   reads it as itself; otherwise every node reads it as itself, with the
///   first reason that holds.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a root whose answer names its scrutinee refines each
///   branch's leaves, and one whose answer does not refines none.
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
#[spec(ensures: |ret| ret.len() == tests.len())]
fn refinements(
    tests: &[Test],
    tracked: &[Maybe<CompTypeId, lowered::Absent>],
    scrutinised: Scrutinised,
    arena: &mut CoreArena,
) -> Vec<Maybe<Refined, refined::Absent>>
{
    let unrefined = |reason| alloc::vec![Maybe::Absent(reason); tests.len()];
    let Some(&Test::Data {
        level,
        family: Maybe::Present(family),
        ref branches,
        ..
    }) = tests.first()
    else {
        return unrefined(refined::Absent::Unswitched);
    };
    if level != TreeLevel::default() {
        return unrefined(refined::Absent::Unswitched);
    }
    let held = match arena.value(scrutinised.scrutinee) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => usize::try_from(u32::from(index)).unwrap_or(usize::MAX),
        _ => usize::MAX,
    };
    if held >= scrutinised.outer.0 {
        return unrefined(refined::Absent::Unbound);
    }
    let Some(&Maybe::Present(motive)) = tracked.first()
    else {
        return unrefined(refined::Absent::Independent);
    };
    if matches!(
        gandr_core_term::strengthen_comp_type(arena, motive),
        Maybe::Present(_)
    ) {
        return unrefined(refined::Absent::Independent);
    }
    let mut refined = unrefined(refined::Absent::Unswitched);
    for (tag, &(arity, at)) in branches.iter().enumerate() {
        if let Some(slot) = refined.get_mut(at.0) {
            *slot = Maybe::Present(Refined {
                held,
                family,
                tag: ConstructorTag::from(tag),
                arity,
            });
        }
    }
    for (position, test) in tests.iter().enumerate().skip(1) {
        let Some(&Maybe::Present(read)) = refined.get(position)
        else {
            continue;
        };
        let mut mark = |at: TestAt| {
            if let Some(slot) = refined.get_mut(at.0) {
                *slot = Maybe::Present(read);
            }
        };
        match *test {
            Test::Pending | Test::Stuck(_) | Test::Leaf { .. } => {},
            Test::Data { ref branches, .. } => {
                for &(_arity, at) in branches {
                    mark(at);
                }
            },
            Test::Boolean { yes, no, .. } | Test::Integer { yes, no, .. } => {
                mark(yes);
                mark(no);
            },
            Test::Split { child, .. } | Test::Record { child, .. } => mark(child),
            Test::Sum { ref branches, .. } => {
                for &at in branches {
                    mark(at);
                }
            },
        }
    }

    refined
}

/// The constructor `tag` of the parameterless family `family` over `fields`.
///
/// # Specification
/// trivial.
fn constructed(
    arena: &mut CoreArena,
    family: ConstantIndex,
    tag: ConstructorTag,
    fields: Vec<ValueId>,
) -> ValueId
{
    let classifier = arena.value_type_data(family, Vec::new());
    arena.value_constructor(classifier, tag, fields)
}

/// The closed constructor term the prefix-ordered `point` spells over
/// `carrier`, whose constructors take `arities` fields, every value it mints
/// reported to `minted` in mint order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the term whose prefix reading is `point`'s constructor nodes,
///   each a constructor of `carrier` over the terms after it; the unminted
///   absence for an empty point.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the point's nodes, not recursion.
/// - measure: the nodes left.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's point is `Base`, the loop arm's case at it
///   and the words' path type alike.
/// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[spec(captures: before = minted.len(), ensures: |ret| minted.len() >= before && matches!(ret, Maybe::Absent(_)) == (minted.len() == before))]
fn spelled_point(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
    (point, arities): (
        &[gandr_core_term::RuleNode],
        &[gandr_kernel_term::FieldCount],
    ),
    minted: &mut Vec<ValueId>,
) -> Maybe<ValueId, lowered::Absent>
{
    let mut built = Vec::new();
    for node in point.iter().rev() {
        let gandr_core_term::RuleNode::Constructor(tag) = *node
        else {
            continue;
        };
        let arity = arities
            .get(usize::from(tag))
            .copied()
            .map_or(0_usize, usize::from);
        let fields: Vec<ValueId> = built
            .drain(built.len().saturating_sub(arity) ..)
            .rev()
            .collect();
        let value = arena.value_constructor(carrier, tag, fields);
        minted.push(value);
        built.push(value);
    }
    built
        .last()
        .copied()
        .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present)
}

/// `ty`, read under `context` binders, with the value `scrutinee` abstracted
/// as one binder more: the motive a dependent split reads.
///
/// # Specification
/// - requires: `ty` and `scrutinee` are read under `context` binders.
/// - ensures: for an intuitionistic variable `context` binders hold, `ty` under
///   one binder more with that variable read as the new binder and every other
///   index read one further out; for any other scrutinee, `ty` under one binder
///   more, reading none of it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an answer naming the scrutinee parameter abstracts it,
///   and one naming another parameter keeps it.
/// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
#[spec(ensures: |ret| arena.comp_type(ret).is_some())]
fn abstracted(
    arena: &mut CoreArena,
    ty: CompTypeId,
    scrutinee: ValueId,
    context: Depth,
) -> CompTypeId
{
    let held = match arena.value(scrutinee) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => usize::try_from(u32::from(index)).unwrap_or(usize::MAX),
        _ => usize::MAX,
    };
    if held >= context.0 {
        return gandr_core_term::shift_comp_type(arena, ty, Binders::ONE);
    }
    let environment: Vec<ValueId> = (0 .. context.0)
        .map(|position| {
            if position == held {
                variable(arena, Depth::default())
            }
            else {
                variable(arena, Depth(position.saturating_add(1)))
            }
        })
        .collect();
    let quoted = arena.value_quote_computation(ty);
    match gandr_core_term::substitute_environment(arena, TermId::Value(quoted), &environment) {
        TermId::Value(substituted) => match arena.value(substituted) {
            Some(&Value::QuoteComputation(motive)) => motive,
            _ => gandr_core_term::shift_comp_type(arena, ty, Binders::ONE),
        },
        TermId::Computation(_) => gandr_core_term::shift_comp_type(arena, ty, Binders::ONE),
    }
}

/// Mint one node of a match's tree over its already minted children.
///
/// # Specification
/// - requires: every child of `test` is minted in `minted` or absent; `read` is
///   the motive [`tracked_motives`] read for this node, and `refined` the
///   constructor [`refinements`] reads the node's scrutinee at.
/// - ensures: as [`Lowerer::mint_case`], for one node; a data case and a
///   dependent split read the read motive; a leaf under a refining root reads
///   the scrutinee's variable as the refined constructor over the root's
///   fields; nothing when a child, the arm's body or a needed motive is absent.
///   A leaf's copy of an exit or of a bind whose rest is distributed is
///   recorded as its original is, and every copy a leaf makes is reported in
///   `copies` beside its original.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::mint_case`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.computation(id).is_some()))]
fn mint_test(
    test: &Test,
    scrutinised: Scrutinised,
    bodies: &[Maybe<ComputationId, lowered::Absent>],
    minted: &[Maybe<ComputationId, lowered::Absent>],
    (read, refined): (
        Maybe<CompTypeId, lowered::Absent>,
        Maybe<Refined, refined::Absent>,
    ),
    sink: &mut Sink<'_>,
    copies: &mut Vec<Carried>,
) -> Maybe<ComputationId, lowered::Absent>
{
    let child = |at: TestAt| {
        minted
            .get(at.0)
            .copied()
            .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
    };
    match *test {
        Test::Pending => Maybe::Absent(lowered::Absent::Unminted),
        Test::Stuck(hole) => Maybe::Present(sink.arena.computation_hole(hole)),
        Test::Leaf {
            arm,
            depth,
            ref bindings,
        } => {
            let Some(&Maybe::Present(body)) = bodies.get(arm.0)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            if depth == Depth::default()
                && bindings.is_empty()
                && matches!(refined, Maybe::Absent(_))
            {
                return Maybe::Present(body);
            }
            let mut environment =
                Vec::with_capacity(bindings.len().saturating_add(scrutinised.outer.0));
            for &level in bindings.iter().rev() {
                environment.push(level_value(sink.arena, scrutinised, depth, level));
            }
            for outer in 0 .. scrutinised.outer.0 {
                let read = match refined {
                    Maybe::Present(refined) if refined.held == outer => {
                        let fields = (0 .. refined.arity)
                            .map(|field| {
                                let level = TreeLevel(field.saturating_add(1));
                                level_value(sink.arena, scrutinised, depth, level)
                            })
                            .collect();
                        constructed(sink.arena, refined.family, refined.tag, fields)
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => {
                        variable(sink.arena, Depth(outer.saturating_add(depth.0)))
                    },
                };
                environment.push(read);
            }
            let mut carried = Vec::new();
            match gandr_core_term::substitute_environment_traced(
                sink.arena,
                TermId::Computation(body),
                &environment,
                &mut carried,
            ) {
                TermId::Computation(substituted) => {
                    exits::mark_copies(sink, &carried);
                    copies.extend_from_slice(&carried);
                    Maybe::Present(substituted)
                },
                TermId::Value(_) => Maybe::Absent(lowered::Absent::Unminted),
            }
        },
        Test::Data {
            level,
            depth,
            ref branches,
            ..
        } => {
            let Maybe::Present(motive) = read
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
            let scrutinee = level_value(sink.arena, scrutinised, depth, level);
            Maybe::Present(
                sink.arena
                    .computation_data_case(scrutinee, motive, lowered_branches),
            )
        },
        Test::Boolean {
            level,
            depth,
            yes,
            no,
        } => match (child(yes), child(no)) {
            (Maybe::Present(left), Maybe::Present(right)) => {
                let scrutinee = level_value(sink.arena, scrutinised, depth, level);
                Maybe::Present(sink.arena.computation_case(scrutinee, &[left, right]))
            },
            _ => Maybe::Absent(lowered::Absent::Unminted),
        },
        Test::Integer {
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
            let branched = sink.arena.computation_case(answer, &[left, right]);
            Maybe::Present(sink.arena.computation_bind(test, branched))
        },
        Test::Split {
            level,
            depth,
            arity,
            dependent,
            child: at,
        } => {
            let Maybe::Present(body) = child(at)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let scrutinee = level_value(sink.arena, scrutinised, depth, level);
            if dependent.0 {
                let Maybe::Present(read) = read
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                return Maybe::Present(sink.arena.computation_dependent_split(
                    scrutinee,
                    ComponentCount::from(arity),
                    read,
                    body,
                ));
            }
            Maybe::Present(sink.arena.computation_split(
                scrutinee,
                ComponentCount::from(arity),
                body,
            ))
        },
        Test::Record {
            level,
            depth,
            ref labels,
            child: at,
        } => {
            let Maybe::Present(mut body) = child(at)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            for (offset, label) in labels.iter().enumerate().rev() {
                let under = Depth(depth.0.saturating_add(offset));
                let record = level_value(sink.arena, scrutinised, under, level);
                let projected = sink
                    .arena
                    .computation_record_projection(record, label.clone());
                body = sink.arena.computation_bind(projected, body);
            }
            Maybe::Present(body)
        },
        Test::Sum {
            level,
            depth,
            ref branches,
        } => {
            let mut lowered_branches = Vec::with_capacity(branches.len());
            for &at in branches {
                let Maybe::Present(branch) = child(at)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                lowered_branches.push(branch);
            }
            let scrutinee = level_value(sink.arena, scrutinised, depth, level);
            Maybe::Present(sink.arena.computation_case(scrutinee, &lowered_branches))
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
        Maybe::Present(literal) => Ok(Matcher::Integer(literal)),
        Maybe::Absent(_) => Err(LoweringRefusal::MalformedLiteral {
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
        Matcher::Binder(variable) => row.bindings.push((variable, level)),
        Matcher::Hole(hole) => {
            if let Maybe::Absent(_) = row.stuck {
                row.stuck = Maybe::Present(hole);
            }
        },
        Matcher::Wild
        | Matcher::Constructor { .. }
        | Matcher::Boolean(_)
        | Matcher::Integer(_)
        | Matcher::Tuple { .. }
        | Matcher::Record { .. }
        | Matcher::Injection { .. } => {},
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

/// The levels `width` fresh binders under `depth` tree binders introduce,
/// outermost first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the levels `depth + 1` through `depth + width`, in order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a split's components and a record's fields each reach
///   their arm at their own level.
/// - witness: `lower::native::tests::telescope_patterns_split_and_project`
#[spec(ensures: |ret| ret.len() == width.0 && ret.iter().enumerate().all(|(offset, level)| level.0 == depth.0.saturating_add(offset).saturating_add(1)))]
fn fresh(
    depth: Depth,
    width: Width,
) -> Vec<TreeLevel>
{
    (0 .. width.0)
        .map(|offset| TreeLevel(depth.0.saturating_add(offset).saturating_add(1)))
        .collect()
}

/// Allocate a slot in `patterns` for each of `queued`, as a fresh stretch
/// of the part store, and queue each on `work` to be read into its slot.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the stretch of the new parts, one per queued pattern in order,
///   each queued on `work` with its slot, the first popped first.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a constructor's, a tuple's and an injection's parts are
///   each read into their own slot.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::telescope_patterns_split_and_project`
#[spec(
    captures: before = (patterns.parts.len(), work.len()),
    ensures: |ret| ret.start == before.0 && ret.end == before.0.saturating_add(queued.len()) && work.len() == before.1.saturating_add(queued.len()),
)]
fn allocated(
    patterns: &mut Written,
    work: &mut Vec<Queued>,
    queued: &[Queued],
) -> Stretch
{
    let start = patterns.parts.len();
    for each in queued {
        let slot = PatternAt(patterns.shapes.len());
        patterns.shapes.push((each.at, Matcher::Wild));
        patterns.parts.push(slot);
    }
    let end = patterns.parts.len();
    for (offset, &each) in queued.iter().enumerate().rev() {
        if let Some(&slot) = patterns.parts.get(start.saturating_add(offset)) {
            work.push(Queued { slot, ..each });
        }
    }

    Stretch { start, end }
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
pub(super) fn record_since(
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
/// - witness: `lower::native::tests::a_leaf_copy_keeps_each_use_naming_its_pattern_variable`
/// - witness: `lower::native::tests::a_leaf_copy_of_a_copy_keeps_the_use_naming_its_binder`
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
/// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
/// - witness: `lower::native::tests::a_leaf_keeps_its_arm_body_written`
/// - witness: `lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
/// - witness: `lower::native::tests::a_leaf_copy_keeps_each_use_naming_its_pattern_variable`
#[spec(ensures: sink.arena.values_since(mark).all(|id| matches!(sink.origins.value(id), Maybe::Present(_)))
    && sink.arena.computations_since(mark).all(|id| match root {
        | Maybe::Present((held, written)) if held == id => sink.origins.computation(id) == Maybe::Present(written),
        | _ => matches!(sink.origins.computation(id), Maybe::Present(_)),
    }))]
fn record_copied_since(
    sink: &mut Sink<'_>,
    mark: gandr_core_term::ArenaWatermark,
    origin: Origin,
    root: Maybe<(ComputationId, Origin), rooted::Absent>,
    carried: &[Carried],
)
{
    let sources = exits::Sources::of(carried);
    for id in sink.arena.values_since(mark) {
        let recorded = sources.value(sink, id, origin);
        sink.origins.record_value(id, recorded);
    }
    for id in sink.arena.computations_since(mark) {
        match root {
            Maybe::Present((held, written)) if held == id => {
                sink.origins.record_computation(id, written);
            },
            Maybe::Present(_) | Maybe::Absent(_) => {
                let recorded = sources.computation(sink, id, origin);
                sink.origins.record_computation(id, recorded);
                sources.keep_case(sink, id);
            },
        }
    }
    for id in sink.arena.value_types_since(mark) {
        let recorded = sources.value_type(sink, id, origin);
        sink.origins.record_value_type(id, recorded);
    }
    for id in sink.arena.comp_types_since(mark) {
        let recorded = sources.comp_type(sink, id, origin);
        sink.origins.record_comp_type(id, recorded);
    }
    exits::label_replaced(sink, carried);
    carry_bindings(sink, carried, mark);
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
    ///   binds and makes the function's fixpoint claim descent; each leading
    ///   argument, which the call erases, is labelled with its parameter's
    ///   written type.
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
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Variable(..))))]
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
                Shape::Form {
                    former: Former::Name,
                    ..
                } => {
                    let written = self.name_at(passed);
                    matches!(
                        self.scope.resolve(frame, written, &mut self.fuel)?,
                        Maybe::Present(found) if found.binder == parameter.frame
                    )
                },
                Shape::Root | Shape::Form { .. } | Shape::Repair(_) | Shape::Layout => false,
            };
            if !unchanged {
                let varied = Site {
                    at: passed,
                    ..descent.call
                };
                return Err(varied.out(FragmentBoundary::NonUniform));
            }
            // The argument is the parameter itself, which the fixpoint binds
            // outside the call: it answers at the parameter's written type.
            if let Maybe::Present(declared) = parameter.declared
                && let Reading::ValueType(read) = self.reading(declared)
            {
                self.labels.push(LabelSite {
                    written: passed.span,
                    held: declared,
                    read: LabelRead::ValueType(read),
                });
            }
        }
        if let Some(held) = self.recursions.get_mut(&bound.binder) {
            held.claimed = Claimed(true);
        }
        self.plan(site, Plan::Variable(bound.index, bound.binder));

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
            Maybe::Present(frame) => Maybe::Present(match self.recursions.get(&frame) {
                Some(held) if held.claimed.0 => FixpointEvidence::StructuralDescent,
                Some(_) | None => FixpointEvidence::Partial,
            }),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}

/// Whether a rule side binds its variables or reads the left side's.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding
{
    /// The left side: a variable's first occurrence takes the next ordinal.
    Binds,
    /// The right side: a variable reads the ordinal the left side gave it.
    Reads,
}

quenchant_shape::reason_enum! {
    /// Why a rule side is not a presented type's.
    pub(crate) mod rule_side {
        /// The reason the side was passed over.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// It applies an operation or a results tuple, or a constructor
            /// of another family.
            Foreign,
            /// Its right side names a variable its left side does not bind.
            Unbound,
        }
    }
}

/// One rule side in pre-order over a family's constructors `names`, its
/// variables numbered through `variables`.
///
/// # Specification
/// - requires: `variables` holds the left side's variables when `binding` reads
///   them.
/// - ensures: one node per term node, a constructor by its position in `names`
///   and a variable by its position in `variables` — appended there on its
///   first occurrence when `binding` binds.
/// - fails: [`rule_side::Absent::Foreign`] for an operation, a results tuple or
///   a constructor `names` does not hold; [`rule_side::Absent::Unbound`] for a
///   variable a reading side meets unbound.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion.
/// - measure: the term nodes still to visit.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::presentation`].
/// - witness: `lower::native::tests::a_presented_family_lowers_its_rules`
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref nodes) => !nodes.is_empty(),
    Maybe::Absent(_) => true,
})]
fn rule_side(
    side: &gandr_theory_levitation::FreeTerm,
    names: &[SourceFragment<'_>],
    variables: &mut Vec<gandr_theory_levitation::Name>,
    binding: Binding,
) -> Maybe<alloc::boxed::Box<[gandr_core_term::RuleNode]>, rule_side::Absent>
{
    let mut nodes = Vec::new();
    let mut pending = Vec::from([side.to_node()]);
    while let Some(node) = pending.pop() {
        match node.view() {
            gandr_theory_levitation::TermView::Var(name) => {
                let position = match variables.iter().position(|bound| bound == name) {
                    Some(position) => position,
                    None if binding == Binding::Binds => {
                        variables.push(name.clone());
                        variables.len().saturating_sub(1)
                    },
                    None => return Maybe::Absent(rule_side::Absent::Unbound),
                };
                let Ok(ordinal) = u32::try_from(position)
                else {
                    return Maybe::Absent(rule_side::Absent::Unbound);
                };
                nodes.push(gandr_core_term::RuleNode::Variable(
                    gandr_core_term::RuleVariable::from(ordinal),
                ));
            },
            gandr_theory_levitation::TermView::Ctor { name, args } => {
                let Some(tag) = names
                    .iter()
                    .position(|&written| <&str>::from(written) == name.as_ref())
                else {
                    return Maybe::Absent(rule_side::Absent::Foreign);
                };
                nodes.push(gandr_core_term::RuleNode::Constructor(
                    ConstructorTag::from(tag),
                ));
                let mark = pending.len();
                pending.extend(args);
                if let Some(children) = pending.get_mut(mark ..) {
                    children.reverse();
                }
            },
            gandr_theory_levitation::TermView::Op { .. }
            | gandr_theory_levitation::TermView::Results { .. } => {
                return Maybe::Absent(rule_side::Absent::Foreign);
            },
        }
    }
    Maybe::Present(nodes.into_boxed_slice())
}
