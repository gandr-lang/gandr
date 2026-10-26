//! The four classes every refusal of the core pipeline answers to, and the
//! tracking issue an unimplemented one names.
//!
//! # Whose fact a failure is, decided by a type
//!
//! A refusal records whose fact a failure is: an absence the author has not
//! supplied yet, a feature gandr has not implemented, a form the author wrote
//! wrongly or the language's design refuses, or a fault of the engine's own or
//! of its caller. A feature not built yet is a different fact from a form that
//! is wrong, and only the first says anything about gandr's reach, so it
//! carries the issue whose landing builds it: every face that shows the
//! refusal names that issue.
//!
//! # One vocabulary below every producer
//!
//! The lowering, the checker and its bridge each classify their own refusals
//! with their own wildcard-free match, and a report groups them under these
//! classes. The classes live in the lowest crate every producer depends on,
//! so no producer names another and the vocabulary is one enum. Which refusal
//! falls in which class, and which issue an unimplemented one names, is
//! decided by the crate that owns the refusal.

use alloc::format;
use alloc::string::String;
use core::fmt;

use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a class names no tracking issue.
    pub mod tracked {
        /// The reason a refusal's class names no issue: it records no
        /// feature gandr has not built.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The author has not supplied it yet.
            UserAbsence,
            /// The author wrote it wrongly, or the design refuses it.
            MalformedSource,
            /// The engine failed.
            EngineFault,
        }
    }
}

/// The issue on gandr's tracker whose landing builds what a refusal or an
/// editor answer is missing.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct TrackingIssue(u16);

impl TrackingIssue
{
    /// Univalence at every stratum, proved as a theorem: a degree, a
    /// catalogue or a bound no certified stratum reaches.
    pub const UNIVALENCE: Self = Self(312);
    /// A universe equivalence over a list whose round trip reads the tail.
    pub const LIST_TAIL: Self = Self(524);
    /// The apart union `A | B`, under the row kinds.
    pub const UNION: Self = Self(2273);
    /// The shell block, `#!{ … }`.
    pub const SHELL_BLOCK: Self = Self(1057);
    /// A projection, `e.1` or `e.field`, where the fragment reads none.
    pub const PROJECTION: Self = Self(1106);
    /// Packages: `pack`, `unpack` and the package type.
    pub const PACKAGES: Self = Self(1108);
    /// A number literal written with the `f32` suffix, under the float rule.
    pub const TYPED_NUMBER: Self = Self(2563);
    /// An operator declaration, and an operator outside the prelude's
    /// vocabulary, which only a declaration would bring.
    pub const OPERATOR_DECLARATION: Self = Self(1111);
    /// A thunk type's grade.
    pub const THUNK_GRADE: Self = Self(1112);
    /// A session action naming as its endpoint a form no fork binds, such as
    /// a function parameter at a session type.
    pub const ENDPOINT_PARAMETER: Self = Self(1862);
    /// An import whose address has a scheme, which nothing resolves.
    pub const SCHEME: Self = Self(1233);
    /// An extern block, binding a library's functions: native interop's
    /// first rung; and a host escape across the same boundary.
    pub const EXTERN_BLOCK: Self = Self(327);
    /// A case or a form over an indexed family.
    pub const INDEXED: Self = Self(1314);
    /// Function extensionality past the first-order coverage.
    pub const FUNEXT: Self = Self(1315);
    /// A universe equivalence outside the decided codes.
    pub const EQUIV: Self = Self(1316);
    /// A `forward` outside the decided codes.
    pub const FORWARD: Self = Self(1835);
    /// A ride the checker cannot move.
    pub const RIDE: Self = Self(1318);
    /// A declaration naming a world, which the kernel does not replay.
    pub const KERNEL_WORLD: Self = Self(1320);
    /// A kinded or parameterized type component under an opaque ascription.
    pub const ASCRIPTION: Self = Self(1321);
    /// A model signature's component relating a many-out operation's results.
    pub const MODEL_MANY_OUT: Self = Self(1322);
    /// A model signature's circuit rule.
    pub const MODEL_CIRCUIT: Self = Self(1323);
    /// A model signature's law over a binding port.
    pub const MODEL_BINDING: Self = Self(2565);
    /// A bare index `ys[i]` of a list no hold holds.
    pub const UNHELD_INDEX: Self = Self(2670);
    /// A model signature's operation abstracting an atom over a port.
    pub const MODEL_ABSTRACTION: Self = Self(1561);
    /// A freshness condition whose rule matches one variable both under an
    /// abstraction and beside it, in a signature where a term can name an
    /// atom.
    pub const UNDECIDED_CONDITION: Self = Self(1934);
    /// A recursive call's claim naming a measure, a stage or a cost.
    pub const RECURSIVE_CLAIM: Self = Self(1497);
    /// Shared sessions: `fork !`, `dup`, `acquire` and `release`.
    pub const SHARED_SESSIONS: Self = Self(1501);
    /// A stage written under a form that places none, a path's carrier.
    pub const PLACED_STAGE: Self = Self(1502);
    /// The unknown type `?`.
    pub const UNKNOWN_TYPE: Self = Self(1503);
    /// A match on a view, `case e with v { … }`.
    pub const CASE_VIEW: Self = Self(1506);
    /// An operation written with a circuit body.
    pub const OPERATION_FILLER: Self = Self(1507);
    /// A fillerless higher cell: a rule between rules.
    pub const HIGHER_CELL: Self = Self(1508);
    /// A reversible map, `<->`.
    pub const REVERSIBLE: Self = Self(1509);
    /// A theory law with an operation nested in producer position.
    pub const NESTED_OPERATION: Self = Self(1510);
    /// A circuit rule rewriting two redexes at once.
    pub const PARALLEL_REDEXES: Self = Self(1511);
    /// A declaration with effects or control past a deep handler, which the
    /// kernel replays as the fold of its effect's free model: the pure kernel
    /// does not replay it yet.
    pub const KERNEL_EFFECTS: Self = Self(2742);
    /// A declaration naming a capability, which the kernel does not replay.
    pub const KERNEL_CAPABILITY: Self = Self(1625);
    /// A declaration holding memory or a buffer, which the kernel does not
    /// replay.
    pub const KERNEL_MEMORY: Self = Self(1626);
    /// A declaration naming a run, a recorded run or a ride, which the kernel
    /// does not replay.
    pub const KERNEL_RUN: Self = Self(1627);
    /// A sealed abstract type, which the kernel does not replay.
    pub const KERNEL_ABSTRACT: Self = Self(1629);
    /// A static lambda the readmission cannot normalise away, which the kernel
    /// does not replay.
    pub const KERNEL_STATIC_LAMBDA: Self = Self(1630);
    /// A staged type in a term, which the kernel does not replay.
    pub const KERNEL_STAGE: Self = Self(1631);
    /// An infix form the lowering does not read: list concatenation, or a
    /// path cons whose left operand is neither a loop nor `back` of one.
    pub const INFIX_FORM: Self = Self(1997);
    /// A match of no arms over a type no data switch reads, written with its
    /// answer type.
    pub const EMPTY_CASE_ANSWER: Self = Self(1998);
    /// A constructor field at a finite grade other than `1`.
    pub const FIELD_GRADE: Self = Self(2033);
    /// `Eq.generic` at a declaration with parameters or indices, a nested or
    /// mutual recursion, or a dependent field; a derived law's induction.
    pub const GENERIC_EQUALITY: Self = Self(2345);
    /// A case whose motive reads its scrutinee: a derived law over a field of
    /// a sum or a tuple, and transitivity's inversion of a conjunction.
    pub const CASE_MOTIVE: Self = Self(2374);
    /// A bind, circuit, codata, derive, manifest sort or theory declaration
    /// standing where a term is read.
    pub const DECLARATION_AS_TERM: Self = Self(2645);
    /// A pattern the lowering does not read where it stands.
    pub const PATTERN_FORM: Self = Self(2647);
    /// An annotation `(e : T)` where a type, or nothing, is read.
    pub const ANNOTATION: Self = Self(2648);
    /// String interpolation with no `string.append` in the prelude.
    pub const INTERPOLATION: Self = Self(2649);
    /// A grade on a list, run or prefix type.
    pub const TYPE_GRADE: Self = Self(2650);
    /// The type abstraction `fn [T] { … }`.
    pub const TYPE_ABSTRACTION: Self = Self(2651);
    /// The statement `val p = e ;`.
    pub const VAL: Self = Self(2652);
    /// A stated type or a method call whose declaration the collection does
    /// not carry.
    pub const UNCARRIED_DECLARATION: Self = Self(2654);
    /// A presentation block whose body the description does not read.
    pub const PRESENTATION: Self = Self(2655);
    /// A recorded or a dialogue move of a shape the lowering does not read.
    pub const MOVES: Self = Self(2656);
    /// A combined supply, an unowned staged supply, or a stage resident of
    /// more than one tile.
    pub const SUPPLIES: Self = Self(2657);
    /// A capability scope over a theory no declaration owns.
    pub const UNOWNED_SCOPE: Self = Self(2658);
    /// A model type, a manifest model type or a model signature of a shape
    /// the lowering does not read.
    pub const MODEL_TYPE: Self = Self(2659);
    /// A session type the protocol builder does not read.
    pub const SESSION_PROTOCOL: Self = Self(2660);
    /// A univalence resident not in digits, or a univalence description the
    /// lowering does not read.
    pub const UA_RESIDENT: Self = Self(2661);
    /// A data block's cell member with parameters, constructor block member
    /// or generator attribute block.
    pub const DATA_MEMBER: Self = Self(2662);
    /// A function-valued field, which the first-order description code does
    /// not hold.
    pub const HIGHER_ORDER_FIELD: Self = Self(2511);
    /// A field whose type names a field before it.
    pub const DEPENDENT_FIELD: Self = Self(2663);
    /// A type with no first-order description reference.
    pub const TYPE_SHAPE: Self = Self(2664);
    /// A description the native interpreter gives no interpretation.
    pub const NATIVE_DECODE: Self = Self(2665);
    /// An operation feeding an output from several monomials, or of an arity
    /// the cell frame cannot hold.
    pub const OPERATION_SHAPE: Self = Self(2666);
    /// A derivation over an indexed sort or a nested model, or a peak
    /// variable no term of its sort stands for.
    pub const DERIVE_INDEXED: Self = Self(2667);
    /// An implicit telescope on a declaration that is no function.
    pub const IMPLICIT_TELESCOPE: Self = Self(2668);
    /// A value lift, a numeric literal, the numeric atom or a universe over a
    /// sort parameter, which the judgement has no rule for.
    pub const JUDGEMENT_FORMER: Self = Self(2669);

    /// The issue's page.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn url(self) -> String
    {
        format!("https://github.com/gandr-lang/gandr/issues/{}", self.0)
    }
}

impl fmt::Display for TrackingIssue
{
    /// `#` and the issue's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "#{}", self.0)
    }
}

/// Whose fact a refusal records.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FailureClass
{
    /// The author has not supplied it yet: reportable as a ledger entry, and
    /// the only class that may become an obligation.
    UserAbsence,
    /// gandr has not implemented what the author wrote; the issue tracks it.
    Unimplemented(TrackingIssue),
    /// The author wrote it wrongly, or the language's design refuses it.
    MalformedSource,
    /// The engine failed for reasons of its own or its caller's.
    EngineFault,
}

impl FailureClass
{
    /// The issue tracking what an unimplemented refusal is missing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn tracking(self) -> Maybe<TrackingIssue, tracked::Absent>
    {
        match self {
            Self::Unimplemented(issue) => Maybe::Present(issue),
            Self::UserAbsence => Maybe::Absent(tracked::Absent::UserAbsence),
            Self::MalformedSource => Maybe::Absent(tracked::Absent::MalformedSource),
            Self::EngineFault => Maybe::Absent(tracked::Absent::EngineFault),
        }
    }
}

impl fmt::Display for FailureClass
{
    /// Writes the class's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::UserAbsence => f.write_str("user absence"),
            Self::Unimplemented(_) => f.write_str("unimplemented"),
            Self::MalformedSource => f.write_str("malformed source"),
            Self::EngineFault => f.write_str("engine fault"),
        }
    }
}
