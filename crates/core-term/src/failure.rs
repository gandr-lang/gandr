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
    /// A `drop` of a session endpoint.
    pub const DROP: Self = Self(1054);
    /// A `forall` type.
    pub const FORALL: Self = Self(1055);
    /// A union or an intersection type.
    pub const UNION_INTERSECTION: Self = Self(1056);
    /// The shell block, `#!{ … }`.
    pub const SHELL_BLOCK: Self = Self(1057);
    /// A projection, `e.1` or `e.field`, where the fragment reads none.
    pub const PROJECTION: Self = Self(1106);
    /// Packages: `pack`, `unpack` and the package type.
    pub const PACKAGES: Self = Self(1108);
    /// A number literal written with its type.
    pub const TYPED_NUMBER: Self = Self(1109);
    /// An operator declaration.
    pub const OPERATOR_DECLARATION: Self = Self(1111);
    /// A thunk type's grade.
    pub const THUNK_GRADE: Self = Self(1112);
    /// Delegation: an endpoint sent over another endpoint.
    pub const DELEGATION: Self = Self(1167);
    /// An unimplemented form or member whose feature no issue of its own
    /// tracks yet: the epic files one for it once a source reaches it.
    pub const UNFILED: Self = Self(1207);
    /// An import whose address has a scheme, which nothing resolves.
    pub const SCHEME: Self = Self(1233);
    /// An extern block, binding a library's functions: native interop's
    /// first rung.
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
    /// A declaration naming a session, which the kernel does not replay.
    pub const KERNEL_SESSION: Self = Self(1319);
    /// A declaration naming a world, which the kernel does not replay.
    pub const KERNEL_WORLD: Self = Self(1320);
    /// A kinded or parameterized type component under an opaque ascription.
    pub const ASCRIPTION: Self = Self(1321);
    /// A model signature's component relating a many-out operation's results.
    pub const MODEL_MANY_OUT: Self = Self(1322);
    /// A model signature's circuit rule.
    pub const MODEL_CIRCUIT: Self = Self(1323);
    /// A model signature's binding operation.
    pub const MODEL_BINDING: Self = Self(1324);
    /// An index `xs[i]` outside a view-answering method's body.
    pub const INDEX: Self = Self(1536);
    /// A model signature's operation abstracting an atom over a port.
    pub const MODEL_ABSTRACTION: Self = Self(1561);
    /// A freshness condition, stated or implied by a variable moved across an
    /// abstraction, whose rule overlaps another or splits a variable across
    /// an abstraction, in a signature where a term can name an atom.
    pub const UNDECIDED_CONDITION: Self = Self(1934);
    /// A recursive call's claim naming a measure, a stage or a cost.
    pub const RECURSIVE_CLAIM: Self = Self(1497);
    /// A function passed as a value with only some of its implicits supplied.
    pub const PARTIAL_SUPPLY: Self = Self(1498);
    /// A `fork` or a `hold` in a match arm that continues its block.
    pub const JOINED_SCOPE: Self = Self(1500);
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
    /// A declaration with effects or control, which the pure kernel does not
    /// replay.
    pub const KERNEL_EFFECTS: Self = Self(1624);
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
    /// path cons whose letter names no loop.
    pub const INFIX_FORM: Self = Self(1997);
    /// A match of no arms over a type no data switch reads, written with its
    /// answer type.
    pub const EMPTY_CASE_ANSWER: Self = Self(1998);
    /// A constructor field at a finite grade other than `1`.
    pub const FIELD_GRADE: Self = Self(2033);

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
