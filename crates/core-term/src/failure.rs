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
    /// The as, list and rest patterns.
    pub const PATTERNS: Self = Self(1051);
    /// A character literal.
    pub const CHARACTER: Self = Self(1052);
    /// A `co` bundle.
    pub const CO_BUNDLE: Self = Self(1053);
    /// A `drop` of a session endpoint.
    pub const DROP: Self = Self(1054);
    /// A `forall` type.
    pub const FORALL: Self = Self(1055);
    /// A union or an intersection type.
    pub const UNION_INTERSECTION: Self = Self(1056);
    /// The shell block, `#!{ … }`.
    pub const SHELL_BLOCK: Self = Self(1057);
    /// A root form that declares nothing, which the lowering reads as no run
    /// target yet.
    pub const RUN_TARGET: Self = Self(1105);
    /// A projection, `e.1` or `e.field`, where the fragment reads none.
    pub const PROJECTION: Self = Self(1106);
    /// An annotation, `(e : T)`, read as a value.
    pub const ANNOTATION_VALUE: Self = Self(1107);
    /// Packages: `pack`, `unpack` and the package type.
    pub const PACKAGES: Self = Self(1108);
    /// A number literal written with its type.
    pub const TYPED_NUMBER: Self = Self(1109);
    /// A record update, `#{ e | l = v, … }`.
    pub const RECORD_UPDATE: Self = Self(1110);
    /// An operator declaration.
    pub const OPERATOR_DECLARATION: Self = Self(1111);
    /// A thunk type's grade.
    pub const THUNK_GRADE: Self = Self(1112);
    /// A module's documentation, which no face shows.
    pub const DOCUMENTATION: Self = Self(1135);
    /// Delegation: an endpoint sent over another endpoint.
    pub const DELEGATION: Self = Self(1167);
    /// A form the fragment refuses under a name that covers several features,
    /// which names its own issue once its refusal is split by feature.
    pub const UNSPLIT: Self = Self(1200);
    /// An import whose address has a scheme, which nothing resolves.
    pub const SCHEME: Self = Self(1233);
    /// A constructor field's grade other than the default `ω`.
    pub const FIELD_GRADE: Self = Self(1295);
    /// A lambda's parameter written with its type.
    pub const LAMBDA_PARAMETER: Self = Self(1310);
    /// A case or a form over an indexed family.
    pub const INDEXED: Self = Self(1314);
    /// Function extensionality past the first-order coverage.
    pub const FUNEXT: Self = Self(1315);
    /// A universe equivalence outside the decided codes.
    pub const EQUIV: Self = Self(1316);
    /// A `forward` outside the decided codes.
    pub const FORWARD: Self = Self(1317);
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
