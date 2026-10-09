//! The checking context: the core context the judgement goes under binders in,
//! wrapped with what the core context does not hold.
//!
//! # A wrapper, not an extension of the core context
//!
//! `gandr-core-term`'s [`Context`] is the flat, de Bruijn, name-free binder
//! stack, and it stays that. What checking adds sits here beside it: the
//! signature table from admission positions to the types declarations
//! supplied, the highest admission position so far, the atoms the literal and
//! unit rules hand out, and the step allowance. A later synthesised context
//! lands in this wrapper too, so no checking concern widens the core crate.
//!
//! # Resolution by admission position
//!
//! A declaration's type enters the signature table only after its own body
//! was judged, and a declaration is admitted only above every position already
//! admitted. A body therefore sees exactly the declarations strictly before
//! it: self-reference and mutual reference find no type, whatever the producer
//! resolved.
//!
//! # Adopted answers
//!
//! A caller that holds a declaration's earlier verdict and has shown it still
//! answers — an incremental checker comparing the verdict's support pointwise
//! — may admit the declaration with the type it supplied before, through
//! [`CheckingContext::adopt`], instead of judging it again. Admission order
//! binds an adopted declaration exactly as a judged one.

use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::Context;
use gandr_core_term::CoreArena;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::formation::FormedValueType;
use crate::refusal::CheckRefusal;
use crate::support::Consulted;
use crate::support::Support;
use crate::support::SupportLog;

quenchant_shape::reason_enum! {
    /// Why the signature table holds no type for a position.
    pub mod signature_table {
        /// The reason no type is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No declaration at that position supplied a type: none was
            /// admitted there yet, its body synthesised nothing, or the
            /// producer withheld it.
            Untyped,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no admission position has been admitted.
    mod admission {
        /// The reason nothing is admitted.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The context has admitted no declaration yet.
            Fresh,
        }
    }
}

/// The work one judgement may spend before it refuses.
///
/// One step is charged per machine transition, so the allowance bounds a run
/// whatever sharing its term has.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CheckBudget(usize);

impl CheckBudget
{
    /// The allowance a caller with no reason to bound the judgement takes.
    pub const DEFAULT: Self = Self(1_000_000_usize);
}

impl From<usize> for CheckBudget
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

impl From<CheckBudget> for usize
{
    /// The number of steps `budget` allows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(budget: CheckBudget) -> Self
    {
        budget.0
    }
}

impl fmt::Display for CheckBudget
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

/// The value types the literal and unit rules synthesise.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Atoms
{
    /// The unit type.
    unit: FormedValueType,
    /// The integer atom.
    integer: FormedValueType,
    /// The string atom.
    string: FormedValueType,
}

/// Which atom a leaf rule synthesises.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Atom
{
    /// The unit type, for the unit value.
    Unit,
    /// The integer atom, for an integer literal.
    Integer,
    /// The string atom, for a string literal.
    String,
}

/// The core context wrapped with the signature table, the admission position,
/// the atoms and the step allowance.
///
/// The context derives nothing: it borrows the whole arena, and an equality
/// or a debug rendering of it would read every node.
pub struct CheckingContext<'arena>
{
    /// The arena every id the judgement reads resolves in.
    arena: &'arena CoreArena,
    /// The binders the judgement is under; empty between judgements.
    binders: Context,
    /// The types declarations supplied, ascending by admission position.
    signatures: Vec<(ConstantIndex, FormedValueType)>,
    /// The highest admission position admitted, or why there is none.
    admitted: Maybe<ConstantIndex, admission::Absent>,
    /// The atoms the leaf rules hand out.
    atoms: Atoms,
    /// The allowance each judgement starts with.
    budget: CheckBudget,
    /// The answers the running supported judgement consulted, when one runs.
    support: SupportLog,
}

impl<'arena> CheckingContext<'arena>
{
    /// A context over `arena` with no declaration admitted, judging under
    /// `budget`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the context holds no binder and no signature, has admitted
    ///   nothing, and reads `arena` without changing it again.
    /// - provides: the context every face and the declaration check run in.
    /// - panics: none.
    /// - intension: mints exactly three value-type nodes into `arena` — the
    ///   unit type, the integer atom and the string atom — which every literal
    ///   and unit rule then hands out, so judging mints nothing further.
    #[inline]
    #[must_use]
    pub fn new(
        arena: &'arena mut CoreArena,
        budget: CheckBudget,
    ) -> Self
    {
        let atoms = Atoms {
            unit: FormedValueType::derived(arena.value_type_unit()),
            integer: FormedValueType::derived(arena.value_type_base(BaseType::Integer)),
            string: FormedValueType::derived(arena.value_type_base(BaseType::String)),
        };
        Self {
            arena,
            binders: Context::new(),
            signatures: Vec::new(),
            admitted: Maybe::Absent(admission::Absent::Fresh),
            atoms,
            budget,
            support: SupportLog::Off,
        }
    }

    /// The allowance each judgement starts with.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn budget(&self) -> CheckBudget
    {
        self.budget
    }

    /// The type the declaration at `constant` supplied.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the type recorded for `constant` when one was.
    /// - provides: `signature_table::Absent::Untyped` when no declaration at
    ///   that position supplied a type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the ascending search,
    ///   separated by a position recorded, a position admitted without a type,
    ///   and a position never admitted.
    /// - witness: `module::tests::a_later_declaration_reads_an_earlier_type`
    /// - witness: `module::tests::a_body_that_synthesised_nothing_supplies_no_type`
    #[inline]
    pub fn signature(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<FormedValueType, signature_table::Absent>
    {
        match self
            .signatures
            .binary_search_by_key(&constant, |&(held, _)| held)
        {
            | Ok(found) => match self.signatures.get(found) {
                | Some(&(_, declared)) => Maybe::Present(declared),
                | None => Maybe::Absent(signature_table::Absent::Untyped),
            },
            | Err(_) => Maybe::Absent(signature_table::Absent::Untyped),
        }
    }

    /// Admit the declaration at `constant` with the type an earlier judgement
    /// of it supplied, without judging it again.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-order position is admissible input and
    ///   refused.
    /// - ensures: on success `constant` is the highest position admitted and
    ///   [`Self::signature`] answers `supplied` for it, exactly as after
    ///   judging a declaration that supplied `supplied`.
    /// - provides: the seat an incremental caller places a reused verdict in;
    ///   the caller, not the context, vouches that the verdict still answers.
    /// - fails: [`CheckRefusal::AdmissionOrder`] when `constant` is not above
    ///   the highest position admitted; the context is unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::AdmissionOrder`] — `constant` does not follow every
    ///   position admitted before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the admission and the record,
    ///   separated by an adopted type a later declaration reads, an adopted
    ///   absence a later declaration finds no type at, and an adoption out of
    ///   order refused with the table unchanged.
    /// - witness: `module::tests::an_adopted_answer_is_read_as_if_judged`
    #[inline]
    pub fn adopt(
        &mut self,
        constant: ConstantIndex,
        supplied: Maybe<FormedValueType, signature_table::Absent>,
    ) -> Result<(), CheckRefusal>
    {
        self.admit(constant)?;
        if let Maybe::Present(declared) = supplied {
            self.record(constant, declared);
        }
        Ok(())
    }

    /// The type the declaration at `constant` supplied, as the judgement reads
    /// it: logged when a supported judgement runs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer [`Self::signature`] gives; while a supported
    ///   judgement runs, the answer is also appended to its log.
    /// - provides: the one read of the table the judgement makes, so the
    ///   support is complete by construction.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surface is the log append, separated by a
    ///   supported judgement whose support is asserted entry by entry and an
    ///   unsupported judgement before it whose reads stay out.
    /// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
    pub(crate) fn consult(
        &mut self,
        constant: ConstantIndex,
    ) -> Maybe<FormedValueType, signature_table::Absent>
    {
        let answer = self.signature(constant);
        if let SupportLog::Recording(ref mut log) = self.support {
            log.push(Consulted::new(constant, answer));
        }
        answer
    }

    /// Start logging the answers handed out, discarding any earlier log.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn start_support(&mut self)
    {
        self.support = SupportLog::Recording(Vec::new());
    }

    /// Stop logging and return the support the log stands for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the support of every answer logged since
    ///   [`Self::start_support`], or the empty support when none was started;
    ///   logging is off afterwards.
    /// - panics: none.
    pub(crate) fn finish_support(&mut self) -> Support
    {
        match core::mem::replace(&mut self.support, SupportLog::Off) {
            | SupportLog::Recording(log) => Support::from_log(log),
            | SupportLog::Off => Support::default(),
        }
    }

    /// The arena every id resolves in, shared for as long as the context reads
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn arena(&self) -> &'arena CoreArena
    {
        self.arena
    }

    /// The binders the judgement is under.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn binders(&mut self) -> &mut Context
    {
        &mut self.binders
    }

    /// The type a leaf rule synthesises.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn atom(
        &self,
        atom: Atom,
    ) -> FormedValueType
    {
        match atom {
            | Atom::Unit => self.atoms.unit,
            | Atom::Integer => self.atoms.integer,
            | Atom::String => self.atoms.string,
        }
    }

    /// Admit the declaration at `constant`.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-order position is admissible input and
    ///   refused.
    /// - ensures: on success `constant` is the highest position admitted.
    /// - provides: the order resolution by position rests on.
    /// - fails: [`CheckRefusal::AdmissionOrder`] when `constant` is not above
    ///   the highest position admitted; the context is unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::AdmissionOrder`] — `constant` does not follow every
    ///   position admitted before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is one strict comparison,
    ///   separated by a first admission, a repeated position and a lower one,
    ///   each refusal asserted with both positions.
    /// - witness: `module::tests::an_admission_out_of_order_is_refused`
    pub(crate) fn admit(
        &mut self,
        constant: ConstantIndex,
    ) -> Result<(), CheckRefusal>
    {
        if let Maybe::Present(admitted) = self.admitted
            && constant <= admitted
        {
            return Err(CheckRefusal::AdmissionOrder { constant, admitted });
        }
        self.admitted = Maybe::Present(constant);
        Ok(())
    }

    /// Record the type the admitted declaration at `constant` supplied.
    ///
    /// # Specification
    /// - requires: `constant` is the position admitted last, so the table stays
    ///   ascending.
    /// - ensures: [`Self::signature`] answers `declared` for `constant`.
    /// - panics: none.
    pub(crate) fn record(
        &mut self,
        constant: ConstantIndex,
        declared: FormedValueType,
    )
    {
        self.signatures.push((constant, declared));
    }
}
