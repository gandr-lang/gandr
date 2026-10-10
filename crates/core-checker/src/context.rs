//! The checking context: the core context the judgement goes under binders in,
//! wrapped with what the core context does not hold.
//!
//! # A wrapper, not an extension of the core context
//!
//! `gandr-core-term`'s [`Context`] is the flat, de Bruijn, name-free binder
//! stack, and it stays that. What checking adds sits here beside it: the
//! signature table from admission positions to the types declarations
//! supplied, the highest admission position so far, the atoms the literal and
//! unit rules hand out, the definitions a code may unfold to, the lifts the
//! judgement decided, and the step allowance. A later synthesised context
//! lands in this wrapper too, so no checking concern widens the core crate.
//!
//! # The context mints
//!
//! A dependent type is rewritten as it is read — a binder's type shifted to
//! the depth it is read at, a codomain instantiated at its argument, a quote's
//! universe minted at its type's level — so the context holds the arena
//! mutably and the judgement mints into it. Every node minted is a type the
//! judgement reads; no term the producer built is changed.
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

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::CompTypeId;
use gandr_core_term::Context;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::code::CodeDefinitions;
use crate::code::Lift;
use crate::code::Unfolded;
use crate::code::unfolding;
use crate::formation::FormedValueType;
use crate::formation::level_of;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::support::Consulted;
use crate::support::Support;
use crate::support::SupportLog;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

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
/// the atoms, the code definitions, the lifts and the step allowance.
///
/// The context derives nothing: it borrows the whole arena, and an equality
/// or a debug rendering of it would read every node.
pub struct CheckingContext<'arena>
{
    /// The arena every id the judgement reads resolves in, and the types it
    /// rewrites are minted into.
    arena: &'arena mut CoreArena,
    /// The binders the judgement is under; empty between judgements.
    binders: Context,
    /// The types declarations supplied, ascending by admission position.
    signatures: Vec<(ConstantIndex, FormedValueType)>,
    /// The highest admission position admitted, or why there is none.
    admitted: Maybe<ConstantIndex, admission::Absent>,
    /// The atoms the leaf rules hand out.
    atoms: Atoms,
    /// The bodies a code constant unfolds to.
    definitions: CodeDefinitions,
    /// The codes checked at a universe above their own, by node.
    lifts: BTreeMap<ValueId, Lift>,
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
    /// - ensures: the context holds no binder, no signature, no definition and
    ///   no lift, and has admitted nothing.
    /// - provides: the context every face and the declaration check run in.
    /// - panics: none.
    /// - intension: mints three value-type nodes into `arena` — the unit type,
    ///   the integer atom and the string atom — which every literal and unit
    ///   rule then hands out.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh context synthesises the three rigid atoms and
    ///   rejects a first undeclared constant; admission and budget cases
    ///   separate leaked prior state and a lost allowance. These cases do not
    ///   quantify over allocation limits.
    /// - witness: `context::tests::the_producer_declares_the_rigid_base_atoms`
    /// - witness: `context::tests::an_undeclared_type_name_is_refused_by_name`
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    #[spec(ensures: |ret| ret.budget.0 == budget.0
        && ret.signatures.is_empty() && ret.definitions.definitions().next().is_none()
        && ret.lifts.is_empty() && matches!(ret.admitted, Maybe::Absent(admission::Absent::Fresh))
        && matches!(ret.support, SupportLog::Off)
        && ret.depth(Zone::Intuitionistic) == BinderDepth::default()
        && ret.depth(Zone::Linear) == BinderDepth::default())]
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
            definitions: CodeDefinitions::new(),
            lifts: BTreeMap::new(),
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
    #[spec(ensures: |ret| {
        let next = self.signatures.partition_point(|&(held, _)| held < constant);
        match self.signatures.get(next) {
            | Some(&(held, declared)) if held == constant => ret == Maybe::Present(declared),
            | Some(_) | None => ret == Maybe::Absent(signature_table::Absent::Untyped),
        }
    })]
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
    /// - ensures: on success `constant` is the highest position admitted,
    ///   [`Self::signature`] answers `supplied` for it, and a present body is
    ///   defined only when a type is supplied, with the elaboration performed
    ///   by [`Self::define`]. A body without a supplied type is not installed.
    /// - provides: the seat an incremental caller places a reused verdict in;
    ///   the caller, not the context, vouches that the verdict still answers,
    ///   and passes the body exactly when the verdict it reuses accepted it.
    /// - fails: [`CheckRefusal::AdmissionOrder`] when `constant` is not above
    ///   the highest position admitted; the context is unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::AdmissionOrder`] — `constant` does not follow every
    ///   position admitted before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the admission, the record and the
    ///   definition, separated by an adopted type a later declaration reads, an
    ///   adopted absence a later declaration finds no type at, an adoption out
    ///   of order refused with the table unchanged, and an adopted body a later
    ///   decode unfolds to.
    /// - witness: `module::tests::an_adopted_answer_is_read_as_if_judged`
    /// - witness: `context::tests::an_adopted_untyped_body_does_not_become_a_definition`
    #[spec(
        captures: [admitted = self.admitted, entries = self.signatures.len(), previous = self.definitions.body(constant)],
        ensures: |ret| match ret {
            | Ok(()) => self.admitted == Maybe::Present(constant)
                && self.signature(constant) == supplied
                && matches!((supplied, unfolds, self.definitions.body(constant)),
                    (Maybe::Present(_), Maybe::Present(_), Maybe::Present(_))
                        | (Maybe::Absent(_), _, Maybe::Absent(_))
                        | (_, Maybe::Absent(_), Maybe::Absent(_))),
            | Err(_) => self.admitted == admitted && self.signatures.len() == entries
                && self.definitions.body(constant) == previous,
        },
    )]
    #[inline]
    pub fn adopt(
        &mut self,
        constant: ConstantIndex,
        supplied: Maybe<FormedValueType, signature_table::Absent>,
        unfolds: Maybe<ValueId, unfolding::Absent>,
    ) -> Result<(), CheckRefusal>
    {
        self.admit(constant)?;
        if let Maybe::Present(declared) = supplied {
            self.record(constant, declared);
            if let Maybe::Present(body) = unfolds {
                self.define(constant, declared, body);
            }
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
    #[spec(
        captures: before = match self.support { SupportLog::Off => None, SupportLog::Recording(ref log) => Some(log.len()) },
        ensures: |ret| ret == self.signature(constant) && match (&self.support, before) {
            | (&SupportLog::Off, None) => true,
            | (&SupportLog::Recording(ref log), Some(count)) => log.len().checked_sub(1) == Some(count)
                && log.last() == Some(&Consulted::new(constant, ret)),
            | _ => false,
        },
    )]
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
    /// - requires: nothing; an earlier log is intentionally discarded.
    /// - ensures: logging is active with no earlier consultation retained.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consecutive supported judgements and preceding
    ///   unsupported reads expose their own exact supports; stale entries or
    ///   failure to start logging change the observed consultation sets.
    /// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
    #[spec(ensures: matches!(self.support, SupportLog::Recording(ref log) if log.is_empty()))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — successful and refused supported judgements expose
    ///   the sorted answers actually read, including an interrupted prefix;
    ///   lost entries or retained recording change the next observed support.
    /// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
    /// - witness: `module::tests::a_refusal_cuts_the_support_where_the_run_stopped`
    #[spec(
        captures: before = match self.support { SupportLog::Off => 0, SupportLog::Recording(ref log) => log.len() },
        ensures: |ret| matches!(self.support, SupportLog::Off)
            && ret.consulted().len() <= before && ret.consulted().is_empty() == (before == 0),
    )]
    pub(crate) fn finish_support(&mut self) -> Support
    {
        match core::mem::replace(&mut self.support, SupportLog::Off) {
            | SupportLog::Recording(log) => Support::from_log(log),
            | SupportLog::Off => Support::default(),
        }
    }

    /// The arena every id resolves in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arena(&self) -> &CoreArena
    {
        self.arena
    }

    /// The arena, for minting the types the judgement rewrites.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn arena_mut(&mut self) -> &mut CoreArena
    {
        self.arena
    }

    /// The bodies a code constant unfolds to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn definitions(&self) -> &CodeDefinitions
    {
        &self.definitions
    }

    /// Define `constant`, accepted at `declared` with `body`: a later decode
    /// of a code naming it unfolds to the body, elaborated.
    ///
    /// # Specification
    /// - requires: `body` was accepted at `declared`.
    /// - ensures: [`Self::definitions`] holds, at `constant`, `body` itself
    ///   unless `declared` is, at its weak head, a value universe above the
    ///   level of the universe `body` inhabits; then the lift of `body` to that
    ///   universe, minted. The definition is the code the kernel admits for the
    ///   declaration, so a decode unfolds alike on either side.
    /// - fails: never; a body whose level cannot be read is defined as it
    ///   stands, and the kernel's replay of an unfolding over it declines
    ///   rather than certifies a wrong one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — code definitions at their natural universe and a
    ///   larger universe are observed by subsequent decoding and independent
    ///   readmission; a missing body or lift changes those outcomes.
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    #[spec(ensures: matches!(self.definitions.body(constant), Maybe::Present(defined)
        if defined == body || matches!(self.arena.value(defined), Some(Value::Quote(lifted))
            if matches!(value_type_view(self.arena, *lifted), Ok(ValueTypeView::Lift { .. })))))]
    pub(crate) fn define(
        &mut self,
        constant: ConstantIndex,
        declared: FormedValueType,
        body: ValueId,
    )
    {
        let elaborated = self.elaborate(declared, body).unwrap_or(body);
        self.definitions.define(constant, elaborated);
    }

    /// `body` at the universe `declared` names: lifted when `declared` is a
    /// value universe above the body's own.
    ///
    /// # Specification
    /// - requires: `body` was accepted at `declared`.
    /// - ensures: as [`Self::define`] states of the definition.
    /// - fails: the refusal reading `declared`'s weak head or the body's level
    ///   gives.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a quoted small type declared at its own universe or a
    ///   larger one is observed through conversion and kernel readmission;
    ///   dropped or incorrectly shaped elaborations change these decisions.
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|elaborated| elaborated == body
        || matches!(self.arena.value(elaborated), Some(Value::Quote(lifted))
            if matches!(value_type_view(self.arena, *lifted), Ok(ValueTypeView::Lift { .. })))))]
    fn elaborate(
        &mut self,
        declared: FormedValueType,
        body: ValueId,
    ) -> Result<ValueId, CheckRefusal>
    {
        let head = self.whnf_value_type(declared.id())?;
        let ValueTypeView::Universe {
            sort: GroundSort::Value,
            level,
        } = value_type_view(self.arena, head)?
        else {
            return Ok(body);
        };
        let target = level.clone();
        let natural = self.code_level(body, &target)?;
        if bool::from(natural.lt(&target)) {
            Ok(Lift::new(natural, target).mint(self.arena, body))
        }
        else {
            Ok(body)
        }
    }

    /// The codes the judgement checked at a universe above their own, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lifts(&self) -> &BTreeMap<ValueId, Lift>
    {
        &self.lifts
    }

    /// Record that the code `at` was checked at a universe above its own.
    ///
    /// # Specification
    /// - requires: the natural level is strictly below the target.
    /// - ensures: `at` has a recorded lift, replacing an earlier record there.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the value bridge on equal, lower and higher code
    ///   levels distinguishes recording a genuine lift from recording an
    ///   equality or refusal; readmission observes the resulting coercion.
    /// - witness: `conversion::tests::the_value_bridge_lifts_a_small_value_code_and_nothing_else`
    /// - witness: `bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    #[spec(
        requires: bool::from(lift.natural().lt(lift.target())),
        ensures: self.lifts.contains_key(&at),
    )]
    pub(crate) fn record_lift(
        &mut self,
        at: ValueId,
        lift: Lift,
    )
    {
        self.lifts.insert(at, lift);
    }

    /// The value type `value_type` stands for at its head: a decode of a code
    /// constant with a body read as the type the body denotes, until the head
    /// is anything else.
    ///
    /// # Specification
    /// - requires: `value_type` is formed.
    /// - ensures: `value_type` itself unless its head is a decode of a constant
    ///   with a body; otherwise the decode of that body at the decode's level,
    ///   read again. A body is defined at the universe its constant was
    ///   declared at, so the decode is at the body's own level. Each unfolding
    ///   is certified by the normaliser's conversion and its constant logged as
    ///   consulted.
    /// - provides: the weak head every rule that reads a type's former reads.
    /// - fails: [`CheckRefusal::Undecided`] at a code whose unfolding the
    ///   machine did not certify; [`CheckRefusal::DanglingNode`] for a node
    ///   that does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — an unfolding was not certified.
    /// - [`CheckRefusal::DanglingNode`] — a node does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — rigid formers and decodes through defined codes are
    ///   observed by conversion, including a static instance; these separate
    ///   changing a rigid id and stopping before a certified unfolding.
    /// - witness: `conversion::tests::a_decode_of_a_defined_code_converts_with_its_body`
    /// - witness: `bridge::tests::family_argument_at_wrong_classifier_raises_the_exact_variant`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|head|
        value_type_view(self.arena, head).is_ok()
            && (matches!(value_type_view(self.arena, value_type), Ok(ValueTypeView::Element { .. })) || head == value_type)))]
    pub(crate) fn whnf_value_type(
        &mut self,
        value_type: ValueTypeId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let mut head = value_type;
        loop {
            let ValueTypeView::Element { code, target } = value_type_view(self.arena, head)?
            else {
                return Ok(head);
            };
            let target = target.clone();
            let Maybe::Present(body) = self.unfold(code)?
            else {
                return Ok(head);
            };
            head = self.arena.value_type_element(body, target);
        }
    }

    /// The computation type `comp_type` stands for at its head, as
    /// [`Self::whnf_value_type`] reads a value type.
    ///
    /// # Specification
    /// - requires: `comp_type` is formed.
    /// - ensures: `comp_type` itself unless its head is a decode of a constant
    ///   with a body; otherwise the decode of that body at the decode's level,
    ///   read again. A computation code is never lifted: the judgement refuses
    ///   one checked above its level.
    /// - provides: the weak head every rule that reads a computation type's
    ///   former reads.
    /// - fails: as [`Self::whnf_value_type`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — an unfolding was not certified.
    /// - [`CheckRefusal::DanglingNode`] — a node does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a computation decode and rigid returner or arrow
    ///   expose the head through checking and readmission; a wrong head or
    ///   altered rigid id changes these results. Arbitrary reduction lengths
    ///   are outside these finite examples.
    /// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|head|
        comp_type_view(self.arena, head).is_ok()
            && (matches!(comp_type_view(self.arena, comp_type), Ok(CompTypeView::Element { .. })) || head == comp_type)))]
    pub(crate) fn whnf_comp_type(
        &mut self,
        comp_type: CompTypeId,
    ) -> Result<CompTypeId, CheckRefusal>
    {
        let mut head = comp_type;
        loop {
            let CompTypeView::Element { code, target } = comp_type_view(self.arena, head)?
            else {
                return Ok(head);
            };
            let target = target.clone();
            let Maybe::Present(body) = self.unfold(code)?
            else {
                return Ok(head);
            };
            head = self.arena.comp_type_element(body, target);
        }
    }

    /// The reduct of one certified step at the code `code`'s head.
    ///
    /// # Specification
    /// - requires: `code` stands beneath the binders the judgement is under.
    /// - ensures: the reduct [`CodeDefinitions::reduce`] gives `code` — a
    ///   constant's body, a static definition at a saturated instance, a static
    ///   redex — its step certified by the normaliser's conversion beneath the
    ///   context's binders and an unfolded definition logged as consulted;
    ///   nothing for any other code. A reduct is another node than `code`, and
    ///   resolves.
    /// - fails: [`CheckRefusal::Undecided`] when the machine does not certify
    ///   the step; [`CheckRefusal::DanglingNode`] for a code that does not
    ///   resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a constant's δ-step, a static instance's
    ///   δβ-step, and a rigid code; the certification is the normaliser's,
    ///   witnessed where it is defined.
    /// - witness: `conversion::tests::a_decode_of_a_defined_code_converts_with_its_body`
    /// - witness: `bridge::tests::family_argument_at_wrong_classifier_raises_the_exact_variant`
    /// - witness: `bridge::tests::a_static_lambda_at_a_dynamic_parameter_is_refused_by_name`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(reduct)) => reduct != code && self.arena.value(reduct).is_some(),
        | Ok(Maybe::Absent(_)) | Err(_) => true,
    })]
    pub(crate) fn unfold(
        &mut self,
        code: ValueId,
    ) -> Result<Maybe<ValueId, unfolding::Absent>, CheckRefusal>
    {
        let Maybe::Present(step) = self.definitions.reduce(self.arena, code)?
        else {
            return Ok(Maybe::Absent(unfolding::Absent::Rigid));
        };
        let certificate = self.definitions.certify(self.arena, step)?;
        if let Unfolded::Definition(constant) = certificate.unfolded() {
            let _answer = self.consult(constant);
        }
        Ok(Maybe::Present(certificate.reduct()))
    }

    /// The code `code` reduces to at its head: [`Self::unfold`] taken until
    /// it gives nothing.
    ///
    /// # Specification
    /// - requires: as [`Self::unfold`].
    /// - ensures: `code` itself when no step fires at its head, otherwise the
    ///   last reduct of the chain of certified steps; the result resolves in
    ///   the arena. That no step fires at the result is not restated
    ///   executably: deciding it is another step, which mints into the arena.
    /// - fails: as [`Self::unfold`].
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `loop` below takes one certified step per turn, not
    ///   recursion.
    /// - measure: the static normal form's distance: each step reduces a δ- or
    ///   β-redex of a well-formed code, and the judgement's step allowance
    ///   bounds every certificate's evaluation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a rigid head, a chain of two constants,
    ///   and a static definition that does not reduce short of its arguments.
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `bridge::tests::a_static_lambda_at_a_dynamic_parameter_is_refused_by_name`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|head| self.arena.value(head).is_some()))]
    pub(crate) fn whnf_code(
        &mut self,
        code: ValueId,
    ) -> Result<ValueId, CheckRefusal>
    {
        let mut head = code;
        loop {
            match self.unfold(head)? {
                | Maybe::Present(reduct) => head = reduct,
                | Maybe::Absent(_) => return Ok(head),
            }
        }
    }

    /// The level of the universe a closed code `code` inhabits, read off the
    /// code: a quote's type's level, a constant's declared universe.
    ///
    /// # Specification
    /// - requires: `code` is an accepted declaration body; `otherwise` is the
    ///   fallback level when its syntax exposes no natural level.
    /// - ensures: the level of the quoted type for a quote, the level of the
    ///   universe a constant was declared at for a constant, and `otherwise`
    ///   for any other code.
    /// - fails: [`CheckRefusal::DanglingNode`] or the refusal reading a quoted
    ///   type's level gives.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quoted and named type codes at equal and increased
    ///   declaration levels expose their natural level through the inserted
    ///   lift and independent readmission; other syntax uses the fallback,
    ///   without a claim that it independently reveals a classifier.
    /// - witness: `bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    #[spec(ensures: |ret| match self.arena.value(code) {
        | None => ret == Err(CheckRefusal::DanglingNode { node: CoreNode::Term(TermNode::Value(code)) }),
        | Some(&Value::Constant(constant)) => match self.signature(constant) {
            | Maybe::Present(declared) => match value_type_view(self.arena, declared.id()) {
                | Ok(ValueTypeView::Universe { level, .. }) => ret.as_ref() == Ok(level),
                | Ok(_) => ret.as_ref() == Ok(otherwise),
                | Err(refusal) => ret == Err(CheckRefusal::from(refusal)),
            },
            | Maybe::Absent(_) => ret.as_ref() == Ok(otherwise),
        },
        | Some(&(Value::Quote(_) | Value::QuoteComputation(_))) => true,
        | Some(_) => ret.as_ref() == Ok(otherwise),
    })]
    fn code_level(
        &mut self,
        code: ValueId,
        otherwise: &Level,
    ) -> Result<Level, CheckRefusal>
    {
        let Some(node) = self.arena.value(code)
        else {
            return Err(CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Value(code)),
            });
        };
        match *node {
            | Value::Quote(quoted) => level_of(self.arena, TypeNode::Value(quoted)),
            | Value::QuoteComputation(quoted) => {
                level_of(self.arena, TypeNode::Computation(quoted))
            },
            | Value::Constant(constant) => match self.consult(constant) {
                | Maybe::Present(declared) => match value_type_view(self.arena, declared.id())? {
                    | ValueTypeView::Universe { level, .. } => Ok(level.clone()),
                    | ValueTypeView::Integer
                    | ValueTypeView::String
                    | ValueTypeView::Unit
                    | ValueTypeView::Thunk(_)
                    | ValueTypeView::Lift { .. }
                    | ValueTypeView::Element { .. }
                    | ValueTypeView::Product(..)
                    | ValueTypeView::StaticPi { .. } => Ok(otherwise.clone()),
                },
                | Maybe::Absent(_) => Ok(otherwise.clone()),
            },
            | Value::Variable { .. }
            | Value::Unit
            | Value::Literal(_)
            | Value::Pair(..)
            | Value::Injection(..)
            | Value::Thunk(_)
            | Value::Lift { .. }
            | Value::StaticLambda(_)
            | Value::StaticApplication(..) => Ok(otherwise.clone()),
        }
    }

    /// The number of binders open in `zone`, without borrowing them mutably.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn depth(
        &self,
        zone: Zone,
    ) -> BinderDepth
    {
        self.binders.depth(zone)
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
    #[spec(
        captures: previous = self.admitted,
        ensures: |ret| match previous {
            | Maybe::Present(admitted) if constant <= admitted => self.admitted == previous
                && ret == Err(CheckRefusal::AdmissionOrder { constant, admitted }),
            | Maybe::Present(_) | Maybe::Absent(_) => ret == Ok(()) && self.admitted == Maybe::Present(constant),
        },
    )]
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
    /// - requires: `constant` is the position admitted last and no type has yet
    ///   been recorded there, so the table stays strictly ascending.
    /// - ensures: [`Self::signature`] answers `declared` for `constant`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — later declarations read earlier supplied types,
    ///   including a refused signed body; absent types remain absent. These
    ///   cases separate omitted or mispositioned records in ordered modules.
    /// - witness: `module::tests::a_later_declaration_reads_an_earlier_type`
    /// - witness: `module::tests::a_refused_signed_body_still_supplies_its_type`
    #[spec(
        requires: self.admitted == Maybe::Present(constant)
            && self.signatures.last().is_none_or(|&(previous, _)| previous < constant),
        captures: before = self.signatures.len(),
        ensures: self.signatures.len().checked_sub(1) == Some(before)
            && self.signatures.last() == Some(&(constant, declared)),
    )]
    pub(crate) fn record(
        &mut self,
        constant: ConstantIndex,
        declared: FormedValueType,
    )
    {
        self.signatures.push((constant, declared));
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::Classifier;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Sort;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;

    use super::Atom;
    use super::CheckBudget;
    use super::CheckingContext;
    use crate::formation::classify_value_type;
    use crate::formation::form_value_type;
    use crate::refusal::CheckRefusal;
    use crate::refusal::Mismatch;

    /// The classifier of a value type at level zero.
    ///
    /// # Specification
    /// trivial.
    fn small() -> Classifier
    {
        Classifier {
            sort: GroundSort::Value,
            level: Level::zero(),
        }
    }

    #[test]
    fn the_producer_declares_the_rigid_base_atoms()
    {
        let mut arena = CoreArena::new();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let atoms = [
            (Atom::Unit, None),
            (Atom::Integer, Some(BaseType::Integer)),
            (Atom::String, Some(BaseType::String)),
        ];
        for (atom, base) in atoms {
            let declared = context.atom(atom);
            let node = context.arena().value_type(declared.id()).cloned();
            assert_eq!(
                node,
                Some(base.map_or(
                    gandr_core_term::ValueType::Unit,
                    gandr_core_term::ValueType::Base
                )),
                "the context mints {atom:?} as the rigid atom of its name"
            );
            let formed = form_value_type(&mut context, declared.id()).unwrap();
            assert_eq!(
                classify_value_type(&context, formed),
                Ok(small()),
                "every atom is a small value type"
            );
        }
    }

    #[test]
    fn an_undeclared_type_name_is_refused_by_name()
    {
        let mut arena = CoreArena::new();
        let name = arena.value_constant(ConstantIndex::from(5_usize));
        let decoded = arena.value_type_element(name, Level::zero());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            form_value_type(&mut context, decoded),
            Err(CheckRefusal::UnknownConstant {
                at: name,
                constant: ConstantIndex::from(5_usize),
            }),
            "a decode of a name no declaration supplied is refused naming the constant"
        );
    }

    #[test]
    fn a_universe_typed_hypothesis_becomes_a_type_variable()
    {
        let mut arena = CoreArena::new();
        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = arena.value_type_element(bound, Level::zero());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, universe);
        let formed = form_value_type(&mut context, decoded).unwrap();
        assert_eq!(
            classify_value_type(&context, formed),
            Ok(small()),
            "a hypothesis of the small universe decodes to a small type"
        );
    }

    #[test]
    fn a_value_typed_hypothesis_does_not_become_a_type_variable()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = arena.value_type_element(bound, Level::zero());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, integer);
        let refused = form_value_type(&mut context, decoded);
        assert!(
            matches!(
                refused,
                Err(CheckRefusal::TypeMismatch(Mismatch::Value { at, synthesised, .. }))
                    if at == bound && synthesised == integer
            ),
            "an integer is no code, so its decode is refused at the variable: {refused:?}"
        );
    }
    #[test]
    fn an_adopted_untyped_body_does_not_become_a_definition()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let code = arena.value_quote(unit);
        let constant = ConstantIndex::from(0_usize);
        let reference = arena.value_constant(constant);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            context.adopt(
                constant,
                quenchant_shape::shape::Maybe::Absent(super::signature_table::Absent::Untyped),
                quenchant_shape::shape::Maybe::Present(code),
            ),
            Ok(())
        );
        assert_eq!(
            crate::synthesise_value(&mut context, reference),
            Err(CheckRefusal::UnknownConstant {
                at: reference,
                constant
            })
        );
        assert_eq!(
            context.unfold(reference),
            Ok(quenchant_shape::shape::Maybe::Absent(
                crate::unfolding::Absent::Rigid
            ))
        );
    }
}
