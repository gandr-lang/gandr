//! The support of a judgement: the signature answers one declaration's
//! judgement read, so a caller holding an earlier verdict can tell whether it
//! still answers for the same declaration.
//!
//! # An output of the judgement, not a scan of the term
//!
//! The constant rule is the one place the judgement reads the signature
//! table, and it reads through the context, which logs each answer while a
//! supported judgement runs. The support is therefore what the run consulted,
//! not what a scan of the term predicts it would: a constant the run never
//! reached because an earlier rule refused is absent, and a constant reached
//! twice is present once. A caller compares the answers pointwise against the
//! answers its own table would give now; equal answers mean the judgement
//! would read exactly what it read before.
//!
//! Context lookups log value-signature, data-signature and codata-signature
//! queries separately, in position and query order, absent answers included,
//! and data and codata support retain the complete schema rather than its
//! universe alone. A refusal stops
//! the log where it stops the judgement. A term scan would include constants
//! never reached and cannot replace this dynamic support; the incremental
//! checker's conservative footprint serves a different purpose. Native
//! signature support and adoption are exercised by
//! `tests::native_formers::native_signature_support_and_adoption`.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::context::signature_table;
use crate::formation::FormedValueType;
use crate::report::Verdict;
use crate::worlds::Located;

quenchant_shape::reason_enum! {
    /// Why a declaration's judgement keeps no failure.
    pub mod kept {
        /// The reason no failure is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The declaration was not refused.
            Accepted,
            /// The declaration was refused before its body was run.
            Unrun,
            /// A module run keeps the failure in its report
            /// ([`crate::ModuleReport::failures`]), not beside its support.
            Reported,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration's judgement keeps no entries of the tables.
    pub mod untabled {
        /// The reason no entries are kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The judgement logged no entries of the tables.
            Unlogged,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration's judgement carries no elaboration.
    pub mod elaborated {
        /// The reason no elaboration is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The body held no computation written where a value is read, or
            /// there was no body.
            Unnested,
            /// The first run refused the body, so nothing was elaborated.
            Unaccepted,
            /// A module run keeps the elaboration in its report
            /// ([`crate::ModuleReport::nested_elaborations`]), not beside its
            /// support.
            Reported,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration's judgement keeps no suspension.
    pub mod waits {
        /// The reason no suspension is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The verdict is not suspended.
            Unsuspended,
            /// A module run keeps the suspension in its report
            /// ([`crate::ModuleReport::suspensions`]), not beside its support.
            Reported,
        }
    }
}

/// One answer a judgement read from the signature table, beside what the
/// world register held of the same declaration: its home and its spending.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Consulted
{
    /// The admission position the judgement asked about.
    constant: ConstantIndex,
    /// The type the table held for it, or why it held none.
    answer: Maybe<FormedValueType, signature_table::Absent>,
    /// The declaration's home and spending, which a located judgement reads
    /// beside its type.
    located: Located,
}

impl Consulted
{
    /// The answer `answer` the table gave for `constant`, the register
    /// holding `located` of it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        constant: ConstantIndex,
        answer: Maybe<FormedValueType, signature_table::Absent>,
        located: Located,
    ) -> Self
    {
        Self {
            constant,
            answer,
            located,
        }
    }

    /// The admission position the judgement asked about.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The type the table held for the position, or why it held none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn answer(&self) -> Maybe<FormedValueType, signature_table::Absent>
    {
        self.answer
    }

    /// The home and the spending the register held of the position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn located(&self) -> Located
    {
        self.located
    }
}

/// One nominal-signature answer, including a missing declaration.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DataConsulted
{
    /// The declaration identity that was read.
    constant: ConstantIndex,
    /// The complete constructor table, not only its universe.
    signature: Option<alloc::sync::Arc<gandr_core_term::DataSignature>>,
}

impl DataConsulted
{
    /// Retain a nominal answer without copying its constructor table.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        constant: ConstantIndex,
        signature: Option<alloc::sync::Arc<gandr_core_term::DataSignature>>,
    ) -> Self
    {
        Self {
            constant,
            signature,
        }
    }

    /// The nominal identity that was read.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The signature that existed when this judgment ran, or its absence.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn signature(&self) -> Option<&gandr_core_term::DataSignature>
    {
        self.signature.as_deref()
    }
}

/// One codata-signature answer, including a missing declaration.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CodataConsulted
{
    /// The declaration identity that was read.
    constant: ConstantIndex,
    /// The complete signature, observations included.
    signature: Option<alloc::sync::Arc<gandr_core_term::CodataSignature>>,
}

impl CodataConsulted
{
    /// Retain a codata answer without copying its observations.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        constant: ConstantIndex,
        signature: Option<alloc::sync::Arc<gandr_core_term::CodataSignature>>,
    ) -> Self
    {
        Self {
            constant,
            signature,
        }
    }

    /// The codata identity that was read.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The signature that existed when this judgment ran, or its absence.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn signature(&self) -> Option<&gandr_core_term::CodataSignature>
    {
        self.signature.as_deref()
    }
}

/// The answers one declaration's judgement consulted, ascending by position,
/// each position once.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Support
{
    /// The answers, ascending by position, without repeats.
    consulted: Vec<Consulted>,
    /// Nominal answers, ascending by position, without repeats.
    data: Vec<DataConsulted>,
    /// Codata answers, ascending by position, without repeats.
    codata: Vec<CodataConsulted>,
}

impl Support
{
    /// The support a log of consultations stands for.
    ///
    /// # Specification
    /// - requires: every entry for one position carries the same answer, which
    ///   holds for one declaration's log because the table changes only after
    ///   the declaration's body was judged.
    /// - ensures: one entry per position the log names, ascending by position.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the sort and the repeat removal,
    ///   separated by a judgement reading positions out of order and one
    ///   position twice.
    /// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
    #[spec(
        captures: [
            before = log.len(),
            first = log.iter().min_by_key(|entry| entry.constant).copied(),
            last = log.iter().max_by_key(|entry| entry.constant).copied(),
            data_before = data.len(),
            data_first = data.iter().map(DataConsulted::constant).min(),
            data_last = data.iter().map(DataConsulted::constant).max(),
            codata_before = codata.len(),
        ],
        ensures: |ret| ret.consulted.len() <= before
            && ret.consulted.first().copied() == first
            && ret.consulted.last().copied() == last
            && ret.consulted.iter().zip(ret.consulted.iter().skip(1))
                .all(|(left, right)| left.constant < right.constant)
            && ret.data.len() <= data_before && ret.data.first().map(DataConsulted::constant) == data_first
            && ret.data.last().map(DataConsulted::constant) == data_last
            && ret.data.iter().zip(ret.data.iter().skip(1)).all(|(left,right)| left.constant < right.constant)
            && ret.codata.len() <= codata_before
            && ret.codata.iter().zip(ret.codata.iter().skip(1)).all(|(left,right)| left.constant < right.constant),
    )]
    pub(crate) fn from_log(
        mut log: Vec<Consulted>,
        mut data: Vec<DataConsulted>,
        mut codata: Vec<CodataConsulted>,
    ) -> Self
    {
        log.sort_by_key(|consulted| consulted.constant);
        log.dedup_by_key(|consulted| consulted.constant);
        data.sort_by_key(DataConsulted::constant);
        data.dedup_by_key(|entry| entry.constant);
        codata.sort_by_key(CodataConsulted::constant);
        codata.dedup_by_key(|entry| entry.constant);
        Self {
            consulted: log,
            data,
            codata,
        }
    }

    /// The answers, ascending by position, each position once.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn consulted(&self) -> &[Consulted]
    {
        &self.consulted
    }

    /// Nominal answers, ascending by position, including absent signatures.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn data_consulted(&self) -> &[DataConsulted]
    {
        &self.data
    }

    /// Codata answers, ascending by position, including absent signatures.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn codata_consulted(&self) -> &[CodataConsulted]
    {
        &self.codata
    }
}

/// Whether the table holds an accepted value declaration as it is written.
///
/// A judgement can enter a declaration in a form other than the written one.
/// It fills the holes of the signature or the body, binds the body's nested
/// runs, or discharges an omitted law. It enters a signature quantified over
/// stages at its plain type, and keeps the position a recursion follows. A
/// caller that seats the written form in place of a judgement gives the same
/// table only for [`Entered::AsWritten`].
///
/// # Specification
/// - executable: none — a data type; [`crate::check_declaration_supported`]
///   states when each variant is given.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration whose omitted implicit is filled enters
///   elaborated, and the declaration it calls enters as written.
/// - witness: `gandr-core-checker-bridge::bridge::tests::a_declaration_whose_implicit_is_filled_enters_elaborated_6549`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Entered
{
    /// The table holds the written signature and the written body, and
    /// nothing beside them; or the verdict defines no body.
    AsWritten,
    /// The table holds a signature or a body that the judgement elaborated,
    /// or a stage signature or a following position beside them.
    Elaborated,
}

/// Whether one declaration's judgement added an entry to a table that a
/// checkpoint does not keep yet.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OtherTables
{
    /// The judgement added no entry to such a table.
    Untouched,
    /// The judgement added an entry to such a table.
    Written,
}

/// The entries one declaration's judgement added to the tables that the
/// bridge reads.
///
/// It holds the rows records, the handlers, the reflexivities, the payloads
/// and the directed flows, each with its value, and whether the judgement
/// added an entry to another table.
///
/// # Specification
/// - executable: none — data declaration; the judgement writes it and a
///   checkpoint keeps it.
///
/// # Adequacy
/// - hypothesis: L3 — a taken item that seats these entries gives the kernel
///   checkpoint of a fresh judgement.
/// - witness: `gandr-surface-lsp::tests::taking::a_supported_judgement_logs_the_entries_each_declaration_adds_7373`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Tabled
{
    /// The rows records, each with its value.
    rows: crate::program::Rows,
    /// The types of each handler, by node.
    handled: alloc::collections::BTreeMap<gandr_core_term::ComputationId, crate::handler::Handled>,
    /// The dialogues of each reflexivity, by node.
    reflexivities: alloc::collections::BTreeMap<gandr_core_term::ValueId, crate::code::Reflexivity>,
    /// The payload type of each send and receive, by node.
    payloads:
        alloc::collections::BTreeMap<gandr_core_term::ComputationId, gandr_core_term::ValueTypeId>,
    /// The forward and function flows, by node.
    directed: alloc::collections::BTreeMap<gandr_core_term::ValueId, crate::forward::Directed>,
    /// Whether the judgement added an entry to another table.
    others: OtherTables,
}

/// The rows records, the handlers, the reflexivities, the payloads and the
/// directed flows of a [`Tabled`], each with its value.
pub type TabledEntries = (
    crate::program::Rows,
    alloc::collections::BTreeMap<gandr_core_term::ComputationId, crate::handler::Handled>,
    alloc::collections::BTreeMap<gandr_core_term::ValueId, crate::code::Reflexivity>,
    alloc::collections::BTreeMap<gandr_core_term::ComputationId, gandr_core_term::ValueTypeId>,
    alloc::collections::BTreeMap<gandr_core_term::ValueId, crate::forward::Directed>,
);

impl Tabled
{
    /// The entries `rows`, `handled`, `reflexivities`, `payloads` and
    /// `directed`, beside `others`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn new(
        (rows, handled, reflexivities, payloads, directed): TabledEntries,
        others: OtherTables,
    ) -> Self
    {
        Self {
            rows,
            handled,
            reflexivities,
            payloads,
            directed,
            others,
        }
    }

    /// The rows records, each with its value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rows(&self) -> &crate::program::Rows
    {
        &self.rows
    }

    /// The types of each handler, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn handled(
        &self
    ) -> &alloc::collections::BTreeMap<gandr_core_term::ComputationId, crate::handler::Handled>
    {
        &self.handled
    }

    /// The dialogues of each reflexivity, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reflexivities(
        &self
    ) -> &alloc::collections::BTreeMap<gandr_core_term::ValueId, crate::code::Reflexivity>
    {
        &self.reflexivities
    }

    /// The payload type of each send and receive, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn payloads(
        &self
    ) -> &alloc::collections::BTreeMap<gandr_core_term::ComputationId, gandr_core_term::ValueTypeId>
    {
        &self.payloads
    }

    /// The forward and function flows, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn directed(
        &self
    ) -> &alloc::collections::BTreeMap<gandr_core_term::ValueId, crate::forward::Directed>
    {
        &self.directed
    }

    /// Whether the judgement added an entry to another table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn others(&self) -> OtherTables
    {
        self.others
    }
}

/// One declaration's verdict, beside the support its judgement consulted and
/// the form the table holds it in.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Supported
{
    /// The verdict.
    verdict: Verdict,
    /// The answers the judgement consulted.
    support: Support,
    /// The form the table holds the declaration in.
    entered: Entered,
    /// The failure of the run that refused the declaration, when this
    /// judgement keeps one.
    failure: Maybe<crate::Failure, kept::Absent>,
    /// What elaborating the body's nested computations did, when this
    /// judgement keeps it.
    elaboration: Maybe<crate::NestedElaboration, elaborated::Absent>,
    /// What a suspended run left undecided, or why this judgement keeps none.
    residue: Maybe<crate::elaboration::Residue, waits::Absent>,
    /// The entries the judgement added to the tables that the bridge reads,
    /// or why this judgement logged none.
    tabled: Maybe<Tabled, untabled::Absent>,
    /// The goal memo's consults of the decision, where a module run that
    /// keeps supports counted them; none otherwise.
    #[cfg(feature = "instrument")]
    memo: crate::tally::MemoTally,
}

impl Supported
{
    /// The verdict `verdict`, reached by consulting `support`, entered so,
    /// beside the `failure` of a refused run, the `elaboration` of its nested
    /// computations and the `residue` of a suspended run.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn new(
        (verdict, support, entered): (Verdict, Support, Entered),
        failure: Maybe<crate::Failure, kept::Absent>,
        (elaboration, residue): (
            Maybe<crate::NestedElaboration, elaborated::Absent>,
            Maybe<crate::elaboration::Residue, waits::Absent>,
        ),
    ) -> Self
    {
        Self {
            verdict,
            support,
            entered,
            failure,
            elaboration,
            residue,
            tabled: Maybe::Absent(untabled::Absent::Unlogged),
            #[cfg(feature = "instrument")]
            memo: crate::tally::MemoTally::NONE,
        }
    }

    /// This verdict, beside the entries `tabled` that its judgement added to
    /// the tables.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn tabling(
        mut self,
        tabled: Tabled,
    ) -> Self
    {
        self.tabled = Maybe::Present(tabled);
        self
    }

    /// The entries the judgement added to the tables that the bridge reads,
    /// or why this judgement logged none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn tabled(&self) -> Maybe<&Tabled, untabled::Absent>
    {
        match self.tabled {
            Maybe::Present(ref tabled) => Maybe::Present(tabled),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// This verdict, whose decision consulted the goal memo as `memo` counts.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    pub(crate) const fn consulting(
        mut self,
        memo: crate::tally::MemoTally,
    ) -> Self
    {
        self.memo = memo;
        self
    }

    /// The goal memo's consults of the decision that gave the verdict.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    #[inline]
    #[must_use]
    pub const fn memo(&self) -> crate::tally::MemoTally
    {
        self.memo
    }

    /// The verdict.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn verdict(&self) -> Verdict
    {
        self.verdict
    }

    /// The answers the judgement consulted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn support(&self) -> &Support
    {
        &self.support
    }

    /// The form the table holds the declaration in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn entered(&self) -> Entered
    {
        self.entered
    }

    /// The failure of the run that refused the declaration; absent for an
    /// accepted declaration, for one refused before its body ran, and for a
    /// module run, which keeps its failures in its report.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn failure(&self) -> Maybe<&crate::Failure, kept::Absent>
    {
        match self.failure {
            Maybe::Present(ref failure) => Maybe::Present(failure),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// What elaborating the body's nested computations did; absent for a body
    /// that holds no nested computation, for one the first run refused, and
    /// for a module run, which keeps its elaborations in its report.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn elaboration(&self) -> Maybe<&crate::NestedElaboration, elaborated::Absent>
    {
        match self.elaboration {
            Maybe::Present(ref elaboration) => Maybe::Present(elaboration),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// What the suspended declaration waits on: its own equations joined with
    /// those of each waiting declaration in `prior` that it read, and its
    /// blockers the holes that `context` owes. Absent for a verdict that is
    /// not suspended, and for a module run, which keeps its suspensions in its
    /// report.
    ///
    /// # Specification
    /// - requires: `context` is the context the declaration was judged in, and
    ///   `prior` holds the suspension of each earlier waiting declaration.
    /// - ensures: as the module run records the suspension of the declaration
    ///   from the same residue.
    /// - panics: none.
    /// - executable: none — the module run that the clause names is not an
    ///   input of this call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each suspended declaration that a supported judgement
    ///   decides in turn keeps the suspension that the module run reports. A
    ///   reader keeps the equations of the declaration that it reads.
    /// - witness: `elaboration::tests::a_supported_judgement_keeps_the_suspension_that_the_module_run_reports`
    #[inline]
    pub fn suspension(
        &self,
        context: &crate::context::CheckingContext<'_>,
        prior: &alloc::collections::BTreeMap<ConstantIndex, crate::elaboration::Suspension>,
    ) -> Maybe<crate::elaboration::Suspension, waits::Absent>
    {
        let residue = match self.residue {
            Maybe::Present(ref residue) => residue,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        match self.verdict {
            Verdict::Suspended(declared) => Maybe::Present(crate::elaboration::Suspension::new(
                declared,
                residue.clone(),
                &context.deferrals().owed,
                prior,
            )),
            Verdict::Data
            | Verdict::Checked { .. }
            | Verdict::Synthesised { .. }
            | Verdict::Owed(_)
            | Verdict::Refused(_) => Maybe::Absent(waits::Absent::Unsuspended),
        }
    }
}

/// Whether the context logs the answers it hands out.
pub(crate) enum SupportLog
{
    /// No supported judgement runs; nothing is logged.
    Off,
    /// A supported judgement runs; each answer is logged in the order read.
    Recording
    {
        /// Value-signature answers in consultation order.
        values: Vec<Consulted>,
        /// Nominal-signature answers in consultation order.
        data: Vec<DataConsulted>,
        /// Codata-signature answers in consultation order.
        codata: Vec<CodataConsulted>,
    },
}
