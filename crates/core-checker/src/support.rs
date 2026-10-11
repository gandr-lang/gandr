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

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::context::signature_table;
use crate::formation::FormedValueType;
use crate::module::Verdict;

/// One answer a judgement read from the signature table.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Consulted
{
    /// The admission position the judgement asked about.
    constant: ConstantIndex,
    /// The type the table held for it, or why it held none.
    answer: Maybe<FormedValueType, signature_table::Absent>,
}

impl Consulted
{
    /// The answer `answer` the table gave for `constant`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        constant: ConstantIndex,
        answer: Maybe<FormedValueType, signature_table::Absent>,
    ) -> Self
    {
        Self { constant, answer }
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

/// The answers one declaration's judgement consulted, ascending by position,
/// each position once.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Support
{
    /// The answers, ascending by position, without repeats.
    consulted: Vec<Consulted>,
    /// Nominal answers, ascending by position, without repeats.
    data: Vec<DataConsulted>,
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
        ],
        ensures: |ret| ret.consulted.len() <= before
            && ret.consulted.first().copied() == first
            && ret.consulted.last().copied() == last
            && ret.consulted.iter().zip(ret.consulted.iter().skip(1))
                .all(|(left, right)| left.constant < right.constant)
            && ret.data.len() <= data_before && ret.data.first().map(DataConsulted::constant) == data_first
            && ret.data.last().map(DataConsulted::constant) == data_last
            && ret.data.iter().zip(ret.data.iter().skip(1)).all(|(left,right)| left.constant < right.constant),
    )]
    pub(crate) fn from_log(
        mut log: Vec<Consulted>,
        mut data: Vec<DataConsulted>,
    ) -> Self
    {
        log.sort_by_key(|consulted| consulted.constant);
        log.dedup_by_key(|consulted| consulted.constant);
        data.sort_by_key(DataConsulted::constant);
        data.dedup_by_key(|entry| entry.constant);
        Self {
            consulted: log,
            data,
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
}

/// One declaration's verdict, beside the support its judgement consulted.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Supported
{
    /// The verdict.
    verdict: Verdict,
    /// The answers the judgement consulted.
    support: Support,
}

impl Supported
{
    /// The verdict `verdict`, reached by consulting `support`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        verdict: Verdict,
        support: Support,
    ) -> Self
    {
        Self { verdict, support }
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
}

/// Whether the context logs the answers it hands out.
pub enum SupportLog
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
    },
}
