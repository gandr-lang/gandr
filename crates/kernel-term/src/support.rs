//! The support every node of a [`TermArena`] carries: exactly the free de
//! Bruijn indices it mentions, gathered from its children's when it is minted,
//! so a reader takes a node's support off its column and nothing walks a term
//! to find one.
//!
//! A binding former's support is its children's seen from outside the binders
//! each child stands under: a lambda's body one binder out, a bind's body but
//! not its bound computation, each case branch but not its scrutinee, a
//! dependent pair's second factor and a dependent arrow's codomain. The
//! support is syntactic and over-approximates dependence, since a use a step
//! would remove still occurs, so it keys and bounds and never decides a
//! strengthening. A node whose child the arena cannot resolve reads every
//! binder: a gap widens what a reader takes into account and never narrows it.
//!
//! # References
//!
//! - `vault:01a12317-453f-7980-9c86-68f75917f3a6` — lineage: what a node
//!   mentions is a function of its content, so its support is computed once,
//!   when the node is minted, and carried (§ codebruijn-carrier, §
//!   footprint-from-support).
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the kernel derives
//!   every support from its own nodes rather than taking one across the bridge
//!   (§ kernel-reassessment-design items 1 and 3).

use alloc::boxed::Box;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::arena::TermArena;
use crate::term::Computation;
use crate::term::DeBruijnIndex;
use crate::term::Value;
use crate::types::CompType;
use crate::types::ValueType;

/// One more than the largest free de Bruijn index a node mentions; zero for a
/// closed node.
///
/// This is the number of enclosing binders the node can reach, which is what
/// the checks that ask only how far a node reaches read.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LooseDepth(u32);

impl From<u32> for LooseDepth
{
    /// The reach of `value` binders.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(value)
    }
}

impl From<LooseDepth> for u32
{
    /// How many binders `depth` reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: LooseDepth) -> Self
    {
        depth.0
    }
}

impl LooseDepth
{
    /// The saturated maximum — the conservative answer, a reach past every
    /// binder.
    const WIDEST: Self = Self(u32::MAX);
}

/// How many indices a word of [`Reads`] holds.
const WORD_INDICES: u32 = u64::BITS;

/// The binders a node reads: exactly the free de Bruijn indices it mentions.
///
/// A set of indices all below 64 is one word, bit `i` for index `i`; a set
/// holding a larger index keeps its indices ascending behind one pointer. The
/// form is canonical, so equality compares sets.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Reads(ReadSet);

/// The forms of [`Reads`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ReadSet
{
    /// Every index is below 64: bit `i` set for index `i`.
    Word(u64),
    /// Some index is 64 or more: the indices, ascending, none repeated.
    Spilled(Box<[DeBruijnIndex]>),
    /// A node whose child the arena could not resolve, which reads every
    /// binder.
    Widest,
}

/// The support of a node the arena cannot resolve: every binder.
pub static WIDEST: Reads = Reads(ReadSet::Widest);

quenchant_shape::reason_enum! {
    /// Why a read set lists no indices.
    pub mod read_indices {
        /// The set is not a list of indices.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The node, or a node below it, could not be resolved, so it reads
            /// every binder.
            Widest,
        }
    }
}

impl Reads
{
    /// The set of `indices`, in canonical form.
    ///
    /// # Specification
    /// - requires: `indices` ascend strictly.
    /// - ensures: [`Self::indices`] yields `indices`.
    /// - provides: the one constructor of a spilled set, which keeps the form
    ///   canonical.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the witness reads back every set it builds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sets on both sides of the word's width, joined and
    ///   stepped out across it, read back and compared.
    /// - witness: `support::tests::reads_are_exactly_the_free_indices`
    #[inline]
    fn of(indices: Vec<DeBruijnIndex>) -> Self
    {
        match indices.last() {
            Some(&last) if u32::from(last) >= WORD_INDICES => {
                Self(ReadSet::Spilled(indices.into_boxed_slice()))
            },
            Some(_) | None => Self(ReadSet::Word(indices.iter().fold(0_u64, |word, &index| {
                word | 1_u64.unbounded_shl(u32::from(index))
            }))),
        }
    }

    /// No index: a closed node's support.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn closed() -> Self
    {
        Self(ReadSet::Word(0))
    }

    /// The one index `index`: one bit of a word below the word's width, so a
    /// variable's set allocates nothing there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn variable(index: DeBruijnIndex) -> Self
    {
        let position = u32::from(index);
        if position < WORD_INDICES {
            Self(ReadSet::Word(1_u64.unbounded_shl(position)))
        }
        else {
            Self(ReadSet::Spilled(Box::new([index])))
        }
    }

    /// The indices read, ascending, or the reason a set reading every binder
    /// lists none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn indices(&self) -> Maybe<ReadIndices<'_>, read_indices::Absent>
    {
        match self.0 {
            ReadSet::Word(word) => Maybe::Present(ReadIndices::Word(word)),
            ReadSet::Spilled(ref indices) => Maybe::Present(ReadIndices::Spilled(indices.iter())),
            ReadSet::Widest => Maybe::Absent(read_indices::Absent::Widest),
        }
    }

    /// One more than the largest index read, zero for none, and the widest
    /// reach for a set reading every binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn depth(&self) -> LooseDepth
    {
        match self.0 {
            ReadSet::Word(word) => LooseDepth(WORD_INDICES.saturating_sub(word.leading_zeros())),
            ReadSet::Spilled(ref indices) => LooseDepth(
                indices
                    .last()
                    .map_or(0, |&last| u32::from(last).saturating_add(1)),
            ),
            ReadSet::Widest => LooseDepth::WIDEST,
        }
    }

    /// The union of this set and `other`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the indices either set reads; every binder when either does.
    /// - provides: a former's support as its children's.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the witness reads back unions inside and across the
    ///   word's width.
    ///
    /// # Clause cost
    /// - bound: one word operation, or, for a set holding an index past the
    ///   word's width, one merge pass over the two sets' indices; no node is
    ///   read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reads::of`].
    /// - witness: `support::tests::reads_are_exactly_the_free_indices`
    #[inline]
    #[must_use]
    pub(crate) fn join(
        self,
        other: &Self,
    ) -> Self
    {
        match (self.0, &other.0) {
            (ReadSet::Word(left), &ReadSet::Word(right)) => Self(ReadSet::Word(left | right)),
            (ReadSet::Widest, _) | (_, &ReadSet::Widest) => Self(ReadSet::Widest),
            (left, _) => {
                let left = Self(left);
                let (Maybe::Present(mut first), Maybe::Present(mut second)) =
                    (left.indices(), other.indices())
                else {
                    return Self(ReadSet::Widest);
                };
                let mut merged = Vec::new();
                let (mut next_first, mut next_second) = (first.next(), second.next());
                loop {
                    match (next_first, next_second) {
                        (Some(one), Some(two)) if one < two => {
                            merged.push(one);
                            next_first = first.next();
                        },
                        (Some(one), Some(two)) if two < one => {
                            merged.push(two);
                            next_second = second.next();
                        },
                        (Some(one), Some(_)) => {
                            merged.push(one);
                            next_first = first.next();
                            next_second = second.next();
                        },
                        (Some(one), None) => {
                            merged.push(one);
                            next_first = first.next();
                        },
                        (None, Some(two)) => {
                            merged.push(two);
                            next_second = second.next();
                        },
                        (None, None) => return Self::of(merged),
                    }
                }
            },
        }
    }

    /// The set seen from outside `binders` binders: each index below `binders`
    /// dropped, every other one lowered by `binders`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `i` for every `i + binders` the set reads; a set reading
    ///   every binder still does.
    /// - provides: a binding former's support of a child standing under its
    ///   binders.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the witness steps sets out across the word's width
    ///   and reads them back.
    ///
    /// # Clause cost
    /// - bound: one word operation, or, for a set holding an index past the
    ///   word's width, one pass over its indices; no node is read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reads::of`].
    /// - witness: `support::tests::reads_are_exactly_the_free_indices`
    /// - witness: `support::tests::every_binding_former_closes_what_it_binds`
    #[inline]
    #[must_use]
    pub(crate) fn under(
        &self,
        binders: Binders,
    ) -> Self
    {
        match self.0 {
            ReadSet::Word(word) => Self(ReadSet::Word(word.unbounded_shr(binders.0))),
            ReadSet::Spilled(ref indices) => Self::of(
                indices
                    .iter()
                    .filter_map(|&index| {
                        u32::from(index)
                            .checked_sub(binders.0)
                            .map(DeBruijnIndex::from)
                    })
                    .collect(),
            ),
            ReadSet::Widest => Self(ReadSet::Widest),
        }
    }
}

/// How many binders a child stands under at its parent.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Binders(u32);

impl Binders
{
    /// A child in the parent's own scope.
    const NONE: Self = Self(0);
    /// A child under one binder.
    const ONE: Self = Self(1);
    /// A child under two binders.
    const TWO: Self = Self(2);
    /// A child under three binders.
    const THREE: Self = Self(3);
}

/// The indices a [`Reads`] holds, ascending.
#[derive(Clone, Debug)]
pub enum ReadIndices<'reads>
{
    /// The indices still to come of a word: its set bits.
    Word(u64),
    /// The indices still to come of a spilled set.
    Spilled(core::slice::Iter<'reads, DeBruijnIndex>),
}

impl Iterator for ReadIndices<'_>
{
    type Item = DeBruijnIndex;

    /// The next index, the lowest bit or entry not yet yielded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<DeBruijnIndex>
    {
        match *self {
            Self::Word(ref mut word) => {
                if *word == 0 {
                    return None;
                }
                let index = word.trailing_zeros();
                *word &= word.wrapping_sub(1);
                Some(DeBruijnIndex::from(index))
            },
            Self::Spilled(ref mut indices) => indices.next().copied(),
        }
    }
}

/// The supports of `children`, joined, each read under `binders` binders.
///
/// # Specification
/// trivial.
#[inline]
fn joined<'child>(
    start: Reads,
    children: impl IntoIterator<Item = &'child Reads>,
    binders: Binders,
) -> Reads
{
    children.into_iter().fold(start, |support, child| {
        if binders == Binders::NONE {
            support.join(child)
        }
        else {
            support.join(&child.under(binders))
        }
    })
}

impl TermArena
{
    /// The support a value minted as `value` carries: the join of its
    /// children's. No value former binds.
    ///
    /// # Specification
    /// - requires: nothing; a child the arena cannot resolve reads every
    ///   binder.
    /// - ensures: a variable's own index, nothing for a closed former, the
    ///   quoted type's support for a quote, and the join of the children's
    ///   supports otherwise.
    /// - provides: the value arm of the support every node carries.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would restate the match; the witnesses
    ///   read each former's support back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on closed and joined values, variables on both sides of
    ///   the word's width, and a child truncated away; exact supports separate
    ///   omitted children, index offsets and a narrowed gap.
    /// - witness: `support::tests::reads_are_exactly_the_free_indices`
    /// - witness: `support::tests::a_closed_value_reads_no_binder`
    /// - witness: `support::tests::an_unresolved_node_reads_every_binder`
    #[inline]
    pub(crate) fn value_carried(
        &self,
        value: &Value,
    ) -> Reads
    {
        let values = |ids: &[crate::arena::ValueId]| {
            joined(
                Reads::closed(),
                ids.iter().map(|&id| self.value_support(id)),
                Binders::NONE,
            )
        };
        match *value {
            Value::Constructor {
                datatype,
                ref fields,
                ..
            } => values(fields).join(self.value_type_support(datatype)),
            Value::Record(ref fields) => joined(
                Reads::closed(),
                fields.values().map(|&id| self.value_support(id)),
                Binders::NONE,
            ),
            Value::Variable(index) => Reads::variable(index),
            Value::ListNil | Value::Constant(_) | Value::Literal(_) => Reads::closed(),
            Value::Tuple(ref components) => values(components),
            Value::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => values(&[forward, backward]).join(self.value_type_support(path_type)),
            Value::SessionPath {
                path_type,
                payload_paths,
                ..
            }
            | Value::SessionFlow {
                flow_type: path_type,
                payload_paths,
                ..
            } => self
                .value_support(payload_paths)
                .clone()
                .join(self.value_type_support(path_type)),
            Value::PathRefl(code)
            | Value::Univalence(code)
            | Value::Here { point: code, .. }
            | Value::Stay { point: code, .. }
            | Value::Injection(_, code)
            | Value::Lift { body: code, .. } => self.value_support(code).clone(),
            Value::ForwardFlow {
                flow_type,
                translator,
                ref outputs,
                ..
            } => values(outputs)
                .join(self.value_support(translator))
                .join(self.value_type_support(flow_type)),
            Value::FunctionFlow {
                flow_type,
                domain,
                codomain,
            } => values(&[domain, codomain]).join(self.value_type_support(flow_type)),
            Value::Higher {
                evidence: ref children,
                ..
            }
            | Value::QuantifiedEvaluation { ref children, .. } => values(children),
            Value::HigherEvaluation { ref components, .. } => joined(
                Reads::closed(),
                components.iter().flat_map(|component| {
                    [component.left, component.right, component.evidence]
                        .map(|id| self.value_support(id))
                }),
                Binders::NONE,
            ),
            Value::PathProduct(first, second)
            | Value::FlowProduct(first, second)
            | Value::ListCons(first, second)
            | Value::StaticApplication(first, second)
            | Value::Then { first, second, .. } => values(&[first, second]),
            Value::Thunk(body) | Value::Returned(body) => self.computation_support(body).clone(),
            Value::Quote(quoted) => self.value_type_support(quoted).clone(),
            Value::QuoteComputation(quoted) => self.comp_type_support(quoted).clone(),
        }
    }

    /// The support a computation minted as `computation` carries.
    ///
    /// Every binding former of the term language is here: a lambda and a
    /// fixpoint bind one argument for the body, a bind binds its payload for
    /// the body only, a case binds each summand for its own branch only, a
    /// data case binds the scrutinee for its motive, a dependent split binds
    /// the scrutinee for its motive and both components for its body, a list
    /// eliminator binds head and tail for its cons branch, a transport or a
    /// ride binds the moving point for its motive, and a related application
    /// binds three for its body.
    ///
    /// # Specification
    /// - requires: nothing; a child the arena cannot resolve reads every
    ///   binder.
    /// - ensures: the join of the children's supports, each bound child's seen
    ///   from outside the binders it stands under.
    /// - provides: the computation arm of the support every node carries.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would restate the match; the witnesses
    ///   read each binding former's support back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on every binding former with a body reading the binders
    ///   it stands under and one past them, and on a bind's two positions;
    ///   exact supports separate closing the wrong child, closing too few or
    ///   too many binders, and a narrowed gap.
    /// - witness: `support::tests::every_binding_former_closes_what_it_binds`
    /// - witness: `support::tests::an_unresolved_node_reads_every_binder`
    #[inline]
    pub(crate) fn computation_carried(
        &self,
        computation: &Computation,
    ) -> Reads
    {
        let values = |ids: &[crate::arena::ValueId]| {
            joined(
                Reads::closed(),
                ids.iter().map(|&id| self.value_support(id)),
                Binders::NONE,
            )
        };
        let body = |id: crate::arena::ComputationId, binders: Binders| {
            self.computation_support(id).under(binders)
        };
        match *computation {
            Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
                ..
            } => joined(
                self.value_support(scrutinee).clone(),
                branches.iter().map(|&id| self.computation_support(id)),
                Binders::NONE,
            )
            .join(&self.comp_type_support(motive).under(Binders::ONE)),
            Computation::SigmaSplit {
                scrutinee,
                motive,
                body: split,
            } => self
                .value_support(scrutinee)
                .clone()
                .join(&self.comp_type_support(motive).under(Binders::ONE))
                .join(&body(split, Binders::TWO)),
            Computation::RecordProjection(record, _) | Computation::TupleProjection(record, _) => {
                self.value_support(record).clone()
            },
            Computation::ListFold {
                element,
                result,
                list,
                on_nil,
                on_cons,
            } => self
                .value_support(list)
                .clone()
                .join(self.value_type_support(element))
                .join(self.value_type_support(result))
                .join(self.computation_support(on_nil))
                .join(&body(on_cons, Binders::TWO)),
            Computation::ListCase {
                list,
                on_nil,
                on_cons,
            } => self
                .value_support(list)
                .clone()
                .join(self.computation_support(on_nil))
                .join(&body(on_cons, Binders::TWO)),
            Computation::Transport(path, value) => values(&[path, value]),
            Computation::PathTransport {
                motive,
                path,
                value,
            }
            | Computation::Ride {
                motive,
                flow: path,
                value,
            } => values(&[path, value]).join(&self.value_type_support(motive).under(Binders::ONE)),
            Computation::TelescopeRide {
                motive,
                flow: path,
                start,
                over,
                value,
            }
            | Computation::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value,
            } => values(&[path, start, over, value]).join(self.comp_type_support(motive)),
            Computation::RelatedApplication {
                path,
                left,
                right,
                evidence,
                body: applied,
            } => values(&[path, left, right, evidence]).join(&body(applied, Binders::THREE)),
            Computation::Lambda(lambda) | Computation::Fixpoint { body: lambda, .. } => {
                body(lambda, Binders::ONE)
            },
            Computation::Application(head, argument) => self
                .computation_support(head)
                .clone()
                .join(self.value_support(argument)),
            Computation::Return(value) | Computation::Force(value) => {
                self.value_support(value).clone()
            },
            Computation::Project(_, pair) => self.computation_support(pair).clone(),
            Computation::Bind(bound, continued) => self
                .computation_support(bound)
                .clone()
                .join(&body(continued, Binders::ONE)),
            Computation::With(ref components) => joined(
                Reads::closed(),
                components.iter().map(|&id| self.computation_support(id)),
                Binders::NONE,
            ),
            Computation::Case {
                scrutinee,
                ref branches,
            } => joined(
                self.value_support(scrutinee).clone(),
                branches.iter().map(|&id| self.computation_support(id)),
                Binders::ONE,
            ),
        }
    }

    /// The support a value type minted as `value_type` carries.
    ///
    /// A type reads binders through the codes it carries, and the dependent
    /// pair is the one binding former on the positive side: its second factor
    /// stands under one binder and its first does not.
    ///
    /// # Specification
    /// - requires: nothing; a child the arena cannot resolve reads every
    ///   binder.
    /// - ensures: nothing for a former carrying no code, the code's support for
    ///   a universe-decoding former, and the join of the children's supports
    ///   otherwise, the dependent pair's second factor seen from outside its
    ///   binder.
    /// - provides: the value-type arm of the support every node carries.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would restate the match; the witnesses
    ///   read each former's support back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on closed types, a type decoding a variable code, a
    ///   dependent pair and a child truncated away.
    /// - witness: `support::tests::a_type_reads_through_its_codes`
    /// - witness: `support::tests::every_binding_former_closes_what_it_binds`
    /// - witness: `support::tests::an_unresolved_node_reads_every_binder`
    #[inline]
    pub(crate) fn value_type_carried(
        &self,
        value_type: &ValueType,
    ) -> Reads
    {
        let types = |ids: &[crate::arena::ValueTypeId]| {
            joined(
                Reads::closed(),
                ids.iter().map(|&id| self.value_type_support(id)),
                Binders::NONE,
            )
        };
        match *value_type {
            ValueType::Data { ref arguments, .. } => joined(
                Reads::closed(),
                arguments.iter().map(|&id| self.value_support(id)),
                Binders::NONE,
            ),
            ValueType::Record(ref fields) => joined(
                Reads::closed(),
                fields.values().map(|&id| self.value_type_support(id)),
                Binders::NONE,
            ),
            ValueType::PathUniverse(source, target) | ValueType::FlowUniverse(source, target) => {
                self.value_support(source)
                    .clone()
                    .join(self.value_support(target))
            },
            ValueType::Path {
                domain,
                left,
                right,
            }
            | ValueType::Flow {
                domain,
                source: left,
                target: right,
            }
            | ValueType::Bridge {
                domain,
                left,
                right,
            } => self
                .value_type_support(domain)
                .clone()
                .join(self.value_support(left))
                .join(self.value_support(right)),
            ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) => {
                Reads::closed()
            },
            ValueType::Product(ref parts) | ValueType::Sum(ref parts) => types(parts),
            ValueType::StaticPi {
                domain: first,
                codomain: second,
            } => types(&[first, second]),
            ValueType::Sigma { first, second } => self
                .value_type_support(first)
                .clone()
                .join(&self.value_type_support(second).under(Binders::ONE)),
            ValueType::Session {
                payloads: inner, ..
            }
            | ValueType::Lift { inner, .. }
            | ValueType::List(inner)
            | ValueType::Staged { base: inner, .. } => self.value_type_support(inner).clone(),
            ValueType::Thunk(body) => self.comp_type_support(body).clone(),
            ValueType::Element { code, .. } => self.value_support(code).clone(),
        }
    }

    /// The support a computation type minted as `comp_type` carries.
    ///
    /// The dependent arrow is the one binding former on the negative side: its
    /// codomain stands under one binder and its domain does not.
    ///
    /// # Specification
    /// - requires: nothing; a child the arena cannot resolve reads every
    ///   binder.
    /// - ensures: the join of the children's supports, the dependent arrow's
    ///   codomain seen from outside its binder, and the code's support for a
    ///   computation decode.
    /// - provides: the computation-type arm of the support every node carries.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would restate the match; the witnesses
    ///   read each former's support back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a returner over a variable code, a dependent arrow
    ///   and a child truncated away.
    /// - witness: `support::tests::a_type_reads_through_its_codes`
    /// - witness: `support::tests::an_unresolved_node_reads_every_binder`
    #[inline]
    pub(crate) fn comp_type_carried(
        &self,
        comp_type: &CompType,
    ) -> Reads
    {
        match *comp_type {
            CompType::Returner(result) => self.value_type_support(result).clone(),
            CompType::Arrow { domain, codomain } => self
                .value_type_support(domain)
                .clone()
                .join(self.comp_type_support(codomain)),
            CompType::Pi { domain, codomain } => self
                .value_type_support(domain)
                .clone()
                .join(&self.comp_type_support(codomain).under(Binders::ONE)),
            CompType::Element { code, .. } => self.value_support(code).clone(),
            CompType::With(ref components) => joined(
                Reads::closed(),
                components.iter().map(|&id| self.comp_type_support(id)),
                Binders::NONE,
            ),
            CompType::Codata { ref arguments, .. } => joined(
                Reads::closed(),
                arguments.iter().map(|&id| self.value_support(id)),
                Binders::NONE,
            ),
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_kernel_strata::Level;
    use quenchant_shape::shape::Maybe;

    use super::Binders;
    use super::LooseDepth;
    use super::Reads;
    use super::WIDEST;
    use super::read_indices;
    use crate::arena::ComputationId;
    use crate::arena::TermArena;
    use crate::term::DeBruijnIndex;
    use crate::term::FixpointEvidence;
    use crate::types::GroundSort;

    /// The indices a support lists, or why it lists none.
    ///
    /// # Specification
    /// trivial.
    fn listed(reads: &Reads) -> Maybe<Vec<DeBruijnIndex>, read_indices::Absent>
    {
        match reads.indices() {
            Maybe::Present(read) => Maybe::Present(read.collect()),
            Maybe::Absent(absent) => Maybe::Absent(absent),
        }
    }

    /// The listing of exactly `indices`.
    ///
    /// # Specification
    /// trivial.
    fn set(
        indices: impl IntoIterator<Item = DeBruijnIndex>
    ) -> Maybe<Vec<DeBruijnIndex>, read_indices::Absent>
    {
        Maybe::Present(indices.into_iter().collect())
    }

    #[test]
    fn reads_are_exactly_the_free_indices()
    {
        let mut arena = TermArena::new();
        let leaves = [0_u32, 3, 63, 64, 70].map(|index| arena.value_variable(index.into()));
        let tuple = arena.value_tuple(&leaves);
        let body = arena.computation_return(tuple);
        let lambda = arena.computation_lambda(body);
        let far = arena.value_variable(DeBruijnIndex::from(64_u32));
        let returned = arena.computation_return(far);
        let stepped = arena.computation_lambda(returned);
        assert_eq!(
            set([0_u32, 3, 63, 64, 70].map(DeBruijnIndex::from)),
            listed(arena.value_support(tuple)),
            "a former reads every index its children read, on both sides of the word"
        );
        assert_eq!(
            set([2_u32, 62, 63, 69].map(DeBruijnIndex::from)),
            listed(arena.computation_support(lambda)),
            "a binder drops index zero and lowers the rest"
        );
        assert_eq!(
            &Reads::variable(DeBruijnIndex::from(63_u32)),
            arena.computation_support(stepped),
            "a spilled set stepped back inside the word takes the word's form"
        );
        assert_eq!(
            set([1_u32, 63, 64].map(DeBruijnIndex::from)),
            listed(
                &Reads::variable(DeBruijnIndex::from(64_u32))
                    .join(&Reads::variable(DeBruijnIndex::from(1_u32)))
                    .join(&Reads::variable(DeBruijnIndex::from(63_u32)))
            ),
            "a union of a word and a spilled set is ascending and repeats nothing"
        );
        assert_eq!(
            LooseDepth::from(71_u32),
            arena.value_support(tuple).depth(),
            "the depth is one more than the largest index read"
        );
        assert_eq!(
            set([0_u32, 66].map(DeBruijnIndex::from)),
            listed(
                &Reads::variable(DeBruijnIndex::from(2_u32))
                    .join(&Reads::variable(DeBruijnIndex::from(68_u32)))
                    .under(Binders::TWO)
            ),
            "stepping out of two binders lowers a spilled set by two"
        );
    }

    #[test]
    fn a_closed_value_reads_no_binder()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let pair = arena.value_tuple(&[unit, unit]);
        assert_eq!(set([]), listed(arena.value_support(pair)));
        assert_eq!(
            LooseDepth::from(0_u32),
            arena.value_support(pair).depth(),
            "a closed composite reaches no binder"
        );
    }

    #[test]
    fn an_unresolved_node_reads_every_binder()
    {
        let mut arena = TermArena::new();
        let floor = arena.watermark();
        let unit = arena.value_unit();
        let computation = arena.computation_return(unit);
        let value_type = arena.value_type_unit();
        let comp_type = arena.comp_type_returner(value_type);
        arena.truncate_to(floor);
        for support in [
            arena.value_support(unit),
            arena.computation_support(computation),
            arena.value_type_support(value_type),
            arena.comp_type_support(comp_type),
        ] {
            assert_eq!(
                Maybe::Absent(read_indices::Absent::Widest),
                listed(support),
                "a truncated id reads every binder rather than none"
            );
            assert_eq!(LooseDepth::WIDEST, support.depth());
        }
        assert_eq!(
            WIDEST,
            Reads::variable(DeBruijnIndex::from(0_u32)).join(&WIDEST),
            "every binder absorbs a join"
        );
        assert_eq!(
            WIDEST,
            WIDEST.under(Binders::THREE),
            "and survives a binder"
        );
    }

    #[test]
    fn every_binding_former_closes_what_it_binds()
    {
        let mut arena = TermArena::new();
        let at = |arena: &mut TermArena, index: u32| arena.value_variable(index.into());
        // A body reading `0` through `binders` and one index past them, which
        // is index 0 outside the former.
        let body = |arena: &mut TermArena, binders: u32| {
            let indices: Vec<_> = (0 ..= binders).map(|index| at(arena, index)).collect();
            let tuple = arena.value_tuple(&indices);
            arena.computation_return(tuple)
        };
        let code = |arena: &mut TermArena, index: u32| {
            let variable = at(arena, index);
            arena.value_type_element(variable, Level::zero())
        };
        let two = at(&mut arena, 2);
        let reads_two = arena.computation_return(two);
        let one = body(&mut arena, 1);
        let pair = body(&mut arena, 2);
        let triple = body(&mut arena, 3);
        let motive_type = code(&mut arena, 1);
        let motive = arena.comp_type_returner(motive_type);
        let unit_type = arena.value_type_unit();
        let scrutinee = at(&mut arena, 2);
        let formers: [(ComputationId, &[u32], &str); 11] = [
            (arena.computation_lambda(one), &[0], "a lambda's body"),
            (
                arena.computation_fixpoint(one, FixpointEvidence::Partial),
                &[0],
                "a fixpoint's body",
            ),
            (
                arena.computation_bind(reads_two, one),
                &[0, 2],
                "a bind's body and not its bound computation",
            ),
            (
                arena.computation_case(scrutinee, &[one, one]),
                &[0, 2],
                "each case branch and not the scrutinee",
            ),
            (
                arena.computation_data_case(scrutinee, motive, alloc::vec![reads_two]),
                &[0, 2],
                "a data case's motive and not its branches",
            ),
            (
                arena.computation_sigma_split(scrutinee, motive, pair),
                &[0, 2],
                "a split's motive by one and its body by two",
            ),
            (
                arena.computation_list_fold(unit_type, unit_type, scrutinee, reads_two, pair),
                &[0, 2],
                "a fold's cons branch by two",
            ),
            (
                arena.computation_list_case(scrutinee, reads_two, pair),
                &[0, 2],
                "a list case's cons branch by two",
            ),
            (
                arena.computation_ride(motive_type, scrutinee, scrutinee),
                &[0, 2],
                "a ride's motive by one",
            ),
            (
                arena.computation_path_transport(motive_type, scrutinee, scrutinee),
                &[0, 2],
                "a transport's motive by one",
            ),
            (
                arena.computation_related_application(
                    scrutinee,
                    (scrutinee, scrutinee),
                    scrutinee,
                    triple,
                ),
                &[0, 2],
                "a related application's body by three",
            ),
        ];
        for (former, expected, binds) in formers {
            assert_eq!(
                set(expected.iter().copied().map(DeBruijnIndex::from)),
                listed(arena.computation_support(former)),
                "{binds}"
            );
        }
        let first = code(&mut arena, 2);
        let sigma = arena.value_type_sigma(first, motive_type);
        assert_eq!(
            set([0_u32, 2].map(DeBruijnIndex::from)),
            listed(arena.value_type_support(sigma)),
            "a dependent pair's second factor and not its first"
        );
        let domain = code(&mut arena, 2);
        let pi = arena.comp_type_pi(domain, motive);
        assert_eq!(
            set([0_u32, 2].map(DeBruijnIndex::from)),
            listed(arena.comp_type_support(pi)),
            "a dependent arrow's codomain and not its domain"
        );
    }

    /// A type reaches binders exactly through the codes it carries.
    #[test]
    fn a_type_reads_through_its_codes()
    {
        let mut arena = TermArena::new();
        let zero = Level::zero();
        let closed = arena.value_type_unit();
        let code = arena.value_variable(DeBruijnIndex::from(2_u32));
        let element = arena.value_type_element(code, zero.clone());
        let returner = arena.comp_type_returner(element);
        let universe = arena.value_type_universe(GroundSort::Value, zero);
        let dependent = arena.comp_type_pi(universe, returner);
        assert_eq!(
            set([]),
            listed(arena.value_type_support(closed)),
            "a type carrying no code reads no binder"
        );
        assert_eq!(
            set([DeBruijnIndex::from(2_u32)]),
            listed(arena.value_type_support(element)),
            "a type read off a variable code reads its index"
        );
        assert_eq!(
            set([DeBruijnIndex::from(1_u32)]),
            listed(arena.comp_type_support(dependent)),
            "and from outside the dependent arrow that index is one lower"
        );
    }
}
