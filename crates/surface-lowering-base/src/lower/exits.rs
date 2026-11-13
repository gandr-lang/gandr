//! The records of the exits the lowering infers.
//!
//! They also record the `return`s the lowering would infer. The lowering puts
//! every exit where its body ends. Its families write these records, and a face
//! and the `explicit-exits` lint read them.

use core::fmt;

use anodized::spec;
use gandr_core_term::ArenaWatermark;
use gandr_core_term::Carried;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::Sources;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use super::Sink;
use crate::origin::Label;
use crate::origin::Labelled;
use crate::origin::Origin;
use crate::origin::Provenance;

/// The exit a tail's polarity determines: `return` over a value, `become`
/// over a computation.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one variant per exit keyword.
/// - provides: the keyword an inferred exit stands for, and the text a fix that
///   writes it inserts.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a value tail and a computation tail, each asserted as its
///   exact exit.
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Exit
{
    /// `return v`: the tail is a value, and the body returns it.
    Return,
    /// `become c`: the tail is a computation, and the body runs it in tail
    /// position.
    Become,
}

impl fmt::Display for Exit
{
    /// Writes the keyword: `return` or `become`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Return => "return",
            Self::Become => "become",
        })
    }
}

/// Whether an attribute on the declaration or the module holding an inferred
/// exit asks for its keyword to be written.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one variant for an `explicit_exits` attribute on the owning
///   declaration or an enclosing module, one for none.
/// - provides: the module's half of the `explicit-exits` lint's switch; the
///   driver's flag is the other.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a module and a declaration carrying the attribute and a
///   declaration carrying none, each asserted as its exact answer.
/// - witness: `gandr-surface-lowering::lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Explicitness
{
    /// An `explicit_exits` attribute decorates the declaration or a module
    /// enclosing it.
    Asked,
    /// No attribute asks.
    Unasked,
}

/// An exit the lowering inferred where a path through a body ends in a form
/// that is no exit.
///
/// The lowering writes the exit the tail's polarity determines and checks it
/// as a written one; this record is what a face reads to show the keyword the
/// source left out, and what the `explicit-exits` lint reports.
///
/// # Specification
/// - requires: nothing to construct this data; the lowering produces it over
///   the tree it lowered.
/// - ensures: the span is the tail's own bytes, so no diagnostic names a
///   keyword the source did not write; the exit is the one the tail's polarity
///   names.
/// - provides: the inferred exits of a lowered module, in source order.
/// - fails: not applicable to the record itself.
/// - panics: not applicable to the record itself.
///
/// # Adequacy
/// - hypothesis: L3 — tails of each polarity, nested in matches and blocks,
///   asserted at their exact spans and exits.
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InferredExit
{
    /// The bytes of the tail the exit was inferred at.
    pub span: ByteSpan,
    /// The exit the tail's polarity names.
    pub exit: Exit,
    /// Whether an attribute asks for the keyword.
    pub explicitness: Explicitness,
}

/// A written `return` the lowering would infer were it left out: the sugared
/// form's tail, written as its value.
///
/// The `return` stands where a path through a body ends and is no statement
/// before the closing brace; it does not cross a handler's frame; and its
/// declaration lowered, under no `explicit_exits` attribute. Its operand is a
/// value, through any grouping, so the exit the bare value's polarity names is
/// the `return` written and leaving the keyword out mints the same term
/// ([`Returned::Value`]); or it is a computation written where the value is
/// read, through any grouping, which the bare tail runs as the computation it
/// is: another term, which the checker elaborates as it does the `return`
/// where it runs the computation there ([`Returned::Run`]). An early exit —
/// one in a statement whose rest it distributes — is no tail and is never
/// listed, nor is a `become`, which a sugared tail keeps.
///
/// # Specification
/// - requires: nothing to construct this data; the lowering produces it over
///   the tree it lowered.
/// - ensures: the span is the `return` form's own bytes and the value's lies
///   inside it, after the keyword.
/// - provides: the exits a formatter may leave out of a lowered module, in
///   source order.
/// - fails: not applicable to the record itself.
/// - panics: not applicable to the record itself.
///
/// # Adequacy
/// - hypothesis: L3 — a tail `return` of a value, in a body, a match arm and a
///   grouping, is listed, and so is one of a call and of an operator, bare and
///   grouped; one of a grouped type, one written as a statement, an early one,
///   one an attribute asks for and one in a refused declaration are not; each
///   listed value lowers as its tail written bare does.
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_return_of_a_value_is_listed_as_elidable_1327`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ElidableExit
{
    /// The bytes of the `return` form.
    pub span: ByteSpan,
    /// The bytes of the value it returns: the tail left without the keyword.
    pub value: ByteSpan,
    /// What the operand is, which decides what the bare tail lowers to.
    pub returned: Returned,
}

/// What an elidable `return` returns.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Returned
{
    /// A value: the bare tail lowers to the same term.
    Value,
    /// A computation written where the value is read: the bare tail lowers to
    /// the computation, and the `return` to the computation run there, which
    /// the checker elaborates to the same body where it runs it.
    Run,
}

/// What the paths through a node do with the body it stands in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the variants are ordered never, sometimes, always, so the greater
///   of two children's is what a form holding both does at least.
/// - provides: the survey's answer, which the classification reads at every
///   statement of a block a path runs through.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a computation with no exit, one with an exit in one arm
///   and one with an exit in every arm, each at one and two depths.
/// - witness: `gandr-surface-lowering::lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Leaves
{
    /// No path leaves: the node holds no exit outside a body of its own.
    #[default]
    Never,
    /// Some path leaves and some ends where the node stands.
    Sometimes,
    /// Every path leaves.
    Always,
}

/// Where the rest of a block goes after one of its statements.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a bound rest is bound once, after the statement's computation
///   returns; a distributed rest continues every local end of it.
/// - provides: the statement half of the commuting.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a statement whose computation holds no exit binds its
///   rest once, and one whose match exits in one arm continues the other.
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Rest
{
    /// The rest is bound once over the statement's computation.
    Bound,
    /// The rest continues every local end of the statement's computation,
    /// which holds an exit.
    Distributed,
}

/// Record, for every copy a rewrite made of an exit, a `break`, a loop or a
/// bind whose rest is distributed, that the copy is one too.
///
/// # Specification
/// - requires: `carried` is what one rewrite reported.
/// - ensures: every computation `carried` maps an exit, a `break`, a loop or a
///   loop's re-hold to is one; every one it maps a distributed bind to is
///   distributed, at the original's origin.
/// - provides: what keeps a match leaf's copy of an arm body commutable.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exit in an arm that binds a field leaves from the
///   leaf's copy of the arm, and a `break` in an arm continues what follows its
///   loop from the leaf's copy.
/// - witness: `gandr-surface-lowering::lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `gandr-surface-lowering::lower::loops::tests::a_break_continues_what_follows_its_loop`
#[spec(ensures: carried.iter().all(|pair| match *pair {
    Carried::Computation(held, written) => (!sink.exits.contains(&held) || sink.exits.contains(&written))
        && (!sink.breaks.contains(&held) || sink.breaks.contains(&written))
        && (!sink.loops.contains(&held) || sink.loops.contains(&written))
        && (!sink.reholds.contains(&held) || sink.reholds.contains(&written))
        && (!sink.distributed.contains_key(&held) || sink.distributed.contains_key(&written)),
    Carried::Value(..) | Carried::ValueType(..) | Carried::CompType(..) => true,
}))]
#[inline]
pub fn mark_copies(
    sink: &mut Sink<'_>,
    carried: &[Carried],
)
{
    for pair in carried {
        if let Carried::Computation(held, written) = *pair {
            for marks in [
                &mut sink.exits,
                &mut sink.breaks,
                &mut sink.loops,
                &mut sink.reholds,
            ] {
                if marks.contains(&held) {
                    let _first = marks.insert(written);
                }
            }
            if let Some(&origin) = sink.distributed.get(&held) {
                let _first = sink.distributed.insert(written, origin);
            }
        }
    }
}

/// Relabel what a rewrite replaced.
///
/// Label each written variable a rewrite replaced with the value that stands
/// for it now, when that value answers at other bytes, and carry every label
/// naming a replaced variable or session action over to its replacement; keep
/// each written value type a rewrite replaced as a stand-in for its
/// replacement.
///
/// # Specification
/// - requires: every node `carried` reports has its origin recorded.
/// - ensures: one label per variable `carried` reports replaced whose origin is
///   written and whose replacement's origin spans other bytes, naming the
///   replacement; a label that named a replaced variable, or the endpoint of a
///   replaced session action, names its replacement; one stand-in per value
///   type `carried` reports replaced whose origin is written and whose
///   replacement's origin spans other bytes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a use of a bound match's binder, instantiated at the
///   value an arm passes, answers at that value's type, through a chain of such
///   instantiations too; a scrutinee a leaf's copy replaces answers at its
///   bytes; a functor's parameter type, renamed to an argument's, answers where
///   the template writes it; an endpoint written in an offer the lowering
///   rebuilds answers at the rebuilt offer.
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
/// - witness: `gandr-surface-lowering::lower::tests::a_type_head_answers_at_what_it_stands_for`
/// - witness: `gandr-surface-lowering::lower::session::tests::each_endpoint_answers_at_its_action`
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_variable_answering_at_its_own_bytes_gains_no_label`
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_renamed_parameter_type_stands_in_only_at_other_bytes`
#[spec(captures: before = sink.origins.labels().len(), ensures: sink.origins.labels().len() >= before)]
#[inline]
pub fn label_replaced(
    sink: &mut Sink<'_>,
    carried: &[Carried],
)
{
    for pair in carried {
        match *pair {
            Carried::Value(replaced, standing) => {
                if !matches!(sink.arena.value(replaced), Some(&Value::Variable { .. })) {
                    continue;
                }
                sink.origins
                    .relabel(&Labelled::Value(replaced), &Labelled::Value(standing));
                let (Maybe::Present(written), Maybe::Present(now)) =
                    (sink.origins.value(replaced), sink.origins.value(standing))
                else {
                    continue;
                };
                if written.provenance() == Provenance::Written && now.span() != written.span() {
                    sink.origins.record_label(Label {
                        span: written.span(),
                        labelled: Labelled::Value(standing),
                    });
                }
            },
            Carried::ValueType(replaced, standing) => {
                let (Maybe::Present(written), Maybe::Present(now)) = (
                    sink.origins.value_type(replaced),
                    sink.origins.value_type(standing),
                )
                else {
                    continue;
                };
                if written.provenance() == Provenance::Written && now.span() != written.span() {
                    sink.origins.record_stand_in(standing, written);
                }
            },
            Carried::Computation(replaced, standing) => {
                if matches!(
                    sink.arena.computation(replaced),
                    Some(&Computation::Session(_))
                ) {
                    sink.origins.relabel_action(replaced, standing);
                }
            },
            Carried::CompType(..) => {},
        }
    }
}

/// Record the origin of every node minted since `mark`, each its source's in
/// `carried`.
///
/// # Specification
/// - requires: nothing has been recorded for a node minted since `mark`, and
///   `carried` reports the rewrite that minted them.
/// - ensures: every node minted since `mark` carries the origin of the first
///   node `carried` reports it rewritten from, or `fallback`; every computation
///   rewritten from a match's root carries the match's record; each written
///   variable the rewrite replaced is labelled as [`label_replaced`] labels it.
/// - provides: the origin half of `carry`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as `carry`.
/// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
#[spec(ensures: sink.arena.computations_since(mark).all(|id| matches!(sink.origins.computation(id), Maybe::Present(_)))
    && sink.arena.values_since(mark).all(|id| matches!(sink.origins.value(id), Maybe::Present(_))))]
#[inline]
pub fn record_copies(
    sink: &mut Sink<'_>,
    mark: ArenaWatermark,
    carried: &[Carried],
    fallback: Origin,
)
{
    let sources = Sources::of(carried);
    for id in sink.arena.values_since(mark) {
        let origin = value_origin(sink, &sources, id, fallback);
        sink.origins.record_value(id, origin);
    }
    for id in sink.arena.computations_since(mark) {
        let origin = computation_origin(sink, &sources, id, fallback);
        sink.origins.record_computation(id, origin);
        keep_case(sink, &sources, id);
    }
    for id in sink.arena.value_types_since(mark) {
        let origin = value_type_origin(sink, &sources, id, fallback);
        sink.origins.record_value_type(id, origin);
    }
    for id in sink.arena.comp_types_since(mark) {
        let origin = comp_type_origin(sink, &sources, id, fallback);
        sink.origins.record_comp_type(id, origin);
    }
    label_replaced(sink, carried);
}

/// The origin of value `id`: the origin of the value it stands for in
/// `sources`, or `fallback`.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn value_origin(
    sink: &Sink<'_>,
    sources: &Sources,
    id: ValueId,
    fallback: Origin,
) -> Origin
{
    sources.values().get(&id).map_or(fallback, |&held| {
        found_or(sink.origins.value(held), fallback)
    })
}

/// The origin of computation `id`: the origin of the computation it stands
/// for in `sources`, or `fallback`.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn computation_origin(
    sink: &Sink<'_>,
    sources: &Sources,
    id: ComputationId,
    fallback: Origin,
) -> Origin
{
    sources.computations().get(&id).map_or(fallback, |&held| {
        found_or(sink.origins.computation(held), fallback)
    })
}

/// The origin of value type `id`: the origin of the value type it stands for
/// in `sources`, or `fallback`.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn value_type_origin(
    sink: &Sink<'_>,
    sources: &Sources,
    id: ValueTypeId,
    fallback: Origin,
) -> Origin
{
    sources.value_types().get(&id).map_or(fallback, |&held| {
        found_or(sink.origins.value_type(held), fallback)
    })
}

/// The origin of computation type `id`: the origin of the computation type it
/// stands for in `sources`, or `fallback`.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn comp_type_origin(
    sink: &Sink<'_>,
    sources: &Sources,
    id: CompTypeId,
    fallback: Origin,
) -> Origin
{
    sources.comp_types().get(&id).map_or(fallback, |&held| {
        found_or(sink.origins.comp_type(held), fallback)
    })
}

/// Record for computation `id` the match record of the computation it stands
/// for in `sources`, when that one roots a match, and the family it
/// eliminates, when it is a data case.
///
/// # Specification
/// - requires: `id` has no match record yet.
/// - ensures: a copy of a match's root carries that match's record; where the
///   source eliminates the value its record names and the copy eliminates a
///   value of its own, the copy's record names the copy's, so the patterns
///   answer where the run judged the copy (#298); a copy of a data case
///   eliminates the source's family.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a match carried under a binder keeps its patterns, a
///   match bound by a `let` whose block continues its local ends answers its
///   patterns at the copy's scrutinee, and a match written in an arm that binds
///   a field names its own arms in the leaf's copy.
/// - witness: `gandr-surface-lowering::lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
/// - witness: `gandr-surface-lowering::lower::native::tests::a_data_case_names_the_family_it_eliminates_809`
#[spec(ensures: sources.computations().get(&id).is_none_or(|&held|
    (matches!(sink.origins.case(held), Maybe::Absent(_)) || matches!(sink.origins.case(id), Maybe::Present(_)))
    && (matches!(sink.origins.elimination(held), Maybe::Absent(_)) || matches!(sink.origins.elimination(id), Maybe::Present(_)))))]
#[inline]
pub fn keep_case(
    sink: &mut Sink<'_>,
    sources: &Sources,
    id: ComputationId,
)
{
    let Some(&held) = sources.computations().get(&id)
    else {
        return;
    };
    if let Maybe::Present(family) = sink.origins.elimination(held) {
        sink.origins.record_elimination(id, family);
    }
    if let Maybe::Present(case) = sink.origins.case(held) {
        let mut kept = case.clone();
        if let (Some(source), Some(copy)) = (
            eliminated(sink.arena.computation(held)),
            eliminated(sink.arena.computation(id)),
        ) && kept.scrutinised == Maybe::Present(source)
        {
            kept.scrutinised = Maybe::Present(copy);
        }
        sink.origins.record_case(id, kept);
    }
}

/// The origin `found` holds, or `fallback`.
///
/// # Specification
/// trivial.
#[inline]
pub const fn found_or<Reason>(
    found: Maybe<Origin, Reason>,
    fallback: Origin,
) -> Origin
where
    Reason: Copy,
{
    match found {
        Maybe::Present(origin) => origin,
        Maybe::Absent(_) => fallback,
    }
}

/// The value a case, a data case or a list case eliminates; nothing for any
/// other node.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn eliminated(node: Option<&Computation>) -> Option<ValueId>
{
    match node {
        Some(
            &(Computation::Case { scrutinee, .. }
            | Computation::DataCase { scrutinee, .. }
            | Computation::ListCase {
                list: scrutinee, ..
            }),
        ) => Some(scrutinee),
        Some(_) | None => None,
    }
}
