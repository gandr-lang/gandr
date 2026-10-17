//! Forward flows in the core: `forward(f)`, decided by computation and admitted
//! by the kernel as the forward flow it replays, and `arrow(d, c)`, the
//! arrow's action on two boundary flows.
//!
//! # The rule
//!
//! `forward(f)` synthesises `Flow(Type, ⌜A⌝, ⌜B⌝)` when `f` synthesises the
//! thunk type `U (A → F B)` of a pure non-dependent arrow, `f` is closed, both
//! codes are first-order — the unit type, the base atoms, sums of at least one
//! summand and products of any arity, as `equiv`'s — and the image of `f` at
//! every pattern of `A`'s coverage is leaf-natural. The coverage is the one
//! `equiv` decides over and the kernel replays: the unit value, a fresh
//! variable at a base atom, each summand's patterns injected first summand
//! first, and each tuple crossing its components' patterns lexicographically.
//! At a pattern `p` standing under its leaves, the normaliser evaluates `f p`
//! with every admitted definition unfolding; the image `thunk(λⁿ. return o)` is
//! leaf-natural when `o` is built from canonical constructors of `B` and
//! variables naming source leaves of the base type the target's position
//! names. A literal, a fresh value, a leaf of another type or an application
//! still stuck is [`CheckRefusal::ForwardUnsupported`]: the kernel's
//! `NonNatural`, decided before the kernel sees it. There is no round trip: a
//! flow demands no inverse.
//!
//! `arrow(d, c)` synthesises `Flow(Type, ⌜U (A → F B)⌝, ⌜U (A' → F B')⌝)` from
//! `d : Flow(Type, A', A)` and `c : Flow(Type, B, B')`: the domain flow runs
//! from the target's argument code to the source's, contravariantly, and the
//! codomain flow from the source's result code to the target's, covariantly —
//! the variance an arrow fixes at each position. Riding a function `g` along
//! it gives `λa'. a ← ride(El, d, a'); b ← g a; ride(El, c, b)`, the kernel's
//! function row. Checked against a flow between two function codes, a boundary
//! whose flow does not run the way its position fixes is
//! [`CheckRefusal::Boundary`], naming that boundary: a domain flow written
//! covariantly, from the source's argument to the target's, is the misdirected
//! boundary. A boundary code outside the first-order vocabulary is
//! [`CheckRefusal::ForwardUnsupported`]: an argument code that is itself a
//! function or universe code is outside the function clause, which would make
//! an argument variable occur at both variances.
//!
//! The judgement records, for each statement it accepts, a [`Directed`]: the
//! classifier, and for `forward` the image and the machine's dialogue at every
//! pattern. The bridge erases a `forward` to the kernel's forward flow over
//! the translator, the images and the dialogues, and an `arrow` to its function
//! flow over the two boundaries; admission regenerates the coverage, checks
//! each image's naturality, replays each dialogue under the definitions it
//! admitted and orients each boundary by its variance, and trusts nothing the
//! core decided.
//!
//! # Decisions
//!
//! - **Spelling and argument order.** `forward(f)` takes the one translator, as
//!   `equiv(f, g)` takes two; `arrow(d, c)` takes the domain boundary then the
//!   codomain boundary, the order the arrow `A → B` writes them. The record
//!   names the forward statement and leaves the arrow's action unnamed; `arrow`
//!   names the type former it acts through. The alternatives were an infix `d
//!   ~> c`, which reads as a flow between the two boundaries rather than one
//!   over them, and deriving the action from a function flow's classifier
//!   alone, under which no direction can be refused. Reversal: a surface that
//!   writes the arrow's action as congruence of `->` would elaborate to
//!   `arrow`.
//! - **Decided by computation.** The core evaluates the translator at the
//!   kernel's coverage and checks naturality itself, so a translator the kernel
//!   would refuse is refused by name at its source. The alternative was erasing
//!   the bare translator and letting the kernel compute the images, which the
//!   kernel's replay does not do: it checks supplied images. Reversal: none
//!   while the kernel's forward flow carries its images.
//! - **Synthesised from its translator.** `f` names both codes, as `equiv`'s
//!   forward translator does. Reversal: a checking rule reading the codes from
//!   `Flow(Type, A, B)` would admit a λ as the translator.
//! - **Leaf-natural images only.** A constant at an infinite base leaf has no
//!   finite certificate, and a sample of the leaf has no authority over every
//!   value; the kernel refuses both, so the core does too. Reversal: a kernel
//!   obligation that certifies a constant map at a finite type by its own
//!   exhaustion.
//!
//! # What a consumer may assume
//!
//! A value's schema evolution is a `forward` from the old code to the new; the
//! compatibility of the two is the `Flow(Type, Old, New)` the core decides and
//! the kernel replays; the move of a value is `ride(\X. X, migration, v)`, and
//! of a value inside any first-order container a ride whose motive is that
//! container over `X`. Two migrations compose by `then`, and a function moves
//! along `arrow(d, c)` by riding its argument back and its result forward.
//! Nothing reverses a flow: a migration that must also run backward is two
//! flows, or an `equiv`.

use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionDecision;
use quenchant_shape::shape::Maybe;

use crate::code::loose_reach;
use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

#[cfg(test)]
mod tests;

/// A forward flow the judgement decided: its classifier, and an image and a
/// dialogue at every pattern of its source code's coverage.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Forward
{
    /// `Flow(Type, ⌜A⌝, ⌜B⌝)`.
    classifier: ValueTypeId,
    /// `thunk(λⁿ. return o)` at each pattern, in coverage order.
    images: Arc<[ValueId]>,
    /// The machine's trace that the translator applied to each pattern
    /// converts to returning its output, in coverage order.
    dialogues: Arc<[Vec<ConversionDecision<()>>]>,
}

impl Forward
{
    /// The flow type the statement inhabits, `Flow(Type, ⌜A⌝, ⌜B⌝)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn classifier(&self) -> ValueTypeId
    {
        self.classifier
    }

    /// The image at each pattern of the source code's coverage, in the
    /// kernel's order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn images(&self) -> &[ValueId]
    {
        &self.images
    }

    /// The dialogue at each pattern, in the kernel's order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn dialogues(&self) -> &[Vec<ConversionDecision<()>>]
    {
        &self.dialogues
    }
}

/// A directed statement the judgement decided, by its former.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Directed
{
    /// `forward(f)`, with its images and dialogues.
    Forward(Forward),
    /// `arrow(d, c)`, at the flow type between its two function codes.
    Function(ValueTypeId),
}

/// A base atom a pattern's leaf stands at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Leaf
{
    /// The integer atom.
    Integer,
    /// The string atom.
    String,
}

/// The two codes the classifier of a forward translator names: `U (A → F B)`
/// gives `(A, B)`.
///
/// # Specification
/// - requires: `classifier` is the type the translator synthesised.
/// - ensures: the domain and the result of the pure non-dependent arrow the
///   classifier is the thunk of, read at their weak heads, as `equiv` reads its
///   forward translator's.
/// - fails: [`CheckRefusal::ForwardUnsupported`] at `at` for a classifier that
///   is no thunk of a pure non-dependent arrow; a weak-head or view refusal as
///   those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a migration names its two record codes, and a literal
///   translator is refused by name.
/// - witness: `forward::tests::a_migration_is_decided_at_every_covering_input`
/// - witness: `forward::tests::what_the_rule_cannot_image_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ForwardUnsupported { at: site }) => site == at,
    | Ok(_) | Err(_) => true,
})]
pub fn codes(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    classifier: ValueTypeId,
) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
{
    match crate::equiv::codes(context, at, classifier) {
        Err(CheckRefusal::EquivUnsupported { .. }) => Err(CheckRefusal::ForwardUnsupported { at }),
        decided => decided,
    }
}

/// Decide `forward(f)` between the codes `(A, B)` the translator named.
///
/// # Specification
/// - requires: `translator` synthesised `U (A → F B)` under the judgement's
///   binders.
/// - ensures: on success the classifier `Flow(Type, ⌜A⌝, ⌜B⌝)` and, at each
///   pattern of `A`'s coverage in the kernel's order, the image `thunk(λⁿ.
///   return o)` of the translator and the machine's trace that the translator
///   applied to the pattern converts to returning `o`.
/// - provides: the decision the judgement's `forward` rule makes and the record
///   the bridge erases.
/// - fails: [`CheckRefusal::ForwardUnsupported`] at `at` for an open
///   translator, a code outside the first-order vocabulary, a coverage past the
///   kernel's allowance, or an image that does not return or is not
///   leaf-natural; an evaluation, weak-head or view refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: the coverage and the naturality walk are `while let` worklists
///   over finite trees, and the images a `for` loop over the patterns, not
///   recursion.
/// - measure: the tasks left, then the patterns left.
///
/// # Adequacy
/// - hypothesis: L3 — a field-dropping migration between two records images
///   every pattern naturally and its dialogues replay in the kernel; a constant
///   string into a string field, an open translator and a list code refuse by
///   name.
/// - witness: `forward::tests::a_migration_is_decided_at_every_covering_input`
/// - witness: `forward::tests::what_the_rule_cannot_image_it_refuses_by_name`
/// - witness: `forward::tests::directed_statements_cross_and_replay`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ForwardUnsupported { at: site }) => site == at,
    | Ok(ref decided) => !decided.images.is_empty() && decided.images.len() == decided.dialogues.len(),
    | Err(_) => true,
})]
pub fn decide(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    translator: ValueId,
    (source, target): (ValueTypeId, ValueTypeId),
) -> Result<Forward, CheckRefusal>
{
    let unsupported = CheckRefusal::ForwardUnsupported { at };
    let reach = loose_reach(context.arena(), CoreNode::Term(TermNode::Value(translator)))?;
    if usize::from(reach) != 0 {
        return Err(unsupported);
    }
    first_order(context, at, target)?;
    let patterns = match crate::equiv::coverage(context, at, source) {
        Ok(Maybe::Present(patterns)) => patterns,
        Ok(Maybe::Absent(_)) | Err(CheckRefusal::UncertifiedStratum { .. }) => {
            return Err(unsupported);
        },
        Err(refusal) => return Err(refusal),
    };
    let mut images = Vec::with_capacity(patterns.len());
    let mut dialogues = Vec::with_capacity(patterns.len());
    for pattern in patterns {
        let leaves = leaves(context, at, pattern.value(), source)?;
        let arena = context.arena_mut();
        let forced = arena.computation_force(translator);
        let applied = arena.computation_application(forced, pattern.value());
        let mut body = applied;
        for _ in 0 .. pattern.binders().0 {
            body = arena.computation_lambda(body);
        }
        let claim = arena.value_thunk(body);
        let Maybe::Present(evaluation) = context.evaluate_claim(claim)?
        else {
            return Err(unsupported);
        };
        let output = evaluation.returned();
        natural(context, at, output, target, &leaves)?;
        let returned = context.arena_mut().computation_return(output);
        let Maybe::Present(dialogue) =
            context.trace_conversion(at, (applied, returned), pattern.binders())?
        else {
            return Err(unsupported);
        };
        images.push(evaluation.normal());
        dialogues.push(dialogue);
    }
    let classifier = flow_between(context, (source, target));
    Ok(Forward {
        classifier,
        images: Arc::from(images),
        dialogues: Arc::from(dialogues),
    })
}

/// `Flow(Type, ⌜from⌝, ⌜to⌝)`.
///
/// # Specification
/// trivial.
fn flow_between(
    context: &mut CheckingContext<'_>,
    (from, to): (ValueTypeId, ValueTypeId),
) -> ValueTypeId
{
    let universe = crate::flow::universe(context.arena_mut());
    let arena = context.arena_mut();
    let from = arena.value_quote(from);
    let to = arena.value_quote(to);
    arena.value_type_flow(universe, from, to)
}

/// Check that every type `code` reaches is the unit type, a base atom, a sum
/// of at least one summand or a product.
///
/// # Specification
/// - requires: `code` is formed under the judgement's binders.
/// - ensures: success exactly when the walk meets only those formers.
/// - fails: [`CheckRefusal::ForwardUnsupported`] at `at` for any other former,
///   a numeric atom among them; a weak-head or view refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a `while let` worklist over the finite type tree.
/// - measure: the types left, each replaced by its strictly smaller parts.
///
/// # Adequacy
/// - hypothesis: L3 — a list target refuses by name.
/// - witness: `forward::tests::what_the_rule_cannot_image_it_refuses_by_name`
/// - witness: `forward::tests::the_rule_reads_canonical_shapes_at_their_own_arity`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ForwardUnsupported { at: site }) => site == at,
    | Ok(()) | Err(_) => true,
})]
fn first_order(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    code: ValueTypeId,
) -> Result<(), CheckRefusal>
{
    let mut pending = Vec::from([code]);
    while let Some(ty) = pending.pop() {
        let head = context.whnf_value_type(ty)?;
        match value_type_view(context.arena(), head)? {
            ValueTypeView::Unit | ValueTypeView::Integer | ValueTypeView::String => {},
            ValueTypeView::Sum(parts) if !parts.is_empty() => {
                pending.extend(parts.iter().copied());
            },
            ValueTypeView::Product(parts) => pending.extend(parts.iter().copied()),
            ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Sum(_)
            | ValueTypeView::List(_)
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Sigma { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Session(_)
            | ValueTypeView::World(_)
            | ValueTypeView::Unknown => return Err(CheckRefusal::ForwardUnsupported { at }),
        }
    }
    Ok(())
}

/// The base atom of each leaf `pattern` binds, by de Bruijn index.
///
/// # Specification
/// - requires: `pattern` is a pattern of `source`'s coverage.
/// - ensures: one entry per index the pattern binds, the atom the source names
///   at that variable's position.
/// - fails: [`CheckRefusal::MachineInvariant`] for a pattern whose shape does
///   not follow its type; a weak-head or view refusal.
/// - panics: none.
/// - executable: none — the atom at each index is what the walk reads off the
///   type, so a predicate would restate the body.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a `while let` worklist over the finite pattern.
/// - measure: the positions left.
///
/// # Adequacy
/// - hypothesis: L3 — a record of a string and an integer reads its two leaves
///   apart, so a field moved to a position of the other atom is refused.
/// - witness: `forward::tests::what_the_rule_cannot_image_it_refuses_by_name`
/// - witness: `forward::tests::the_rule_reads_canonical_shapes_at_their_own_arity`
fn leaves(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    pattern: ValueId,
    source: ValueTypeId,
) -> Result<Vec<Maybe<Leaf, unread::Absent>>, CheckRefusal>
{
    let invariant = CheckRefusal::MachineInvariant;
    let mut found: Vec<Maybe<Leaf, unread::Absent>> = Vec::new();
    let mut pending = Vec::from([(pattern, source)]);
    while let Some((value, ty)) = pending.pop() {
        let head = context.whnf_value_type(ty)?;
        let leaf = match value_type_view(context.arena(), head)? {
            ValueTypeView::Integer => Maybe::Present(Leaf::Integer),
            ValueTypeView::String => Maybe::Present(Leaf::String),
            ValueTypeView::Unit => continue,
            ValueTypeView::Product(parts) => {
                let parts = parts.to_vec();
                match context.arena().value(value) {
                    Some(&Value::Tuple(ref components)) if components.len() == parts.len() => {
                        pending.extend(components.iter().copied().zip(parts));
                    },
                    _ => return Err(invariant),
                }
                continue;
            },
            ValueTypeView::Sum(parts) => {
                let parts = parts.to_vec();
                let Some(&Value::Injection(summand, payload)) = context.arena().value(value)
                else {
                    return Err(invariant);
                };
                let part = parts.get(usize::from(summand)).copied().ok_or(invariant)?;
                pending.push((payload, part));
                continue;
            },
            ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::List(_)
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Sigma { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Session(_)
            | ValueTypeView::World(_)
            | ValueTypeView::Unknown => return Err(CheckRefusal::ForwardUnsupported { at }),
        };
        let Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) = context.arena().value(value)
        else {
            return Err(invariant);
        };
        let index = usize::try_from(u32::from(index)).ok().ok_or(invariant)?;
        let length = index.checked_add(1).ok_or(invariant)?;
        if found.len() < length {
            found.resize(length, Maybe::Absent(unread::Absent::Unbound));
        }
        let slot = found.get_mut(index).ok_or(invariant)?;
        *slot = leaf;
    }
    Ok(found)
}

/// Check that `output` is a canonical value of `target` whose base positions
/// are variables naming source leaves of the same atom.
///
/// # Specification
/// - requires: `output` stands under the pattern's leaves; `leaves` is the
///   pattern's leaf table.
/// - ensures: success exactly when every position of `target` is met by its own
///   former's canonical value — a tuple of the product's arity, an injection
///   into an existing summand, the unit value — and every base position by a
///   variable whose leaf is that base atom.
/// - fails: [`CheckRefusal::ForwardUnsupported`] at `at` otherwise: a literal,
///   a fresh or mistyped variable, an application still stuck; a weak-head or
///   view refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a `while let` worklist over the finite output.
/// - measure: the positions left.
///
/// # Adequacy
/// - hypothesis: L3 — a field copied naturally passes, and a constant string at
///   a string field refuses by name, as the kernel refuses it as `NonNatural`.
/// - witness: `forward::tests::what_the_rule_cannot_image_it_refuses_by_name`
/// - witness: `forward::tests::the_rule_reads_canonical_shapes_at_their_own_arity`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ForwardUnsupported { at: site }) => site == at,
    | Ok(()) | Err(_) => true,
})]
fn natural(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    output: ValueId,
    target: ValueTypeId,
    leaves: &[Maybe<Leaf, unread::Absent>],
) -> Result<(), CheckRefusal>
{
    let unsupported = CheckRefusal::ForwardUnsupported { at };
    let mut pending = Vec::from([(output, target)]);
    while let Some((value, ty)) = pending.pop() {
        let head = context.whnf_value_type(ty)?;
        let wanted = match value_type_view(context.arena(), head)? {
            ValueTypeView::Integer => Leaf::Integer,
            ValueTypeView::String => Leaf::String,
            ValueTypeView::Unit => match context.arena().value(value) {
                Some(&Value::Tuple(ref components)) if components.is_empty() => continue,
                _ => return Err(unsupported),
            },
            ValueTypeView::Product(parts) => {
                let parts = parts.to_vec();
                match context.arena().value(value) {
                    Some(&Value::Tuple(ref components)) if components.len() == parts.len() => {
                        pending.extend(components.iter().copied().zip(parts));
                        continue;
                    },
                    _ => return Err(unsupported),
                }
            },
            ValueTypeView::Sum(parts) => {
                let parts = parts.to_vec();
                match context.arena().value(value) {
                    Some(&Value::Injection(summand, payload)) => {
                        let part = parts
                            .get(usize::from(summand))
                            .copied()
                            .ok_or(unsupported)?;
                        pending.push((payload, part));
                        continue;
                    },
                    _ => return Err(unsupported),
                }
            },
            ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::List(_)
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Sigma { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Session(_)
            | ValueTypeView::World(_)
            | ValueTypeView::Unknown => return Err(unsupported),
        };
        let Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) = context.arena().value(value)
        else {
            return Err(unsupported);
        };
        let index = usize::try_from(u32::from(index)).ok().ok_or(unsupported)?;
        if leaves.get(index) != Some(&Maybe::Present(wanted)) {
            return Err(unsupported);
        }
    }
    Ok(())
}

/// The first-order type the code `code` quotes.
///
/// # Specification
/// - requires: `code` is formed under the judgement's binders.
/// - ensures: the quoted type, when `code` reduces to a quote of a first-order
///   type.
/// - fails: [`CheckRefusal::ForwardUnsupported`] at `at` for a code that
///   reduces to no quote or quotes a type outside the first-order vocabulary;
///   the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — two migrations' codes decode to the records they quote.
/// - witness: `forward::tests::a_function_flow_forms_in_variance_order`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ForwardUnsupported { at: site }) => site == at,
    | Ok(_) | Err(_) => true,
})]
fn decoded(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    code: ValueId,
) -> Result<ValueTypeId, CheckRefusal>
{
    let head = context.whnf_code(code)?;
    let Some(&Value::Quote(quoted)) = context.arena().value(head)
    else {
        return Err(CheckRefusal::ForwardUnsupported { at });
    };
    first_order(context, at, quoted)?;
    Ok(quoted)
}

/// `U (domain → F result)`, pure.
///
/// # Specification
/// trivial.
fn function_code(
    context: &mut CheckingContext<'_>,
    (domain, result): (ValueTypeId, ValueTypeId),
) -> ValueId
{
    let thunk = crate::equiv::translator(context, (domain, result));
    context.arena_mut().value_quote(thunk)
}

/// The flow type `arrow(d, c)` synthesises from the types its boundaries
/// synthesised.
///
/// # Specification
/// - requires: `domain` synthesised `domain_type` and `codomain` synthesised
///   `codomain_type`, both under the judgement's binders.
/// - ensures: from `domain : Flow(Type, A', A)` and `codomain : Flow(Type, B,
///   B')`, `Flow(Type, ⌜U (A → F B)⌝, ⌜U (A' → F B')⌝)`.
/// - fails: [`CheckRefusal::ShapeMismatch`] wanting a flow at a boundary whose
///   type is no flow type; [`CheckRefusal::ForwardUnsupported`] at `at` for a
///   boundary code that is no first-order code; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — two migrations over a reader's argument and result form
///   the flow from the old reader's code to the new one's.
/// - witness: `forward::tests::a_function_flow_forms_in_variance_order`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ForwardUnsupported { at: site }) => site == at,
    | Ok(_) | Err(_) => true,
})]
pub fn arrow(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    (domain, domain_type): (ValueId, ValueTypeId),
    (codomain, codomain_type): (ValueId, ValueTypeId),
) -> Result<ValueTypeId, CheckRefusal>
{
    let (_, later, earlier) =
        crate::flow::endpoints(context, TermNode::Value(domain), domain_type)?;
    let (_, produced, widened) =
        crate::flow::endpoints(context, TermNode::Value(codomain), codomain_type)?;
    let later = decoded(context, at, later)?;
    let earlier = decoded(context, at, earlier)?;
    let produced = decoded(context, at, produced)?;
    let widened = decoded(context, at, widened)?;
    let source = function_code(context, (earlier, produced));
    let target = function_code(context, (later, widened));
    let universe = crate::flow::universe(context.arena_mut());
    Ok(context
        .arena_mut()
        .value_type_flow(universe, source, target))
}

/// Check the function flow `at`, which synthesised `synthesised`, against the
/// flow type `expected`, naming the boundary that runs against its variance.
///
/// # Specification
/// - requires: `at` is `arrow(domain, codomain)` and synthesised `synthesised`
///   by [`arrow`], so its source is `⌜U (Y → F Z)⌝` and its target `⌜U (X → F
///   W)⌝` for a domain of type `Flow(Type, X, Y)` and a codomain of type
///   `Flow(Type, Z, W)`.
/// - ensures: success when the synthesised type converts to `expected`.
///   Otherwise, when `expected` is a flow between two function codes `U (A → F
///   B)` and `U (A' → F B')`, the domain's flow `X ⇝ Y` is compared against `A'
///   ⇝ A` and the codomain's `Z ⇝ W` against `B ⇝ B'`.
/// - fails: [`CheckRefusal::Boundary`] at the first boundary whose flow does
///   not convert to the one its position fixes; otherwise the value bridge's
///   refusal for the whole.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a domain flow written from the source's argument to the
///   target's is refused naming the domain, and the flow written the other way
///   checks.
/// - witness: `forward::tests::a_misdirected_boundary_is_refused_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::Boundary { at: site }) => site == domain || site == codomain,
    | Ok(()) | Err(_) => true,
})]
pub fn against(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    (domain, codomain): (ValueId, ValueId),
    (synthesised, expected): (ValueTypeId, ValueTypeId),
    tally: &mut crate::conversion::ConversionCount,
) -> Result<(), CheckRefusal>
{
    let whole = match crate::conversion::value_bridge(context, at, synthesised, expected, tally) {
        Ok(()) => return Ok(()),
        Err(refusal @ CheckRefusal::TypeMismatch(_)) => refusal,
        Err(refusal) => return Err(refusal),
    };
    let node = TermNode::Value(at);
    let (_, found_source, found_target) = crate::flow::endpoints(context, node, synthesised)?;
    let (_, wanted_source, wanted_target) = crate::flow::endpoints(context, node, expected)?;
    let (
        Maybe::Present((earlier, produced)),
        Maybe::Present((later, widened)),
        Maybe::Present((argument, result)),
        Maybe::Present((narrowed, extended)),
    ) = (
        function_parts(context, found_source)?,
        function_parts(context, found_target)?,
        function_parts(context, wanted_source)?,
        function_parts(context, wanted_target)?,
    )
    else {
        return Err(whole);
    };
    for (boundary, found, wanted) in [
        (domain, (later, earlier), (narrowed, argument)),
        (codomain, (produced, widened), (result, extended)),
    ] {
        let found = flow_between(context, found);
        let wanted = flow_between(context, wanted);
        let mut scratch = crate::conversion::ConversionCount::default();
        match crate::conversion::value_bridge(context, boundary, found, wanted, &mut scratch) {
            Ok(()) => {},
            Err(CheckRefusal::TypeMismatch(_)) => {
                return Err(CheckRefusal::Boundary { at: boundary });
            },
            Err(refusal) => return Err(refusal),
        }
    }
    Err(whole)
}

/// The argument and result types of the function code `code` quotes, when it
/// quotes `U (A → F B)`.
///
/// # Specification
/// - requires: `code` is formed under the judgement's binders.
/// - ensures: `(A, B)` for a quote of a thunk of a pure non-dependent arrow,
///   nothing for any other code.
/// - fails: the unfolding's refusal.
/// - panics: none.
/// - executable: none — reading the code is the unfolding the body performs, so
///   a predicate would restate it.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`against`].
/// - witness: `forward::tests::a_misdirected_boundary_is_refused_by_name`
fn function_parts(
    context: &mut CheckingContext<'_>,
    code: ValueId,
) -> Result<Maybe<(ValueTypeId, ValueTypeId), unread::Absent>, CheckRefusal>
{
    let head = context.whnf_code(code)?;
    let Some(&Value::Quote(quoted)) = context.arena().value(head)
    else {
        return Ok(Maybe::Absent(unread::Absent::Unbound));
    };
    let head = context.whnf_value_type(quoted)?;
    let ValueTypeView::Thunk(computation) = value_type_view(context.arena(), head)?
    else {
        return Ok(Maybe::Absent(unread::Absent::Unbound));
    };
    let computation = context.whnf_comp_type(computation)?;
    let CompTypeView::Arrow { domain, codomain } = comp_type_view(context.arena(), computation)?
    else {
        return Ok(Maybe::Absent(unread::Absent::Unbound));
    };
    let codomain = context.whnf_comp_type(codomain)?;
    match comp_type_view(context.arena(), codomain)? {
        CompTypeView::Returner { result, .. } => Ok(Maybe::Present((domain, result))),
        CompTypeView::With(..)
        | CompTypeView::Arrow { .. }
        | CompTypeView::Pi { .. }
        | CompTypeView::Element { .. }
        | CompTypeView::Unknown => Ok(Maybe::Absent(unread::Absent::Unbound)),
    }
}

quenchant_shape::reason_enum! {
    /// Why a position reads no leaf or no function code.
    pub mod unread {
        /// The reason nothing was read.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The index binds no leaf, or the code quotes no function type.
            Unbound,
        }
    }
}
