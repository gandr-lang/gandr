//! The unifier: equations between core values and types, decided by
//! decomposition where both sides are rigid and by binding where one side is
//! a metavariable, and postponed where neither answers most generally.
//!
//! # Boundaries
//!
//! - A refutation is evidence no instantiation of the metavariables changes:
//!   two introduction forms or two type formers with different heads, or a
//!   metavariable occurring strongly rigidly in what it would be bound to.
//! - Every other equation the run cannot answer most generally is postponed in
//!   the metacontext's store with its [`Reason`] and the unsolved metavariables
//!   that block it, and re-enters the run when one of them is solved. A neutral
//!   against a rigid side ([`Reason::Neutral`]), a binder the carried support
//!   names ([`Reason::Escape`]: the support over-approximates dependence) and a
//!   flexible occurrence ([`Reason::Occurs`]) wait there; so do the fragment's
//!   edges, a definition ([`Reason::Unfolding`]), a gradual side
//!   ([`Reason::Gradual`]), an applied metavariable ([`Reason::Spine`]), a
//!   former the fragment does not decompose ([`Reason::Outside`]) and a
//!   metavariable of a wider context in a solution ([`Reason::Pruning`]).

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::fill_hole;
use gandr_core_term::hole::TermId;
use gandr_core_term::shift_value;
use gandr_core_term::strengthen_value;
use gandr_kernel_strata::Level;
use quenchant_shape::shape::Maybe;

use crate::meta::MetaId;
use crate::meta::Metas;

/// The steps one run may take before it postpones what is left: far past any
/// equation an application poses, so a run is total on untrusted input.
const BUDGET: u32 = 0x0001_0000;

/// One side of an equation, in the family both sides share.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Side
{
    /// A value.
    Value(ValueId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// One equation, posed under `scope` intuitionistic binders.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Equation
{
    /// The binders both sides stand under.
    scope: Binders,
    /// The left side.
    left: Side,
    /// The right side.
    right: Side,
}

impl Equation
{
    /// The equation `left = right` under `scope` binders.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        scope: Binders,
        left: Side,
        right: Side,
    ) -> Self
    {
        Self { scope, left, right }
    }

    /// The binders both sides stand under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scope(&self) -> Binders
    {
        self.scope
    }

    /// The left side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left(&self) -> Side
    {
        self.left
    }

    /// The right side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right(&self) -> Side
    {
        self.right
    }
}

/// What a run decided.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Verdict
{
    /// Every equation holds under the bindings made, and the store is empty.
    Solved,
    /// No equation is refuted, and the store holds the equations that wait:
    /// [`Metas::postponed`] lists them.
    Postponed,
    /// No binding of the metavariables makes the equations hold.
    Refuted(Refutation),
}

/// Evidence that no solution exists, stable under every instantiation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Refutation
{
    /// Two introduction forms, or two type formers, with different heads.
    Clash
    {
        /// The left side.
        left: Side,
        /// The right side.
        right: Side,
    },
    /// The metavariable occurs strongly rigidly, under introduction forms
    /// only, in the value it would be bound to.
    Occurs
    {
        /// The metavariable.
        meta: MetaId,
        /// The value.
        within: ValueId,
    },
}

/// Why an equation waits in the store.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reason
{
    /// A definition on a side: only unfolding could decide the pair.
    Unfolding,
    /// A hole no metacontext declares, a marked value or the unknown type:
    /// consistent with everything, so nothing is forced.
    Gradual,
    /// A metavariable applied to arguments.
    Spine,
    /// A former the fragment does not decompose.
    Outside,
    /// Two sides of different families.
    Families,
    /// A neutral against a rigid side, or two distinct neutrals: a conversion
    /// failure, which a singleton type or an instantiation can still close.
    Neutral,
    /// Two decodes at different levels.
    Levels,
    /// The value a metavariable would be bound to mentions a metavariable of
    /// a wider context.
    Pruning
    {
        /// The metavariable being bound.
        meta: MetaId,
        /// The metavariable of the wider context.
        other: MetaId,
    },
    /// The value's carried support names a binder the metavariable's context
    /// does not hold; the support over-approximates dependence, so this is no
    /// refutation.
    Escape
    {
        /// The metavariable.
        meta: MetaId,
    },
    /// The metavariable occurs in the value it would be bound to, but not
    /// strongly rigidly.
    Occurs
    {
        /// The metavariable.
        meta: MetaId,
    },
    /// A metavariable occurring under fewer binders than its context holds.
    Scope
    {
        /// The metavariable.
        meta: MetaId,
    },
    /// A linear variable, which no metavariable stands for.
    Linear,
    /// A node the arena does not hold.
    Dangling,
    /// The run spent its steps before reaching the equation.
    Budget,
}

/// An equation the solver could not answer most generally when it met it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Postponed
{
    /// The equation.
    equation: Equation,
    /// Why it waits.
    reason: Reason,
    /// The unsolved metavariables whose solution re-poses it.
    blockers: Vec<MetaId>,
}

impl Postponed
{
    /// The equation that waits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn equation(&self) -> Equation
    {
        self.equation
    }

    /// Why it waits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reason(&self) -> Reason
    {
        self.reason
    }

    /// The unsolved metavariables whose solution re-poses it; none when only
    /// a later rung of the fragment can.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn blockers(&self) -> &[MetaId]
    {
        &self.blockers
    }
}

/// Why a step did not decide its equation.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Stop
{
    /// No solution exists.
    Refuted(Refutation),
    /// The equation waits, for the reason, on the blockers.
    Postpone(Reason, Vec<MetaId>),
}

impl Stop
{
    /// The equation waits for `reason` on nothing a solution can change.
    ///
    /// # Specification
    /// trivial.
    const fn wait(reason: Reason) -> Self
    {
        Self::Postpone(reason, Vec::new())
    }
}

/// How a value reads to the unifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Head
{
    /// An unsolved metavariable.
    Flex(MetaId),
    /// A gradual hole or a marked value.
    Gradual,
    /// A definition.
    Unfold,
    /// The metavariable applied to arguments.
    Spine(MetaId),
    /// A former the fragment does not decompose.
    Outside,
    /// A former the fragment decomposes.
    Rigid,
}

/// How a value type or a computation type reads to the unifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeHead<'arena>
{
    /// The decode of a code, at a level.
    Code(ValueId, &'arena Level),
    /// The unknown type.
    Gradual,
    /// A former the fragment does not decompose.
    Outside,
    /// A former the fragment decomposes.
    Rigid,
}

/// Whether a hole stands in a term, and how.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Occurrence
{
    /// The hole stands in the term on a path of introduction forms.
    Strong,
    /// The hole stands in the term, under some other former.
    Stands,
    /// The hole is absent from the term.
    Absent,
}

/// What a step does once the sides are classified.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Action
{
    /// The pair is decided, its children pushed.
    Done,
    /// Bind a metavariable to a value.
    Bind(MetaId, ValueId),
    /// Bind a metavariable to the quote of a value type.
    Quote(MetaId, ValueTypeId),
    /// Bind a metavariable to the quote of a computation type.
    QuoteComputation(MetaId, CompTypeId),
}

/// Solve `equations` in order, binding `metas` where an equation forces it
/// and postponing in its store what no step answers most generally.
///
/// # Specification
/// - requires: every metavariable occurring in an equation is declared in
///   `metas` with a context of at most the equation's binders.
/// - ensures: [`Verdict::Solved`] when every equation holds once each bound
///   metavariable is read as its solution, weakened past the binders between
///   its context and the occurrence, and the store is empty;
///   [`Verdict::Postponed`] when nothing is refuted and the store holds what
///   waits; a binding is made only where an equation forces it, and a postponed
///   equation whose blocker is bound is posed again in the same run. The
///   bindings and the store before a refutation stand.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — an implicit's decode against a base type is bound to the
///   base type's quote, a data type's argument to the argument the other side
///   writes; a definition, a gradual side, an applied metavariable, a neutral
///   against a constructor and an escape read from a support wait by name while
///   the equations after them are solved; a postponed equation wakes when its
///   blocker is bound, and two orders of one problem end alike; a strongly
///   rigid occurrence is refuted and a flexible one waits.
/// - witness: `tests::solve::a_decoded_metavariable_takes_the_quote`
/// - witness: `tests::solve::a_data_argument_is_read_off_the_other_side`
/// - witness: `tests::solve::a_solution_naming_an_inner_binder_waits`
/// - witness: `tests::solve::the_fragment_postpones_by_name`
/// - witness: `tests::solve::a_postponed_equation_wakes_in_either_order`
/// - witness: `tests::solve::a_metavariable_in_its_own_solution_is_refuted`
/// - witness: `tests::solve::a_flexible_occurrence_waits`
#[inline]
#[spec(captures: waiting = metas.postponed().is_empty(),
    ensures: |output| (equations.is_empty() && waiting) <= (output == Verdict::Solved)
        && (matches!(output, Verdict::Refuted(_)) || ((output == Verdict::Postponed) != metas.postponed().is_empty())))]
pub fn solve(
    arena: &mut CoreArena,
    metas: &mut Metas,
    equations: &[Equation],
) -> Verdict
{
    let mut work: Vec<Equation> = equations.iter().rev().copied().collect();
    let mut remaining = BUDGET;
    while let Some(equation) = work.pop() {
        let Some(left) = remaining.checked_sub(1)
        else {
            work.push(equation);
            for spent in core::mem::take(&mut work).into_iter().rev() {
                metas.postpone(Postponed {
                    equation: spent,
                    reason: Reason::Budget,
                    blockers: Vec::new(),
                });
            }
            break;
        };
        remaining = left;
        match step(arena, metas, equation, &mut work) {
            Ok(()) => {},
            Err(Stop::Refuted(refutation)) => return Verdict::Refuted(refutation),
            Err(Stop::Postpone(reason, blockers)) => metas.postpone(Postponed {
                equation,
                reason,
                blockers,
            }),
        }
    }
    if metas.postponed().is_empty() {
        Verdict::Solved
    }
    else {
        Verdict::Postponed
    }
}

/// Decide one equation, pushing what it decomposes into and what a binding
/// wakes.
///
/// `Ok` when the pair is decided or decomposed, its children pushed onto
/// `work`; otherwise why it stops.
///
/// # Specification
/// trivial.
fn step(
    arena: &mut CoreArena,
    metas: &mut Metas,
    equation: Equation,
    work: &mut Vec<Equation>,
) -> Result<(), Stop>
{
    let Equation { scope, left, right } = equation;
    let action = match (left, right) {
        (Side::Value(one), Side::Value(other)) => values(arena, metas, scope, (one, other), work)?,
        (Side::ValueType(one), Side::ValueType(other)) => {
            value_types(arena, metas, scope, (one, other), work)?
        },
        (Side::CompType(one), Side::CompType(other)) => {
            comp_types(arena, metas, scope, (one, other), work)?
        },
        (Side::Value(_), Side::ValueType(_) | Side::CompType(_))
        | (Side::ValueType(_), Side::Value(_) | Side::CompType(_))
        | (Side::CompType(_), Side::Value(_) | Side::ValueType(_)) => {
            return Err(Stop::wait(Reason::Families));
        },
    };
    let (meta, term) = match action {
        Action::Done => return Ok(()),
        Action::Bind(meta, term) => (meta, term),
        Action::Quote(meta, quoted) => (meta, arena.value_quote(quoted)),
        Action::QuoteComputation(meta, quoted) => (meta, arena.value_quote_computation(quoted)),
    };
    bind(arena, metas, scope, meta, term)?;
    work.extend(metas.wake(meta).into_iter().rev());
    Ok(())
}

/// A value read through every solved metavariable standing at its root,
/// each solution weakened past the binders between its context and `scope`.
///
/// The result's root is no solved metavariable; a metavariable standing under
/// fewer binders than its context holds waits as [`Reason::Scope`].
///
/// # Specification
/// trivial.
///
/// # Termination
/// - reason: a `for` loop bounded by one more than the metavariable count; a
///   chain of solutions is acyclic, since the occurs check reads through every
///   solution, so it is at most that long.
fn resolve(
    arena: &mut CoreArena,
    metas: &Metas,
    scope: Binders,
    value: ValueId,
) -> Result<ValueId, Stop>
{
    let mut current = value;
    for _ in 0 ..= usize::from(metas.count()) {
        let Some(&Value::Hole(hole)) = arena.value(current)
        else {
            return Ok(current);
        };
        let Maybe::Present(meta) = metas.meta(hole)
        else {
            return Ok(current);
        };
        let (Maybe::Present(solution), Maybe::Present(declared)) =
            (metas.solution(meta), metas.scope(meta))
        else {
            return Ok(current);
        };
        let past = u32::from(scope)
            .checked_sub(u32::from(declared))
            .ok_or_else(|| Stop::wait(Reason::Scope { meta }))?;
        current = shift_value(arena, solution, Binders::from(past)).settle(arena);
    }
    Ok(current)
}

/// How `value` reads to the unifier.
///
/// A hole `metas` declares reads [`Head::Flex`] until it is solved, and a
/// static application whose head chain ends at an unsolved one
/// [`Head::Spine`]; a solved one there is a redex the fragment does not
/// reduce.
///
/// # Specification
/// trivial.
///
/// # Termination
/// - reason: the head chain descends to strictly older nodes of an arena that
///   mints children before parents, so the `while` loop ends.
fn head(
    arena: &CoreArena,
    metas: &Metas,
    value: &Value,
) -> Head
{
    match *value {
        Value::Hole(hole) => match metas.meta(hole) {
            Maybe::Present(meta) => Head::Flex(meta),
            Maybe::Absent(_) => Head::Gradual,
        },
        Value::Mark { .. } => Head::Gradual,
        Value::Constant(_) => Head::Unfold,
        Value::StaticApplication(mut function, _) => {
            while let Some(&Value::StaticApplication(inner, _)) = arena.value(function) {
                function = inner;
            }
            match arena.value(function) {
                Some(&Value::Hole(hole)) => match metas.meta(hole) {
                    Maybe::Present(meta) if matches!(metas.solution(meta), Maybe::Absent(_)) => {
                        Head::Spine(meta)
                    },
                    Maybe::Present(_) => Head::Outside,
                    Maybe::Absent(_) => Head::Gradual,
                },
                Some(_) | None => Head::Outside,
            }
        },
        Value::Variable { .. }
        | Value::Literal(_)
        | Value::Tuple(_)
        | Value::Injection(..)
        | Value::ListNil
        | Value::ListCons(..)
        | Value::Quote(_)
        | Value::QuoteComputation(_)
        | Value::StaticLambda(_)
        | Value::Constructor { .. }
        | Value::Record(_) => Head::Rigid,
        Value::Primitive { .. }
        | Value::PathRefl(_)
        | Value::PathProduct(..)
        | Value::PathEquiv { .. }
        | Value::Here(_)
        | Value::Funext(..)
        | Value::Equiv(..)
        | Value::Univalence(..)
        | Value::Ua { .. }
        | Value::SessionRelated { .. }
        | Value::Stay(_)
        | Value::Then(..)
        | Value::FlowProduct(..)
        | Value::Forward(_)
        | Value::FunctionFlow(..)
        | Value::Recorded(_)
        | Value::Returned(_)
        | Value::Nested(_)
        | Value::Run(_)
        | Value::Thunk(_)
        | Value::Lift { .. }
        | Value::Reify(_) => Head::Outside,
    }
}

/// Why a side that is not rigid makes its equation wait, if it does.
///
/// # Specification
/// trivial.
fn obstruction(head: Head) -> Option<Stop>
{
    match head {
        Head::Gradual => Some(Stop::wait(Reason::Gradual)),
        Head::Unfold => Some(Stop::wait(Reason::Unfolding)),
        Head::Spine(meta) => Some(Stop::Postpone(Reason::Spine, Vec::from([meta]))),
        Head::Outside => Some(Stop::wait(Reason::Outside)),
        Head::Flex(_) | Head::Rigid => None,
    }
}

/// Decide two values.
///
/// One side an unsolved metavariable and the other neither gradual nor an
/// applied metavariable is a binding; two rigid values sharing a head push
/// their children; differing introduction forms clash; anything else waits.
///
/// # Specification
/// trivial.
fn values(
    arena: &mut CoreArena,
    metas: &Metas,
    scope: Binders,
    (one, other): (ValueId, ValueId),
    work: &mut Vec<Equation>,
) -> Result<Action, Stop>
{
    let one = resolve(arena, metas, scope, one)?;
    let other = resolve(arena, metas, scope, other)?;
    if one == other {
        return Ok(Action::Done);
    }
    let (Some(first), Some(second)) = (arena.value(one), arena.value(other))
    else {
        return Err(Stop::wait(Reason::Dangling));
    };
    let (first_head, second_head) = (head(arena, metas, first), head(arena, metas, second));
    if let (Head::Flex(a), Head::Flex(b)) = (first_head, second_head) {
        return Ok(flex_flex(metas, (a, one), (b, other)));
    }
    for (flex, rigid, rigid_head) in [
        (first_head, other, second_head),
        (second_head, one, first_head),
    ] {
        if let Head::Flex(meta) = flex {
            return match rigid_head {
                Head::Gradual => Err(Stop::Postpone(Reason::Gradual, Vec::from([meta]))),
                Head::Spine(applied) => {
                    Err(Stop::Postpone(Reason::Spine, Vec::from([meta, applied])))
                },
                Head::Flex(_) | Head::Unfold | Head::Outside | Head::Rigid => {
                    Ok(Action::Bind(meta, rigid))
                },
            };
        }
    }
    if let Some(stop) = obstruction(first_head).or_else(|| obstruction(second_head)) {
        return Err(stop);
    }
    rigid_values(
        scope,
        (first, second),
        (Side::Value(one), Side::Value(other)),
        work,
    )?;
    Ok(Action::Done)
}

/// Two distinct unsolved metavariables: the one of the deeper context bound
/// to the other's hole, so the solution mentions nothing its context lacks.
///
/// The metavariable whose context holds more binders is bound, the later one at
/// a tie.
///
/// # Specification
/// trivial.
fn flex_flex(
    metas: &Metas,
    (one, one_hole): (MetaId, ValueId),
    (other, other_hole): (MetaId, ValueId),
) -> Action
{
    let deeper_first = match (metas.scope(one), metas.scope(other)) {
        (Maybe::Present(first), Maybe::Present(second)) => (first, one) >= (second, other),
        (Maybe::Present(_) | Maybe::Absent(_), Maybe::Absent(_))
        | (Maybe::Absent(_), Maybe::Present(_)) => true,
    };
    if deeper_first {
        Action::Bind(one, other_hole)
    }
    else {
        Action::Bind(other, one_hole)
    }
}

/// Decompose two rigid values sharing a head, refute two introduction forms
/// whose heads differ, or postpone a variable against anything else.
///
/// The children are pushed, a static lambda's body under one more binder;
/// differing heads or payloads of two introduction forms clash; two distinct
/// variables, or a variable against an introduction form, wait as
/// [`Reason::Neutral`], since a singleton type relates them; a linear variable
/// waits as [`Reason::Linear`].
///
/// # Specification
/// trivial.
fn rigid_values(
    scope: Binders,
    (first, second): (&Value, &Value),
    (left, right): (Side, Side),
    work: &mut Vec<Equation>,
) -> Result<(), Stop>
{
    let clash = Stop::Refuted(Refutation::Clash { left, right });
    let push = |work: &mut Vec<Equation>, scope: Binders, one: Side, other: Side| {
        work.push(Equation::new(scope, one, other));
    };
    match (first, second) {
        (
            &Value::Variable {
                zone: one_zone,
                index: one_index,
            },
            &Value::Variable {
                zone: other_zone,
                index: other_index,
            },
        ) => {
            if one_zone == Zone::Linear || other_zone == Zone::Linear {
                return Err(Stop::wait(Reason::Linear));
            }
            if one_index != other_index {
                return Err(Stop::wait(Reason::Neutral));
            }
        },
        (&Value::Literal(ref one), &Value::Literal(ref other)) => {
            if one != other {
                return Err(clash);
            }
        },
        (&Value::Tuple(ref one), &Value::Tuple(ref other)) => {
            if one.len() != other.len() {
                return Err(clash);
            }
            for (&a, &b) in one.iter().zip(other.iter()).rev() {
                push(work, scope, Side::Value(a), Side::Value(b));
            }
        },
        (&Value::Injection(one_summand, one), &Value::Injection(other_summand, other)) => {
            if one_summand != other_summand {
                return Err(clash);
            }
            push(work, scope, Side::Value(one), Side::Value(other));
        },
        (&Value::ListNil, &Value::ListNil) => {},
        (&Value::ListCons(one_head, one_tail), &Value::ListCons(other_head, other_tail)) => {
            push(work, scope, Side::Value(one_tail), Side::Value(other_tail));
            push(work, scope, Side::Value(one_head), Side::Value(other_head));
        },
        (&Value::Quote(one), &Value::Quote(other)) => {
            push(work, scope, Side::ValueType(one), Side::ValueType(other));
        },
        (&Value::QuoteComputation(one), &Value::QuoteComputation(other)) => {
            push(work, scope, Side::CompType(one), Side::CompType(other));
        },
        (&Value::StaticLambda(one), &Value::StaticLambda(other)) => {
            push(work, scope.deeper(), Side::Value(one), Side::Value(other));
        },
        (
            &Value::Constructor {
                datatype: one_type,
                tag: one_tag,
                fields: ref one_fields,
            },
            &Value::Constructor {
                datatype: other_type,
                tag: other_tag,
                fields: ref other_fields,
            },
        ) => {
            if one_tag != other_tag || one_fields.len() != other_fields.len() {
                return Err(clash);
            }
            for (&a, &b) in one_fields.iter().zip(other_fields.iter()).rev() {
                push(work, scope, Side::Value(a), Side::Value(b));
            }
            push(
                work,
                scope,
                Side::ValueType(one_type),
                Side::ValueType(other_type),
            );
        },
        (&Value::Record(ref one), &Value::Record(ref other)) => {
            if one.len() != other.len() || !one.keys().eq(other.keys()) {
                return Err(clash);
            }
            for (&a, &b) in one.values().zip(other.values()).rev() {
                push(work, scope, Side::Value(a), Side::Value(b));
            }
        },
        (&Value::Variable { .. }, _) | (_, &Value::Variable { .. }) => {
            return Err(Stop::wait(Reason::Neutral));
        },
        _ => return Err(clash),
    }
    Ok(())
}

/// A value type with the code of a decode read through solved
/// metavariables; the decode of a quote is the quoted type.
///
/// The type comes back unchanged unless it decodes a code that resolves to
/// another value, and is then the decode of that value.
///
/// # Specification
/// trivial.
fn resolve_value_type(
    arena: &mut CoreArena,
    metas: &Metas,
    scope: Binders,
    value_type: ValueTypeId,
) -> Result<ValueTypeId, Stop>
{
    let Some(&ValueType::Element { code, ref target }) = arena.value_type(value_type)
    else {
        return Ok(value_type);
    };
    let target = target.clone();
    let resolved = resolve(arena, metas, scope, code)?;
    Ok(if resolved == code {
        value_type
    }
    else {
        arena.value_type_element(resolved, target)
    })
}

/// A computation type with the code of a decode read through solved
/// metavariables, as [`resolve_value_type`] reads a value type.
///
/// # Specification
/// trivial.
fn resolve_comp_type(
    arena: &mut CoreArena,
    metas: &Metas,
    scope: Binders,
    comp_type: CompTypeId,
) -> Result<CompTypeId, Stop>
{
    let Some(&CompType::Element { code, ref target }) = arena.comp_type(comp_type)
    else {
        return Ok(comp_type);
    };
    let target = target.clone();
    let resolved = resolve(arena, metas, scope, code)?;
    Ok(if resolved == code {
        comp_type
    }
    else {
        arena.comp_type_element(resolved, target)
    })
}

/// How a value type reads to the unifier.
///
/// # Specification
/// trivial.
const fn value_type_head(value_type: &ValueType) -> TypeHead<'_>
{
    match *value_type {
        ValueType::Element { code, ref target } => TypeHead::Code(code, target),
        ValueType::Unknown => TypeHead::Gradual,
        ValueType::Data { .. }
        | ValueType::Record(_)
        | ValueType::Base(_)
        | ValueType::Product(_)
        | ValueType::Sigma { .. }
        | ValueType::Sum(_)
        | ValueType::List(_)
        | ValueType::Thunk(_)
        | ValueType::Universe { .. }
        | ValueType::Lift { .. }
        | ValueType::Abstract(_)
        | ValueType::StaticPi { .. } => TypeHead::Rigid,
        ValueType::PathUniverse(..)
        | ValueType::Path { .. }
        | ValueType::Flow { .. }
        | ValueType::Run(_)
        | ValueType::Staged { .. }
        | ValueType::Stack { .. }
        | ValueType::Session(_)
        | ValueType::Capability { .. }
        | ValueType::Kept { .. }
        | ValueType::World(_) => TypeHead::Outside,
    }
}

/// How a computation type reads to the unifier.
///
/// # Specification
/// trivial.
const fn comp_type_head(comp_type: &CompType) -> TypeHead<'_>
{
    match *comp_type {
        CompType::Element { code, ref target } => TypeHead::Code(code, target),
        CompType::Unknown => TypeHead::Gradual,
        CompType::Returner { .. }
        | CompType::Arrow { .. }
        | CompType::Pi { .. }
        | CompType::With(_)
        | CompType::Codata { .. } => TypeHead::Rigid,
    }
}

/// What a decode facing a rigid type does: bind its code's metavariable to
/// the type's quote, or wait.
///
/// A flexible code gives the metavariable it stands for. Any other code's
/// decode is stuck — a decode of a quote is the quoted type by construction —
/// so the equation waits: as [`Reason::Neutral`] for a rigid code, by the
/// code's own obstruction otherwise.
///
/// # Specification
/// trivial.
fn decoded_against(
    arena: &CoreArena,
    metas: &Metas,
    code: ValueId,
) -> Result<MetaId, Stop>
{
    let Some(value) = arena.value(code)
    else {
        return Err(Stop::wait(Reason::Dangling));
    };
    let code_head = head(arena, metas, value);
    match code_head {
        Head::Flex(meta) => Ok(meta),
        Head::Rigid | Head::Gradual | Head::Unfold | Head::Spine(_) | Head::Outside => {
            Err(obstruction(code_head).unwrap_or(Stop::wait(Reason::Neutral)))
        },
    }
}

/// The unsolved metavariable a code stands for, if it is one.
///
/// # Specification
/// trivial.
fn flexible(
    arena: &CoreArena,
    metas: &Metas,
    code: ValueId,
) -> Option<MetaId>
{
    match arena.value(code).map(|value| head(arena, metas, value)) {
        Some(Head::Flex(meta)) => Some(meta),
        Some(Head::Gradual | Head::Unfold | Head::Spine(_) | Head::Outside | Head::Rigid)
        | None => None,
    }
}

/// Two decodes at different levels wait on the metavariables their codes are:
/// solved, both may decode to one type.
///
/// # Specification
/// trivial.
fn levels_differ(
    arena: &CoreArena,
    metas: &Metas,
    codes: [ValueId; 2],
) -> Stop
{
    let blockers = codes
        .into_iter()
        .filter_map(|code| flexible(arena, metas, code))
        .collect();
    Stop::Postpone(Reason::Levels, blockers)
}

/// Decide two value types.
///
/// Two decodes compare their codes at one level and wait at two; a decode of
/// an unsolved metavariable against a rigid type binds it to the type's
/// quote; two rigid types sharing a former push their children, a dependent
/// pair's second factor under one more binder; differing formers clash; a
/// gradual or undecomposed side waits.
///
/// # Specification
/// trivial.
fn value_types(
    arena: &mut CoreArena,
    metas: &Metas,
    scope: Binders,
    (one, other): (ValueTypeId, ValueTypeId),
    work: &mut Vec<Equation>,
) -> Result<Action, Stop>
{
    let one = resolve_value_type(arena, metas, scope, one)?;
    let other = resolve_value_type(arena, metas, scope, other)?;
    if one == other {
        return Ok(Action::Done);
    }
    let (left, right) = (Side::ValueType(one), Side::ValueType(other));
    let (Some(first), Some(second)) = (arena.value_type(one), arena.value_type(other))
    else {
        return Err(Stop::wait(Reason::Dangling));
    };
    match (value_type_head(first), value_type_head(second)) {
        (TypeHead::Code(a, at), TypeHead::Code(b, bt)) => {
            if at != bt {
                return Err(levels_differ(arena, metas, [a, b]));
            }
            work.push(Equation::new(scope, Side::Value(a), Side::Value(b)));
            Ok(Action::Done)
        },
        (TypeHead::Gradual, _) | (_, TypeHead::Gradual) => Err(Stop::wait(Reason::Gradual)),
        (TypeHead::Outside, _) | (_, TypeHead::Outside) => Err(Stop::wait(Reason::Outside)),
        (TypeHead::Code(code, _), TypeHead::Rigid) => {
            decoded_against(arena, metas, code).map(|meta| Action::Quote(meta, other))
        },
        (TypeHead::Rigid, TypeHead::Code(code, _)) => {
            decoded_against(arena, metas, code).map(|meta| Action::Quote(meta, one))
        },
        (TypeHead::Rigid, TypeHead::Rigid) => {
            rigid_value_types(scope, (first, second), (left, right), work)?;
            Ok(Action::Done)
        },
    }
}

/// Decompose two rigid value types sharing a former, or refute them.
///
/// The children are pushed; differing formers or payloads clash.
///
/// # Specification
/// trivial.
fn rigid_value_types(
    scope: Binders,
    (first, second): (&ValueType, &ValueType),
    (left, right): (Side, Side),
    work: &mut Vec<Equation>,
) -> Result<(), Stop>
{
    let clash = Stop::Refuted(Refutation::Clash { left, right });
    let pairs = |work: &mut Vec<Equation>, one: &[ValueTypeId], other: &[ValueTypeId]| {
        if one.len() != other.len() {
            return Err(Stop::Refuted(Refutation::Clash { left, right }));
        }
        for (&a, &b) in one.iter().zip(other.iter()).rev() {
            work.push(Equation::new(scope, Side::ValueType(a), Side::ValueType(b)));
        }
        Ok(())
    };
    match (first, second) {
        (
            &ValueType::Data {
                declaration: one_declaration,
                arguments: ref one,
            },
            &ValueType::Data {
                declaration: other_declaration,
                arguments: ref other,
            },
        ) => {
            if one_declaration != other_declaration || one.len() != other.len() {
                return Err(clash);
            }
            for (&a, &b) in one.iter().zip(other.iter()).rev() {
                work.push(Equation::new(scope, Side::Value(a), Side::Value(b)));
            }
        },
        (&ValueType::Record(ref one), &ValueType::Record(ref other)) => {
            if one.len() != other.len() || !one.keys().eq(other.keys()) {
                return Err(clash);
            }
            for (&a, &b) in one.values().zip(other.values()).rev() {
                work.push(Equation::new(scope, Side::ValueType(a), Side::ValueType(b)));
            }
        },
        (&ValueType::Base(ref one), &ValueType::Base(ref other)) => {
            if one != other {
                return Err(clash);
            }
        },
        (&ValueType::Product(ref one), &ValueType::Product(ref other))
        | (&ValueType::Sum(ref one), &ValueType::Sum(ref other)) => pairs(work, one, other)?,
        (
            &ValueType::Sigma {
                first: one_first,
                second: one_second,
            },
            &ValueType::Sigma {
                first: other_first,
                second: other_second,
            },
        ) => {
            work.push(Equation::new(
                scope.deeper(),
                Side::ValueType(one_second),
                Side::ValueType(other_second),
            ));
            work.push(Equation::new(
                scope,
                Side::ValueType(one_first),
                Side::ValueType(other_first),
            ));
        },
        (&ValueType::List(one), &ValueType::List(other)) => {
            work.push(Equation::new(
                scope,
                Side::ValueType(one),
                Side::ValueType(other),
            ));
        },
        (&ValueType::Thunk(one), &ValueType::Thunk(other)) => {
            work.push(Equation::new(
                scope,
                Side::CompType(one),
                Side::CompType(other),
            ));
        },
        (
            &ValueType::Universe {
                sort: ref one_sort,
                level: ref one_level,
            },
            &ValueType::Universe {
                sort: ref other_sort,
                level: ref other_level,
            },
        ) => {
            if one_sort != other_sort || one_level != other_level {
                return Err(clash);
            }
        },
        (
            &ValueType::Lift {
                inner: one,
                target: ref one_target,
            },
            &ValueType::Lift {
                inner: other,
                target: ref other_target,
            },
        ) => {
            if one_target != other_target {
                return Err(clash);
            }
            work.push(Equation::new(
                scope,
                Side::ValueType(one),
                Side::ValueType(other),
            ));
        },
        (&ValueType::Abstract(one), &ValueType::Abstract(other)) => {
            if one != other {
                return Err(clash);
            }
        },
        (
            &ValueType::StaticPi {
                domain: one_domain,
                codomain: one_codomain,
            },
            &ValueType::StaticPi {
                domain: other_domain,
                codomain: other_codomain,
            },
        ) => {
            work.push(Equation::new(
                scope,
                Side::ValueType(one_codomain),
                Side::ValueType(other_codomain),
            ));
            work.push(Equation::new(
                scope,
                Side::ValueType(one_domain),
                Side::ValueType(other_domain),
            ));
        },
        _ => return Err(clash),
    }
    Ok(())
}

/// Decide two computation types, as [`value_types`] decides value types: a
/// dependent function's codomain under one more binder, a function against a
/// dependent function waiting, since conversion may relate a dependent one
/// whose codomain ignores its binder to a plain one.
///
/// # Specification
/// trivial.
fn comp_types(
    arena: &mut CoreArena,
    metas: &Metas,
    scope: Binders,
    (one, other): (CompTypeId, CompTypeId),
    work: &mut Vec<Equation>,
) -> Result<Action, Stop>
{
    let one = resolve_comp_type(arena, metas, scope, one)?;
    let other = resolve_comp_type(arena, metas, scope, other)?;
    if one == other {
        return Ok(Action::Done);
    }
    let (left, right) = (Side::CompType(one), Side::CompType(other));
    let (Some(first), Some(second)) = (arena.comp_type(one), arena.comp_type(other))
    else {
        return Err(Stop::wait(Reason::Dangling));
    };
    match (comp_type_head(first), comp_type_head(second)) {
        (TypeHead::Code(a, at), TypeHead::Code(b, bt)) => {
            if at != bt {
                return Err(levels_differ(arena, metas, [a, b]));
            }
            work.push(Equation::new(scope, Side::Value(a), Side::Value(b)));
            Ok(Action::Done)
        },
        (TypeHead::Gradual, _) | (_, TypeHead::Gradual) => Err(Stop::wait(Reason::Gradual)),
        (TypeHead::Outside, _) | (_, TypeHead::Outside) => Err(Stop::wait(Reason::Outside)),
        (TypeHead::Code(code, _), TypeHead::Rigid) => {
            decoded_against(arena, metas, code).map(|meta| Action::QuoteComputation(meta, other))
        },
        (TypeHead::Rigid, TypeHead::Code(code, _)) => {
            decoded_against(arena, metas, code).map(|meta| Action::QuoteComputation(meta, one))
        },
        (TypeHead::Rigid, TypeHead::Rigid) => {
            rigid_comp_types(scope, (first, second), (left, right), work)?;
            Ok(Action::Done)
        },
    }
}

/// Decompose two rigid computation types sharing a former, or refute them.
///
/// The children are pushed, a dependent function's codomain under one more
/// binder; a function against a dependent function waits as
/// [`Reason::Outside`]; differing formers or payloads clash.
///
/// # Specification
/// trivial.
fn rigid_comp_types(
    scope: Binders,
    (first, second): (&CompType, &CompType),
    (left, right): (Side, Side),
    work: &mut Vec<Equation>,
) -> Result<(), Stop>
{
    let clash = Stop::Refuted(Refutation::Clash { left, right });
    match (first, second) {
        (
            &CompType::Returner {
                result: one,
                effects: ref one_effects,
            },
            &CompType::Returner {
                result: other,
                effects: ref other_effects,
            },
        ) => {
            if one_effects != other_effects {
                return Err(clash);
            }
            work.push(Equation::new(
                scope,
                Side::ValueType(one),
                Side::ValueType(other),
            ));
        },
        (
            &CompType::Arrow {
                domain: one_domain,
                codomain: one_codomain,
            },
            &CompType::Arrow {
                domain: other_domain,
                codomain: other_codomain,
            },
        ) => {
            work.push(Equation::new(
                scope,
                Side::CompType(one_codomain),
                Side::CompType(other_codomain),
            ));
            work.push(Equation::new(
                scope,
                Side::ValueType(one_domain),
                Side::ValueType(other_domain),
            ));
        },
        (
            &CompType::Pi {
                domain: one_domain,
                codomain: one_codomain,
            },
            &CompType::Pi {
                domain: other_domain,
                codomain: other_codomain,
            },
        ) => {
            work.push(Equation::new(
                scope.deeper(),
                Side::CompType(one_codomain),
                Side::CompType(other_codomain),
            ));
            work.push(Equation::new(
                scope,
                Side::ValueType(one_domain),
                Side::ValueType(other_domain),
            ));
        },
        (&CompType::Arrow { .. }, &CompType::Pi { .. })
        | (&CompType::Pi { .. }, &CompType::Arrow { .. }) => {
            return Err(Stop::wait(Reason::Outside));
        },
        (&CompType::With(ref one), &CompType::With(ref other)) => {
            if one.len() != other.len() {
                return Err(clash);
            }
            for (&a, &b) in one.iter().zip(other.iter()).rev() {
                work.push(Equation::new(scope, Side::CompType(a), Side::CompType(b)));
            }
        },
        (
            &CompType::Codata {
                declaration: one_declaration,
                arguments: ref one,
            },
            &CompType::Codata {
                declaration: other_declaration,
                arguments: ref other,
            },
        ) => {
            if one_declaration != other_declaration || one.len() != other.len() {
                return Err(clash);
            }
            for (&a, &b) in one.iter().zip(other.iter()).rev() {
                work.push(Equation::new(scope, Side::Value(a), Side::Value(b)));
            }
        },
        _ => return Err(clash),
    }
    Ok(())
}

/// Whether `meta`'s hole stands in `term`, read through every solution of a
/// metavariable that stands there, and whether it stands strongly rigidly.
///
/// [`Occurrence::Absent`] exactly when the hole stands neither in `term` nor,
/// transitively, in the solution of a solved metavariable standing in it;
/// [`Occurrence::Strong`] when one occurrence is reached from `term`'s root
/// through introduction forms and solutions only.
///
/// # Specification
/// trivial.
///
/// # Termination
/// - reason: each solved metavariable is scanned at most once, which the `seen`
///   marks enforce; the `while` loop pops one pending value per pass.
fn occurs(
    arena: &mut CoreArena,
    metas: &Metas,
    meta: MetaId,
    term: ValueId,
) -> Occurrence
{
    let Maybe::Present(hole) = metas.hole(meta)
    else {
        return Occurrence::Absent;
    };
    let mut seen = alloc::vec![false; usize::from(metas.count())];
    let mut pending = Vec::from([term]);
    while let Some(scanned) = pending.pop() {
        if stands_in(arena, hole, scanned) == Occurrence::Stands {
            return strongly(arena, metas, hole, term);
        }
        for other in metas.ids() {
            let (Maybe::Present(solution), Maybe::Present(other_hole)) =
                (metas.solution(other), metas.hole(other))
            else {
                continue;
            };
            let Some(mark) = seen.get_mut(usize::from(other))
            else {
                continue;
            };
            if *mark || stands_in(arena, other_hole, scanned) == Occurrence::Absent {
                continue;
            }
            *mark = true;
            pending.push(solution);
        }
    }
    Occurrence::Absent
}

/// Whether `hole` is reached from `term`'s root through introduction forms
/// and the solutions of solved metavariables only — a cycle no instantiation
/// removes, [`Occurrence::Strong`] — or not, [`Occurrence::Stands`].
///
/// # Specification
/// trivial.
///
/// # Termination
/// - reason: each node is visited at most once, which the `visited` set
///   enforces, and the arena holds finitely many; the `while` loop pops one
///   pending node per pass.
fn strongly(
    arena: &CoreArena,
    metas: &Metas,
    hole: gandr_core_term::hole::HoleId,
    term: ValueId,
) -> Occurrence
{
    let mut visited = BTreeSet::new();
    let mut pending = Vec::from([term]);
    while let Some(at) = pending.pop() {
        if !visited.insert(at) {
            continue;
        }
        match arena.value(at) {
            Some(&Value::Hole(found)) => {
                if found == hole {
                    return Occurrence::Strong;
                }
                if let Maybe::Present(other) = metas.meta(found)
                    && let Maybe::Present(solution) = metas.solution(other)
                {
                    pending.push(solution);
                }
            },
            Some(&Value::Tuple(ref items)) => pending.extend(items.iter().copied()),
            Some(&Value::Constructor { ref fields, .. }) => pending.extend(fields.iter().copied()),
            Some(&Value::Record(ref fields)) => pending.extend(fields.values().copied()),
            Some(&Value::Injection(_, inner) | &Value::StaticLambda(inner)) => pending.push(inner),
            Some(&Value::ListCons(first, rest)) => pending.extend([first, rest]),
            Some(_) | None => {},
        }
    }
    Occurrence::Stands
}

/// The unsolved metavariables whose holes stand in `term`.
///
/// # Specification
/// trivial.
fn standing(
    arena: &mut CoreArena,
    metas: &Metas,
    term: ValueId,
) -> Vec<MetaId>
{
    let mut found = Vec::new();
    for other in metas.ids() {
        if let (Maybe::Present(other_hole), Maybe::Absent(_)) =
            (metas.hole(other), metas.solution(other))
            && stands_in(arena, other_hole, term) == Occurrence::Stands
        {
            found.push(other);
        }
    }
    found
}

/// Whether `hole` stands in `term`: filling it leaves `term` unchanged
/// exactly when it does not.
///
/// # Specification
/// trivial.
fn stands_in(
    arena: &mut CoreArena,
    hole: gandr_core_term::hole::HoleId,
    term: ValueId,
) -> Occurrence
{
    let subject = TermId::Value(term);
    if fill_hole(arena, subject, hole, subject) == subject {
        Occurrence::Absent
    }
    else {
        Occurrence::Stands
    }
}

/// Bind `meta` to `term`, written under `scope` binders, once the occurs
/// check, the context check and the support allow it.
///
/// On success `meta` is bound to `term` lowered into its context. A `term`
/// holding `meta` strongly rigidly is refuted; one holding it elsewhere, one
/// holding a metavariable of a wider context or a linear variable, and one
/// whose carried support names a binder the context lacks wait in the store.
///
/// # Specification
/// trivial.
fn bind(
    arena: &mut CoreArena,
    metas: &mut Metas,
    scope: Binders,
    meta: MetaId,
    term: ValueId,
) -> Result<(), Stop>
{
    let waits = |reason| Stop::Postpone(reason, Vec::from([meta]));
    let Maybe::Present(declared) = metas.scope(meta)
    else {
        return Err(Stop::wait(Reason::Scope { meta }));
    };
    let past = u32::from(scope)
        .checked_sub(u32::from(declared))
        .ok_or_else(|| waits(Reason::Scope { meta }))?;
    match occurs(arena, metas, meta, term) {
        Occurrence::Strong => return Err(Stop::Refuted(Refutation::Occurs { meta, within: term })),
        Occurrence::Stands => {
            return Err(Stop::Postpone(
                Reason::Occurs { meta },
                standing(arena, metas, term),
            ));
        },
        Occurrence::Absent => {},
    }
    for other in metas.ids() {
        let (Maybe::Present(other_hole), Maybe::Present(other_scope)) =
            (metas.hole(other), metas.scope(other))
        else {
            continue;
        };
        if other != meta
            && other_scope > declared
            && stands_in(arena, other_hole, term) == Occurrence::Stands
        {
            return Err(Stop::Postpone(
                Reason::Pruning { meta, other },
                Vec::from([meta, other]),
            ));
        }
    }
    let (linear, escapes) = match arena.value_support(term) {
        Some(support) => (
            support.indices(Zone::Linear).next().is_some(),
            support
                .indices(Zone::Intuitionistic)
                .next()
                .is_some_and(|innermost| u32::from(innermost) < past),
        ),
        None => return Err(Stop::wait(Reason::Dangling)),
    };
    if linear {
        return Err(waits(Reason::Linear));
    }
    if escapes {
        return Err(waits(Reason::Escape { meta }));
    }
    let solution = match strengthen_value(arena, term, Binders::from(past)) {
        Maybe::Present(lowered) => lowered.settle(arena),
        Maybe::Absent(_) => return Err(waits(Reason::Escape { meta })),
    };
    metas.bind(meta, solution);
    Ok(())
}
