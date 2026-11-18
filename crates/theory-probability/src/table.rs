//! Variables with finite domains, the scopes they make, and the tables of
//! weights over a scope.
//!
//! A table over a scope holds one weight for each assignment of values to its
//! variables. The variables of a scope are in ascending order, and the entry
//! of an assignment counts its values with the last variable fastest, as the
//! digits of a number with mixed radices.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroUsize;

use anodized::spec;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_ordered_algebras::OrderedSemiring;

use crate::error::InferenceError;

/// A variable of a factor graph, numbered from zero.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Variable(u32);

impl From<u32> for Variable
{
    /// The variable with this number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(number: u32) -> Self
    {
        Self(number)
    }
}

impl From<Variable> for u32
{
    /// The number of the variable.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(variable: Variable) -> Self
    {
        variable.0
    }
}

impl fmt::Display for Variable
{
    /// Renders the variable as its number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// The number of values that a variable takes.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Arity(u32);

impl From<u32> for Arity
{
    /// The arity with this number of values.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<Arity> for u32
{
    /// The number of values.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arity: Arity) -> Self
    {
        arity.0
    }
}

/// A value of a variable, numbered from zero below its arity.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Value(u32);

impl From<u32> for Value
{
    /// The value with this number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(number: u32) -> Self
    {
        Self(number)
    }
}

impl From<Value> for u32
{
    /// The number of the value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Value) -> Self
    {
        value.0
    }
}

/// One variable of a scope: its arity, and the distance between two entries
/// that differ in its value alone.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Slot
{
    /// The variable.
    variable: Variable,
    /// Its arity as given.
    arity: Arity,
    /// Its arity, at least one.
    values: NonZeroUsize,
    /// The product of the arities of the variables after it.
    stride: NonZeroUsize,
}

/// Whether one scope lies within another.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Inclusion
{
    /// Each variable of the first is a variable of the second, with the same
    /// arity.
    Within,
    /// Some variable of the first is not a variable of the second.
    Beyond,
}

/// A set of variables, each with its arity, in ascending order.
///
/// # Specification
/// - ensures: the variables ascend with no repeat, each arity is at least one,
///   and the width is the product of the arities.
/// - provides: the width, the variables and the value of a variable at an
///   entry.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is [`Scope::new`]'s.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Scope
{
    /// The variables in ascending order.
    slots: Vec<Slot>,
    /// The number of entries of a table over the scope.
    width: NonZeroUsize,
}

impl Scope
{
    /// The scope of `variables`, each with its arity, in any order.
    ///
    /// # Specification
    /// - ensures: the variables in ascending order, with the product of their
    ///   arities as the width.
    /// - fails: a variable named twice, an arity of zero, and a width past the
    ///   machine's integers are each refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Repeated`]: a variable is named twice.
    /// - [`InferenceError::NoValue`]: an arity is zero.
    /// - [`InferenceError::TooLarge`]: the product of the arities passes the
    ///   machine's integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — scopes given out of order, with a repeat and with an
    ///   arity of zero, against each refusal and the width.
    /// - witness: `tests::inference::a_scope_orders_its_variables_and_refuses_a_repeat`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |scope| scope.slots.windows(2).all(|pair| pair.first().map(|slot| slot.variable) < pair.get(1).map(|slot| slot.variable))))]
    #[inline]
    pub fn new(mut variables: Vec<(Variable, Arity)>) -> Result<Self, InferenceError>
    {
        variables.sort_unstable_by_key(|&(variable, _)| variable);
        if let Some(&[(repeated, _), _]) = variables
            .windows(2)
            .find(|pair| matches!(*pair, [(first, _), (second, _)] if first == second))
        {
            return Err(InferenceError::Repeated(repeated));
        }
        let mut width = NonZeroUsize::MIN;
        let mut slots = Vec::with_capacity(variables.len());
        for &(variable, arity) in variables.iter().rev() {
            let values = usize::try_from(arity.0)
                .ok()
                .and_then(NonZeroUsize::new)
                .ok_or(InferenceError::NoValue(variable))?;
            slots.push(Slot {
                variable,
                arity,
                values,
                stride: width,
            });
            width = width.checked_mul(values).ok_or(InferenceError::TooLarge)?;
        }
        slots.reverse();
        Ok(Self { slots, width })
    }

    /// The number of entries of a table over the scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn width(&self) -> Width
    {
        Width::from(self.width.get())
    }

    /// The variables, in ascending order, each with its arity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn variables(&self) -> impl Iterator<Item = (Variable, Arity)> + '_
    {
        self.slots.iter().map(|slot| (slot.variable, slot.arity))
    }

    /// The value of `variable` at `entry`, or nothing when the scope does not
    /// hold the variable or the entry lies past the width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value(
        &self,
        entry: Entry,
        variable: Variable,
    ) -> Option<Value>
    {
        let raw = usize::from(entry);
        if raw >= self.width.get() {
            return None;
        }
        let slot = self.slot(variable)?;
        let value = raw
            .div_euclid(slot.stride.get())
            .rem_euclid(slot.values.get());
        u32::try_from(value).ok().map(Value)
    }

    /// The slot of `variable`, by binary search.
    ///
    /// # Specification
    /// trivial.
    fn slot(
        &self,
        variable: Variable,
    ) -> Option<&Slot>
    {
        let place = self
            .slots
            .binary_search_by_key(&variable, |slot| slot.variable)
            .ok()?;
        self.slots.get(place)
    }

    /// Whether the scope lies within `other`, by one walk of the two orders.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn inclusion(
        &self,
        other: &Self,
    ) -> Inclusion
    {
        let mut theirs = other.slots.iter();
        let within = self.slots.iter().all(|slot| {
            theirs
                .by_ref()
                .find(|candidate| candidate.variable >= slot.variable)
                .is_some_and(|candidate| {
                    candidate.variable == slot.variable && candidate.arity == slot.arity
                })
        });
        if within {
            Inclusion::Within
        }
        else {
            Inclusion::Beyond
        }
    }

    /// The variables of both scopes.
    ///
    /// # Specification
    /// - ensures: each variable that both scopes hold, with its arity, so the
    ///   meet holds no more variables than either scope.
    /// - fails: a variable whose two arities differ is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Mismatched`]: the two scopes give a variable two
    ///   arities.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the overlaps of the cliques of the network and of the
    ///   contextual family are each the shared variables.
    /// - witness: `tests::inference::the_clique_marginals_glue_and_a_changed_weight_is_obstructed`
    #[spec(ensures: |ref ret| ret.as_ref().ok().is_none_or(|meet| meet.slots.len() <= self.slots.len() && meet.slots.len() <= other.slots.len()))]
    pub(crate) fn meet(
        &self,
        other: &Self,
    ) -> Result<Self, InferenceError>
    {
        let shared = self
            .slots
            .iter()
            .filter_map(|slot| {
                other.slot(slot.variable).map(|theirs| {
                    if theirs.arity == slot.arity {
                        Ok((slot.variable, slot.arity))
                    }
                    else {
                        Err(InferenceError::Mismatched(slot.variable))
                    }
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(shared)
    }

    /// The variables of every scope of `scopes`.
    ///
    /// # Specification
    /// - ensures: each variable that some scope holds, with its arity.
    /// - fails: a variable with two arities, and a width past the machine's
    ///   integers, are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Mismatched`]: two scopes give a variable two
    ///   arities.
    /// - [`InferenceError::TooLarge`]: the product of the arities passes the
    ///   machine's integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the contextual family's three scopes join to its
    ///   three variables, whose eight assignments the check reads.
    /// - witness: `tests::inference::a_contextual_family_glues_and_is_refused_a_joint`
    #[spec(captures: [listed = scopes.clone().collect::<Vec<_>>()], ensures: |ref ret| ret.as_ref().map_or(true, |join| listed.iter().all(|scope| scope.inclusion(join) == Inclusion::Within)))]
    pub(crate) fn join<'scopes>(
        scopes: impl Iterator<Item = &'scopes Self> + Clone
    ) -> Result<Self, InferenceError>
    {
        let mut variables: Vec<(Variable, Arity)> = scopes.flat_map(Self::variables).collect();
        variables.sort_unstable();
        variables.dedup();
        if let Some(&[(mismatched, _), _]) = variables
            .windows(2)
            .find(|pair| matches!(*pair, [(first, _), (second, _)] if first == second))
        {
            return Err(InferenceError::Mismatched(mismatched));
        }
        Self::new(variables)
    }

    /// The arity of `variable`, when the scope holds it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn holds(
        &self,
        variable: Variable,
    ) -> Option<Arity>
    {
        self.slot(variable).map(|slot| slot.arity)
    }

    /// The number of variables that both scopes hold.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn shared(
        &self,
        other: &Self,
    ) -> Width
    {
        Width::from(
            self.slots
                .iter()
                .filter(|slot| other.slot(slot.variable).is_some())
                .count(),
        )
    }

    /// The entry of `onto` that `entry` of the scope restricts to, by a
    /// binary search for each variable of `onto`, with no allocation:
    /// nothing when `onto` holds a variable that the scope does not.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn restrict(
        &self,
        entry: Entry,
        onto: &Self,
    ) -> Option<Entry>
    {
        let raw = usize::from(entry);
        onto.slots
            .iter()
            .try_fold(0_usize, |sum, target| {
                let slot = self.slot(target.variable)?;
                (raw.div_euclid(slot.stride.get())
                    .rem_euclid(slot.values.get()))
                .checked_mul(target.stride.get())?
                .checked_add(sum)
            })
            .map(Entry::from)
    }

    /// How the entries of the scope read as entries of `onto`, which lies
    /// within it: nothing when it does not.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn projection(
        &self,
        onto: &Self,
    ) -> Option<Projection>
    {
        if onto.inclusion(self) == Inclusion::Beyond {
            return None;
        }
        let steps = self
            .slots
            .iter()
            .map(|slot| Step {
                stride: slot.stride,
                values: slot.values,
                onto: onto
                    .slot(slot.variable)
                    .map_or(0, |theirs| theirs.stride.get()),
            })
            .collect();
        Some(Projection { steps })
    }
}

/// One variable of a projection: where its value sits in an entry of each
/// scope.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Step
{
    /// The variable's stride in the larger scope.
    stride: NonZeroUsize,
    /// The variable's arity.
    values: NonZeroUsize,
    /// The variable's stride in the smaller scope, or zero when that scope
    /// does not hold it.
    onto: usize,
}

/// How each entry of a scope reads as an entry of a scope within it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Projection
{
    /// One step for each variable of the larger scope.
    steps: Vec<Step>,
}

impl Projection
{
    /// The entry of the smaller scope that `entry` of the larger restricts
    /// to: the entry whose values are the values of `entry` at the variables
    /// of the smaller scope.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn entry(
        &self,
        entry: Entry,
    ) -> Option<Entry>
    {
        let raw = usize::from(entry);
        self.steps
            .iter()
            .try_fold(0_usize, |sum, step| {
                (raw.div_euclid(step.stride.get())
                    .rem_euclid(step.values.get()))
                .checked_mul(step.onto)?
                .checked_add(sum)
            })
            .map(Entry::from)
    }
}

/// The weights over a scope, one for each entry.
///
/// # Specification
/// - ensures: one weight for each entry of the scope.
/// - provides: the scope and the weights.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is [`Table::new`]'s.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Table<E>
{
    /// The variables of the table.
    scope: Scope,
    /// One weight for each entry of the scope.
    weights: Vec<E>,
}

impl<E> Table<E>
{
    /// The table over `scope` with `weights`, the entry of each the count of
    /// its values with the last variable fastest.
    ///
    /// # Specification
    /// - ensures: the table holds the weights in their order.
    /// - fails: a number of weights that is not the scope's width is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Width`]: the number of weights is not the width.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a table with one weight short is refused with both
    ///   counts.
    /// - witness: `tests::inference::a_scope_orders_its_variables_and_refuses_a_repeat`
    #[spec(captures: [fits = scope.width.get() == weights.len()], ensures: |ref ret| ret.is_ok() == fits)]
    #[inline]
    pub fn new(
        scope: Scope,
        weights: Vec<E>,
    ) -> Result<Self, InferenceError>
    {
        if weights.len() != scope.width.get() {
            return Err(InferenceError::Width {
                expected: Width::from(scope.width.get()),
                given: Width::from(weights.len()),
            });
        }
        Ok(Self { scope, weights })
    }

    /// The variables of the table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scope(&self) -> &Scope
    {
        &self.scope
    }

    /// The weights, one for each entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn weights(&self) -> &[E]
    {
        &self.weights
    }
}

impl<E: Clone> Table<E>
{
    /// The table over `scope` with `weight` at each entry.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn filled(
        scope: Scope,
        weight: &E,
    ) -> Self
    {
        let weights = vec![weight.clone(); scope.width.get()];
        Self { scope, weights }
    }

    /// The sum of the weights over each entry of `onto`, which lies within
    /// the scope, written into `into`.
    ///
    /// # Specification
    /// - ensures: `into` holds, at each entry of `onto`, the semiring sum of
    ///   the weights whose entries restrict to it.
    /// - fails: a scope not within the table's, and a sum past the carrier, are
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Uncovered`]: `onto` does not lie within the scope.
    /// - [`InferenceError::Overflow`]: a sum passes the carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each marginal of the network against the sum over its
    ///   worlds.
    /// - witness: `tests::inference::sum_product_gives_the_marginals_of_the_network`
    #[spec(ensures: |ref ret| ret.is_err() || into.len() == onto.width.get())]
    pub(crate) fn marginal_into<S>(
        &self,
        semiring: &S,
        onto: &Scope,
        into: &mut Vec<E>,
    ) -> Result<(), InferenceError>
    where
        S: OrderedSemiring<Element = E>,
    {
        let projection = self
            .scope
            .projection(onto)
            .ok_or(InferenceError::Uncovered)?;
        into.clear();
        into.resize(onto.width.get(), semiring.zero());
        for (entry, weight) in self.weights.iter().enumerate() {
            let target = projection
                .entry(Entry::from(entry))
                .ok_or(InferenceError::TooLarge)?;
            let slot = into
                .get_mut(usize::from(target))
                .ok_or(InferenceError::TooLarge)?;
            *slot = semiring
                .add(slot, weight)
                .map_err(|_outside| InferenceError::Overflow)?;
        }
        Ok(())
    }

    /// The table of the sums over each entry of `onto`.
    ///
    /// # Specification
    /// - ensures: the marginal of the table on `onto`.
    /// - fails: as [`Table::marginal_into`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Uncovered`]: `onto` does not lie within the scope.
    /// - [`InferenceError::Overflow`]: a sum passes the carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each marginal of the network against the sum over its
    ///   worlds.
    /// - witness: `tests::inference::sum_product_gives_the_marginals_of_the_network`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |table| table.scope == *onto))]
    pub(crate) fn marginal<S>(
        &self,
        semiring: &S,
        onto: &Scope,
    ) -> Result<Self, InferenceError>
    where
        S: OrderedSemiring<Element = E>,
    {
        let mut weights = Vec::new();
        self.marginal_into(semiring, onto, &mut weights)?;
        Ok(Self {
            scope: onto.clone(),
            weights,
        })
    }

    /// The weight at `entry`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn at(
        &self,
        entry: Entry,
    ) -> Option<&E>
    {
        self.weights.get(usize::from(entry))
    }

    /// The weights, to be changed in place.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn weights_mut(&mut self) -> &mut [E]
    {
        &mut self.weights
    }

    /// Multiply each weight by the weight of `factor` at the entry it
    /// restricts to: the factor's scope lies within the table's.
    ///
    /// # Specification
    /// - ensures: each weight is the semiring product of the old weight and the
    ///   factor's weight at its restriction.
    /// - fails: a factor over a variable the table does not hold, and a product
    ///   past the carrier, are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Uncovered`]: the factor holds a variable the table
    ///   does not.
    /// - [`InferenceError::Overflow`]: a product passes the carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the potentials of the network's cliques are the
    ///   products of its factors, which each marginal reads.
    /// - witness: `tests::inference::sum_product_gives_the_marginals_of_the_network`
    #[spec(ensures: |ref ret| ret.is_err() || self.weights.len() == self.scope.width.get())]
    pub(crate) fn multiply_by<S>(
        &mut self,
        semiring: &S,
        factor: &Self,
    ) -> Result<(), InferenceError>
    where
        S: OrderedSemiring<Element = E>,
    {
        for (entry, weight) in self.weights.iter_mut().enumerate() {
            let at = self
                .scope
                .restrict(Entry::from(entry), &factor.scope)
                .ok_or(InferenceError::Uncovered)?;
            let by = factor.at(at).ok_or(InferenceError::Uncovered)?;
            *weight = semiring
                .multiply(weight, by)
                .map_err(|_outside| InferenceError::Overflow)?;
        }
        Ok(())
    }
}
