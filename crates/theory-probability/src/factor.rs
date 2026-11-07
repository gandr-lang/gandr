//! A factor graph: variables with finite domains, and factors whose exact
//! weights lie over their scopes.

use alloc::vec::Vec;

use anodized::spec;

use crate::error::InferenceError;
use crate::table::Arity;
use crate::table::Scope;
use crate::table::Table;
use crate::table::Variable;

/// Variables numbered from zero, each with its arity, and factors over them.
///
/// # Specification
/// - ensures: each variable of each factor is a variable of the graph, with the
///   graph's arity for it.
/// - provides: the arities, the factors and the scope of every variable.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`FactorGraph::new`]'s.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FactorGraph<E>
{
    /// The arity of each variable, by its number.
    arities: Vec<Arity>,
    /// The factors.
    factors: Vec<Table<E>>,
}

impl<E> FactorGraph<E>
{
    /// The graph of the variables whose arities `arities` lists by number,
    /// with `factors`.
    ///
    /// # Specification
    /// - ensures: the graph holds the factors in their order.
    /// - fails: a factor over a variable past the list, or with another arity
    ///   for it, is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Unknown`]: a factor names a variable past the list.
    /// - [`InferenceError::Mismatched`]: a factor gives a variable another
    ///   arity.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a factor over a fifth variable of four, and one with
    ///   a third value for a binary variable, are each refused.
    /// - witness: `tests::inference::a_scope_orders_its_variables_and_refuses_a_repeat`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |graph| graph.factors.iter().all(|factor| factor.scope().variables().all(|(variable, arity)| graph.arity(variable) == Some(arity)))))]
    #[inline]
    pub fn new(
        arities: Vec<Arity>,
        factors: Vec<Table<E>>,
    ) -> Result<Self, InferenceError>
    {
        for factor in &factors {
            for (variable, arity) in factor.scope().variables() {
                let listed = usize::try_from(u32::from(variable))
                    .ok()
                    .and_then(|place| arities.get(place))
                    .ok_or(InferenceError::Unknown(variable))?;
                if *listed != arity {
                    return Err(InferenceError::Mismatched(variable));
                }
            }
        }
        Ok(Self { arities, factors })
    }

    /// The arity of each variable, by its number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arities(&self) -> &[Arity]
    {
        &self.arities
    }

    /// The factors.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn factors(&self) -> &[Table<E>]
    {
        &self.factors
    }

    /// The arity of `variable`, when the graph holds it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn arity(
        &self,
        variable: Variable,
    ) -> Option<Arity>
    {
        usize::try_from(u32::from(variable))
            .ok()
            .and_then(|place| self.arities.get(place))
            .copied()
    }

    /// The scope of every variable of the graph.
    ///
    /// # Specification
    /// - ensures: each variable with its arity.
    /// - fails: an arity of zero, and a width past the machine's integers, are
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::NoValue`]: an arity is zero.
    /// - [`InferenceError::TooLarge`]: the product of the arities passes the
    ///   machine's integers.
    /// - [`InferenceError::Unknown`]: the graph holds more variables than their
    ///   numbers count.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the joint of the network over the scope of its four
    ///   variables is the reference that each marginal meets.
    /// - witness: `tests::inference::sum_product_gives_the_marginals_of_the_network`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |scope| scope.variables().count() == self.arities.len()))]
    #[inline]
    pub fn scope(&self) -> Result<Scope, InferenceError>
    {
        let variables = self
            .arities
            .iter()
            .enumerate()
            .map(|(place, &arity)| {
                u32::try_from(place)
                    .map(|number| (Variable::from(number), arity))
                    .map_err(|_past| InferenceError::TooLarge)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Scope::new(variables)
    }
}
