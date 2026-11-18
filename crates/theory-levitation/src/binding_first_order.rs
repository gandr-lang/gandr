//! Typed identification between binding trees and canonical SSC q/p terms.
//!
//! Context parameters are implicit, as in generated equation notation. These
//! maps cover normal representatives, not arbitrary explicit substitutions.

use alloc::format;
use alloc::vec::Vec;

use anodized::spec;

use crate::binding::BindingError;
use crate::binding::BindingHead;
use crate::binding::BindingJudgement;
use crate::binding::BindingTerm;
use crate::binding::SimplySorted;
use crate::binding::same_sort;
use crate::boundary::VariableIndex;
use crate::code::Name;
use crate::rule::FreeTerm;
use crate::rule::TermNode;
use crate::rule::TermView;
use crate::tree::TreeRef;

/// A first-order normal representative with the context erased syntax needs.
///
/// # Specification
/// - provides: canonical structural equality including ambient context and
///   result sort, with q/p variables and source operations in argument order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FirstOrderJudgement
{
    /// Ambient representable sorts, oldest first.
    pub context: Vec<Name>,
    /// The term's sort.
    pub sort: Name,
    /// Canonical q/p syntax, with implicit context parameters.
    pub term: FreeTerm,
}

impl<G> SimplySorted<'_, G>
{
    /// Identify a typed binding term with its generated first-order normal
    /// form.
    ///
    /// # Specification
    /// - ensures: each variable becomes `$q` of its sort followed by one `$p`
    ///   weakening per newer context entry, each named by the sort it crosses;
    ///   operations keep their arguments in order, each under its own binder
    ///   telescope. Context and sort are kept.
    /// - fails: invalid input judgements are refused before translation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the exact `BindingError` from [`Self::check`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independently written mixed-sort q/p normal forms on
    ///   three signatures and both composites over generated judgements
    ///   distinguish reversed variables, a weakening named by the wrong sort, a
    ///   lost binder telescope and reordered arguments.
    /// - witness: `tests::glf::model::identification`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |first_order|
        first_order.context == judgement.context && first_order.sort == judgement.sort))]
    pub fn to_first_order(
        &self,
        judgement: &BindingJudgement,
    ) -> Result<FirstOrderJudgement, BindingError>
    {
        self.check(judgement)?;
        let mut scope = judgement.context.clone();
        let mut work = alloc::vec![Encode::Term(judgement.term.0.to_ref())];
        let mut terms = Vec::new();
        while let Some(step) = work.pop() {
            match step {
                Encode::Restore(length) => scope.truncate(length),
                Encode::Argument(node, port) => {
                    work.push(Encode::Restore(scope.len()));
                    scope.extend(port.bindings.iter().map(|binder| binder.sort.clone()));
                    work.push(Encode::Term(node));
                },
                Encode::Term(node) => match *node.head() {
                    BindingHead::Variable(index) => {
                        let position = scope
                            .len()
                            .checked_sub(usize::from(index))
                            .and_then(|length| length.checked_sub(1))
                            .ok_or(BindingError::UnboundVariable(index))?;
                        let sort = scope.get(position).ok_or(BindingError::InvalidState)?;
                        let mut term = FreeTerm::op(format!("$q_{sort}"), []);
                        for crossed in scope.iter().skip(position.saturating_add(1)) {
                            term = FreeTerm::op(format!("$sub_{sort}"), [
                                term,
                                FreeTerm::op(format!("$p_{crossed}"), []),
                            ]);
                        }
                        terms.push(term);
                    },
                    BindingHead::Operation(ref name, count) => {
                        let operation = self.operation(name)?;
                        work.push(Encode::Close(name, usize::from(count)));
                        work.extend(
                            node.children()
                                .zip(&operation.arity.inputs)
                                .map(|(child, port)| Encode::Argument(child, port)),
                        );
                    },
                },
                Encode::Close(name, count) => {
                    let start = terms
                        .len()
                        .checked_sub(count)
                        .ok_or(BindingError::InvalidState)?;
                    let arguments: Vec<FreeTerm> = terms.drain(start ..).rev().collect();
                    terms.push(FreeTerm::op(name.clone(), arguments));
                },
            }
        }
        let term = terms.pop().ok_or(BindingError::InvalidState)?;
        Ok(FirstOrderJudgement {
            context: judgement.context.clone(),
            sort: judgement.sort.clone(),
            term,
        })
    }

    /// Recover a binding judgement from a canonical generated q/p
    /// representative.
    ///
    /// # Specification
    /// - ensures: inverse to [`Self::to_first_order`] on typed canonical
    ///   representatives; the result passes [`Self::check`].
    /// - fails: noncanonical substitutions, wrong q/p sorts and malformed
    ///   source operations are refused rather than silently normalized.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `NonCanonical` for non-normal SSC expressions, otherwise the
    /// corresponding typed `BindingError`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independently written first-order inputs exercise the
    ///   reverse composite; L3 — a `$q` of the wrong sort and an explicit
    ///   substitution on an operation distinguish canonical admission from
    ///   unchecked erasure.
    /// - witness: `tests::glf::model::identification`
    /// - witness: `tests::glf::model::typing_boundaries`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |binding|
        binding.context == judgement.context && binding.sort == judgement.sort))]
    pub fn from_first_order(
        &self,
        judgement: &FirstOrderJudgement,
    ) -> Result<BindingJudgement, BindingError>
    {
        self.check_context(&judgement.context)?;
        let mut scope = judgement.context.clone();
        let mut work = alloc::vec![Decode::Term(judgement.term.to_node(), &judgement.sort)];
        let mut terms: Vec<BindingTerm> = Vec::new();
        while let Some(step) = work.pop() {
            match step {
                Decode::Restore(length) => scope.truncate(length),
                Decode::Argument(node, port) => {
                    work.push(Decode::Restore(scope.len()));
                    scope.extend(port.bindings.iter().map(|binder| binder.sort.clone()));
                    work.push(Decode::Term(node, &port.sort));
                },
                Decode::Weaken(sort) => {
                    scope.push(sort);
                    let term = terms.pop().ok_or(BindingError::InvalidState)?;
                    let BindingHead::Variable(index) = *term.0.to_ref().head()
                    else {
                        return Err(BindingError::NonCanonical);
                    };
                    terms.push(BindingTerm::variable(VariableIndex::from(
                        usize::from(index).saturating_add(1),
                    )));
                },
                Decode::Close(name, count) => {
                    let start = terms
                        .len()
                        .checked_sub(count)
                        .ok_or(BindingError::InvalidState)?;
                    let arguments: Vec<BindingTerm> = terms.drain(start ..).rev().collect();
                    terms.push(BindingTerm::operation(name.clone(), arguments));
                },
                Decode::Term(node, expected) => {
                    let TermView::Op { name, args } = node.view()
                    else {
                        return Err(BindingError::NonCanonical);
                    };
                    if name.as_ref().strip_prefix("$q_") == Some(expected.as_ref()) {
                        if args.into_iter().next().is_some() || scope.last() != Some(expected) {
                            return Err(BindingError::NonCanonical);
                        }
                        terms.push(BindingTerm::variable(VariableIndex::from(0)));
                    }
                    else if name.as_ref().strip_prefix("$sub_") == Some(expected.as_ref()) {
                        let mut args = args.into_iter();
                        let body = args.next().ok_or(BindingError::NonCanonical)?;
                        let weakening = args.next().ok_or(BindingError::NonCanonical)?;
                        let crossed = scope.pop().ok_or(BindingError::NonCanonical)?;
                        let TermView::Op {
                            name,
                            args: parameters,
                        } = weakening.view()
                        else {
                            return Err(BindingError::NonCanonical);
                        };
                        if args.next().is_some()
                            || parameters.into_iter().next().is_some()
                            || name.as_ref().strip_prefix("$p_") != Some(crossed.as_ref())
                        {
                            return Err(BindingError::NonCanonical);
                        }
                        work.push(Decode::Weaken(crossed));
                        work.push(Decode::Term(body, expected));
                    }
                    else {
                        let operation = self.operation(name)?;
                        let output = operation
                            .arity
                            .outputs
                            .first()
                            .ok_or(BindingError::InvalidState)?;
                        same_sort(expected, &output.sort)?;
                        if args.len() != operation.arity.inputs.len() {
                            return Err(BindingError::Arity(name.clone()));
                        }
                        work.push(Decode::Close(name, args.len()));
                        work.extend(
                            args.into_iter()
                                .zip(&operation.arity.inputs)
                                .map(|(child, port)| Decode::Argument(child, port)),
                        );
                    }
                },
            }
        }
        let term = terms.pop().ok_or(BindingError::InvalidState)?;
        let result = BindingJudgement {
            context: judgement.context.clone(),
            sort: judgement.sort.clone(),
            term,
        };
        self.check(&result)?;
        Ok(result)
    }
}

/// First-order encoding continuations.
enum Encode<'term, 'signature>
{
    /// Visit a binding subtree.
    Term(TreeRef<'term, BindingHead>),
    /// Enter one argument's local telescope.
    Argument(
        TreeRef<'term, BindingHead>,
        &'signature crate::arity::SortRef,
    ),
    /// Restore the ambient scope.
    Restore(usize),
    /// Reassemble a source operation.
    Close(&'term Name, usize),
}

/// First-order decoding continuations.
enum Decode<'term, 'signature>
{
    /// Read a term at an expected sort.
    Term(TermNode<'term>, &'signature Name),
    /// Enter one argument's local telescope.
    Argument(TermNode<'term>, &'signature crate::arity::SortRef),
    /// Restore the ambient scope.
    Restore(usize),
    /// Cross a representable sort after reading a weakened variable.
    Weaken(Name),
    /// Reassemble a source operation.
    Close(&'term Name, usize),
}
