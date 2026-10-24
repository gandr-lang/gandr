//! The admission of a definition's operation rules: the kernel decides that
//! the rules an operation was written as converge, reading the declarations
//! admitted before it, and that the definition's body is their decision tree.
//!
//! A definition carrying no rule owes nothing. A definition carrying rules is
//! admitted only when [`OperationRules::converge`] accepts them over the
//! environment: their constructors name admitted data declarations, their
//! calls name the definition itself or ruled definitions admitted before it,
//! every rule is oriented by the path order and every critical pair joins.
//! Its body must then be the rules' decision tree ([`link`]): each leaf the
//! right side of a rule whose left side matches the cases above it.

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::OperationRules;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RuleScope;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use crate::env::Entries;
use crate::error::KernelError;

mod link;

pub use link::OperationBodyFault;

/// The nodes one definition's convergence decision may scan or copy.
///
/// Every rule system the corpus writes decides in a few thousand; the bound
/// only keeps a pathological system from running unbounded.
const CONVERGENCE_FUEL: u64 = 1 << 22;

/// The declarations admitted before a ruled definition, as its rules read
/// them.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct Admitted<'entries>(&'entries Entries);

impl RuleScope for Admitted<'_>
{
    /// The field count of a constructor of an admitted data declaration.
    ///
    /// # Specification
    /// trivial.
    fn fields(
        &self,
        family: ConstantIndex,
        tag: ConstructorTag,
    ) -> Option<FieldCount>
    {
        match *self.0.get(usize::from(family))?.content() {
            DeclarationContent::Data {
                ref constructors, ..
            } => constructors
                .get(usize::from(tag))
                .map(|fields| FieldCount::from(fields.len())),
            DeclarationContent::Codata { .. }
            | DeclarationContent::Def { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::AbstractType { .. } => None,
        }
    }

    /// The presentation of an admitted data declaration.
    ///
    /// # Specification
    /// trivial.
    fn presentation(
        &self,
        family: ConstantIndex,
    ) -> Option<&Presentation>
    {
        let entry = self.0.get(usize::from(family))?;
        match *entry.content() {
            DeclarationContent::Data { .. } => Some(entry.declaration().presentation()),
            DeclarationContent::Codata { .. }
            | DeclarationContent::Def { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::AbstractType { .. } => None,
        }
    }

    /// The rules of an admitted ruled definition.
    ///
    /// # Specification
    /// trivial.
    fn rules(
        &self,
        constant: ConstantIndex,
    ) -> Option<&OperationRules>
    {
        let rules = self
            .0
            .get(usize::from(constant))?
            .declaration()
            .operation_rules();
        (!rules.rules().is_empty()).then_some(rules)
    }
}

/// Decide the operation rules of the definition admitted at `position` after
/// `entries`, declared at `declared` with `body`.
///
/// # Specification
/// - requires: `entries` are the declarations admitted before `position`;
///   `declared` and `body` live in `arena`.
/// - ensures: `Ok(())` exactly when `rules` is empty, or
///   [`OperationRules::converge`] accepts it over `entries` within the
///   admission's fuel and `body` is its decision tree ([`link::link`]); `arena`
///   holds what it held on entry.
/// - provides: the kernel's own decision that an operation's rules converge and
///   that its body computes them, re-derived at every admission and replay, so
///   no producer's verdict is taken on trust.
/// - fails: [`KernelError::OperationRulesRefused`] naming the first refused
///   rule and its fault, then [`KernelError::OperationBodyUnlinked`] naming the
///   body's first fault.
/// - panics: none.
/// - measure: the convergence fuel, then the body's tree.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — an operation over an earlier data declaration and an
///   earlier ruled operation admits, the same rules forged to part are refused
///   naming the pair, a rule calling a later definition is refused, and a body
///   one leaf of which is not its rule's is refused naming the rule.
/// - witness: `ruled::tests::rules_over_the_environment_admit_and_a_forged_pair_is_refused`
/// - witness: `ruled::tests::a_body_is_admitted_only_as_its_rules_decision_tree`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && (ret.is_ok() || matches!(ret, Err(KernelError::OperationRulesRefused(_) | KernelError::OperationBodyUnlinked(_)))),
)]
pub fn admit(
    arena: &mut TermArena,
    entries: &Entries,
    position: ConstantIndex,
    (declared, body): (ValueTypeId, ValueId),
    rules: &OperationRules,
) -> Result<(), KernelError>
{
    if rules.rules().is_empty() {
        return Ok(());
    }
    rules
        .converge(
            position,
            &Admitted(entries),
            &mut RewriteFuel::from(CONVERGENCE_FUEL),
        )
        .map_err(KernelError::OperationRulesRefused)?;
    link::link(arena, entries, position, declared, body, rules)
        .map_err(KernelError::OperationBodyUnlinked)
}

#[cfg(test)]
mod tests;
