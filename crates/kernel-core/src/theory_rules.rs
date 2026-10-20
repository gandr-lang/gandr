//! The admission of a presentation: a definition whose type is the
//! presentation code and whose body is a presentation has its rules decided
//! by the kernel as its value states them.
//!
//! The presentation code is recognised by its constructor table
//! ([`gandr_kernel_term::presentation_code`]): an unparametrised, unindexed
//! data declaration whose constructors have exactly the code's string and
//! recursive fields. A definition at that type whose body is a constructor
//! value is a presentation, and [`gandr_kernel_term::TheoryRules`] reads its
//! rule chain and decides it: every rule well formed and decreased by the
//! stated order, every derived rule the normal forms of the critical pair it
//! names, every critical pair joined. A body that is no constructor value
//! names an earlier definition, decided at its own admission.

use anodized::spec;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::PRESENTATION_FUEL;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::TheoryRules;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::presentation_code;

use crate::env::AdmittedDeclaration;
use crate::error::KernelError;

/// Decide the rules of the presentation a definition declared at `declared`
/// with `body` states, when `declared` is the presentation code.
///
/// # Specification
/// - requires: `entries` are the declarations admitted before the definition;
///   `declared` and `body` live in `arena`.
/// - ensures: `Ok(())` when `declared` is no unapplied data type whose
///   declaration is the presentation code, or `body` is no constructor value;
///   otherwise exactly when [`TheoryRules::read`] reads `body` and
///   [`TheoryRules::decide`] accepts it within the admission's fuel.
/// - provides: the kernel's own decision that a presentation's rules converge
///   and decide what its written rules generate, re-derived at every admission
///   and replay, so no producer's verdict is taken on trust.
/// - fails: [`KernelError::PresentationRulesRefused`] naming the first refused
///   rule and its fault.
/// - panics: none.
/// - measure: the decision's fuel.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a presentation stating a unit law readmits, the same
///   presentation forged with a second law rewriting the unit's call apart is
///   refused naming the pair, and a completed group readmits from the peaks its
///   value names.
/// - witness: `theory_rules::tests::a_presentation_is_admitted_only_when_its_rules_converge`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(KernelError::PresentationRulesRefused(_))))]
pub fn admit(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    (declared, body): (ValueTypeId, ValueId),
) -> Result<(), KernelError>
{
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = arena.value_type(declared)
    else {
        return Ok(());
    };
    let coded = arguments.is_empty()
        && entries
            .get(usize::from(declaration))
            .is_some_and(|entry| match *entry.content() {
                DeclarationContent::Data {
                    ref parameters,
                    ref indices,
                    ref constructors,
                    ..
                } => {
                    parameters.is_empty()
                        && indices.is_empty()
                        && bool::from(presentation_code(arena, declaration, constructors))
                },
                DeclarationContent::Codata { .. }
                | DeclarationContent::Def { .. }
                | DeclarationContent::Axiom { .. }
                | DeclarationContent::AbstractType { .. } => false,
            });
    if !coded || !matches!(arena.value(body), Some(&Value::Constructor { .. })) {
        return Ok(());
    }
    TheoryRules::read(arena, body)
        .and_then(|rules| rules.decide(&mut RewriteFuel::from(PRESENTATION_FUEL)))
        .map_err(KernelError::PresentationRulesRefused)
}

#[cfg(test)]
mod tests;
