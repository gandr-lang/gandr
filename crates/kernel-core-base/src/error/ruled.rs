//! Why the body of a ruled definition is not the decision tree of its rules.

use gandr_kernel_term::RuleIndex;

/// Why a ruled definition's body is not its rules' decision tree.
///
/// # Specification
/// - provides: the first fault the walk of the body meets.
/// - panics: none.
/// - executable: none — data declaration.
///
/// # Adequacy
/// - hypothesis: L3 — a body whose leaf returns another constructor than its
///   rule is refused naming that rule, and one that is no fixpoint is refused
///   for its shape.
/// - witness: `gandr-kernel-core::ruled::tests::a_body_is_admitted_only_as_its_rules_decision_tree`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OperationBodyFault
{
    /// The body is not a thunked fixpoint over one lambda per input, or a
    /// case of its tree is not over a data declaration's whole constructor
    /// table with one lambda per field.
    Shape,
    /// No rule's left side matches what the cases above a leaf learned.
    Unmatched,
    /// A leaf is the right side of no rule whose left side matches it; the
    /// first rule that matches.
    Apart(RuleIndex),
}
