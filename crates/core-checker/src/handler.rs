//! A capability scope over a theory checked as a model of it.
//!
//! A scope that handles a theory owes each of the theory's laws: read
//! through the scope's clauses ([`gandr_core_term::handler`]), the law's two
//! sides convert with every metavariable rigid
//! ([`crate::code::CodeDefinitions::convert_rigidly`]). The obligations are
//! built where the scope is lowered and decided once the declaration holding
//! it is judged; a scope whose clauses are not shown to identify a law's
//! sides is refused `HandlerUnlawful`, naming the scope, the law and its two
//! sides as read.
//!
//! # Examples
//!
//! ```text
//! handle st : StatePutGet with sort S = Integer { … } with {
//!   pure(x) => pure x,
//!   oper get(k) => k(4),
//!   oper put(s, k) => k(unit)
//! }
//! ```
//!
//! Put-get's left side resumes `k` at `4` and its right side at `s`: the
//! scope is refused at `putGet`.

use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::failure::Failure;
use crate::failure::Pursuit;
use crate::failure::Stage;
use crate::failure::judged;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;

/// Decide that every law in `laws` holds of the clauses it is read through.
///
/// # Specification
/// - requires: each law's sides are computations of the context's arena beneath
///   the same binders.
/// - ensures: success when every law's two sides convert, every metavariable
///   rigid and no definition unfolding.
/// - fails: [`CheckRefusal::HandlerUnlawful`] at the first law, in order, whose
///   sides are not shown to convert.
/// - panics: none.
/// - executable: none — the verdict is the machine's on terms it evaluates; the
///   witnesses observe both answers through the corpus.
///
/// # Errors
/// The first law the clauses are not shown to satisfy.
///
/// # Adequacy
/// - hypothesis: L3 — a scope over get-get whose clauses identify its sides is
///   admitted, and one over put-get whose clauses tell them apart is refused at
///   the law.
/// - witness: `module::tests::a_scope_is_checked_as_a_model_of_its_theory_2272`
pub fn lawful(
    context: &CheckingContext<'_>,
    laws: &[gandr_core_term::handler::HandlerLaw],
) -> Result<(), Failure>
{
    let Some(law) = laws.iter().find(|law| {
        context
            .definitions()
            .convert_rigidly(context.arena(), (law.left, law.right))
            != Maybe::Present(())
    })
    else {
        return Ok(());
    };
    Err(Failure::bare(
        CheckRefusal::HandlerUnlawful {
            at: law.scope,
            rule: law.rule,
            left: law.left,
            right: law.right,
        },
        Pursuit::new(
            CoreNode::Term(TermNode::Computation(law.scope)),
            Maybe::Absent(judged::Absent::Synthesised),
            Stage::Starting,
        ),
    ))
}
