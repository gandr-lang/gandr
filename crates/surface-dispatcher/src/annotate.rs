//! The value types that focusing writes into the IL (#8161): the type of each
//! bind's binder and of each field of a structural former, joined from the
//! annotations that the checker's judgement gave, beside the signature of each
//! declared family.
//!
//! The judgement gives one annotation at the rule of each bind, and one for
//! each field of each structural former that it checks. The module's run reads
//! the type of each annotation through the solutions of its declaration's
//! implicits, so each type here is solved. [`typed`] joins the annotations of
//! a module in one pass.
//!
//! The table keys a binder's type by the head of its bind. The second run of a
//! body judges the body that the elaboration rebuilds (#4466), so a bind that
//! the elaboration makes has its own annotation.
//!
//! A field of a declared constructor takes no type from the annotations. Its
//! layout is a fact of its declaration, so focusing reads the type that the
//! family's signature states for it.
//!
//! # Boundaries
//!
//! - **A node that two occurrences type apart holds a conflict.** Two sites can
//!   share one node of the core arena. The table keys a type by the node. A key
//!   that takes two contents holds [`Recorded::Conflict`], and focusing counts
//!   the position as a conflict. Two ids of one content are one type.
//! - **A site that no rule annotates holds no type.** Focusing counts the
//!   position as missed.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use gandr_core_checker::Annotation;
use gandr_core_checker::Site;
use gandr_core_sequent::Recorded;
use gandr_core_sequent::Typed;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldPosition;

/// The table of the binder types and the field types that `annotations` give
/// over `core`, beside the signatures `declared` of the families in scope.
///
/// # Specification
/// - requires: `annotations` are a module report's over `core`, and `declared`
///   the signatures that the run admits.
/// - ensures: the head of each annotated bind is keyed with its annotations'
///   type, and each annotated field with its annotations' type; a key that two
///   annotations give two contents holds a conflict; no other key is held. The
///   table holds `declared` unchanged.
/// - panics: none.
/// - executable: none — unwitnessable provenance: the annotations must be the
///   run of a module over `core`, and the call holds no judgement to check them
///   against.
///
/// # Cost
/// - allocation: the table, growth within the annotations
///
/// # Adequacy
/// - hypothesis: L3 — a pair, a cons cell and a bind over a returner are each
///   read at the types that their judgements give.
/// - witness: `annotate::tests::the_join_reads_each_field_and_binder_at_its_occurrence_8161`
pub(crate) fn typed(
    core: &CoreArena,
    annotations: &[Annotation],
    declared: BTreeMap<ConstantIndex, Arc<DataSignature>>,
) -> Typed
{
    let same = |old, new| {
        gandr_core_term::equal_type_syntax(core, old, new)
            == gandr_core_term::CertificateEquality::Equal
    };
    let mut binders: BTreeMap<ComputationId, Recorded> = BTreeMap::new();
    let mut fields: BTreeMap<(ValueId, FieldPosition), Recorded> = BTreeMap::new();
    for annotation in annotations {
        match annotation.site {
            Site::Binder(head) => Recorded::join(&mut binders, head, annotation.ty, same),
            Site::Field(former, position) => {
                Recorded::join(&mut fields, (former, position), annotation.ty, same);
            },
        }
    }
    Typed::checked(binders, fields, declared)
}

#[cfg(test)]
mod tests;
