//! A keyed-index schema: a factory's dialogue, project and provenance
//! indexes stated as one schema.
//!
//! The three indexes a dialogue factory keeps over its content-addressed
//! receipts are each a hand-encoded key family in a byte-keyed index:
//!
//! - **dialogue**: an attempt and a sequence number to the receipt of the move
//!   made there;
//! - **project**: a task's name to its entry — its standing, its heads and the
//!   refusals recorded against it;
//! - **provenance**: a subject digest, of any width, to every move that named
//!   it, with the task, the attempt and the role it was named in.
//!
//! Stated as one schema, each family is a table or a kept inverse, and what
//! the hand-encoded families left to convention is a total arrow the store
//! checks:
//!
//! | Index | Question | Here |
//! | ----- | -------- | ---- |
//! | dialogue | the moves of an attempt, in sequence | preimage of `move_attempt`, ordered by `move_seq` |
//! | project | the task of a name | preimage of `task_name` |
//! | project | the tasks of a standing | preimage of `task_standing` |
//! | project | the refusals of a task | preimage of `refusal_task` |
//! | provenance | the namings of a digest | preimage of `subject_digest`, then of `naming_subject` |
//!
//! One equation holds the provenance index to the dialogue: a naming's task
//! is the task of the attempt its move was made in,
//! `naming_task = naming_move ; move_attempt ; attempt_task`. The
//! hand-encoded provenance key repeats the task beside the attempt and
//! nothing checks that they agree; here an edit that makes them disagree is
//! refused by the equation's name.
//!
//! Attribute values are canonical bytes the caller chooses: `Number` is
//! `u64le`, `Text` UTF-8, `Digest` and `Bytes` opaque, `Standing` and
//! `Role` one tag byte each. The schema's identity is pinned by
//! `tests::keyed::the_keyed_schema_identity_is_pinned`; a change to any name,
//! arrow, attribute, indexing or equation changes it.

use crate::schema::Indexing;
use crate::schema::Presentation;
use crate::schema::Schema;
use crate::schema::SchemaError;

/// The keyed-index schema's presentation.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn presentation() -> Presentation
{
    Presentation::new()
        .object("Task")
        .object("Attempt")
        .object("Move")
        .object("Refusal")
        .object("Subject")
        .object("Naming")
        .attribute_type("Bytes")
        .attribute_type("Digest")
        .attribute_type("Number")
        .attribute_type("Role")
        .attribute_type("Standing")
        .attribute_type("Text")
        .arrow("attempt_task", "Attempt", "Task", Indexing::Indexed)
        .arrow("move_attempt", "Move", "Attempt", Indexing::Indexed)
        .arrow("refusal_task", "Refusal", "Task", Indexing::Indexed)
        .arrow("naming_move", "Naming", "Move", Indexing::Indexed)
        .arrow("naming_subject", "Naming", "Subject", Indexing::Indexed)
        .arrow("naming_task", "Naming", "Task", Indexing::Indexed)
        .attribute("task_name", "Task", "Text", Indexing::Indexed)
        .attribute("task_standing", "Task", "Standing", Indexing::Indexed)
        .attribute("task_heads", "Task", "Bytes", Indexing::Unindexed)
        .attribute("attempt_number", "Attempt", "Number", Indexing::Unindexed)
        .attribute("move_seq", "Move", "Number", Indexing::Unindexed)
        .attribute("move_receipt", "Move", "Bytes", Indexing::Unindexed)
        .attribute("refusal_commit", "Refusal", "Digest", Indexing::Unindexed)
        .attribute("refusal_reason", "Refusal", "Text", Indexing::Unindexed)
        .attribute("subject_digest", "Subject", "Digest", Indexing::Indexed)
        .attribute("naming_role", "Naming", "Role", Indexing::Unindexed)
        .equation("naming_task_agrees", "Naming", ["naming_task"], [
            "naming_move",
            "move_attempt",
            "attempt_task",
        ])
}

/// The keyed-index schema.
///
/// # Specification
/// - ensures: on success the schema [`presentation`] states.
/// - fails: never for this presentation; the signature carries
///   [`Schema::present`]'s refusals.
/// - panics: none.
/// - executable: none — the schema is pinned by its identity.
///
/// # Errors
/// [`SchemaError`], which this presentation does not raise.
///
/// # Adequacy
/// - hypothesis: L2 — the schema presents and its identity is the pinned
///   hexadecimal.
/// - witness: `tests::keyed::the_keyed_schema_identity_is_pinned`
#[inline]
pub fn schema() -> Result<Schema, SchemaError>
{
    Schema::present(&presentation())
}
