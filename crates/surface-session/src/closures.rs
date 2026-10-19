//! The import closures this process's sessions readmitted, held so that an
//! admission of a document laid out after the same closure resumes the
//! closure's readmission rather than repeating it.
//!
//! # A closure is readmitted once per process
//!
//! **Choice.** An editor rechecks a document by laying it out after its import
//! closure and judging the whole text; the kernel readmitted every declaration
//! of it on every recheck, though an edit to the document's own text leaves the
//! closure alone. A store per process holds the readmission of each closure
//! recently admitted — the kernel environment its declarations built, the
//! positions they took and their outcomes, as [`Crossed`] records them — under
//! the closure's text and its declarations' checkpoints. An admission whose
//! closure text is held, byte for byte, and whose closure declarations'
//! checkpoints — content, the answers each consulted and its typing — are
//! pointwise the held ones resumes from it, and the kernel is offered the
//! document's own declarations alone: the text selects the candidate, the
//! comparison of what the judgement recorded admits it, so nothing below the
//! elaborator is keyed by a name, a position or a session. Every session
//! reads the one store: a second connection opening the document, or a
//! session over another document importing the same closure, resumes too.
//! The store holds a few closures and lets the one asked for longest ago go.
//!
//! **Alternatives.** A record per session resumes nothing for a second
//! connection, the shape a language server's tests and its faces both take. A
//! key of the closure's text alone would resume a closure whose text is
//! unchanged while a source it reaches through another root reads otherwise;
//! the checkpoints are what the judgement read, and they are what admits. A
//! digest of the text as the key still compares the bytes on a hit, the whole
//! cost of comparing them, and keys by something other than the content it
//! names. Per-declaration reuse — resuming each closure declaration whose
//! checkpoint is unchanged after an edit to an imported source — needs the
//! readmission to cross a source at a time into one environment, which is the
//! forest that composes each imported source once.
//!
//! **Reversal.** When each imported source is composed once, into one arena
//! and one kernel environment, a source's readmission is kept beside its
//! lowering and judgement, keyed as they are, and this store goes.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::sync::Mutex;
use std::sync::PoisonError;

use anodized::spec;
use gandr_core_checker::bridge::Crossed;
use gandr_core_incremental::ItemCheckpoint;
use gandr_surface_syntax::SourceText;

/// The most closures [`CLOSURES`] holds before it lets the one asked for
/// longest ago go: the closures of the few documents an editor has open.
const CLOSURES_HELD: usize = 8;

/// One closure's readmission, under the text and the checkpoints that select
/// and admit it.
#[derive(Debug)]
struct Held
{
    /// The closure's text: the laid-out revision before the document's own.
    text: String,
    /// The checkpoints of the closure's declarations, in order.
    checkpoints: Vec<ItemCheckpoint>,
    /// What readmitting them built.
    crossed: Arc<Crossed>,
    /// The tick of the store's clock it was last asked for at.
    used: u64,
}

/// Every closure the process holds.
#[derive(Debug)]
struct Closures
{
    /// The closures, in no order.
    held: Vec<Held>,
    /// Ticks once per question.
    clock: u64,
}

/// The process's closures, shared by every session.
static CLOSURES: Mutex<Closures> = Mutex::new(Closures {
    held: Vec::new(),
    clock: 0_u64,
});

/// The readmission the process holds for the closure laid out as `text` whose
/// declarations' checkpoints are `checkpoints`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the readmission [`keep`] last held under a text equal to `text`
///   byte for byte and checkpoints equal to `checkpoints` pointwise, now the
///   one asked for last; `None` when the store holds none.
/// - provides: the candidate a session's admission resumes the closure from.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause reads the store the call locks; the witness
///   admits a closure, then resumes it.
///
/// # Adequacy
/// - hypothesis: L3 — an edit to a document's own text resumes its closure, and
///   an edit to a source of the closure does not.
/// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
pub fn find(
    text: SourceText<'_>,
    checkpoints: &[ItemCheckpoint],
) -> Option<Arc<Crossed>>
{
    let mut closures = CLOSURES.lock().unwrap_or_else(PoisonError::into_inner);
    closures.clock = closures.clock.saturating_add(1);
    let now = closures.clock;
    let found = closures
        .held
        .iter_mut()
        .find(|held| held.text == <&str>::from(text) && held.checkpoints == checkpoints)
        .map(|held| {
            held.used = now;
            Arc::clone(&held.crossed)
        });
    drop(closures);
    found
}

/// Hold `crossed`, the readmission of the closure laid out as `text` whose
/// declarations' checkpoints are `checkpoints`, in place of any held under
/// both, letting the one asked for longest ago go past [`CLOSURES_HELD`].
///
/// # Specification
/// - requires: `crossed` records the readmission of declarations judged to
///   `checkpoints`, laid out as `text`.
/// - ensures: [`find`] of `text` and `checkpoints` answers `crossed` until a
///   later [`keep`] replaces it or lets it go; the store holds at most
///   [`CLOSURES_HELD`].
/// - provides: the record a later admission of the same closure resumes from.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`find`].
/// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
#[spec(requires: usize::from(crossed.boundary()) == checkpoints.len())]
pub fn keep(
    text: String,
    checkpoints: Vec<ItemCheckpoint>,
    crossed: Crossed,
)
{
    let mut closures = CLOSURES.lock().unwrap_or_else(PoisonError::into_inner);
    closures.clock = closures.clock.saturating_add(1);
    let now = closures.clock;
    closures
        .held
        .retain(|held| held.text != text || held.checkpoints != checkpoints);
    closures.held.push(Held {
        text,
        checkpoints,
        crossed: Arc::new(crossed),
        used: now,
    });
    while closures.held.len() > CLOSURES_HELD {
        let oldest = closures
            .held
            .iter()
            .enumerate()
            .min_by_key(|&(_, held)| held.used)
            .map(|(index, _)| index);
        let Some(oldest) = oldest
        else {
            break;
        };
        let _gone = closures.held.swap_remove(oldest);
    }
    drop(closures);
}
