//! The import closures this process's sessions lowered, held so that a
//! document laid out after the same closure lowers and is judged on its own
//! source alone.
//!
//! An editor rechecks a document by laying it out after its import closure.
//! A source lowers alike whatever follows it, so the closure's lowering is the
//! same for every revision of the document: the store holds it under the
//! closure's text, its sources and the grammar's fingerprint, and a recheck
//! resumes it for the document's own source
//! ([`ClosureLowering::resume`](gandr_surface_lowering::ClosureLowering::resume)).
//! The closure's own declarations are judged, focused, settled and spelled
//! once per corpus root, the first time a document laid after it is judged
//! under that root ([`JudgedClosure`]), and every revision is lowered after
//! that judgement's arena and judged on a copy of its state. A closure a
//! document cannot be laid after
//! ([`Unheld`](gandr_surface_dispatcher::Unheld)) is held as such, so its
//! documents are lowered whole without the closure being parsed again. Every
//! session reads the one store, and every lowering it holds is under the
//! dispatcher's budget over the empty outermost scope, the one a session
//! lowers under; it holds a few closures and lets the one asked for longest
//! ago go.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::PoisonError;

use anodized::spec;
use gandr_core_incremental::Checkpoints;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::JudgedClosure;
use gandr_surface_lowering::ClosureLowering;
use gandr_surface_lowering::UnitSource;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::SourceText;

/// The most closures [`LOWERINGS`] holds before it lets the one asked for
/// longest ago go: the closures of the few documents an editor has open.
const LOWERINGS_HELD: usize = 8;

/// What the store holds for a closure.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub enum Held
{
    /// The closure's lowering.
    Lowered(Arc<Closure>),
    /// No lowering: a document laid after the closure is lowered whole.
    Whole,
}

/// A closure's lowering, with its own declarations' judgement under each root
/// once a document laid after it asks for it, and the checkpoints of its
/// declarations' items once a submission has judged them.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Closure
{
    /// The closure's lowering.
    lowering: Arc<ClosureLowering>,
    /// Its own declarations judged under the unbounded grant a session judges
    /// under and settled under the strict root, made the first time it is
    /// asked for.
    strict: OnceLock<Option<JudgedClosure>>,
    /// The same, settled under the fixture root.
    fixture: OnceLock<Option<JudgedClosure>>,
    /// The checkpoints of the items its declarations lead a submitted program
    /// with, kept by the first submission that judged them.
    checkpoints: OnceLock<Checkpoints>,
}

impl Closure
{
    /// `lowering`, its declarations not judged yet.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn new(lowering: ClosureLowering) -> Self
    {
        Self {
            lowering: Arc::new(lowering),
            strict: OnceLock::new(),
            fixture: OnceLock::new(),
            checkpoints: OnceLock::new(),
        }
    }

    /// The closure's lowering.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn lowering(&self) -> &ClosureLowering
    {
        &self.lowering
    }

    /// The closure's own declarations judged under
    /// [`HostGrant::UNBOUNDED`] and settled under `root`, judged the first
    /// time any session asks under `root`: `None` when its lowering did not
    /// reach its end.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`JudgedClosure::new`] of the lowering under the unbounded
    ///   grant and `root`, the same answer on every call under `root`.
    /// - provides: the state every revision of a document laid after the
    ///   closure is judged from.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause names a judgement the first call alone
    ///   makes; the session's witness judges a document cold and warm.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document judged with the closure's judgement made
    ///   by an earlier session and with it made fresh composes alike.
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    pub fn judged(
        &self,
        root: CorpusRoot,
    ) -> Option<&JudgedClosure>
    {
        let slot = match root {
            CorpusRoot::Strict => &self.strict,
            CorpusRoot::Fixture => &self.fixture,
        };
        slot.get_or_init(|| {
            JudgedClosure::new(Arc::clone(&self.lowering), &HostGrant::UNBOUNDED, root)
        })
        .as_ref()
    }

    /// The checkpoints of the items the closure's declarations lead a
    /// submitted program with, once a submission has kept them.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn checkpoints(&self) -> Option<&Checkpoints>
    {
        self.checkpoints.get()
    }

    /// Keep `checkpoints` as the closure's items' checkpoints, unless a
    /// submission kept them before.
    ///
    /// # Specification
    /// - requires: `checkpoints` are a submission's checkpoints of the items
    ///   the closure's declarations lead its program with.
    /// - ensures: the closure holds checkpoints, the first kept.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a second session's first submission over a document
    ///   laid after the closure adopts the closure's items.
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    #[spec(ensures: self.checkpoints.get().is_some())]
    pub fn keep_checkpoints<Make>(
        &self,
        checkpoints: Make,
    ) where
        Make: FnOnce() -> Checkpoints,
    {
        let _kept = self.checkpoints.get_or_init(checkpoints);
    }
}

/// One closure's lowering, under the text, sources and grammar that select
/// it.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Entry
{
    /// The closure's text: the laid-out revision before the document's own.
    text: String,
    /// The closure's sources, in the order the unit admits them.
    sources: Vec<UnitSource>,
    /// The grammar the closure was parsed under.
    grammar: GrammarFingerprint,
    /// What the store holds for it.
    held: Held,
    /// The tick of the store's clock it was last asked for at.
    used: u64,
}

/// Every closure lowering the process holds.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Lowerings
{
    /// The closures, in no order.
    held: Vec<Entry>,
    /// Ticks once per question.
    clock: u64,
}

/// The process's closure lowerings, shared by every session.
static LOWERINGS: Mutex<Lowerings> = Mutex::new(Lowerings {
    held: Vec::new(),
    clock: 0_u64,
});

/// What the process holds for the closure laid out as `text`, whose sources
/// are `sources`, under the grammar `grammar`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: what [`keep`] last held under a text equal to `text` byte for
///   byte, sources equal to `sources` and the grammar `grammar`, now the one
///   asked for last; `None` when the store holds none.
/// - provides: the lowering a session resumes for a document laid after the
///   closure.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause reads the store the call locks; the witness
///   submits an importer twice and lowers its closure once.
///
/// # Adequacy
/// - hypothesis: L3 — an importer submitted twice finds its closure's lowering
///   the second time.
/// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
pub fn find(
    text: SourceText<'_>,
    sources: &[UnitSource],
    grammar: GrammarFingerprint,
) -> Option<Held>
{
    let mut lowerings = LOWERINGS.lock().unwrap_or_else(PoisonError::into_inner);
    lowerings.clock = lowerings.clock.saturating_add(1);
    let now = lowerings.clock;
    let found = lowerings
        .held
        .iter_mut()
        .find(|entry| {
            entry.grammar == grammar && entry.sources == sources && entry.text == <&str>::from(text)
        })
        .map(|entry| {
            entry.used = now;
            entry.held.clone()
        });
    drop(lowerings);
    found
}

/// Hold `held` for the closure laid out as `text`, whose sources are
/// `sources`, under the grammar `grammar`, in place of any held under all
/// three, letting the one asked for longest ago go past [`LOWERINGS_HELD`].
///
/// # Specification
/// - requires: a lowering `held` holds is of `text` as `sources` lays it out,
///   under `grammar`.
/// - ensures: [`find`] of `text`, `sources` and `grammar` answers `held` until
///   a later [`keep`] replaces it or lets it go; the store holds at most
///   [`LOWERINGS_HELD`].
/// - provides: the record a later recheck of a document laid after the same
///   closure resumes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`find`].
/// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
#[spec(requires: match held {
    Held::Lowered(ref lowered) => <&str>::from(lowered.lowering().text()) == text
        && lowered.lowering().unit().sources() == sources.as_slice(),
    Held::Whole => true,
})]
pub fn keep(
    text: String,
    sources: Vec<UnitSource>,
    grammar: GrammarFingerprint,
    held: Held,
)
{
    let mut lowerings = LOWERINGS.lock().unwrap_or_else(PoisonError::into_inner);
    lowerings.clock = lowerings.clock.saturating_add(1);
    let now = lowerings.clock;
    lowerings
        .held
        .retain(|entry| entry.grammar != grammar || entry.sources != sources || entry.text != text);
    lowerings.held.push(Entry {
        text,
        sources,
        grammar,
        held,
        used: now,
    });
    while lowerings.held.len() > LOWERINGS_HELD {
        let oldest = lowerings
            .held
            .iter()
            .enumerate()
            .min_by_key(|&(_, entry)| entry.used)
            .map(|(index, _)| index);
        let Some(oldest) = oldest
        else {
            break;
        };
        let _gone = lowerings.held.swap_remove(oldest);
    }
    drop(lowerings);
}
