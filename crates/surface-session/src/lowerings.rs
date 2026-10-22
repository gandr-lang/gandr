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
//! under that root ([`JudgedClosure`]), and the incremental pass over their
//! items is run once beside it ([`Led`]). Every revision is lowered after the
//! arena that pass left and judged on a copy of the closure's state, and the
//! incremental pass over it starts after the closure's items. A closure a
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
use gandr_core_checker::CheckBudget;
use gandr_core_incremental::Leading;
use gandr_core_incremental::lead;
use gandr_core_term::CoreArena;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::JudgedClosure;
use gandr_surface_lowering::ClosureLowering;
use gandr_surface_lowering::UnitSource;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::SourceText;

use crate::edit::Snapshot;
use crate::item_source::program;

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

/// A closure's lowering, with its own declarations' judgement and the
/// incremental pass's state after their items, each under each root once a
/// document laid after it asks for it, and the snapshot images of their items
/// once a submission has made them.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Closure
{
    /// The closure's lowering.
    lowering: Arc<ClosureLowering>,
    /// What is made of it under the strict root.
    strict: Rooted,
    /// What is made of it under the fixture root.
    fixture: Rooted,
    /// The snapshot of the items its declarations lead a submitted program
    /// with, kept by the first submission that read them.
    snapshot: OnceLock<Snapshot>,
}

/// What is made of a closure's own declarations under one root, each the
/// first time it is asked for.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Rooted
{
    /// The declarations judged under the unbounded grant a session judges
    /// under and settled under the root.
    judged: OnceLock<Option<JudgedClosure>>,
    /// The incremental pass's state after their items.
    led: OnceLock<Option<Led>>,
}

/// The incremental pass's state after a closure's items, and the arena the
/// pass left.
///
/// A document laid after the closure is lowered onto that arena, so that the
/// pass over each of its revisions starts after the closure's items.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Led
{
    /// The closure's judged arena, the pass's nodes minted after it.
    arena: CoreArena,
    /// The pass's state after the closure's items.
    leading: Arc<Leading>,
}

impl Led
{
    /// The incremental pass's state after the items of `judged`'s closure's
    /// declarations, and the arena it left: `None` when the closure's lowering
    /// has no module or its items cannot be ordered.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`lead`] over the program of the closure's own module
    ///   ([`ClosureLowering::alone`]) on a copy of `judged`'s arena
    ///   ([`JudgedClosure::arena`]), under the default allowance a session
    ///   judges under, beside the arena the pass left.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause names a pass over a program no argument
    ///   carries; the session's witness submits a document after it and
    ///   compares with a fresh judgement on a fresh state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document laid after the closure, submitted after
    ///   this state, judges only its own items and composes as a fresh
    ///   judgement lowered onto a fresh state's arena does.
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    #[inline]
    #[must_use]
    pub fn of(judged: &JudgedClosure) -> Option<Self>
    {
        let (module, _) = judged.lowering().alone()?;
        let mut items = program(&module, judged.arena().clone()).ok()?;
        let (_, leading) = lead(&mut items, CheckBudget::DEFAULT).ok()?;
        // Each revision lowers onto a copy of this arena, which the freeze
        // makes cost the revision's own nodes alone.
        let mut arena = items.arena().clone();
        arena.freeze();
        Some(Self {
            arena,
            leading: Arc::new(leading),
        })
    }

    /// The arena a document laid after the closure is lowered onto.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn arena(&self) -> &CoreArena
    {
        &self.arena
    }

    /// The pass's state after the closure's items.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn leading(&self) -> &Arc<Leading>
    {
        &self.leading
    }
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
            strict: Rooted::default(),
            fixture: Rooted::default(),
            snapshot: OnceLock::new(),
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

    /// What is made of the closure under `root`.
    ///
    /// # Specification
    /// trivial.
    const fn rooted(
        &self,
        root: CorpusRoot,
    ) -> &Rooted
    {
        match root {
            CorpusRoot::Strict => &self.strict,
            CorpusRoot::Fixture => &self.fixture,
        }
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
        self.rooted(root)
            .judged
            .get_or_init(|| {
                JudgedClosure::new(Arc::clone(&self.lowering), &HostGrant::UNBOUNDED, root)
            })
            .as_ref()
    }

    /// The incremental pass's state after the closure's declarations' items,
    /// beside the judgement under `root`, made the first time any session
    /// asks under `root`: `None` when there is no judgement under `root` or
    /// [`Led::of`] it is `None`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Led::of`] the judgement [`judged`](Self::judged) gives
    ///   under `root`, the same answer on every call under `root`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause names a pass the first call alone makes;
    ///   the session's witness submits a document after it twice.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Led::of`].
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    pub fn led(
        &self,
        root: CorpusRoot,
    ) -> Option<&Led>
    {
        self.rooted(root)
            .led
            .get_or_init(|| self.judged(root).and_then(Led::of))
            .as_ref()
    }

    /// The snapshot of the items the closure's declarations lead a submitted
    /// program with, once a submission has kept it.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn snapshot(&self) -> Option<&Snapshot>
    {
        self.snapshot.get()
    }

    /// Keep `snapshot` as the snapshot of the closure's items, unless a
    /// submission kept one before.
    ///
    /// # Specification
    /// - requires: `snapshot` is [`Snapshot::leading`] of a submission's
    ///   snapshot, ending where the closure's declarations' items end.
    /// - ensures: the closure holds a snapshot, the first kept.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each revision of a document laid after the closure
    ///   shares the closure's items' images, and its edits are the document's
    ///   own.
    /// - witness: `tests::session::a_document_after_its_closure_shares_the_closure_s_images_776`
    #[spec(ensures: self.snapshot.get().is_some())]
    pub fn keep_snapshot<Make>(
        &self,
        snapshot: Make,
    ) where
        Make: FnOnce() -> Snapshot,
    {
        let _kept = self.snapshot.get_or_init(snapshot);
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
