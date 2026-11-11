//! The long operations of the toolset: `check`, `test`, `replay` and `run`.
//! The toolset acknowledges each one at once, as it acknowledges every call,
//! and answers it by a callback when its job ends.
//!
//! One thread of the toolset holds the jobs. `check` and `test` run on the
//! hub's pool through the [`Verbs`] that the driver gives the toolset, so they
//! print what `gandr check` and `gandr test` print. The text of the result is
//! the last line that the verb prints, its verdict, and the display holds each
//! line that it prints, its faults last. `run` runs on the pool too. It takes
//! the lock of the workspace and runs the declaration as the run lens of the
//! document runs it, so the text is the line that the lens shows. The lens
//! holds the lock for the whole run too.
//! `replay` runs no work of its own. The hub admits each revision that an
//! editor gives it, and the job answers when the admission of the revision
//! that it names ends. Its text counts the declarations by the kernel's
//! warrant.
//!
//! # Retirement and cancellation
//!
//! A newer revision of a document that the hub holds retires each `check` and
//! each `test` whose paths hold the document, and each `replay` of the
//! document. A document that closes retires them too. The retired call
//! answers at once, and its text names the document and its version now. The
//! result of its job is never delivered. A `POST` to `/cancel_tool_call` with
//! the `id` of a job, or to `/close_thread` with its `group_id`, ends the job
//! in the same way, and its text says `cancelled`. A walk stops at its next
//! write of a line. A run goes on to the end of its own budget, and its result
//! is dropped.
//!
//! # Progress
//!
//! In the hub's build with the `instrument` feature, the toolset watches the
//! hub's activity while a job runs. Each tick of the fold that has events
//! reaches each running job as a `view_update` of the type `activity`. Its
//! content is the activity card of the tick: the run of the toolset, the
//! events of the tick and the row of each core. A runtime keeps the latest
//! view of each thread, so each card stands alone.
//!
//! # Boundaries
//!
//! A crash of the hub loses no call: the row of each call is in the store
//! before its acknowledgement, and the toolset that opens the store next
//! answers a job that did not end with an error. A job holds one row in the
//! store and one entry here until it ends.
//!
//! A pool of one thread runs each job on the thread of the jobs. There, a
//! newer revision and a cancel wait until the job ends, and they then drop
//! its result. The hub of `gandr serve` has a pool at the host's width.
//!
//! # References
//!
//! - `vault:01a1c6b9-f57a-73c2-b24a-a7b1663d22a8` — anchor: §
//!   agent-layer-toolset: `check`, `replay`, `run` and `test` as the long
//!   operations of the toolset.
//! - `vault:01a1c6b9-f57a-73c2-b24a-a7c22a34adad` — anchor: the acknowledgement
//!   at once, the callback when the job ends, and the `view_update` of a
//!   running call.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::panic::AssertUnwindSafe;
use std::io;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::Sender;

#[cfg(feature = "instrument")]
use gandr_core_fork::activity::Activity;
use gandr_surface_dispatcher::Generations;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Retired;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Watch;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_lsp::DocumentVersion;
use gandr_surface_lsp::Workspace;
use gandr_surface_render_remote::DocVersion;
use gandr_surface_render_remote::Warrant;
use quenchant_shape::shape::Maybe;

use super::Answer;
use super::Ending;
use super::Held;
use super::Pending;
use super::deliver::Row;
use super::owe_answer;
use crate::face::lock;
use crate::tools;
use crate::tools::Job;

/// The verbs that walk sources, as the driver runs them on its command line.
/// The driver gives them to the toolset, so `check` and `test` print what
/// `gandr check` and `gandr test` print.
pub trait Verbs: Send + Sync
{
    /// Walk `paths` under `verb` on `pool`, as the command line walks them,
    /// and write what the verb prints to `printed` and each fault to
    /// `faulted`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The first write error, which stops the walk.
    fn walk(
        &self,
        verb: Verb,
        paths: Vec<PathBuf>,
        pool: &Pool,
        streams: (&mut dyn Write, &mut dyn Write),
    ) -> io::Result<()>;

    /// Walk as [`Verbs::walk`] walks, and mark each job of the walk on
    /// `rings`, the rings of `pool` that the hub folds for its watchers. Verbs
    /// that mark nothing walk as [`Verbs::walk`] walks.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The first write error, which stops the walk.
    #[cfg(feature = "instrument")]
    #[inline]
    fn walk_recording(
        &self,
        verb: Verb,
        paths: Vec<PathBuf>,
        (pool, _rings): (&Pool, &Activity),
        streams: (&mut dyn Write, &mut dyn Write),
    ) -> io::Result<()>
    {
        self.walk(verb, paths, pool, streams)
    }
}

/// What the thread of the jobs hears.
pub(super) enum Command
{
    /// Start the job of the call `Pending`.
    Start(Pending, Job),
    /// The hub published the document again, or forgot it.
    Changed(DocumentUri),
    /// An admission of the document ended.
    Settled(DocumentUri),
    /// End each job that a cancel or a closure names.
    End(Ending),
    /// A job of the pool ended.
    Finished,
    /// The toolset stops.
    Stop,
}

impl Ending
{
    /// Each call of `rows` that this ending names.
    ///
    /// # Specification
    /// trivial.
    fn named<'rows, Rows>(
        &self,
        rows: Rows,
    ) -> Vec<Row>
    where
        Rows: Iterator<Item = &'rows Row>,
    {
        rows.filter(|&row| {
            let Row::Call(ref group_id, ref id) = *row
            else {
                return false;
            };
            self.group_id.as_ref().is_none_or(|named| named == group_id)
                && self.id.as_ref().is_none_or(|named| named == id)
        })
        .cloned()
        .collect()
    }
}

/// What a job answers: its text, and the lines that display it.
pub(super) struct Outcome
{
    /// The text of the result.
    text: String,
    /// The lines that display the result, none when they are empty.
    display: String,
}

impl Outcome
{
    /// An answer whose text and display are `text`.
    ///
    /// # Specification
    /// trivial.
    fn line(text: String) -> Self
    {
        Self {
            display: text.clone(),
            text,
        }
    }

    /// An answer whose text is `text`, with no display.
    ///
    /// # Specification
    /// trivial.
    const fn bare(text: String) -> Self
    {
        Self {
            text,
            display: String::new(),
        }
    }
}

/// A job on the pool: its call, and the version of each document that it
/// reads.
struct Running
{
    /// The call.
    pending: Pending,
    /// Each document that the hub holds and the job reads, at the version it
    /// reads.
    documents: BTreeMap<DocumentUri, DocumentVersion>,
}

/// A replay that waits for the admission of its revision.
struct Awaited
{
    /// The call.
    pending: Pending,
    /// The document.
    document: DocumentUri,
    /// The revision whose admission it waits for.
    version: DocumentVersion,
}

/// The jobs of the toolset: on the pool, waiting for an admission, and the
/// rows that read each document.
struct Jobs
{
    /// The jobs on the pool, one slot for each call.
    generations: Generations<Row, (), Outcome>,
    /// The hub's pool.
    pool: Arc<Pool>,
    /// The jobs on the pool, by the row of their call.
    running: BTreeMap<Row, Running>,
    /// The replays that wait, by the row of their call.
    awaited: BTreeMap<Row, Awaited>,
    /// The rows that read each document, which a newer revision retires.
    documents: BTreeMap<DocumentUri, BTreeSet<Row>>,
}

/// Run each job that `commands` starts, and answer it when it ends, until
/// the toolset stops. Each job of the pool sends its end on `finished`.
///
/// # Specification
/// trivial.
pub(super) fn run<Log>(
    commands: Receiver<Command>,
    finished: Sender<Command>,
    held: &Held<'_, Log>,
) where
    Log: Write,
{
    let pool = Arc::clone(lock(held.workspace).pool());
    let mut jobs = Jobs {
        generations: Generations::waking(
            Arc::clone(&pool),
            Arc::new(move || drop(finished.send(Command::Finished))),
        ),
        pool,
        running: BTreeMap::new(),
        awaited: BTreeMap::new(),
        documents: BTreeMap::new(),
    };
    for command in commands {
        match command {
            Command::Start(pending, job) => jobs.start(pending, job, held),
            Command::Changed(document) => jobs.changed(&document, held),
            Command::Settled(document) => jobs.settled(&document, held),
            Command::End(ending) => jobs.end(&ending, held),
            Command::Finished => jobs.finished(held),
            Command::Stop => break,
        }
    }
}

impl Jobs
{
    /// Start `job`, the job of the call `pending`.
    ///
    /// # Specification
    /// trivial.
    fn start<Log>(
        &mut self,
        pending: Pending,
        job: Job,
        held: &Held<'_, Log>,
    ) where
        Log: Write,
    {
        let row = Row::Call(pending.group_id.clone(), pending.id.clone());
        match job {
            Job::Check(paths) => self.walk(row, pending, (Verb::Check(Goals::Gated), paths), held),
            Job::Test(paths) => self.walk(row, pending, (Verb::Test, paths), held),
            Job::Replay(document) => self.replay(row, pending, document, held),
            Job::Run { document, entry } => {
                #[cfg(feature = "instrument")]
                view(&pending, held);
                drop(self.running.insert(row.clone(), Running {
                    pending,
                    documents: BTreeMap::new(),
                }));
                let workspace = Arc::clone(held.workspace);
                let _submitted = self.generations.submit(row, (), move |_watch| {
                    Ok(ran(&workspace, (&document, &entry)))
                });
            },
        }
    }

    /// Walk `paths` under `verb` on the pool for the call `pending`, the row
    /// `row`, and follow each document that the hub holds under a path.
    ///
    /// # Specification
    /// trivial.
    fn walk<Log>(
        &mut self,
        row: Row,
        pending: Pending,
        (verb, paths): (Verb, Vec<PathBuf>),
        held: &Held<'_, Log>,
    ) where
        Log: Write,
    {
        let Some(verbs) = held.verbs
        else {
            answer(
                &pending,
                Outcome::bare(String::from("Error: this hub runs no verb")),
                held,
            );
            return;
        };
        let roots: BTreeSet<PathBuf> = paths
            .iter()
            .map(|path| std::path::absolute(path).unwrap_or_else(|_| path.clone()))
            .collect();
        let documents: BTreeMap<DocumentUri, DocumentVersion> = lock(held.workspace)
            .held()
            .filter(|&(uri, _version)| root_of(&uri.path(), &roots).is_some())
            .map(|(uri, version)| (uri.clone(), version))
            .collect();
        self.follow(&row, documents.keys());
        #[cfg(feature = "instrument")]
        view(&pending, held);
        drop(
            self.running
                .insert(row.clone(), Running { pending, documents }),
        );
        // The view watches the activity now, so the hub's rings exist.
        let walking = Walking {
            pool: Arc::clone(&self.pool),
            #[cfg(feature = "instrument")]
            rings: lock(held.workspace).activity().rings(),
        };
        let verbs = Arc::clone(verbs);
        let _submitted = self.generations.submit(row, (), move |watch| {
            walked(&*verbs, (verb, paths), &walking, watch)
        });
    }

    /// Answer the call `pending`, the row `row`, with the admission of the
    /// revision of `document` that the hub holds now: at once when it ended,
    /// and when it ends otherwise.
    ///
    /// # Specification
    /// trivial.
    fn replay<Log>(
        &mut self,
        row: Row,
        pending: Pending,
        document: DocumentUri,
        held: &Held<'_, Log>,
    ) where
        Log: Write,
    {
        let workspace = lock(held.workspace);
        let Some(version) = version_of(&workspace, &document)
        else {
            drop(workspace);
            let refusal = alloc::format!("Error: the hub does not hold {document}");
            answer(&pending, Outcome::bare(refusal), held);
            return;
        };
        let replayed = replayed(&workspace, &document, version);
        drop(workspace);
        if let Some(outcome) = replayed {
            answer(&pending, outcome, held);
            return;
        }
        self.follow(&row, [&document]);
        drop(self.awaited.insert(row, Awaited {
            pending,
            document,
            version,
        }));
    }

    /// Note that `row` reads each document of `documents`.
    ///
    /// # Specification
    /// trivial.
    fn follow<'documents, Documents>(
        &mut self,
        row: &Row,
        documents: Documents,
    ) where
        Documents: IntoIterator<Item = &'documents DocumentUri>,
    {
        for document in documents {
            let _fresh = self
                .documents
                .entry(document.clone())
                .or_default()
                .insert(row.clone());
        }
    }

    /// Retire each job that reads `document` at a version other than the one
    /// that the hub holds.
    ///
    /// # Specification
    /// trivial.
    fn changed<Log>(
        &mut self,
        document: &DocumentUri,
        held: &Held<'_, Log>,
    ) where
        Log: Write,
    {
        // A document that no job reads costs this lookup.
        let Some(rows) = self.documents.get(document)
        else {
            return;
        };
        let now = version_of(&lock(held.workspace), document);
        let retired: Vec<Row> = rows
            .iter()
            .filter(|&row| self.read(row, document) != now)
            .cloned()
            .collect();
        for row in retired {
            let text = retirement(document, now);
            self.close(&row, Outcome::bare(text), held);
        }
    }

    /// The version of `document` that the job of `row` reads.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &self,
        row: &Row,
        document: &DocumentUri,
    ) -> Option<DocumentVersion>
    {
        self.running.get(row).map_or_else(
            || self.awaited.get(row).map(|awaited| awaited.version),
            |running| running.documents.get(document).copied(),
        )
    }

    /// Answer each replay of `document` whose admission ended.
    ///
    /// # Specification
    /// trivial.
    fn settled<Log>(
        &mut self,
        document: &DocumentUri,
        held: &Held<'_, Log>,
    ) where
        Log: Write,
    {
        let Some(rows) = self.documents.get(document)
        else {
            return;
        };
        let workspace = lock(held.workspace);
        let ended: Vec<(Row, Outcome)> = rows
            .iter()
            .filter_map(|row| {
                let awaited = self.awaited.get(row)?;
                replayed(&workspace, document, awaited.version)
                    .map(|outcome| (row.clone(), outcome))
            })
            .collect();
        drop(workspace);
        for (row, outcome) in ended {
            self.close(&row, outcome, held);
        }
    }

    /// End each job that `ending` names, answered as cancelled.
    ///
    /// # Specification
    /// trivial.
    fn end<Log>(
        &mut self,
        ending: &Ending,
        held: &Held<'_, Log>,
    ) where
        Log: Write,
    {
        let ended = ending.named(self.running.keys().chain(self.awaited.keys()));
        for row in ended {
            self.close(&row, Outcome::bare(String::from("cancelled")), held);
        }
    }

    /// Answer each job of the pool that ended and whose call is open.
    ///
    /// # Specification
    /// trivial.
    fn finished<Log>(
        &mut self,
        held: &Held<'_, Log>,
    ) where
        Log: Write,
    {
        while let Maybe::Present(delivered) = self.generations.ready() {
            self.close(&delivered.slot, delivered.output, held);
        }
    }

    /// Answer the call of `row` with `outcome`, when it is open, and let go of
    /// its job: its slot on the pool, its wait and the documents it reads.
    ///
    /// # Specification
    /// trivial.
    fn close<Log>(
        &mut self,
        row: &Row,
        outcome: Outcome,
        held: &Held<'_, Log>,
    ) where
        Log: Write,
    {
        // A slot that ended has no generation to stop, and its entry goes.
        self.generations.retire(row);
        let (pending, documents) = match self.running.remove(row) {
            Some(running) => (running.pending, running.documents.into_keys().collect()),
            None => match self.awaited.remove(row) {
                Some(awaited) => (awaited.pending, Vec::from([awaited.document])),
                None => return,
            },
        };
        for document in documents {
            if let Some(rows) = self.documents.get_mut(&document) {
                let _removed = rows.remove(row);
                if rows.is_empty() {
                    drop(self.documents.remove(&document));
                }
            }
        }
        answer(&pending, outcome, held);
    }
}

/// The root of `roots` that `path` lies under, or is, when one holds it.
///
/// # Specification
/// trivial.
fn root_of<'roots>(
    path: &Path,
    roots: &'roots BTreeSet<PathBuf>,
) -> Option<&'roots PathBuf>
{
    path.ancestors().find_map(|ancestor| roots.get(ancestor))
}

/// The version of `document` that `workspace` holds, when it holds the
/// document.
///
/// # Specification
/// trivial.
fn version_of(
    workspace: &Workspace,
    document: &DocumentUri,
) -> Option<DocumentVersion>
{
    workspace
        .held()
        .find(|&(uri, _version)| uri == document)
        .map(|(_uri, version)| version)
}

/// The text of a job that a newer revision of `document` retired: the
/// version that the hub holds `now`, or the closure of the document.
///
/// # Specification
/// trivial.
fn retirement(
    document: &DocumentUri,
    now: Option<DocumentVersion>,
) -> String
{
    now.map_or_else(
        || alloc::format!("retired: {document} closed"),
        |version| alloc::format!("retired: {document} is at version {version}"),
    )
}

/// The answer of a replay of `document` at `version`, once the admission of
/// that revision ended: the declarations counted by the kernel's warrant, and
/// the kernel's title of each. None while the account is of another revision
/// or a declaration waits for the kernel.
///
/// # Specification
/// trivial.
fn replayed(
    workspace: &Workspace,
    document: &DocumentUri,
    version: DocumentVersion,
) -> Option<Outcome>
{
    let (id, cards) = workspace.accounted(document)?;
    if id.version != DocVersion::from(version) {
        return None;
    }
    let (mut admitted, mut refused, mut withheld, mut checked) = (0_u32, 0_u32, 0_u32, 0_u32);
    let mut display = String::new();
    for card in &cards {
        let warrant = card
            .kernel
            .as_ref()
            .map_or(Warrant::Withheld, |mark| mark.warrant);
        let count = match warrant {
            Warrant::Pending => return None,
            Warrant::Replayed => &mut admitted,
            Warrant::Refused => &mut refused,
            Warrant::Withheld => &mut withheld,
            Warrant::Checked => &mut checked,
        };
        *count = count.saturating_add(1);
        let title = card.kernel.as_ref().map_or_else(
            || <&'static str>::from(card.verdict),
            |mark| mark.title.as_str(),
        );
        display.push_str(&card.name);
        display.push_str(": ");
        display.push_str(title);
        display.push('\n');
    }
    Some(Outcome {
        text: alloc::format!(
            "replay of version {version}: {admitted} replayed, {refused} refused, {withheld} \
             withheld, {checked} checked"
        ),
        display,
    })
}

/// What a walk runs on: the hub's pool, and the rings that the hub folds
/// while a watcher follows its activity.
struct Walking
{
    /// The hub's pool.
    pool: Arc<Pool>,
    /// The rings of the pool that the hub folds, while it has a watcher.
    #[cfg(feature = "instrument")]
    rings: Option<Arc<Activity>>,
}

impl Walking
{
    /// Walk `paths` under `verb` with `verbs`, marking each job on the rings
    /// when the hub folds them.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The first write error, which stops the walk.
    fn walk(
        &self,
        verbs: &dyn Verbs,
        (verb, paths): (Verb, Vec<PathBuf>),
        streams: (&mut dyn Write, &mut dyn Write),
    ) -> io::Result<()>
    {
        #[cfg(feature = "instrument")]
        if let Some(ref rings) = self.rings {
            return verbs.walk_recording(verb, paths, (&self.pool, rings), streams);
        }
        verbs.walk(verb, paths, &self.pool, streams)
    }
}

/// The answer of a walk of `paths` under `verb` on `walking` by `verbs`: the
/// verdict line, and each line that the verb prints. A walk whose job
/// `watch` retires stops at its next write.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Retired`] once the job is retired.
fn walked(
    verbs: &dyn Verbs,
    (verb, paths): (Verb, Vec<PathBuf>),
    walking: &Walking,
    watch: &Watch,
) -> Result<Outcome, Retired>
{
    let (mut printed, mut faulted) = (Printed::new(watch), Printed::new(watch));
    // A panic of the verb ends its job alone, not the thread of the jobs.
    let walked = std::panic::catch_unwind(AssertUnwindSafe(|| {
        walking.walk(verbs, (verb, paths), (&mut printed, &mut faulted))
    }));
    watch.poll()?;
    let mut display = String::from_utf8_lossy(&printed.bytes).into_owned();
    let text = match walked {
        Ok(Ok(())) => display.lines().rfind(|line| !line.is_empty()).map_or_else(
            || String::from("Error: the verb printed nothing"),
            String::from,
        ),
        Ok(Err(error)) => alloc::format!("Error: {error}"),
        Err(_panic) => String::from("Error: the verb panicked"),
    };
    display.push_str(&String::from_utf8_lossy(&faulted.bytes));
    Ok(Outcome { text, display })
}

/// The answer of a run of the declaration `entry` of `document`, as its run
/// lens runs it, under the lock of `workspace`.
///
/// # Specification
/// trivial.
fn ran(
    workspace: &Mutex<Workspace>,
    (document, entry): (&DocumentUri, &String),
) -> Outcome
{
    let ran = tools::ran(&lock(workspace), (document, entry));
    match ran {
        Ok(line) => Outcome::line(line),
        Err(refusal) => Outcome::bare(alloc::format!("Error: {refusal}")),
    }
}

/// Answer the call `pending` with `outcome`: keep the answer in the store,
/// owe its result, and end the view of its job.
///
/// # Specification
/// trivial.
fn answer<Log>(
    pending: &Pending,
    outcome: Outcome,
    held: &Held<'_, Log>,
) where
    Log: Write,
{
    let Outcome { text, display } = outcome;
    let answer = Answer {
        group_id: pending.group_id.clone(),
        id: pending.id.clone(),
        text,
        display: (!display.is_empty()).then_some(display),
        version: None,
        subscription: None,
    };
    owe_answer(pending, &answer, held.store, held.deliveries, held.log);
    #[cfg(feature = "instrument")]
    lock(held.subscriptions).unview(
        &Row::Call(pending.group_id.clone(), pending.id.clone()),
        held.deliveries,
    );
}

/// Start the view of the job of `pending`: each tick of the hub's activity
/// reaches it as a view update until it ends.
///
/// # Specification
/// trivial.
#[cfg(feature = "instrument")]
fn view<Log>(
    pending: &Pending,
    held: &Held<'_, Log>,
) where
    Log: Write,
{
    let viewed = lock(held.subscriptions).view(pending);
    if let Err(error) = viewed {
        drop(writeln!(
            lock(held.log),
            "the toolset did not watch the activity for the call {} of {}: {error}",
            pending.id,
            pending.group_id
        ));
    }
}

/// The lines that a verb writes, kept until its job ends. A write fails once
/// the job is retired, so the walk stops there.
struct Printed<'watch>
{
    /// The job's watch.
    watch: &'watch Watch,
    /// The bytes written.
    bytes: Vec<u8>,
}

impl<'watch> Printed<'watch>
{
    /// No line yet, for the job that `watch` watches.
    ///
    /// # Specification
    /// trivial.
    const fn new(watch: &'watch Watch) -> Self
    {
        Self {
            watch,
            bytes: Vec::new(),
        }
    }
}

impl Write for Printed<'_>
{
    /// Keep `buf`, unless the job is retired.
    ///
    /// # Specification
    /// trivial.
    fn write(
        &mut self,
        buf: &[u8],
    ) -> io::Result<usize>
    {
        self.watch.poll().map_err(io::Error::other)?;
        self.bytes.extend_from_slice(buf);
        Ok(buf.len())
    }

    /// Nothing waits to be written.
    ///
    /// # Specification
    /// trivial.
    fn flush(&mut self) -> io::Result<()>
    {
        Ok(())
    }
}
