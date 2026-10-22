//! The workspace's diagnostics: each source under the opened folders that no
//! editor holds, judged as an editor's copy is and reported to a client that
//! pulls `workspace/diagnostic`.
//!
//! # A sweep, one source at a time, behind the open documents
//!
//! A pull is answered once every source it reports is current: judged at the
//! connection's verbosity and spelling over a closure that still reads as it
//! did. A source whose report is not current is judged on the worker pool as
//! an open document is, in a session of its own, its imports read as the
//! editors hold them, and the pull waits for it. The connection judges one
//! such source at a time, and starts the next only while none of its open
//! documents is being judged, so an edit waits for at most one source's
//! judgement; once none is left, every pull waiting is answered.
//!
//! The sweep works in passes. A pass lists the sources once, and each step
//! resumes it after the sources it found current, so a step looks at the
//! files of one source rather than of every source before it. At its end the
//! sources are listed and looked at once more: a source written behind the
//! pass, added, or reading an import written since is judged again before any
//! pull is answered.
//!
//! A report stays current while every file its judgement read is unchanged:
//! the source, and every path an import of its closure names, resolved or not.
//! A file is seen by its length and modification time, a file an editor holds
//! by the digest of the editor's text, and a path with no file as missing. A
//! file written between its read and the look at it is seen at its next
//! change.
//!
//! Each report is named by the digest of its JSON text, as a document's pull
//! is, and answered `unchanged` when the pull names that digest. A source an
//! editor holds is left out: its own pull answers it.
//!
//! The alternatives were judging every source when the pull arrives, which
//! holds the connection while the folder is judged, and judging the sources
//! alongside the open documents, which makes an edit wait for the folder. The
//! choice reverses if a folder's sources outnumber what one connection judges
//! between two pulls: the sweep then needs a pool of its own.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;
use std::time::SystemTime;

use anodized::spec;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_dispatcher::Shadows;
use gandr_surface_pretty::Spelling;

use crate::protocol::Diagnostic;
use crate::protocol::DiagnosticReport;
use crate::protocol::DocumentUri;
use crate::protocol::WorkspaceDiagnosticParams;
use crate::protocol::WorkspaceDocumentReport;
use crate::protocol::WorkspaceReport;
use crate::rpc::RequestId;
use crate::tokens::ResultId;

/// How a file read for a judgement was when it was read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Seen
{
    /// A file on disk, by its length and modification time.
    Disk
    {
        /// Its length in bytes.
        length: u64,
        /// When it was last modified, where the platform keeps it.
        modified: Option<SystemTime>,
    },
    /// A file an editor holds, by the digest of the editor's text.
    Held(ResultId),
    /// A path with no file.
    Missing,
}

impl Seen
{
    /// How the file at `path` is now, an editor's copy read as `shadows` holds
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn now(
        path: &Path,
        shadows: &dyn Shadows,
    ) -> Self
    {
        if let Some(text) = shadows.shadowed(path) {
            return Self::Held(ResultId::of_json(<&str>::from(text)));
        }
        std::fs::metadata(path).map_or(Self::Missing, |metadata| Self::Disk {
            length: metadata.len(),
            modified: metadata.modified().ok(),
        })
    }
}

/// What a source's judgement read and reported.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Swept
{
    /// Each file the judgement read, as it was.
    pub closure: Vec<(PathBuf, Seen)>,
    /// The verbosity and spelling it was reported at.
    pub rendering: (Verbosity, Spelling),
    /// What it reported.
    pub diagnostics: Vec<Diagnostic>,
}

/// A source being judged for the workspace's diagnostics.
#[derive(Debug)]
pub struct Sweeping
{
    /// The source's URI, the judgement's slot.
    pub uri: DocumentUri,
    /// Its path.
    pub path: PathBuf,
    /// The text judged.
    pub text: String,
    /// Each file the judgement reads, as it was.
    pub closure: Vec<(PathBuf, Seen)>,
    /// The verbosity and spelling it is judged at.
    pub rendering: (Verbosity, Spelling),
}

/// A sweep's pass over the sources: listed once when it starts, and resumed
/// where it stopped at each step.
#[derive(Debug)]
enum Pass
{
    /// No pass: the next step lists the sources.
    Idle,
    /// The sources listed, the first `current` of them found current.
    Running
    {
        /// The sources, as listed when the pass started.
        sources: Vec<PathBuf>,
        /// How many of them the pass found current, in order.
        current: usize,
    },
    /// The sources, each found current at the pass's end.
    Done(Vec<PathBuf>),
}

/// One connection's sweep: what each source last reported, the pass over the
/// sources, and the pulls waiting for it.
#[derive(Debug)]
pub struct Sweep
{
    /// Each source's last report, by its path.
    reports: BTreeMap<PathBuf, Swept>,
    /// The pass the pulls waiting are answered at the end of.
    pass: Pass,
    /// The pulls waiting, in the order read.
    waiting: Vec<(RequestId, WorkspaceDiagnosticParams)>,
}

/// The report `reports` keeps for `path` when it is current at `rendering`,
/// each file read as `shadows` holds it: reported at that verbosity and
/// spelling over files that each read as they did, as [`Seen::now`] sees them.
///
/// # Specification
/// trivial.
fn current<'reports>(
    reports: &'reports BTreeMap<PathBuf, Swept>,
    path: &Path,
    rendering: (Verbosity, Spelling),
    shadows: &dyn Shadows,
) -> Option<&'reports Swept>
{
    reports.get(path).filter(|swept| {
        swept.rendering == rendering
            && swept
                .closure
                .iter()
                .all(|&(ref read, ref seen)| Seen::now(read, shadows) == *seen)
    })
}

impl Sweep
{
    /// No report, no pass, and no pull waiting.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            reports: BTreeMap::new(),
            pass: Pass::Idle,
            waiting: Vec::new(),
        }
    }

    /// Hold the pull `id` with `params` until every source it reports is
    /// current.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn wait(
        &mut self,
        id: RequestId,
        params: WorkspaceDiagnosticParams,
    )
    {
        self.waiting.push((id, params));
    }

    /// The pulls waiting, in the order read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn waiting(&self) -> &[(RequestId, WorkspaceDiagnosticParams)]
    {
        &self.waiting
    }

    /// Take every pull waiting.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn release(&mut self) -> Vec<(RequestId, WorkspaceDiagnosticParams)>
    {
        core::mem::take(&mut self.waiting)
    }

    /// Keep what `sweeping` reported, `diagnostics`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn keep(
        &mut self,
        sweeping: Sweeping,
        diagnostics: Vec<Diagnostic>,
    )
    {
        let _replaced = self.reports.insert(sweeping.path, Swept {
            closure: sweeping.closure,
            rendering: sweeping.rendering,
            diagnostics,
        });
    }

    /// The next source the pass finds not current at `rendering`, each file
    /// read as `shadows` holds it, the sources listed by `list` when a pass
    /// starts and when it ends.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: with no pass, one starts over the sources `list` answers. The
    ///   pass resumes after the sources it found current: the first source from
    ///   there with no report, one reported at another verbosity or spelling,
    ///   or one that read a file which now differs from how it was read, as
    ///   [`Seen::now`] sees it, is answered, and the pass stops at it. At the
    ///   pass's end the sources are listed again and each is looked at again:
    ///   the first not current is answered and the pass resumes at it over the
    ///   new list; with none, the pass is done, and none is answered until
    ///   [`Sweep::finished`] takes it.
    /// - provides: the source a sweep judges next, each source looked at once a
    ///   pass but at the pass's end.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source never judged, one judged and unchanged, and
    ///   one whose import was rewritten after the pass looked at it, each
    ///   answered as stated.
    /// - witness: `server::tests::a_workspace_pull_reports_each_source_no_editor_holds_1824`
    /// - witness: `sweep::tests::a_pass_looks_again_at_a_source_written_behind_it_1824`
    #[spec(ensures: |ret| ret.is_none() || matches!(self.pass, Pass::Running { .. }))]
    #[inline]
    pub fn next(
        &mut self,
        list: &dyn Fn() -> Vec<PathBuf>,
        rendering: (Verbosity, Spelling),
        shadows: &dyn Shadows,
    ) -> Option<PathBuf>
    {
        let (sources, from) = match core::mem::replace(&mut self.pass, Pass::Idle) {
            Pass::Idle => (list(), 0_usize),
            Pass::Running { sources, current } => (sources, current),
            Pass::Done(sources) => {
                self.pass = Pass::Done(sources);
                return None;
            },
        };
        let stale = |sources: &[PathBuf], from: usize| {
            sources
                .iter()
                .enumerate()
                .skip(from)
                .find(|&(_, path)| current(&self.reports, path, rendering, shadows).is_none())
                .map(|(at, path)| (at, path.clone()))
        };
        if let Some((at, path)) = stale(&sources, from) {
            self.pass = Pass::Running {
                sources,
                current: at,
            };
            return Some(path);
        }
        let listed = list();
        if let Some((at, path)) = stale(&listed, 0_usize) {
            self.pass = Pass::Running {
                sources: listed,
                current: at,
            };
            return Some(path);
        }
        self.pass = Pass::Done(listed);
        None
    }

    /// The sources of the pass that is done, which ends it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the sources [`Sweep::next`] found each current at the end of
    ///   its pass, once, the next step starting a pass of its own; none while a
    ///   pass runs or none has started.
    /// - provides: the sources a pull is answered over.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pass done taken once, and a running pass not.
    /// - witness: `sweep::tests::a_pass_looks_again_at_a_source_written_behind_it_1824`
    #[spec(ensures: |ret| ret.is_none() || matches!(self.pass, Pass::Idle))]
    #[inline]
    pub fn finished(&mut self) -> Option<Vec<PathBuf>>
    {
        match core::mem::replace(&mut self.pass, Pass::Idle) {
            Pass::Done(sources) => Some(sources),
            running @ (Pass::Idle | Pass::Running { .. }) => {
                self.pass = running;
                None
            },
        }
    }

    /// The report of each of `sources` that holds one, against the ids
    /// `params` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one report per source of `sources` with a report kept, in
    ///   order, at the source's `file` URI and no version: what it reported,
    ///   named by [`ResultId::of_json`] of it, unchanged when `params` names
    ///   that id for the URI, and whole otherwise.
    /// - provides: the answer to `workspace/diagnostic`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal reported whole, the same report named by
    ///   its id answered unchanged, and a source rewritten to check reported
    ///   whole and empty.
    /// - witness: `server::tests::a_workspace_pull_reports_each_source_no_editor_holds_1824`
    #[spec(ensures: |ret| ret.items.len() <= sources.len())]
    #[inline]
    #[must_use]
    pub fn report(
        &self,
        sources: &[PathBuf],
        params: &WorkspaceDiagnosticParams,
    ) -> WorkspaceReport
    {
        let previous: BTreeMap<&DocumentUri, &ResultId> = params
            .previous_result_ids
            .iter()
            .map(|held| (&held.uri, &held.value))
            .collect();
        WorkspaceReport {
            items: sources
                .iter()
                .filter_map(|path| {
                    let swept = self.reports.get(path)?;
                    let uri = DocumentUri::of_path(path)?;
                    let result_id = ResultId::of_json(&swept.diagnostics);
                    let report = if previous.get(&uri) == Some(&&result_id) {
                        DiagnosticReport::Unchanged { result_id }
                    }
                    else {
                        DiagnosticReport::Full {
                            result_id,
                            items: swept.diagnostics.clone(),
                        }
                    };
                    Some(WorkspaceDocumentReport {
                        uri,
                        version: None,
                        report,
                    })
                })
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;
    use std::path::PathBuf;

    use gandr_surface_diagnostics::Verbosity;
    use gandr_surface_dispatcher::Unshadowed;
    use gandr_surface_pretty::Spelling;

    use super::Seen;
    use super::Sweep;
    use super::Sweeping;
    use crate::protocol::DocumentUri;

    #[test]
    fn a_pass_looks_again_at_a_source_written_behind_it_1824()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-sweep-pass-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch tree is created");
        let sources: Vec<PathBuf> = ["a.gandr", "b.gandr"]
            .into_iter()
            .map(|file| directory.join(file))
            .collect();
        for path in &sources {
            std::fs::write(path, "def x : Integer ;\n").expect("the source is written");
        }
        let rendering = (Verbosity::User, Spelling::Unicode);
        let mut sweep = Sweep::new();
        let keep = |sweep: &mut Sweep, path: &PathBuf| {
            sweep.keep(
                Sweeping {
                    uri: DocumentUri::of_path(path).expect("a path names a file URI"),
                    path: path.clone(),
                    text: String::new(),
                    closure: Vec::from([(path.clone(), Seen::now(path, &Unshadowed))]),
                    rendering,
                },
                Vec::new(),
            );
        };
        let list = || sources.clone();
        let mut judged = Vec::new();
        while let Some(path) = sweep.next(&list, rendering, &Unshadowed) {
            keep(&mut sweep, &path);
            judged.push(path.clone());
            if judged.len() == 2_usize {
                std::fs::write(&sources[0_usize], "def x : Integer ;\ndef x = 1 ;\n")
                    .expect("the first source is rewritten behind the pass");
            }
            assert!(judged.len() <= 3_usize, "the pass ends: {judged:?}");
        }
        assert_eq!(
            judged,
            [
                sources[0_usize].clone(),
                sources[1_usize].clone(),
                sources[0_usize].clone()
            ],
            "each source is judged in order, and the one written behind the pass again at its end"
        );
        assert_eq!(
            sweep.next(&list, rendering, &Unshadowed),
            None,
            "a pass done answers no source until it is taken"
        );
        assert_eq!(
            sweep.finished(),
            Some(sources.clone()),
            "the pass done is taken once"
        );
        assert_eq!(sweep.finished(), None, "and only once");
        assert_eq!(
            sweep.next(&list, rendering, &Unshadowed),
            None,
            "a new pass over current sources is done at once"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }
}
