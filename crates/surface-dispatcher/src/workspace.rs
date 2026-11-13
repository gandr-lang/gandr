//! A workspace: the packages a `workspace.gandr` gathers, found above them.
//!
//! # A workspace names its members
//!
//! [`Workspace::discover`] walks up from a path to the first directory that
//! holds `workspace.gandr`, as Cargo walks up to the `Cargo.toml` holding
//! `[workspace]`. The workspace is not a package: its source declares no
//! package source. It states what its members share as a model of
//! `Gandr.Workspace`, which each member's `package.gandr` imports and reads,
//! and it names its members by a free-standing `pub def members :
//! List(String)`, its `List` listed from `std.list`, each a directory below the
//! workspace that roots a package.
//!
//! [`Workspace::members`] reads that list by checking the workspace's source
//! alone and running `members`, so the list is gandr and never a second
//! manifest language. The same run reads the fields of the model. The checker
//! writes `workspace.gandr.toml` beside the source from these fields. A verb
//! works on every member when it gets the directory of the workspace. It does
//! the same when it gets no path in a workspace but outside all of its
//! packages. All the packages below the workspace share one
//! `workspace.gandr.lock`.
//!
//! # References
//!
//! - `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: a package's
//!   metadata is written in gandr rather than in a manifest language, and a
//!   workspace's members are named the same way.

use core::convert::Infallible;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::HostGrant;
use crate::component::lay_out;
use crate::compose::Composed;
use crate::compose::Lowered;
use crate::compose::LoweringCount;
use crate::compose::judge_lowering;
use crate::compose::lower_unit_source;
use crate::engine::Engine;
use crate::entry::answered::Answered;
use crate::entry::answered::Spelling;
use crate::entry::answered::Unran;
use crate::entry::evaluation::Terminal;
use crate::entry::evaluation::declaration_name;
use crate::package::Package;
use crate::package::WorkspaceManifest;
use crate::package::package_root;
use crate::package::toolchain::Separated;
use crate::package::toolchain::Toolchain;
use crate::program::Program;
use crate::root::classify;
use crate::walk::SourceFault;
use crate::walk::Standing;
use crate::walk::Step;

/// The file name of a workspace's source, at the workspace's root.
pub const WORKSPACE: &str = "workspace.gandr";

/// The file name of the manifest that the checker writes beside the source of
/// a workspace.
pub const WORKSPACE_MANIFEST: &str = "workspace.gandr.toml";

/// The declaration of a workspace's source that names its members.
const MEMBERS: &str = "members";

/// The fields of the `Workspace` model that the manifest of a workspace
/// records, in the order in which the checker reads them.
const FIELDS: [&str; 4] = [
    "Workspace.version",
    "Workspace.gandr",
    "Workspace.features",
    "Workspace.systems",
];

/// A workspace: the directory holding its source.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Workspace
{
    /// The directory holding [`WORKSPACE`].
    root: PathBuf,
}

impl Workspace
{
    /// The workspace `from` sits in, found by walking up from it to the first
    /// directory holding a workspace source.
    ///
    /// # Specification
    /// - requires: nothing; a relative path is read against the working
    ///   directory.
    /// - ensures: the first directory from `from` up — `from` itself when it is
    ///   a directory, else the directory holding it — that holds [`WORKSPACE`]
    ///   as a file, canonical; `Unworkspaced` when no directory up to the
    ///   filesystem's root holds one, or `from` cannot be canonicalized.
    /// - provides: the workspace search a verb in no package reads.
    /// - fails: a path in no workspace is the typed absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the workspace's directory, a member's leaf and a
    ///   directory below it in no package each find the workspace, and a
    ///   directory with no workspace above it finds none.
    /// - witness: `tests::package::a_workspace_walks_every_member_it_names_2687`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(ref workspace) => workspace.root.join(WORKSPACE).is_file(),
        Maybe::Absent(workspace_root::Absent::Unworkspaced) => true,
    })]
    #[inline]
    pub fn discover(from: &Path) -> Maybe<Self, workspace_root::Absent>
    {
        let unworkspaced = Maybe::Absent(workspace_root::Absent::Unworkspaced);
        let Ok(canonical) = from.canonicalize()
        else {
            return unworkspaced;
        };
        let start = if canonical.is_dir() {
            canonical.as_path()
        }
        else {
            match canonical.parent() {
                Some(parent) => parent,
                None => return unworkspaced,
            }
        };
        start
            .ancestors()
            .find(|directory| directory.join(WORKSPACE).is_file())
            .map_or(unworkspaced, |root| {
                Maybe::Present(Self {
                    root: root.to_path_buf(),
                })
            })
    }

    /// The directory holding the workspace's source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root(&self) -> &Path
    {
        &self.root
    }

    /// The workspace's source, [`WORKSPACE`] at its root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn source(&self) -> PathBuf
    {
        self.root.join(WORKSPACE)
    }

    /// The path of the manifest of the workspace: [`WORKSPACE_MANIFEST`]
    /// beside its source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn manifest(&self) -> PathBuf
    {
        self.root.join(WORKSPACE_MANIFEST)
    }

    /// The packages that the workspace names, in the order of its `members`.
    /// Also the workspace, with the manifest that its model states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the function reads the source of the workspace. It checks the
    ///   source over the sources that it imports, as the walk lays them out. In
    ///   this one check, it runs `members` and the `version`, `gandr`,
    ///   `features` and `systems` of the `Workspace` model. Each string of the
    ///   list is a directory below the root. [`Package::discover`] finds a
    ///   package from this directory, and the package root must be this
    ///   directory. The manifest holds `version`, the members as the list names
    ///   them, and the toolchain that [`Toolchain::read`] reads. [`Unstated`]
    ///   names the first field that is not declared or that runs to no string.
    ///   It also names a `gandr` that states no constraint.
    /// - provides: the packages that a verb works on in the workspace, and the
    ///   manifest that `gandr check` writes for it.
    /// - fails: [`Unmembered::Unread`] for a source that cannot be read,
    ///   [`Unmembered::Refused`] for one that does not compose or is refused as
    ///   a whole, [`Unmembered::Undeclared`] for one declaring no `members`,
    ///   [`Unmembered::Unlisted`] for `members` running to no list of strings,
    ///   and [`Unmembered::Unpackaged`] for a member rooting no package.
    /// - panics: none.
    /// - executable: none — `members` is run on the program's machine, which a
    ///   predicate could only check by running it again; the witness observes
    ///   each outcome.
    ///
    /// # Errors
    /// The first of the faults above that the workspace meets.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a workspace naming two members reads both in order;
    ///   one naming a directory with no package source, and one whose `members`
    ///   is a string, are refused with what they state.
    /// - witness: `tests::package::a_workspace_walks_every_member_it_names_2687`
    #[inline]
    pub fn members<E>(&self) -> Result<(Vec<Package>, Gathered), Unmembered>
    where
        E: Engine,
    {
        let [came, version, gandr, features, systems] = match ran_alone::<E, 5>(
            &self.source(),
            [MEMBERS, FIELDS[0], FIELDS[1], FIELDS[2], FIELDS[3]].map(SurfaceName::from),
        ) {
            Ok(came) => came,
            Err(Unran::Unread { message }) => return Err(Unmembered::Unread { message }),
            Err(Unran::Refused { why }) => return Err(Unmembered::Refused { why }),
        };
        let came = match came {
            Maybe::Present(came) => came,
            Maybe::Absent(declaration_name::Absent::Undeclared) => {
                return Err(Unmembered::Undeclared);
            },
        };
        let Some(named) = Spelling::from(came.as_str()).listed()
        else {
            return Err(Unmembered::Unlisted { came });
        };
        let packages = named
            .iter()
            .map(|member| {
                let directory = self.root.join(member);
                let rooted = directory.canonicalize().ok();
                match Package::discover(&directory) {
                    Maybe::Present(package) if rooted.as_deref() == Some(package.root()) => {
                        Ok(package)
                    },
                    Maybe::Present(_) | Maybe::Absent(package_root::Absent::Unpackaged) => {
                        Err(Unmembered::Unpackaged {
                            member: member.clone(),
                        })
                    },
                }
            })
            .collect::<Result<Vec<Package>, Unmembered>>()?;
        let manifest = stated([version, gandr, features, systems]).and_then(
            |[version, gandr, features, systems]| {
                let toolchain =
                    Toolchain::read(gandr.clone(), Separated(&features), Separated(&systems))
                        .map_err(|_unconstrained| Unstated::Unconstrained { came: gandr })?;
                Ok(WorkspaceManifest::new(version, named, toolchain))
            },
        );
        Ok((packages, Gathered {
            workspace: self.clone(),
            manifest,
        }))
    }
}

/// Each of the [`FIELDS`] of a workspace model as a string. The function
/// decodes the string from the spelling of the run of the field.
///
/// # Specification
/// - requires: `came` holds what each of [`FIELDS`] ran to, in order.
/// - ensures: the string of each field, which is the decoded content of a
///   quoted spelling. [`Unstated::Undeclared`] names the first field that the
///   source does not declare. [`Unstated::Unstrung`] names the first field
///   whose run is not a string.
/// - fails: as `ensures`.
/// - panics: none.
/// - executable: none — a clause would state the body again.
///
/// # Errors
/// [`Unstated::Undeclared`] and [`Unstated::Unstrung`].
///
/// # Adequacy
/// - hypothesis: L3 — a workspace's model reads each field, and one leaving
///   `gandr` undefined is refused at it.
/// - witness: `tests::package::a_workspace_s_packages_share_one_lock_4921`
fn stated(came: [Maybe<String, declaration_name::Absent>; 4]) -> Result<[String; 4], Unstated>
{
    let mut read: [String; 4] = Default::default();
    for ((slot, came), field) in read.iter_mut().zip(came).zip(FIELDS) {
        let came = match came {
            Maybe::Present(came) => came,
            Maybe::Absent(declaration_name::Absent::Undeclared) => {
                return Err(Unstated::Undeclared { field });
            },
        };
        *slot = match Spelling::from(came.as_str()).quoted() {
            Some((string, rest)) if rest == Spelling::from("") => string,
            Some(_) | None => return Err(Unstated::Unstrung { field, came }),
        };
    }
    Ok(read)
}

/// A workspace that a verb works on, and the manifest that its model states.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Gathered
{
    /// The workspace.
    pub workspace: Workspace,
    /// What its `Workspace` model states for its manifest, or why the model
    /// states no manifest.
    pub manifest: Result<WorkspaceManifest, Unstated>,
}

/// Why the model of a workspace states no manifest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unstated
{
    /// The source of the workspace does not declare the field.
    Undeclared
    {
        /// The field, by its path from the top level of the source.
        field: &'static str,
    },
    /// The field runs to a value that is not a string.
    Unstrung
    {
        /// The field, by its path from the top level of the source.
        field: &'static str,
        /// The spelling of the value that its run gives.
        came: String,
    },
    /// `Workspace.gandr` states no constraint.
    Unconstrained
    {
        /// The value that it runs to.
        came: String,
    },
}

impl core::fmt::Display for Unstated
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Undeclared { field } => write!(
                f,
                "`{WORKSPACE}` does not declare `{field}`. The checker writes no \
                 `{WORKSPACE_MANIFEST}`. Import `std.build` and declare `module Workspace : \
                 Model(Gandr.Workspace)` in it."
            ),
            Self::Unstrung { field, ref came } => write!(
                f,
                "`{field}` runs to `{came}`, which is not a string. The checker writes no \
                 `{WORKSPACE_MANIFEST}`."
            ),
            Self::Unconstrained { ref came } => write!(
                f,
                "`{}` is `{came}`, which states no constraint. The checker writes no \
                 `{WORKSPACE_MANIFEST}`. Write `>= <major>.<minor>`, or write nothing to accept \
                 all versions.",
                FIELDS[1]
            ),
        }
    }
}

impl core::error::Error for Unstated
{
}

/// What each declaration of `names` in the source at `source` runs to,
/// spelled, the source checked once, alone over the sources it imports.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the source read, laid out over its imports as the walk lays them
///   out, lowered and judged under the strict root, and each of `names` run on
///   the program's machine in order, its value spelled; `Undeclared` at a name
///   the source declares nowhere.
/// - provides: the one reading of the values a source states about its own
///   workspace, site or manifold: a workspace's `members`, a site's model and a
///   manifold's.
/// - fails: [`Unran::Unread`] for a source that cannot be read, and
///   [`Unran::Refused`] for one that does not compose or is refused as a whole.
/// - panics: none.
/// - executable: none — each name is run on the program's machine, which a
///   predicate could only check by running it again.
///
/// # Errors
/// [`Unran`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses of [`Workspace::members`], [`Site::read`]
///   and [`Manifold::read`].
/// - witness: `tests::package::a_workspace_walks_every_member_it_names_2687`
/// - witness: `tests::manifold::a_site_and_a_manifold_read_from_their_files_3374`
///
/// [`Site::read`]: crate::manifold::Site::read
/// [`Manifold::read`]: crate::manifold::Manifold::read
#[inline]
pub fn ran_alone<E, const NAMES: usize>(
    source: &Path,
    names: [SurfaceName<'_>; NAMES],
) -> Result<[Maybe<String, declaration_name::Absent>; NAMES], Unran>
where
    E: Engine,
{
    alone::<E, _>(source, |program| {
        names.map(|name| match program.named(name) {
            Maybe::Present(constant) => Maybe::Present(E::evaluate(program, constant).to_string()),
            Maybe::Absent(absent) => Maybe::Absent(absent),
        })
    })
}

/// What the function `function` of the source at `source` answers at the
/// string `argument`, read as its host reads it, the source checked once as
/// [`ran_alone`] checks it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the source checked as [`ran_alone`] checks it, and `function`
///   forced and applied to `argument` on the program's machine, every operation
///   no handler of the run claims declined. A run answering a string is
///   [`Answered::Text`] holding it whole, whatever seal keeps the answer's
///   type; any other end is [`Answered::Other`]. `Undeclared` when the source
///   declares no `function`.
/// - provides: a host's reading of a value only it may hold, such as the secret
///   a site's `Secrets` model answers, which no printed run spells.
/// - fails: as [`ran_alone`].
/// - panics: none.
/// - executable: none — the function is run on the program's machine, which a
///   predicate could only check by running it again.
///
/// # Errors
/// [`Unran`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus secrets model answers the far site's secret at
///   its name, sealed as it is, and a source declaring no such function is
///   undeclared; an answer other than a string is not generated.
/// - witness: `tests::manifold::a_site_reads_its_secret_from_the_model_given_3375`
#[inline]
pub fn answered_alone<E>(
    source: &Path,
    function: SurfaceName<'_>,
    argument: StringLiteral,
) -> Result<Maybe<Answered, declaration_name::Absent>, Unran>
where
    E: Engine,
{
    alone::<E, _>(source, |program| {
        let constant = match program.named(function) {
            Maybe::Present(constant) => constant,
            Maybe::Absent(absent) => return Maybe::Absent(absent),
        };
        let mut core = CoreArena::new();
        let argument = core.value_literal(Literal::Text(argument));
        let read = match E::call(program, constant, &[argument], &mut core, &mut Unhosted) {
            Ok(Terminal::Read(read)) => read,
            Ok(Terminal::Ended(ended)) => {
                return Maybe::Present(Answered::Other(ended.to_string()));
            },
            Err(never) => match never {},
        };
        Maybe::Present(match core.computation(read) {
            Some(&Computation::Return(answer)) => match core.value(answer) {
                Some(&Value::Literal(Literal::Text(ref text))) => {
                    Answered::Text(String::from(text.as_ref()))
                },
                Some(_) | None => Answered::Other(String::from("a value other than a string")),
            },
            Some(_) | None => Answered::Other(String::from("a computation other than a return")),
        })
    })
}

/// What `read` makes of the program the source at `source` composes to,
/// checked alone over the sources it imports.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Unran`], as [`ran_alone`].
fn alone<E, Read>(
    source: &Path,
    read: impl FnOnce(&mut Program<'_>) -> Read,
) -> Result<Read, Unran>
where
    E: Engine,
{
    let text = std::fs::read_to_string(source).map_err(|error| Unran::Unread {
        message: error.to_string(),
    })?;
    stepped_alone::<E, _, _>(source, SourceText::from(text.as_str()), |step| match step {
        Step::Source {
            composed: Composed::Settled { mut program, .. },
            ..
        } => Ok(read(&mut program)),
        Step::Source {
            composed: Composed::Refused(refusal),
            ..
        } => Err(Unran::Refused {
            why: refusal.to_string(),
        }),
        Step::Fault { fault, .. } => Err(Unran::Refused {
            why: fault.to_string(),
        }),
    })?
}

/// What `read` makes of the step the source at `source`, written `text`,
/// takes through the pipeline, checked as [`ran_alone`] checks a source.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `text` laid out at `source` over the sources it imports, as the
///   walk lays a source out, lowered and judged under the strict root; `read`
///   given the step the walk would yield for it: the source under the root
///   `source` is classified into, standing as its composition decides, or the
///   fault composing it met.
/// - provides: a judgement of a source's text other than its file's, with what
///   `check` reports of it, such as the program a deployment check writes a
///   check into.
/// - fails: [`Unran::Refused`] when the grammar does not build.
/// - panics: none.
/// - executable: none — as [`ran_alone`].
///
/// # Errors
/// [`Unran::Refused`].
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses of [`ran_alone`], and of the deployment
///   check judged over a program's text.
/// - witness: `tests::manifold::a_site_and_a_manifold_read_from_their_files_3374`
/// - witness: `tests::manifold::a_world_s_row_is_judged_against_its_site_s_offer_3523`
#[inline]
pub fn stepped_alone<E, Read, Reader>(
    source: &Path,
    text: SourceText<'_>,
    read: Reader,
) -> Result<Read, Unran>
where
    E: Engine,
    Reader: FnOnce(Step<'_>) -> Read,
{
    let grammar = built_in().map_err(|error| Unran::Refused {
        why: error.to_string(),
    })?;
    let root = classify(source);
    let laid = lay_out(&grammar, source, root, text);
    let laid_text = SourceText::from(laid.text.as_str());
    let mut lowerings = LoweringCount::default();
    let step = match lower_unit_source(&grammar, laid_text, &laid.unit, &mut lowerings).and_then(
        |lowering| {
            judge_lowering::<E>(
                CorpusRoot::Strict,
                (lowering, laid_text),
                &HostGrant::UNBOUNDED,
                laid.base,
            )
        },
    ) {
        Ok(composed) => Step::Source {
            path: source,
            root,
            text: laid_text,
            base: laid.base,
            standing: Standing::of(root, &composed),
            composed,
        },
        Err(fault) => Step::Fault {
            path: source,
            fault: SourceFault::Compose(fault),
        },
    };
    Ok(read(step))
}

/// What `read` makes of the module the source at `source`, written `text`,
/// lowers to over the sources it imports, and of the unit's text its spans
/// index, before anything judges it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `text` laid out at `source` over the sources it imports, as the
///   walk lays a source out, and lowered; `read` given the module and the
///   unit's text.
/// - provides: what a source declares, read without judging it: the worlds a
///   deployment's program declares and what each requires, and the offer a
///   site's file writes.
/// - fails: [`Unran::Refused`] for a text that does not lower, or is refused as
///   a whole.
/// - panics: none.
/// - executable: none — the module is the lowering's, which a clause would
///   restate whole.
///
/// # Errors
/// [`Unran::Refused`].
///
/// # Adequacy
/// - hypothesis: L3 — a deployment's program read for its worlds, each with the
///   row it requires or none, and a site's file read for its offer.
/// - witness: `tests::manifold::a_world_s_row_is_judged_against_its_site_s_offer_3523`
#[inline]
pub fn lowered_alone<Read, Reader>(
    source: &Path,
    text: SourceText<'_>,
    read: Reader,
) -> Result<Read, Unran>
where
    Reader: FnOnce(&LoweredModule<'_>, SourceText<'_>) -> Read,
{
    let grammar = built_in().map_err(|error| Unran::Refused {
        why: error.to_string(),
    })?;
    let laid = lay_out(&grammar, source, classify(source), text);
    let laid_text = SourceText::from(laid.text.as_str());
    let mut lowerings = LoweringCount::default();
    let lowering =
        lower_unit_source(&grammar, laid_text, &laid.unit, &mut lowerings).map_err(|fault| {
            Unran::Refused {
                why: fault.to_string(),
            }
        })?;
    match lowering.into_lowered() {
        Lowered::Module { module, .. } => Ok(read(&module, laid_text)),
        Lowered::Refused(refusal) => Err(Unran::Refused {
            why: refusal.to_string(),
        }),
    }
}

/// The file of each source the source at `source` lays out over, its own
/// among them, each canonical.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the canonical path of each source of the unit `source` lays out
///   as the walk lays it out, in the unit's order, the prelude, which no file
///   holds, left out.
/// - provides: the files a manifold imports, among which its sites are found.
/// - fails: [`Unran::Unread`] for a source that cannot be read, and
///   [`Unran::Refused`] when the grammar does not build.
/// - panics: none.
/// - executable: none — the clause reads the file system.
///
/// # Errors
/// [`Unran::Unread`] and [`Unran::Refused`].
///
/// # Adequacy
/// - hypothesis: L3 — a manifold's sites are found among the files it imports.
/// - witness: `tests::manifold::a_world_s_row_is_judged_against_its_site_s_offer_3523`
#[inline]
pub fn sources_alone(source: &Path) -> Result<Vec<PathBuf>, Unran>
{
    let text = std::fs::read_to_string(source).map_err(|error| Unran::Unread {
        message: error.to_string(),
    })?;
    let grammar = built_in().map_err(|error| Unran::Refused {
        why: error.to_string(),
    })?;
    let laid = lay_out(
        &grammar,
        source,
        classify(source),
        SourceText::from(text.as_str()),
    );
    Ok(laid
        .paths
        .into_iter()
        .filter(|path| path.is_file())
        .collect())
}

/// A host answering nothing: every operation offered stays unhandled.
struct Unhosted;

impl HostHandler for Unhosted
{
    type Abort = Infallible;

    /// Decline the operation.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        _request: HostRequest<'_>,
        _values: &mut HostValues<'_>,
    ) -> HostReply<Infallible>
    {
        HostReply::Decline
    }
}

quenchant_shape::reason_enum! {
    /// Why a path stands in no workspace.
    pub mod workspace_root {
        /// No directory from the path up holds a workspace source.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `workspace.gandr` stands in any directory from the path up.
            Unworkspaced,
        }
    }
}

/// Why a workspace names no packages.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unmembered
{
    /// The workspace's source cannot be read.
    Unread
    {
        /// What reading it met.
        message: String,
    },
    /// The workspace's source does not compose, or is refused as a whole.
    Refused
    {
        /// Why, spelled.
        why: String,
    },
    /// The workspace's source declares no `members`.
    Undeclared,
    /// `members` runs to no list of strings.
    Unlisted
    {
        /// What its run came to, spelled.
        came: String,
    },
    /// A member's directory roots no package.
    Unpackaged
    {
        /// The member, as `members` lists it.
        member: String,
    },
}

impl core::fmt::Display for Unmembered
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Unread { ref message } => write!(f, "`{WORKSPACE}` cannot be read: {message}"),
            Self::Refused { ref why } => {
                write!(f, "`{WORKSPACE}` is refused as a whole: {why}")
            },
            Self::Undeclared => write!(
                f,
                "`{WORKSPACE}` declares no `{MEMBERS}`: declare `pub def {MEMBERS} : \
                 List(String)`, its `List` from `std.list`, naming its packages"
            ),
            Self::Unlisted { ref came } => write!(
                f,
                "`{MEMBERS}` of `{WORKSPACE}` runs to `{came}`, not to a list of strings"
            ),
            Self::Unpackaged { ref member } => write!(
                f,
                "the member `{member}` of `{WORKSPACE}` roots no package: no `package.gandr` stands \
                 in it"
            ),
        }
    }
}

impl core::error::Error for Unmembered
{
}
