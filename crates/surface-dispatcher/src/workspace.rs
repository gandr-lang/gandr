//! A workspace: the packages a `workspace.gandr` gathers, found above them.
//!
//! # A workspace names its members
//!
//! [`Workspace::discover`] walks up from a path to the first directory that
//! holds `workspace.gandr`, as Cargo walks up to the `Cargo.toml` holding
//! `[workspace]`. The workspace is not a package: its source declares no
//! library, and the checker writes no manifest for it. It states what its
//! members share as a model of `Gandr.Workspace`, which each member's
//! `lib.gandr` imports and reads, and it names its members by a free-standing
//! `pub def members : List(String)`, each a directory below the workspace
//! that roots a package.
//!
//! [`Workspace::members`] reads that list by checking the workspace's source
//! alone and running `members`, so the list is gandr and never a second
//! manifest language. A verb given no path in a workspace but in none of its
//! packages, or given the workspace's directory, works on every member.
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
use gandr_surface_lowering::decode_escapes;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::HostGrant;
use crate::component::lay_out;
use crate::compose::Composed;
use crate::compose::Lowered;
use crate::compose::LoweringCount;
use crate::compose::judge_lowering;
use crate::compose::lower_unit_source;
use crate::evaluate::Program;
use crate::evaluate::Terminal;
use crate::evaluate::declaration_name;
use crate::manifold::Placed;
use crate::package::Package;
use crate::package::package_root;
use crate::root::classify;
use crate::walk::SourceFault;
use crate::walk::Standing;
use crate::walk::Step;

/// The file name of a workspace's source, at the workspace's root.
pub const WORKSPACE: &str = "workspace.gandr";

/// The declaration of a workspace's source that names its members.
const MEMBERS: &str = "members";

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

    /// The packages the workspace names, in the order its `members` lists
    /// them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the workspace's source read, checked over the sources it
    ///   imports, as the walk lays them out, and its `members` run; each string
    ///   of the list a directory below the root, and the package
    ///   [`Package::discover`] finds from it, which must be rooted at that
    ///   directory.
    /// - provides: the packages a verb works on in the workspace.
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
    ///   one naming a directory with no library, and one whose `members` is a
    ///   string, are refused with what they state.
    /// - witness: `tests::package::a_workspace_walks_every_member_it_names_2687`
    #[inline]
    pub fn members(&self) -> Result<Vec<Package>, Unmembered>
    {
        let [came] = match ran_alone(&self.source(), [SurfaceName::from(MEMBERS)]) {
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
        let Some(named) = Spelling(&came).listed()
        else {
            return Err(Unmembered::Unlisted { came });
        };
        named
            .into_iter()
            .map(|member| {
                let directory = self.root.join(&member);
                let rooted = directory.canonicalize().ok();
                match Package::discover(&directory) {
                    Maybe::Present(package) if rooted.as_deref() == Some(package.root()) => {
                        Ok(package)
                    },
                    Maybe::Present(_) | Maybe::Absent(package_root::Absent::Unpackaged) => {
                        Err(Unmembered::Unpackaged { member })
                    },
                }
            })
            .collect()
    }
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
///   package, workspace, site or manifold: a workspace's `members`, a library's
///   `dependencies`, a site's model and a manifold's.
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
/// - hypothesis: L3 — the witnesses of [`Workspace::members`],
///   [`Package::dependencies`], [`Site::read`] and [`Manifold::read`].
/// - witness: `tests::package::a_workspace_walks_every_member_it_names_2687`
/// - witness: `tests::package::a_lock_is_written_once_and_reads_alike_from_anywhere_3072`
/// - witness: `manifold::tests::a_site_and_a_manifold_read_from_their_files_3374`
///
/// [`Site::read`]: crate::manifold::Site::read
/// [`Manifold::read`]: crate::manifold::Manifold::read
#[inline]
pub fn ran_alone<const NAMES: usize>(
    source: &Path,
    names: [SurfaceName<'_>; NAMES],
) -> Result<[Maybe<String, declaration_name::Absent>; NAMES], Unran>
{
    alone(source, |program| {
        names.map(|name| match program.named(name) {
            Maybe::Present(constant) => Maybe::Present(program.evaluate(constant).to_string()),
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
/// - witness: `manifold::tests::a_site_reads_its_secret_from_the_model_given_3375`
#[inline]
pub fn answered_alone(
    source: &Path,
    function: SurfaceName<'_>,
    argument: StringLiteral,
) -> Result<Maybe<Answered, declaration_name::Absent>, Unran>
{
    alone(source, |program| {
        let constant = match program.named(function) {
            Maybe::Present(constant) => constant,
            Maybe::Absent(absent) => return Maybe::Absent(absent),
        };
        let mut core = CoreArena::new();
        let argument = core.value_literal(Literal::Text(argument));
        let read = match program.call(constant, &[argument], &mut core, &mut Unhosted) {
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
fn alone<Read>(
    source: &Path,
    read: impl FnOnce(&mut Program<'_>) -> Read,
) -> Result<Read, Unran>
{
    let text = std::fs::read_to_string(source).map_err(|error| Unran::Unread {
        message: error.to_string(),
    })?;
    stepped_alone(source, SourceText::from(text.as_str()), |step| match step {
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
/// - witness: `manifold::tests::a_site_and_a_manifold_read_from_their_files_3374`
/// - witness: `manifold::tests::a_world_s_requirement_is_judged_against_its_site_s_offer_3376`
#[inline]
pub fn stepped_alone<Read, Reader>(
    source: &Path,
    text: SourceText<'_>,
    read: Reader,
) -> Result<Read, Unran>
where
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
            judge_lowering(
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
///   deployment's program declares and what each requires.
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
///   theory it requires or none.
/// - witness: `manifold::tests::a_world_s_requirement_is_judged_against_its_site_s_offer_3376`
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
/// - witness: `manifold::tests::a_world_s_requirement_is_judged_against_its_site_s_offer_3376`
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

/// What a function a source declares answered its host.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Answered
{
    /// A string, whole.
    Text(String),
    /// Any other end, spelled: the evaluation the run ended with, or the kind
    /// of value it answered, never the value.
    Other(String),
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

/// Why [`ran_alone`] or [`answered_alone`] ran nothing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unran
{
    /// The source cannot be read.
    Unread
    {
        /// What reading it met.
        message: String,
    },
    /// The source does not compose, or is refused as a whole.
    Refused
    {
        /// Why, spelled.
        why: String,
    },
}

/// A run's value as the machine spells it, read from its start.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Spelling<'text>(&'text str);

impl<'text> From<&'text str> for Spelling<'text>
{
    /// Reads the text as a run's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl Spelling<'_>
{
    /// The strings the spelling lists: `cons("a", cons("b", nil))` is `a`
    /// then `b`, each decoded as a string literal is; none for any other
    /// spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the strings of a spelling `cons(s₁, cons(s₂, … nil))`, each
    ///   `sᵢ` a quoted string read up to its unescaped closing quote and
    ///   decoded, in order; none when anything else stands anywhere in it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a reading of the spelling, which a
    ///   clause would restate whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two members, none, and a string standing alone each
    ///   read as listed or not.
    /// - witness: `workspace::tests::a_run_s_spelling_lists_its_strings_2687`
    #[inline]
    fn listed(self) -> Option<Vec<String>>
    {
        self.listed_as(Self::quoted)
    }

    /// The dependencies the spelling lists: `cons(#{.alias = "a", .coordinate
    /// = Path("../a")}, nil)` is the alias `a` at the path `../a`, each string
    /// decoded; none for any other spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the alias and path of each element of a spelling `cons(d₁,
    ///   cons(d₂, … nil))`, each `dᵢ` written `#{.alias = a, .coordinate =
    ///   Path(p)}` with `a` and `p` quoted strings, in order; none when
    ///   anything else stands anywhere in it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::listed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two dependencies, none, and a record missing its
    ///   coordinate each read as listed or not.
    /// - witness: `workspace::tests::a_run_s_spelling_lists_its_dependencies_3072`
    #[inline]
    pub fn dependencies(self) -> Option<Vec<(String, String)>>
    {
        self.listed_as(|spelling| {
            let (alias, Self(rest)) = Self(spelling.0.strip_prefix("#{.alias = ")?).quoted()?;
            let (path, Self(rest)) = Self(rest.strip_prefix(", .coordinate = Path(")?).quoted()?;
            Some(((alias, path), Self(rest.strip_prefix(")}")?)))
        })
    }

    /// The placements the spelling lists: `cons(At("far", #{.key = "<key>",
    /// .secret = "far", .sockets = "127.0.0.1:4733"}), nil)` is the world
    /// `far` at the site of that key and socket, once, and `Instances("far",
    /// #{…}, 2)` is it twice; none for any other spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each element of a spelling `cons(p₁, cons(p₂, … nil))` read
    ///   in order, each `pᵢ` written `At(n, s)`, read with the count `1`, or
    ///   `Instances(n, s, c)`, read with the count `c` as spelled, `n` a quoted
    ///   string decoded and `s` a site's model spelled `#{.key = k, .secret =
    ///   e, .sockets = o}`, its labels in the order a run spells them and `k`
    ///   and `o` read as quoted strings decoded; none when anything else stands
    ///   anywhere in it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::listed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a placement of each constructor, none, and one whose
    ///   site lacks its sockets each read as listed or not.
    /// - witness: `workspace::tests::a_run_s_spelling_lists_its_placements_3374`
    pub(crate) fn placements(self) -> Option<Vec<Placed>>
    {
        self.listed_as(|spelling| {
            let (counted, rest) = match spelling.0.strip_prefix("At(") {
                Some(rest) => (false, rest),
                None => (true, spelling.0.strip_prefix("Instances(")?),
            };
            let (name, Self(rest)) = Self(rest).quoted()?;
            let (key, Self(rest)) = Self(rest.strip_prefix(", #{.key = ")?).quoted()?;
            let (_secret, Self(rest)) = Self(rest.strip_prefix(", .secret = ")?).quoted()?;
            let (sockets, Self(rest)) = Self(rest.strip_prefix(", .sockets = ")?).quoted()?;
            let rest = rest.strip_prefix('}')?;
            let (count, rest) = if counted {
                rest.strip_prefix(", ")?.split_once(')')?
            }
            else {
                ("1", rest.strip_prefix(')')?)
            };
            Some((
                Placed {
                    name,
                    key,
                    sockets,
                    count: String::from(count),
                },
                Self(rest),
            ))
        })
    }

    /// The elements the spelling lists, each read by `element`.
    ///
    /// # Specification
    /// trivial.
    fn listed_as<T>(
        self,
        element: impl Fn(Self) -> Option<(T, Self)>,
    ) -> Option<Vec<T>>
    {
        let mut rest = self.0;
        let mut elements = Vec::new();
        while let Some(after) = rest.strip_prefix("cons(") {
            let (read, Self(after)) = element(Self(after))?;
            elements.push(read);
            rest = after.strip_prefix(", ")?;
        }
        let closers = rest.strip_prefix("nil")?;
        (closers.len() == elements.len() && closers.bytes().all(|byte| byte == b')'))
            .then_some(elements)
    }

    /// The string literal the spelling opens with, decoded, and what follows
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn quoted(self) -> Option<(String, Self)>
    {
        let content = self.0.strip_prefix('"')?;
        let mut escaped = false;
        for (at, character) in content.char_indices() {
            match character {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                '"' => {
                    let written = content.get(.. at)?;
                    let after = content.get(at.saturating_add(1) ..)?;
                    return Some((decode_escapes(SourceFragment::from(written)), Self(after)));
                },
                _ => {},
            }
        }
        None
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
                 List(String)` naming its packages"
            ),
            Self::Unlisted { ref came } => write!(
                f,
                "`{MEMBERS}` of `{WORKSPACE}` runs to `{came}`, not to a list of strings"
            ),
            Self::Unpackaged { ref member } => write!(
                f,
                "the member `{member}` of `{WORKSPACE}` roots no package: no `lib.gandr` stands \
                 in it or in its `src` directory"
            ),
        }
    }
}

impl core::error::Error for Unmembered
{
}

#[cfg(test)]
mod tests
{
    use super::Spelling;

    #[test]
    fn a_run_s_spelling_lists_its_strings_2687()
    {
        assert_eq!(
            Spelling("cons(\"hello\", cons(\"tools\", nil))").listed(),
            Some(Vec::from([String::from("hello"), String::from("tools")])),
            "two members read in order"
        );
        assert_eq!(
            Spelling("nil").listed(),
            Some(Vec::new()),
            "no member reads as none"
        );
        assert_eq!(
            Spelling("cons(\"a \\\"b\\\"\", nil)").listed(),
            Some(Vec::from([String::from("a \"b\"")])),
            "a member's escapes are decoded"
        );
        for other in [
            "\"hello\"",
            "cons(\"a\", nil",
            "cons(\"a\", nil))",
            "cons(1, nil)",
        ] {
            assert_eq!(Spelling(other).listed(), None, "`{other}` lists no strings");
        }
    }

    #[test]
    fn a_run_s_spelling_lists_its_dependencies_3072()
    {
        let pair = |alias: &str, path: &str| (String::from(alias), String::from(path));
        assert_eq!(
            Spelling(
                "cons(#{.alias = \"hello\", .coordinate = Path(\"../hello\")}, cons(#{.alias = \
                 \"tools\", .coordinate = Path(\"../tools\")}, nil))"
            )
            .dependencies(),
            Some(Vec::from([
                pair("hello", "../hello"),
                pair("tools", "../tools")
            ])),
            "two dependencies read in order"
        );
        assert_eq!(
            Spelling("nil").dependencies(),
            Some(Vec::new()),
            "no dependency reads as none"
        );
        assert_eq!(
            Spelling("cons(#{.alias = \"hello\"}, nil)").dependencies(),
            None,
            "a dependency without its coordinate lists nothing"
        );
    }

    #[test]
    fn a_run_s_spelling_lists_its_placements_3374()
    {
        let placed = |name: &str, sockets: &str, count: &str| crate::manifold::Placed {
            name: String::from(name),
            key: String::from("k"),
            sockets: String::from(sockets),
            count: String::from(count),
        };
        let site = |sockets: &str| {
            format!("#{{.key = \"k\", .secret = \"far\", .sockets = \"{sockets}\"}}")
        };
        assert_eq!(
            Spelling(&format!(
                "cons(At(\"far\", {}), cons(Instances(\"near\", {}, 2), nil))",
                site("127.0.0.1:4733"),
                site("")
            ))
            .placements(),
            Some(Vec::from([
                placed("far", "127.0.0.1:4733", "1"),
                placed("near", "", "2")
            ])),
            "a placement of each constructor reads its site's key and sockets in order, `At` \
             counting one"
        );
        assert_eq!(
            Spelling("nil").placements(),
            Some(Vec::new()),
            "no placement reads as none"
        );
        assert_eq!(
            Spelling("cons(At(\"far\", #{.key = \"k\", .secret = \"far\"}), nil)").placements(),
            None,
            "a placement whose site lacks its sockets lists nothing"
        );
    }
}
