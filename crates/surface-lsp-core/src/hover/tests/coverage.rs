//! The coverage of names: each name that the highlighter marks answers the
//! editor, or the coverage ledger holds its kind.
//!
//! A use answers a definition request with one link at least. The type table
//! names each binder at its span, and rename, references and a binder's hover
//! use that name. Each name hovers more than the bare stub that knows only
//! the rule of its tile. A name that fails one of the three is a gap.
//!
//! A gap's key is its surface, its highlight role and the rule of the tile at
//! it. A key holds no path and no line, so an edit of a source keeps it. The
//! ledger `coverage.ledger` at the crate's root holds the kinds the corpus
//! owes. A gap whose key the ledger lacks fails the sweep. A whole sweep also
//! fails on a held key that no gap carries.

use alloc::collections::BTreeMap;
use std::path::Path;

use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use gandr_workflow_debt_ledger::Header;
use gandr_workflow_debt_ledger::Ledger;
use gandr_workflow_debt_ledger::Text;
use quenchant_shape::shape::Maybe;

use super::super::TILE_OF;
use super::super::hover;
use super::super::hovering;
use super::PLAIN;
use super::checked;
use crate::goto::Goto;
use crate::goto::targets;
use crate::position::Position;
use crate::protocol::Answer;
use crate::protocol::DocumentUri;
use crate::protocol::Linked;
use crate::reading::Reading;

/// The ledger's header: the owner of its keys and the shape of each line.
const HEADER: Header<'static> = Header(
    "The kinds of name that the editor answers nothing at, owed by gandr #4304.\n\
     key: <surface> <role> <rule>. The surface is definition, binder or hover.\n\
     SURFACE_LSP_COVERAGE_WRITE_LEDGER=1 under the sweeps profile writes this file.",
);

/// Which answer a name lacks.
///
/// # Specification
/// - provides: the first word of a gap's key.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Surface
{
    /// A use whose definition request answers no link.
    Definition,
    /// A binder the type table does not name at its span.
    Binder,
    /// A name whose hover is absent or only the bare stub.
    Hover,
}

impl core::fmt::Display for Surface
{
    /// Writes the surface as the ledger spells it.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::Definition => "definition",
            Self::Binder => "binder",
            Self::Hover => "hover",
        })
    }
}

/// What a span is to the editor: a use of what it refers to, a binder, or no
/// name.
///
/// # Specification
/// - provides: the surface an unindexed name fails on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Name
{
    /// A use: a variable, a call, a constructor, a type or a member.
    Use,
    /// A binder: a function's, a value's or a parameter's name.
    Binder,
    /// A keyword, a literal, a comment or another span that names nothing.
    Unnamed,
}

/// What `role` marks a span as.
///
/// # Specification
/// trivial.
const fn name(role: HlRole) -> Name
{
    match role {
        HlRole::Variable
        | HlRole::FunctionCall
        | HlRole::Constructor
        | HlRole::Type
        | HlRole::TypeBuiltin
        | HlRole::TypeVariable
        | HlRole::Member => Name::Use,
        HlRole::FunctionDef | HlRole::VariableDef | HlRole::VariableParam => Name::Binder,
        HlRole::Keyword
        | HlRole::Operator
        | HlRole::Number
        | HlRole::Boolean
        | HlRole::Character
        | HlRole::StringLit
        | HlRole::Escape
        | HlRole::Comment
        | HlRole::Hole
        | HlRole::Label
        | HlRole::Path
        | HlRole::Directive
        | HlRole::Other => Name::Unnamed,
    }
}

/// The gaps of one source. Each key maps to the first site that carries it:
/// its line, then the name in backquotes.
///
/// # Specification
/// - provides: what one source owes, for a test and for the sweep.
#[repr(transparent)]
#[derive(Debug, Default, Eq, PartialEq)]
struct Gaps(BTreeMap<String, String>);

/// The gaps of `text`, the source at `path`, after a session checks it.
///
/// # Specification
/// - requires: `path` is absolute.
/// - ensures: one key for each kind of gap among the source's name spans, with
///   the first site of that kind in source order.
/// - provides: the gaps a test asserts and the sweep compares with the ledger.
/// - fails: never.
/// - panics: when `path` names no file URI, or a span starts off a character
///   boundary.
/// - executable: none — the outcome is what the session and the server's
///   requests answer, which only a second run of them could restate.
///
/// # Adequacy
/// - hypothesis: L3 — an unused parameter keys its binder gap and its builtin
///   type's definition gap at their exact sites; the exemplar keys its builtin
///   universe alone; a name read as a use where it binds, or a span in a
///   comment read as a name, changes either set.
/// - witness: `hover::tests::coverage::an_unused_parameter_is_a_binder_gap_4580`
/// - witness: `hover::tests::coverage::the_exemplar_answers_each_name_it_declares`
fn gaps(
    text: SourceText<'_>,
    path: &Path,
) -> Gaps
{
    let written = <&str>::from(text);
    let session = checked(text);
    let reading = Reading::of(text);
    let hovering = hovering(text, path, &session, &gandr_surface_dispatcher::Unshadowed);
    let table = hovering.table();
    let index = LineIndex::new(written.into());
    let uri = DocumentUri::of_path(path).expect("a corpus path is a file URI");
    let tiles = reading.tiles();
    let stub = format!("\n\n{TILE_OF} `");
    let mut found = Gaps::default();
    for span in reading.spans() {
        let name = name(span.role);
        if name == Name::Unnamed {
            continue;
        }
        let start = usize::from(span.range.start());
        // The highlighter also marks code inside documentation. No tile holds
        // such a span, and no request reads it as a name.
        let holder = tiles.partition_point(|tile| usize::from(tile.span.start()) <= start);
        let Some(rule) = holder
            .checked_sub(1)
            .and_then(|last| tiles.get(last))
            .filter(|tile| start < usize::from(tile.span.end()))
            .map(|tile| tile.rule)
        else {
            continue;
        };
        let at = ByteOffset::from(start);
        let position = Position::of_byte(&index, RenderOffset::from(start))
            .expect("a span starts on a boundary");
        let mut lacks = Vec::with_capacity(2);
        // A name is a use when the table holds its referent, and a binder when
        // the table names it. The role decides only how an unindexed name
        // fails, since a declaring name and its use share a role.
        if matches!(table.referent(at), Maybe::Present(_)) {
            // A linked request answers links, never locations.
            let answer = targets(
                text,
                &uri,
                &hovering,
                position,
                Goto::Definition,
                Linked(true),
            );
            if !matches!(answer, Answer::Links(ref links) if !links.is_empty()) {
                lacks.push(Surface::Definition);
            }
        }
        else if matches!(table.named_at(at), Maybe::Absent(_)) {
            lacks.push(match name {
                Name::Use | Name::Unnamed => Surface::Definition,
                Name::Binder => Surface::Binder,
            });
        }
        let hovers = match hover(text, &session, &reading, &hovering, position, PLAIN) {
            Maybe::Present(shown) => !shown.contents.value.contains(stub.as_str()),
            Maybe::Absent(_) => false,
        };
        if !hovers {
            lacks.push(Surface::Hover);
        }
        let spelled = written
            .get(start .. usize::from(span.range.end()))
            .unwrap_or_default();
        let line = written
            .get(.. start)
            .unwrap_or_default()
            .matches('\n')
            .count()
            .saturating_add(1);
        for surface in lacks {
            found
                .0
                .entry(format!("{surface} {:?} {rule}", span.role))
                .or_insert_with(|| format!("{line} `{spelled}`"));
        }
    }
    found
}

/// The path of the ledger.
///
/// # Specification
/// trivial.
fn ledger_path() -> std::path::PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR")).join("coverage.ledger")
}

/// A parameter that no use reads is a binder the table does not name. Its
/// hover still gives its type. The builtin `Integer` has no definition.
#[test]
fn an_unused_parameter_is_a_binder_gap_4580()
{
    let text = SourceText::from("def first(x : Integer, y : Integer) -> Integer = x;\n");
    assert_eq!(
        gaps(text, Path::new("/unused.gandr")),
        Gaps(BTreeMap::from([
            (
                String::from("binder VariableParam def_value"),
                String::from("1 `y`")
            ),
            (
                String::from("definition TypeBuiltin primitive_type"),
                String::from("1 `Integer`")
            ),
        ]))
    );
}

/// The exemplar answers each name but the builtin universe it declares its
/// family in.
#[test]
fn the_exemplar_answers_each_name_it_declares()
{
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/model/basics/every-name-answers.gandr");
    let written = std::fs::read_to_string(&path).expect("the exemplar is read");
    assert_eq!(
        gaps(SourceText::from(written.as_str()), &path),
        Gaps(BTreeMap::from([(
            String::from("definition TypeBuiltin universe_type"),
            String::from("17 `Type`")
        )]))
    );
}

/// The sweep over the names of the corpus. Under a pull-request profile it
/// visits the sample below and each source the change adds or modifies.
/// Under `nightly` it visits the night's slice. Under `sweeps` it visits each
/// source, and it judges each held key.
mod sweeps
{
    use gandr_workflow_sweep::Coverage;
    use gandr_workflow_sweep::Nights;
    use gandr_workflow_sweep::Rotation;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use gandr_workflow_sweep::corpus;

    use super::BTreeMap;
    use super::HEADER;
    use super::Ledger;
    use super::SourceText;
    use super::Text;
    use super::gaps;
    use super::ledger_path;

    /// The sample: seven sources, as the tile sweep draws, within the suite's
    /// bound of a second for each test.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_corpus_name_answers_or_is_owed"),
        size: SampleSize(7),
    };

    /// The nights the nightly profile takes to visit each source, as the tile
    /// sweep takes.
    const NIGHTS: Nights = Nights(7);

    /// Whether a run judges a held key that no gap carries.
    ///
    /// # Specification
    /// - provides: the half of the verdict that a whole run alone can give.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Stale
    {
        /// The run visits each source, so a held key with no gap is stale.
        Judged,
        /// The run visits a part, so a held key with no gap may be elsewhere.
        Unjudged,
    }

    /// No name of the corpus answers nothing unless the ledger holds its kind.
    #[test]
    fn every_corpus_name_answers_or_is_owed()
    {
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        let stale = if sweep.coverage() == Coverage::Full && sweep.rotation() == Rotation::Whole {
            Stale::Judged
        }
        else {
            Stale::Unjudged
        };
        answers_or_is_owed(&sweep, stale);
    }

    /// The change's sources beside the fixed set.
    #[test]
    fn every_corpus_name_answers_or_is_owed_changed()
    {
        answers_or_is_owed(
            &Sweep::asked().expect("the run's sweep resolves").changed(),
            Stale::Unjudged,
        );
    }

    /// Each gap of each source `sweep` visits has its key in the ledger, and,
    /// when `stale` is judged, each held key has a gap.
    ///
    /// # Specification
    /// trivial.
    fn answers_or_is_owed(
        sweep: &Sweep,
        stale: Stale,
    )
    {
        eprintln!("{}", sweep.rotation());
        let sources = sweep.visit_rotating(
            SAMPLE,
            NIGHTS,
            &corpus::sources().expect("the corpus reads"),
        );
        let mut found: BTreeMap<String, String> = BTreeMap::new();
        for source in &sources {
            let written = std::fs::read_to_string(&source.path).expect("a corpus source is read");
            for (key, site) in gaps(SourceText::from(written.as_str()), &source.path).0 {
                found
                    .entry(key)
                    .or_insert_with(|| format!("{}:{site}", source.name));
            }
        }
        let path = ledger_path();
        if stale == Stale::Judged && std::env::var_os("SURFACE_LSP_COVERAGE_WRITE_LEDGER").is_some()
        {
            let text = gandr_workflow_debt_ledger::write(HEADER, found.keys());
            std::fs::write(&path, text).expect("the ledger is written");
            return;
        }
        let held_text = std::fs::read_to_string(&path).expect("the ledger is read");
        let held = Ledger::<String>::read(Text(&held_text)).expect("each ledger line is a key");
        let keys: Vec<&String> = found.keys().collect();
        let verdict = held.check(&keys, |key| (*key).clone());
        let mut refused: Vec<String> = verdict
            .new
            .iter()
            .map(|key| {
                format!(
                    "new: {key} at {}",
                    found.get(**key).map_or("", String::as_str)
                )
            })
            .collect();
        if stale == Stale::Judged {
            refused.extend(verdict.stale.iter().map(|key| format!("stale: {key}")));
        }
        assert!(
            refused.is_empty(),
            "{} kinds disagree with the ledger. Close a new kind, or hold it in the \
             ledger under its issue. Delete the line of a stale kind:\n{}",
            refused.len(),
            refused.join("\n")
        );
    }
}
