//! The coverage of names: each name that the highlighter marks answers the
//! editor, or the sweep gives its kind as a gap.
//!
//! A use answers a definition request with one link at least. The type table
//! names each binder at its span, and rename, references and a binder's hover
//! use that name. Each name hovers more than the bare stub that knows only
//! the rule of its tile. A name that fails one of the three is a gap.
//!
//! A gap's key is its surface, its highlight role and the rule of the tile at
//! it. A key holds no path and no line, so an edit of a source keeps it. The
//! sweep gives the keys of the corpus as the kind `unanswered` of the outputs.
//! That kind is a ratchet: its difference refuses a head that adds a key.

use alloc::collections::BTreeMap;
use std::path::Path;

use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
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
    /// Writes the surface as the key of a gap spells it.
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
/// - provides: the gaps a test asserts and the sweep gives to the outputs.
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
            String::from("19 `Type`")
        )]))
    );
}

/// The sweep over the names of the corpus. Under a pull-request profile it
/// visits the sample below. Under `nightly` it visits the night's slice.
/// Under `sweeps`, and in a run of the outputs, it visits each source.
mod sweeps
{
    use gandr_workflow_output_store::Kind;
    use gandr_workflow_output_store::given;
    use gandr_workflow_sweep::Nights;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use gandr_workflow_sweep::corpus;

    use super::BTreeMap;
    use super::SourceText;
    use super::gaps;

    /// The sample: seven sources, as the tile sweep draws, within the suite's
    /// bound of a second for each test.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_corpus_name_gives_its_gaps"),
        size: SampleSize(7),
    };

    /// The nights the nightly profile takes to visit each source, as the tile
    /// sweep takes.
    const NIGHTS: Nights = Nights(7);

    /// Each source that the sweep visits gives its gaps. When the environment
    /// names a run of the outputs, the sweep visits each source, and it gives
    /// the keys as the one value `corpus` of the kind `unanswered`, one line
    /// for each key.
    #[test]
    fn every_corpus_name_gives_its_gaps()
    {
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        eprintln!("{}", sweep.rotation());
        let corpus = corpus::sources().expect("the corpus reads");
        let asked = given::asked().is_some();
        let sources = if asked {
            corpus
        }
        else {
            sweep.visit_rotating(SAMPLE, NIGHTS, &corpus)
        };
        let mut found: BTreeMap<String, String> = BTreeMap::new();
        for source in &sources {
            let written = std::fs::read_to_string(&source.path).expect("a corpus source is read");
            for (key, site) in gaps(SourceText::from(written.as_str()), &source.path).0 {
                found
                    .entry(key)
                    .or_insert_with(|| format!("{}:{site}", source.name));
            }
        }
        for (key, site) in &found {
            eprintln!("{key} at {site}");
        }
        if asked {
            let mut value = String::new();
            for key in found.keys() {
                value.push_str(key);
                value.push('\n');
            }
            let _given = given::give(Kind("unanswered"), "corpus", value.as_bytes())
                .unwrap_or_else(|error| panic!("the gaps of the corpus go to the store: {error}"));
        }
    }
}
