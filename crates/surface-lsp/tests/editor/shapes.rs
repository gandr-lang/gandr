//! The content half of the hover guarantee: the shape each node kind's answer
//! takes, and the transcripts of the headline sources' hovers.
//!
//! The sweep counts, per node kind, the positions answered at the node; the
//! shapes say what such an answer holds. A name — a declaration's, a binder's,
//! a pattern's, a use's — answers `<name> : <type>`, the name as written and
//! a type that parses; a constructor in a pattern answers the same at a type
//! whose result is the type its pattern answers, the scrutinee's; a written
//! type answers `<type> : <universe>`; a literal its native type; a keyword or
//! a delimiter of a term the form's type alone; a keyword or a delimiter of a
//! declaration the declaration's own answer, and a statement's keyword in its
//! body — a tile of the declaration's own form — its statement's type. A kind
//! whose answers have no stable shape is named in [`SHAPELESS`] with why and
//! not held.
//!
//! The alternative was a transcript for the whole corpus, which no review can
//! read. The transcripts here hold six sources, and the shapes hold the rest.
//! The gate of outputs compares each transcript with the transcript of the
//! base. The shapes return to transcripts of a generated distribution when one
//! exists (issue #386).

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;
use std::path::Path;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use gandr_workflow_output_store::Kind;
use gandr_workflow_output_store::given;
use serde_json::Value;

use super::buffer::Offset;
use super::buffer::Position;
use super::buffer::Text;
use super::scenarios::Every;
use super::scenarios::Hovered;
use super::scenarios::MEANINGLESS;
use super::scenarios::Owner;
use super::scenarios::Source;
use super::scenarios::corpus;
use super::scenarios::hovered;
use super::scenarios::spot;

/// The node kinds whose answers have no stable shape, each with why: the
/// sweep counts their positions but holds no shape on them.
const SHAPELESS: &[(&str, &str)] = &[];

/// The sources whose every hover is a value of the kind `hovers` of the store
/// of outputs: univalence's computation rule by `here`, path induction over
/// the based path space, transport at `here`, function extensionality by
/// computation, the circle, and a theory with a documented model module, whose
/// hover shows the module's documentation (#1135).
const HEADLINE: [&str; 6] = [
    "fixture/model/higher-cells/ua-corolla.gandr",
    "fixture/model/identity/transport-dependent.gandr",
    "fixture/model/identity/transport-path.gandr",
    "fixture/model/identity/funext.gandr",
    "fixture/model/identity/circle.gandr",
    "fixture/model/include/monoid.gandr",
];

/// How one position's answer stands against its kind's shape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Judged
{
    /// It has the shape its kind demands.
    Shaped,
    /// It answers at its node in another shape.
    Unshaped,
    /// No shape is held: the position is layout, a comment, unanswered,
    /// answered by an ancestor — a coverage miss the sweep counts on its own —
    /// or of a kind with no meaning or no stable shape of its own.
    Unheld,
}

/// What an answer at a node of one kind holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Shape
{
    /// `<written> : <type>`, the node's text as the source writes it and a
    /// type that parses; the written name alone and the lowering's refusal for
    /// a declaration it refused; the type alone where the node spans lines.
    Subject,
    /// As [`Self::Subject`], and the type's result — past its last top-level
    /// `=>`, or the whole type — is the type the constructor's pattern answers:
    /// the scrutinee's, at that place.
    Constructor,
    /// `<written> : <universe>`, or the universe alone where the written type
    /// spans lines: `Type`, `Type[…]`, or a static arrow of those; or, for a
    /// value written as a type's argument — a constructor, a code — the value's
    /// `<written> : <type>`, as [`Self::Subject`] holds it.
    Universe,
    /// The literal's native type alone.
    Native(&'static str),
    /// A type that parses, alone: the type of the form the tile belongs to,
    /// then the type an outer judgement checked it against when that differs;
    /// or, where the source writes the form as one name, as [`Self::Subject`].
    Form,
    /// The declaration's own answer — its name and type, or its name and its
    /// refusal — or, on a rule's arrow, the direction the order chose; or, on
    /// a statement's keyword in the body, about a range starting past the
    /// declaration's, the statement's type as [`Self::Form`] holds it.
    Declaration,
}

/// The shape answers at `owner`'s node take, by its kind.
///
/// # Specification
/// - requires: `owner`'s kind is a kind the sweep measures.
/// - ensures: a name kind `… name`, a term's or a pattern's name and a type's
///   variable [`Shape::Subject`], a pattern's constructor name
///   [`Shape::Constructor`]; a pattern form [`Shape::Subject`]; a literal
///   [`Shape::Native`] at its native type; any other type form
///   [`Shape::Universe`]; any other term form and a block a form writes after
///   its tile [`Shape::Form`]; any other declaration form
///   [`Shape::Declaration`].
/// - panics: a kind of no sort the sweep knows.
/// - executable: none — the ensures clause is the table the body is; a
///   predicate restating it would be its second copy.
///
/// # Adequacy
/// - hypothesis: L3 — the sweep holds every measured kind to the shape this
///   names, and a kind whose answers changed shape moves its row.
/// - witness: `tests::editor::scenarios::sweeps::hovering_every_position_of_each_corpus_source_answers_without_fault`
fn shape_of(owner: &Owner) -> Shape
{
    match owner.kind.as_str() {
        "pattern constructor_pattern name" => Shape::Constructor,
        "expression number" | "type number" => Shape::Native("Integer"),
        "expression string" => Shape::Native("String"),
        "expression unit" => Shape::Native("Unit"),
        "expression boolean" | "type boolean" => Shape::Native("Bool"),
        "expression identifier"
        | "expression constructor"
        | "pattern identifier"
        | "type type_variable" => Shape::Subject,
        named if named.ends_with(" name") => Shape::Subject,
        pattern if pattern.starts_with("pattern ") => Shape::Subject,
        ty if ty.starts_with("type ") => Shape::Universe,
        term if term.starts_with("expression ")
            || term.starts_with("instantiation ")
            || term.starts_with("block ") =>
        {
            Shape::Form
        },
        declaration
            if declaration.starts_with("item ") || declaration.starts_with("module_member ") =>
        {
            Shape::Declaration
        },
        other => panic!("no shape for the kind `{other}`"),
    }
}

/// Where a hover answered a position: at the position's own node, or past it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Reach
{
    /// The answer's range lies inside the node's.
    AtNode,
    /// The answer's range reaches past the node: an ancestor answered.
    Ancestor,
}

/// Where the hover `shown` answers `owner`'s node.
///
/// # Specification
/// - requires: `shown` answered a position of `text` that `owner` holds.
/// - ensures: [`Reach::AtNode`] exactly when the answer's range starts at or
///   after the node's start and ends at or before its end.
/// - panics: the answer carries no range.
/// - executable: none — the answer's range is protocol JSON the call reads into
///   positions itself; no predicate over the return alone restates it.
///
/// # Adequacy
/// - hypothesis: L3 — the sweep separates answers at the node from an
///   ancestor's by this, against the rows #389 recorded.
/// - witness: `tests::editor::scenarios::sweeps::hovering_every_position_of_each_corpus_source_answers_without_fault`
pub(super) fn reach(
    text: Text<'_>,
    owner: &Owner,
    shown: &Value,
) -> Reach
{
    let start = spot(&shown["range"]["start"]);
    let end = spot(&shown["range"]["end"]);
    let node_start = Position::of(text, Offset(owner.node.0));
    let node_end = Position::of(text, Offset(owner.node.1));
    if (node_start.line, node_start.character) <= (start.line, start.character)
        && (end.line, end.character) <= (node_end.line, node_end.character)
    {
        Reach::AtNode
    }
    else {
        Reach::Ancestor
    }
}

/// The text of the first `gandr` block of the hover text `value`.
///
/// # Specification
/// trivial.
fn first_block(value: Text<'_>) -> Option<Text<'_>>
{
    let opened = value.0.strip_prefix("```gandr\n")?;
    let end = opened.find("\n```")?;
    opened.get(.. end).map(Text)
}

/// The type `value` says an outer judgement checked its term against, when it
/// says one.
///
/// # Specification
/// trivial.
fn checked_against(value: Text<'_>) -> Option<Text<'_>>
{
    let (_, against) = value.0.split_once("\n\nchecked against\n\n")?;
    first_block(Text(against))
}

/// The result of the type `spelled`: what follows its last top-level `=>`,
/// or all of it.
///
/// # Specification
/// trivial.
fn result(spelled: Text<'_>) -> Text<'_>
{
    let mut depth = 0_usize;
    let mut after = 0_usize;
    for (at, glyph) in spelled.0.char_indices() {
        match glyph {
            '(' | '[' | '{' | '⟨' => depth = depth.saturating_add(1),
            ')' | ']' | '}' | '⟩' => depth = depth.saturating_sub(1),
            '=' if depth == 0
                && spelled
                    .0
                    .get(at ..)
                    .is_some_and(|rest| rest.starts_with("=> ")) =>
            {
                after = at.saturating_add("=> ".len());
            },
            _ => {},
        }
    }
    Text(spelled.0.get(after ..).unwrap_or(spelled.0).trim())
}

/// Whether each answer of `hovers`, the positions of `source`, has the shape
/// its kind demands.
///
/// # Specification
/// - requires: `hovers` is [`hovered`] over `source` under `grammar`.
/// - ensures: one judgement per position, in order: [`Judged::Unheld`] for a
///   comment, layout, an unanswered position, an answer past the node and a
///   kind [`MEANINGLESS`] or [`SHAPELESS`] names; otherwise [`Judged::Shaped`]
///   when the answer holds its kind's [`Shape`] — every type in it parsing as a
///   signature's type with no repair — and [`Judged::Unshaped`] when not.
/// - provides: the sweep's shape column.
/// - panics: a kind of no sort the sweep knows.
///
/// # Adequacy
/// - hypothesis: L3 — the sweep's rows count what this judges over the whole
///   corpus, red where a kind's answers lost their shape.
/// - witness: `tests::editor::scenarios::sweeps::hovering_every_position_of_each_corpus_source_answers_without_fault`
#[spec(ensures: |ret| ret.len() == hovers.len())]
pub(super) fn judged(
    grammar: &Pbg,
    source: &Source,
    hovers: &[Hovered],
) -> Vec<Judged>
{
    let text = Text(&source.text);
    let written = |range: (usize, usize)| source.text.get(range.0 .. range.1).unwrap_or_default();
    let mut parsed: BTreeMap<String, bool> = BTreeMap::new();
    let mut parses = |spelled: &str| {
        *parsed.entry(String::from(spelled)).or_insert_with(|| {
            let signature = format!("def shape :  {spelled} ;\n");
            parse(grammar, SourceText::from(signature.as_str()))
                .is_ok_and(|parsed| parsed.obligations().is_empty())
        })
    };
    // A universe: `Type` or `Type[…]`, alone or in a static arrow.
    let universe = |spelled: &str| {
        spelled.split("->").all(|part| {
            let atom = part
                .trim_matches(|glyph: char| glyph == '(' || glyph == ')' || glyph.is_whitespace());
            atom == "Type" || (atom.starts_with("Type[") && atom.ends_with(']'))
        })
    };
    // Each constructor pattern's own answer, and each form's first name: the
    // declaration a declaration's tiles answer for.
    let mut patterns: BTreeMap<(usize, usize), String> = BTreeMap::new();
    let mut names: BTreeMap<(usize, usize), &str> = BTreeMap::new();
    for hover in hovers {
        let Some(ref owner) = hover.owner
        else {
            continue;
        };
        if owner.kind == "pattern constructor_pattern"
            && let Some(block) = hover.shown["contents"]["value"]
                .as_str()
                .and_then(|value| first_block(Text(value)))
        {
            let _first = patterns
                .entry(owner.node)
                .or_insert_with(|| String::from(block.0));
        }
        if owner.kind.ends_with(" name") {
            let _first = names
                .entry(owner.form)
                .or_insert_with(|| written(owner.node));
        }
    }
    hovers
        .iter()
        .map(|hover| {
            let Some(ref owner) = hover.owner
            else {
                return Judged::Unheld;
            };
            let Some(value) = hover.shown["contents"]["value"].as_str()
            else {
                return Judged::Unheld;
            };
            if MEANINGLESS
                .iter()
                .chain(SHAPELESS)
                .any(|&(kind, _)| kind == owner.kind)
            {
                return Judged::Unheld;
            }
            if reach(text, owner, &hover.shown) == Reach::Ancestor {
                return Judged::Unheld;
            }
            let Some(Text(block)) = first_block(Text(value))
            else {
                return Judged::Unshaped;
            };
            if let Some(Text(against)) = checked_against(Text(value))
                && !parses(against)
            {
                return Judged::Unshaped;
            }
            let node = written(owner.node);
            let refused = |name: &str| block == name && value.contains("\n\nrefused: ");
            let typed = |name: &str| {
                let rest = block.strip_prefix(name)?;
                rest.strip_prefix(" : ")
            };
            let shaped = match shape_of(owner) {
                Shape::Subject | Shape::Constructor if node.contains('\n') => parses(block),
                Shape::Subject => typed(node).is_some_and(&mut parses) || refused(node),
                Shape::Constructor => typed(node).is_some_and(|ty| {
                    let scrutinee = if owner.form == owner.node {
                        Some(ty)
                    }
                    else {
                        patterns.get(&owner.form).and_then(|pattern| {
                            let rest = pattern.strip_prefix(written(owner.form))?;
                            rest.strip_prefix(" : ")
                        })
                    };
                    scrutinee.is_some_and(|scrutinee| {
                        result(Text(ty)) == result(Text(scrutinee)) || ty == scrutinee
                    }) && parses(ty)
                }),
                Shape::Universe if node.contains('\n') => universe(block),
                Shape::Universe => typed(node).is_some_and(|ty| universe(ty) || parses(ty)),
                Shape::Native(native) => block == native,
                Shape::Form => parses(block) || typed(node).is_some_and(&mut parses),
                Shape::Declaration => {
                    // A statement's keyword in the body — `let`, `fork` — is a
                    // tile of the declaration's own form, and answers the
                    // statement's computation about a range starting past the
                    // declaration's: a term form's answer.
                    let inner = spot(&hover.shown["range"]["start"])
                        != Position::of(text, Offset(owner.node.0));
                    block.starts_with("oriented ")
                        || names.get(&owner.node).is_some_and(|&name| {
                            typed(name).is_some_and(&mut parses) || refused(name)
                        })
                        || (inner && parses(block))
                },
            };
            if shaped {
                Judged::Shaped
            }
            else {
                Judged::Unshaped
            }
        })
        .collect()
}

/// The transcript of `source`'s hovers: one line per run of written positions
/// a hover answers alike, in source order.
///
/// # Specification
/// - requires: `hovers` is [`hovered`] over `source`.
/// - ensures: comments and layout are left out; each maximal run of the other
///   positions sharing one answer is a line: its first and last positions,
///   one-based `line:column`, the text from the first to the last, at most 24
///   characters, newlines as `⏎`, then `⇒` and the answer — its text as
///   [`shown_value`] writes it — then `@` and its range — or `∅` when nothing
///   answers.
/// - panics: when the corpus directory beside this crate does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — the six transcripts hold every answer of their sources; a
///   changed type, range or gap moves a line.
/// - witness: `tests::editor::shapes::the_headline_sources_give_their_hovers`
#[spec(ensures: |ret| ret.lines().count() <= hovers.len())]
fn transcript(
    source: &Source,
    hovers: &[Hovered],
) -> String
{
    let text = Text(&source.text);
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root resolves")
        .display()
        .to_string();
    let place = |offset: usize| {
        let at = Position::of(text, Offset(offset));
        format!(
            "{}:{}",
            at.line.saturating_add(1),
            at.character.saturating_add(1)
        )
    };
    let answer = |shown: &Value| {
        shown["contents"]["value"].as_str().map_or_else(
            || String::from("∅"),
            |value| {
                let start = spot(&shown["range"]["start"]);
                let end = spot(&shown["range"]["end"]);
                format!(
                    "{} @{}:{}-{}:{}",
                    shown_value(value, &corpus),
                    start.line.saturating_add(1),
                    start.character.saturating_add(1),
                    end.line.saturating_add(1),
                    end.character.saturating_add(1)
                )
            },
        )
    };
    let mut runs: Vec<(usize, usize, &Value)> = Vec::new();
    for hover in hovers.iter().filter(|hover| hover.owner.is_some()) {
        match runs.last_mut() {
            Some(&mut (_, ref mut last, shown)) if *shown == hover.shown => *last = hover.offset,
            Some(_) | None => runs.push((hover.offset, hover.offset, &hover.shown)),
        }
    }
    let mut out = String::new();
    let mut shown_text = String::new();
    for (first, last, shown) in runs {
        let end = source
            .text
            .get(last ..)
            .and_then(|rest| rest.chars().next())
            .map_or(last, |glyph| last.saturating_add(glyph.len_utf8()));
        let spanned: String = source
            .text
            .get(first .. end)
            .unwrap_or_default()
            .replace('\n', "⏎");
        shown_text.clear();
        shown_text.extend(spanned.chars().take(24));
        if spanned.chars().nth(24).is_some() {
            shown_text.push('…');
        }
        let _written = writeln!(
            out,
            "{}-{} {shown_text} ⇒ {}",
            place(first),
            place(last),
            answer(shown)
        );
    }
    out
}

/// The hover text `value` as a transcript writes it: its fences dropped, its
/// newlines as `⏎`, each absolute path between backticks made canonical, and
/// the path of the repository root `root` as `<corpus>`.
///
/// # Specification
/// - requires: `root` is the canonical path of the repository root.
/// - ensures: the result holds no `root`; a path that names a file through a
///   link or a `..` segment is written as its canonical path, so it is under
///   `<corpus>` when its file is in the repository.
///
/// # Adequacy
/// - hypothesis: L3 — a checkout whose path is not canonical writes the
///   transcript that a canonical checkout writes.
/// - witness: `tests::editor::shapes::a_transcript_names_each_path_under_the_root_alone`
#[spec(ensures: |ret| !ret.contains(root))]
fn shown_value(
    value: &str,
    root: &str,
) -> String
{
    let unfenced = value
        .replace("```gandr\n", "")
        .replace("\n```", "")
        .replace('\n', "⏎");
    let mut canonical = String::with_capacity(unfenced.len());
    let mut rest = unfenced.as_str();
    while let Some((before, opened)) = rest.split_once('`') {
        canonical.push_str(before);
        canonical.push('`');
        let Some((span, after)) = opened.split_once('`')
        else {
            rest = opened;
            break;
        };
        let path = Path::new(span);
        match path.is_absolute().then(|| path.canonicalize()) {
            Some(Ok(resolved)) => {
                let _written = write!(canonical, "{}", resolved.display());
            },
            Some(Err(_)) | None => canonical.push_str(span),
        }
        canonical.push('`');
        rest = after;
    }
    canonical.push_str(rest);
    canonical.replace(root, "<corpus>")
}

/// The first absolute path that the transcript `text` holds: a word that starts
/// with `/` and a name, and holds a second `/`. A word ends at a space, a
/// newline, `⏎`, a backtick, a quote or a parenthesis.
///
/// # Specification
/// - ensures: a found path starts with `/` and is a word of `text`.
///
/// # Adequacy
/// - hypothesis: L3 — a transcript written from a checkout outside the
///   repository root's canonical path names that path, and this finds it.
/// - witness: `tests::editor::shapes::a_transcript_names_each_path_under_the_root_alone`
#[spec(ensures: |ret| ret.is_none_or(|held| held.starts_with('/') && text.contains(held)))]
fn host_path(text: &str) -> Option<&str>
{
    text.split(|glyph: char| {
        glyph.is_whitespace() || matches!(glyph, '⏎' | '`' | '"' | '\'' | '(' | ')')
    })
    .find(|word| {
        word.strip_prefix('/').is_some_and(|tail| {
            tail.starts_with(|glyph: char| glyph.is_alphanumeric() || matches!(glyph, '_' | '.'))
                && tail.contains('/')
        })
    })
}

/// Each headline source's hovers, as one text that names no absolute path.
/// Each text goes to the store of outputs as a value of the kind `hovers`,
/// when the environment names a run of the tests of the kind. The gate of
/// outputs compares each value with the value of the base.
#[test]
fn the_headline_sources_give_their_hovers()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let sources = corpus();
    let mut suffix = String::new();
    for path in HEADLINE {
        suffix.clear();
        let _written = write!(
            suffix,
            "corpus/{}",
            path.strip_prefix("fixture/").unwrap_or(path)
        );
        let source = sources
            .iter()
            .find(|source| source.uri.ends_with(suffix.as_str()))
            .unwrap_or_else(|| panic!("`{path}` is a corpus source"));
        let hovers = hovered(&grammar, source, Every(1));
        let text = transcript(source, &hovers);
        if let Some(held) = host_path(&text) {
            panic!(
                "the hovers of `{path}` hold the absolute path `{held}`; a hover names a path under `<corpus>` alone"
            );
        }
        let _given = given::give(Kind("hovers"), path, text.as_bytes())
            .unwrap_or_else(|error| panic!("the hovers of `{path}` go to the store: {error}"));
    }
}

/// A hover path through a `..` segment is written under `<corpus>`, and a
/// transcript that names a path outside the repository root is found.
#[test]
fn a_transcript_names_each_path_under_the_root_alone()
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root resolves");
    let root = root.display().to_string();
    let value = format!(
        "```gandr\nimport \"./circle-base.gandr\";\n```\n\nReads `{root}/crates/../corpus/model/identity/circle-base.gandr`."
    );
    let shown = shown_value(&value, &root);
    assert_eq!(
        shown,
        "import \"./circle-base.gandr\";⏎⏎Reads `<corpus>/corpus/model/identity/circle-base.gandr`."
    );
    assert_eq!(host_path(&shown), None);
    assert_eq!(
        host_path("1:1-1:9 import ⇒ Reads `/srv/checkout/corpus/model/a.gandr`. @1:1-1:9"),
        Some("/srv/checkout/corpus/model/a.gandr")
    );
    assert_eq!(host_path("1:3-1:3 / ⇒ a / b @1:1-1:5"), None);
}
