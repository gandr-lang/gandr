//! The scenarios: the corpus typed, erased and hovered, scripted edits that
//! break and fix a document, and random edit scripts undone to where they
//! started.
//!
//! The corpus scenarios and the random scripts are sweeps, in [`sweeps`]: each
//! visits its stated sample under every pull-request profile and every source
//! and every script under the `sweeps` profile; nightly, the erasure visits
//! the night's slice of the corpus and the typing the night's part of sixteen
//! of every source.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::num::NonZeroUsize;
use core::panic::AssertUnwindSafe;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::panic::catch_unwind;
use std::path::Path;
use std::sync::Mutex;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use percent_encoding::AsciiSet;
use percent_encoding::NON_ALPHANUMERIC;
use percent_encoding::utf8_percent_encode;
use proptest::prelude::Just;
use proptest::prelude::ProptestConfig;
use proptest::prelude::Strategy;
use proptest::prelude::any;
use proptest::prop_assert_eq;
use proptest::prop_oneof;
use proptest::proptest;
use proptest::sample::select;
use serde_json::Value;
use serde_json::json;

use super::buffer::Buffer;
use super::buffer::History;
use super::buffer::Key;
use super::buffer::Offset;
use super::buffer::Position;
use super::buffer::Text;
use super::buffer::Typing;
use super::client::Client;
use super::client::Method;
use super::client::Quiet;
use super::client::Record;
use super::editing::Oracle;
use super::editing::Session;
use super::editing::panic_message;
use super::shapes;
use super::typist::Stride;

/// The node kinds the hover sweep counts: the kind — its form's grammar
/// sort, then its named kind — of the corpus positions whose smallest
/// meaningful node is of that kind. The sweep prints, per kind, how many
/// positions it holds and how many are answered at the node, in shape
/// ([`shapes`]), by an ancestor, by nothing, with a `?` and in another shape
/// than the kind's; the counts are a report, not a gate (#467). A kind whose
/// answers wait on an issue names it. A kind measured with no row here and
/// none in [`MEANINGLESS`] fails the sweep, so a new kind is decided rather
/// than counted silently, and so does a row whose kind the corpus no longer
/// has.
const COUNTED: &[&str] = &[
    "expression abort_expression",
    "expression abort_expression name",
    "expression access_expression",
    "expression access_expression name",
    "expression become_expression",
    "expression binary_expression",
    "expression bind_expression",
    "expression bind_expression name",
    "expression block",
    "expression block name",
    "expression boolean",
    "expression break_expression",
    "expression break_value_expression",
    "expression call_expression", // `?`
    "expression case_expression",
    "expression character",
    "expression close_expression",
    "expression co_expression",
    "expression co_expression name",
    "expression constructor",
    "expression continue_expression",
    "expression double_quoted_string",
    "expression drop_expression", // `?`
    "expression dup_expression",
    "expression file_descriptor",
    "expression for_expression",
    "expression for_expression name",
    "expression force_expression",
    "expression forget_model_expression",
    "expression glob_expression",
    "expression glob_expression name",
    "expression handle_expression",
    "expression handle_expression name",
    "expression hole",
    "expression hold_expression",
    "expression host_escape",
    "expression identifier",
    "expression if_expression",
    "expression index_expression",
    "expression instantiation_expression",
    "expression labelled_sum_expression",
    "expression labelled_sum_expression name",
    "expression lambda_expression",
    "expression lambda_expression name",
    "expression lazy_record_expression",
    "expression lazy_record_expression name",
    "expression list_expression",
    "expression list_operator",
    "expression loop_expression",
    "expression migrate_expression",
    "expression migrate_expression name",
    "expression number",
    "expression offer_expression",
    "expression pack_expression",
    "expression pack_model_expression",
    "expression parenthesized_expression",
    "expression pipeline",
    "expression projection_expression",
    "expression projection_expression name",
    "expression pure_expression",
    "expression redirection_operator",
    "expression resume_expression",
    "expression resume_expression name",
    "expression return_expression",
    "expression run_expression",
    "expression select_expression",
    "expression select_expression name",
    "expression send_expression",
    "expression shell_block",
    "expression shell_word",
    "expression single_quoted_string",
    "expression string",
    "expression subshell",
    "expression telescope_expression",
    "expression telescope_expression name",
    "expression thunk_expression",
    "expression type_quote_expression",
    "expression typed_number",
    "expression unary_expression",
    "expression unit",
    "expression variable_expansion",
    "expression view_expression",
    "expression view_expression name",
    "expression while_expression",
    "expression wildcard",
    "instantiation instantiation_expression",
    "instantiation instantiation_expression name",
    "item circuit_declaration",
    "item circuit_declaration name",
    "item codata_declaration",
    "item codata_declaration name",
    "item data_declaration",
    "item data_declaration name",
    "item def_value",
    "item def_value name",
    "item derive_declaration",
    "item derive_declaration name",
    "item extern_block",
    "item extern_block name",
    "item import_declaration",
    "item import_declaration name",
    "item module_declaration",
    "item module_declaration name",
    "item operator_declaration",
    "item rec_block",
    "item theory_declaration",
    "item theory_declaration name",
    "item world_declaration",
    "item world_declaration name",
    "module_member module_declaration",
    "module_member module_declaration name",
    "pattern as_pattern",
    "pattern as_pattern name",
    "pattern cons_pattern",
    "pattern cons_pattern name",
    "pattern constructor_pattern",
    "pattern constructor_pattern name",
    "pattern hole",
    "pattern identifier",
    "pattern labelled_sum_pattern",
    "pattern labelled_sum_pattern name",
    "pattern list_pattern",
    "pattern literal_pattern",
    "pattern or_pattern",
    "pattern telescope_pattern",
    "pattern telescope_pattern name",
    "pattern tuple_pattern",
    "pattern unit",
    "pattern wildcard",
    "type at_type",
    "type at_type name",
    "type capability_type",
    "type capability_type name",
    "type end_session_type",
    "type equivalence_type",
    "type f_type",
    "type f_type name",
    "type function_type",
    "type isomorphism_type",
    "type labelled_sum_type",
    "type lazy_product_type",
    "type lazy_record_type",
    "type manifest_sort",
    "type manifest_sort name",
    "type manifest_type",
    "type moded_type name",
    "type mu_session_type",
    "type mu_session_type name",
    "type number",
    "type package_type",
    "type package_type name",
    "type parenthesized_type",
    "type path_type",
    "type primitive_type",
    "type product_type",
    "type receive_session_type",
    "type representable_universe_type",
    "type send_session_type",
    "type staged_type",
    "type staged_type name",
    "type static_abstraction",
    "type static_abstraction name",
    "type sum_type",
    "type telescope_type",
    "type type_application",
    "type type_application name",
    "type type_identifier",
    "type type_path",
    "type type_path name",
    "type type_variable",
    "type u_type",
    "type universe_flow_type",
    "type universe_type",
    "type unknown_type",
    "type value_function_type",
];

/// The node kinds with no meaning of their own to hover, each with why: the
/// sweep counts their positions but does not list them in [`COUNTED`].
pub(super) const MEANINGLESS: &[(&str, &str)] = &[
    (
        "grout",
        "the parser's repair of text the source did not write: no node the source wrote",
    ),
    (
        "item attribute_block",
        "an attribute's brackets and keywords state what its declaration is expected to do: the \
         declaration's head answers them",
    ),
    (
        "item attribute_block name",
        "an attribute's name is the expectation it states, no term or type: the declaration's \
         head answers it",
    ),
    (
        "item pub_declaration",
        "a `pub` mark exports the declaration after it and is no term or type: the declaration's \
         head answers it",
    ),
];

/// The tile labels a form spells a name with: a tile so labelled names
/// something of its own — a declaration, a parameter, a loop, a word
/// pattern's letter, a constructor pattern's constructor — so the sweep counts
/// it as a node apart from the form that holds it.
const NAMES: [&str; 4] = [
    "identifier",
    "constructor",
    "type_identifier",
    "type_variable",
];

/// The texts a random edit script starts from.
const SEEDS: [&str; 4] = [
    "",
    "def a : Integer ;\ndef a = 1 ;\n",
    "def f(x : Integer) -> -F Integer {\n  return x\n}\n",
    "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\ndef rec down(n : Nat) -> -F Nat {\n  case n {\n    Zero => return n,\n    Succ(p) => become down[<](p)\n  }\n}\n",
];

/// What a random script types, one token per step.
const TOKENS: [&str; 34] = [
    "def", " ", "a", "x", "1", "\"", "(", ")", "{", "}", "[", "]", ":", ";", ",", "=", "->", "=>",
    "<-", "-F", "+U", "Integer", "return", "become", "case", "thunk", "force", "run", "fn", "data",
    "Type", "//", "é", "😀",
];

/// What a random script pastes.
const SNIPPETS: [&str; 4] = [
    "def b = a ;\n",
    "case n {\n  Zero => return n\n}",
    "\"text\"",
    "thunk { return 1 }",
];

/// The bytes a `file` URI's path keeps unescaped: RFC 3986's unreserved
/// characters and the separator.
const PATH: &AsciiSet = &NON_ALPHANUMERIC
    .remove(b'-')
    .remove(b'.')
    .remove(b'_')
    .remove(b'~')
    .remove(b'/');

/// One corpus source as an editor opens it.
pub(super) struct Source
{
    /// Its `file` URI.
    pub uri: String,
    /// Its text.
    pub text: String,
}

/// Every corpus source, in path order, under its canonical path so it
/// classifies as the walk classifies it.
///
/// # Specification
/// - requires: the corpus crate sits beside this one.
/// - ensures: one source per `.gandr` file under the corpus's `strict` and
///   `fixture` roots, in path order, each with its percent-escaped `file` URI.
/// - provides: the texts the hover goldens read.
/// - panics: the corpus cannot be read.
///
/// # Adequacy
/// - hypothesis: L3 — the goldens find each headline source here; an empty or
///   truncated walk loses one.
/// - witness: `tests::editor::shapes::the_headline_sources_hover_as_their_goldens`
#[spec(ensures: |ret| ret.len() > 100)]
pub(super) fn corpus() -> Vec<Source>
{
    opened(&gandr_workflow_sweep::corpus::sources().expect("the corpus reads"))
}

/// `sources` as an editor opens them: each one's percent-escaped `file` URI
/// and its text, in the order given.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one source per one given, in order, each URI the `file` URI of
///   its canonical path.
/// - provides: what the corpus sweeps type, erase and hover.
/// - panics: a source cannot be read or its path is not UTF-8.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus sweep opens its sources through this; a lost
///   source or a URI the walk does not classify fails a sweep.
/// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
#[spec(ensures: |ret| ret.len() == sources.len() && ret.iter().all(|source|
    source.uri.starts_with("file://")
        && Path::new(&source.uri).extension().is_some_and(|extension| extension == "gandr")))]
pub(super) fn opened(sources: &[gandr_workflow_sweep::Source]) -> Vec<Source>
{
    sources
        .iter()
        .map(|source| {
            let text = std::fs::read_to_string(&source.path).expect("a corpus source reads");
            let spelled = source.path.to_str().expect("a corpus path is UTF-8");
            Source {
                uri: format!("file://{}", utf8_percent_encode(spelled, PATH)),
                text,
            }
        })
        .collect()
}

/// How the hovers of one node kind's corpus positions answered.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Coverage
{
    /// The positions counted.
    positions: usize,
    /// Those a hover answered at the position's own node, or inside it.
    at_node: usize,
    /// Those a hover answered at a range reaching past the position's node:
    /// an ancestor's answer.
    ancestor: usize,
    /// Those no hover answered.
    unanswered: usize,
    /// Those a hover answered with a `?` in it, wherever it answered.
    unknown: usize,
    /// Those a hover answered in the shape the kind demands.
    shaped: usize,
    /// Those a hover answered in another shape.
    unshaped: usize,
}

impl Coverage
{
    /// This coverage with `other`'s counts added.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &mut self,
        other: Self,
    )
    {
        self.positions = self.positions.saturating_add(other.positions);
        self.at_node = self.at_node.saturating_add(other.at_node);
        self.ancestor = self.ancestor.saturating_add(other.ancestor);
        self.unanswered = self.unanswered.saturating_add(other.unanswered);
        self.unknown = self.unknown.saturating_add(other.unknown);
        self.shaped = self.shaped.saturating_add(other.shaped);
        self.unshaped = self.unshaped.saturating_add(other.unshaped);
    }
}

/// The smallest node with a meaning of its own holding one written leaf of a
/// source.
#[derive(Clone, Debug)]
pub(super) struct Owner
{
    /// The leaf's byte range.
    pub leaf: (usize, usize),
    /// The node's byte range.
    pub node: (usize, usize),
    /// The byte range of the form the leaf is a tile of: the node's own for a
    /// form's keyword or an atom, the form spelling it for a name.
    pub form: (usize, usize),
    /// The node's kind: its form's grammar sort, then its named kind.
    pub kind: String,
}

/// The owner of every written leaf of `text`, in source order.
///
/// # Specification
/// - requires: `text` parses under `grammar`.
/// - ensures: one owner per tile and grout of the tree, ordered by where the
///   leaf starts: a name a form spells as one of its own tiles — an identifier,
///   a constructor, a type's name or variable, such as a declaration's name, a
///   parameter, a loop or a word pattern's letter, and a positional label, the
///   number after one of the form's `.` tiles (#408) — is owned by itself, as
///   kind `<sort> <form> name`, its form the form spelling it; any other tile
///   of the form its parent completes — a keyword, a delimiter, an operator —
///   by that form; any other tile, an atom such as a name, a constructor or a
///   literal, by itself; grout by itself, as kind `grout`. A kind is the sort
///   of the owning form's mold and its named kind, so a name in a pattern and a
///   name in a term are two kinds. Every leaf inside an attribute block or a
///   module member's inline `@[ … ]` — its payload's strings, numbers and names
///   as well as its own tiles — is owned by the attribute, as kind `item
///   attribute_block`, or `item attribute_block name` for a name: an
///   attribute's payload states what its declaration is expected to do, not a
///   term of the program.
/// - provides: the node a hover at a leaf answers by node.
/// - panics: the grammar does not know a mold of the tree, or the parse faults.
///
/// # Adequacy
/// - hypothesis: L3 — the sweep's per-kind table separates a pattern's name,
///   the operator of a cons pattern and the keywords of a match, each measured
///   against the answers the issue recorded.
/// - witness: `tests::editor::scenarios::sweeps::hovering_every_position_of_each_corpus_source_answers_without_fault`
#[spec(ensures: |ret| ret.is_sorted_by_key(|owner| owner.leaf.0)
    && ret.iter().all(|owner| owner.node.0 <= owner.leaf.0 && owner.leaf.1 <= owner.node.1
        && owner.form.0 <= owner.node.0 && owner.node.1 <= owner.form.1))]
fn owners(
    grammar: &Pbg,
    text: SourceText<'_>,
) -> Vec<Owner>
{
    let parsed = parse(grammar, text).expect("a corpus source parses");
    let tree = parsed.tree();
    let mut parents: Vec<Option<NodeIndex>> = vec![None; usize::from(tree.node_count())];
    for position in tree.positions() {
        for child in tree.children(position) {
            if let Some(held) = parents.get_mut(usize::from(child)) {
                *held = Some(position);
            }
        }
    }
    let kind = |mold: MoldId| {
        format!(
            "{} {}",
            grammar
                .mold(mold)
                .expect("a tree's mold is known")
                .sort
                .name(),
            grammar.named_kind(mold).expect("a tree's mold is known").0
        )
    };
    let rule = |mold: MoldId| grammar.rule_of(mold).expect("a tree's mold is known").name;
    let range = |node: &Node| {
        (
            usize::from(node.span().start()),
            usize::from(node.span().end()),
        )
    };
    let mut owners = Vec::new();
    let mut attributes: Vec<(usize, usize)> = Vec::new();
    let mut after_dot: Option<(usize, usize)> = None;
    for position in tree.positions() {
        let node = tree.node(position).expect("a position names a node");
        let (owner, form, kind) = match node.label() {
            NodeLabel::Meld(form) => {
                if grammar.named_kind(form).expect("a tree's mold is known").0 == "attribute_block"
                {
                    attributes.push(range(node));
                }
                // A module member writes its attributes inline, as its own
                // `@[ … ]` tiles before its keyword.
                if kind(form) == "module_member module_declaration" {
                    let mut open = None;
                    for child in tree.children(position) {
                        let Some(child) = tree.node(child)
                        else {
                            continue;
                        };
                        let NodeLabel::Tile(tile) = child.label()
                        else {
                            continue;
                        };
                        match (
                            grammar.mold(tile).expect("a tree's mold is known").label,
                            open,
                        ) {
                            ("@[", None) => open = Some(range(child).0),
                            ("]", Some(start)) => {
                                attributes.push((start, range(child).1));
                                open = None;
                            },
                            ("def" | "type", None) => break,
                            _ => {},
                        }
                    }
                }
                continue;
            },
            NodeLabel::Tile(mold) => {
                let parent = parents
                    .get(usize::from(position))
                    .copied()
                    .flatten()
                    .and_then(|parent| tree.node(parent));
                let label = grammar.mold(mold).expect("a tree's mold is known").label;
                let dotted = after_dot.take();
                match parent.map(|parent| (parent, parent.label())) {
                    Some((parent, NodeLabel::Meld(form))) if rule(form) == rule(mold) => {
                        // A positional label, the number after a form's `.`, names
                        // its entry as a written label does.
                        if label == "." {
                            after_dot = Some(range(parent));
                        }
                        if NAMES.contains(&label)
                            || (label == "number" && dotted == Some(range(parent)))
                        {
                            (range(node), range(parent), format!("{} name", kind(form)))
                        }
                        else {
                            (range(parent), range(parent), kind(form))
                        }
                    },
                    Some(_) | None => (range(node), range(node), kind(mold)),
                }
            },
            NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. } => {
                (range(node), range(node), String::from("grout"))
            },
            NodeLabel::Wald | NodeLabel::Space | NodeLabel::Doc => continue,
        };
        owners.push(Owner {
            leaf: range(node),
            node: owner,
            form,
            kind,
        });
    }
    for owner in &mut owners {
        if let Some(&block) = attributes
            .iter()
            .find(|block| block.0 <= owner.leaf.0 && owner.leaf.1 <= block.1)
        {
            owner.kind = if owner.kind.ends_with(" name") {
                String::from("item attribute_block name")
            }
            else {
                String::from("item attribute_block")
            };
            owner.node = block;
            owner.form = block;
        }
    }
    owners.sort_by_key(|owner| owner.leaf.0);
    owners
}

/// The protocol position `at`.
///
/// # Specification
/// trivial.
pub(super) fn spot(at: &Value) -> Position
{
    let coordinate = |name: &str| {
        at[name]
            .as_u64()
            .and_then(|coordinate| u32::try_from(coordinate).ok())
            .expect("a position's coordinates are 32-bit")
    };
    Position {
        line: coordinate("line"),
        character: coordinate("character"),
    }
}

#[test]
fn positions_count_utf16_code_units()
{
    let text = Text("é😀x\ny");
    assert_eq!(
        Position::of(text, Offset(0)),
        Position {
            line: 0,
            character: 0
        },
        "the origin"
    );
    assert_eq!(
        Position::of(text, Offset("é".len())),
        Position {
            line: 0,
            character: 1
        },
        "a two-byte character is one code unit"
    );
    assert_eq!(
        Position::of(text, Offset("é😀".len())),
        Position {
            line: 0,
            character: 3
        },
        "an astral character is two code units"
    );
    assert_eq!(
        Position::of(text, Offset("é😀x\n".len())),
        Position {
            line: 1,
            character: 0
        },
        "a newline starts the next line"
    );
}

#[test]
fn assisted_typing_closes_and_steps_over_pairs()
{
    let mut buffer = Buffer::holding(Text(""), Typing::Assisted);
    let _typed: Vec<_> = "f("
        .chars()
        .map(|typed| buffer.type_char(Key(typed)))
        .collect();
    assert_eq!(
        (buffer.text(), buffer.cursor()),
        (Text("f()"), Offset(2)),
        "an opener closes itself"
    );
    assert!(
        buffer.type_char(Key(')')).is_empty(),
        "a typed closer steps over the inserted one"
    );
    assert_eq!(buffer.cursor(), Offset(3), "the cursor passes the closer");
    let _space = buffer.type_char(Key(' '));
    let _brace = buffer.type_char(Key('{'));
    let _enter = buffer.enter();
    assert_eq!(
        (buffer.text(), buffer.cursor()),
        (Text("f() {\n  \n}"), Offset(8)),
        "Enter between braces opens an indented line"
    );
    let _undone = buffer.undo();
    assert_eq!(
        (buffer.text(), buffer.cursor()),
        (Text("f() {}"), Offset(5)),
        "undo restores the pair"
    );
    let _deleted = buffer.backspace();
    assert_eq!(
        buffer.text(),
        Text("f() "),
        "backspace inside an empty pair deletes both"
    );
    let mut quoted = Buffer::holding(Text(""), Typing::Assisted);
    let _opened = quoted.type_char(Key('"'));
    let _letter = quoted.type_char(Key('a'));
    assert!(
        quoted.type_char(Key('"')).is_empty(),
        "a closing quote steps over"
    );
    assert_eq!(quoted.text(), Text("\"a\""), "the string is closed once");
    let mut nested = Buffer::holding(Text("  "), Typing::Assisted);
    let _outdented = nested.type_char(Key('}'));
    assert_eq!(
        nested.text(),
        Text("}"),
        "a closer first on a line outdents"
    );
}

/// One step of a random edit script.
#[derive(Clone, Copy, Debug)]
enum Edit
{
    /// Type a token, one keystroke per character.
    Type(&'static str),
    /// Press Enter.
    Enter,
    /// Press backspace.
    Backspace,
    /// Press delete.
    Delete,
    /// Move the cursor to this many thousandths of the text.
    Move(usize),
    /// Delete the cursor's line.
    DeleteLine,
    /// Paste a snippet at the cursor.
    Paste(&'static str),
    /// Undo the latest edit.
    Undo,
}

/// The edits a random script draws from, weighted towards typing.
///
/// # Specification
/// trivial.
fn edit() -> impl Strategy<Value = Edit>
{
    prop_oneof![
        6 => select(TOKENS.as_slice()).prop_map(Edit::Type),
        2 => Just(Edit::Enter),
        3 => Just(Edit::Backspace),
        1 => Just(Edit::Delete),
        3 => (0_usize ..= 1000_usize).prop_map(Edit::Move),
        1 => Just(Edit::DeleteLine),
        1 => select(SNIPPETS.as_slice()).prop_map(Edit::Paste),
        2 => Just(Edit::Undo),
    ]
}

/// Apply `edit` to `session`, keystroke by keystroke.
///
/// # Specification
/// trivial.
fn apply(
    session: &mut Session,
    edit: Edit,
)
{
    match edit {
        Edit::Type(token) => token
            .chars()
            .for_each(|typed| session.type_char(Key(typed))),
        Edit::Enter => session.enter(),
        Edit::Backspace => session.backspace(),
        Edit::Delete => session.delete(),
        Edit::Move(thousandths) => {
            let text = session.buffer().text().0;
            let at = text
                .len()
                .saturating_mul(thousandths)
                .checked_div(1000_usize)
                .expect("a thousandth divides");
            let at = text.floor_char_boundary(at);
            session.move_to(Offset(at));
        },
        Edit::DeleteLine => {
            let text = session.buffer().text().0;
            let cursor = session.buffer().cursor().0;
            let start = text
                .get(.. cursor)
                .and_then(|before| before.rfind('\n'))
                .map_or(0_usize, |newline| newline.saturating_add(1));
            let end = text
                .get(cursor ..)
                .and_then(|after| after.find('\n'))
                .map_or(text.len(), |newline| {
                    cursor.saturating_add(newline).saturating_add(1)
                });
            session.replace(Offset(start), Offset(end), Text(""));
        },
        Edit::Paste(snippet) => {
            let cursor = session.buffer().cursor();
            session.replace(cursor, cursor, Text(snippet));
        },
        Edit::Undo => session.undo(),
    }
}

/// Visit every source, spread over the machine's cores, the longest first so
/// no core is left with a long source at the end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `visit` ran once on each source; a panic in any visit fails the
///   caller once every worker has stopped, its message naming the source the
///   visit was given.
/// - provides: the corpus scenarios' wall time divided by the cores.
/// - panics: a visit panics.
/// - executable: none — the visits' effects are their own assertions, made on
///   worker threads; the call returns nothing that records them.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus scenarios visit through here; one shared index
///   hands each source to exactly one worker, and a panic in a worker fails the
///   scope, so a failing source fails the scenario, and the run's log names it.
/// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
fn each_in_parallel(
    sources: &[Source],
    visit: impl Fn(&Source) + Sync,
)
{
    let mut ordered: Vec<&Source> = sources.iter().collect();
    ordered.sort_by_key(|source| core::cmp::Reverse(source.text.len()));
    let next = AtomicUsize::new(0_usize);
    let workers = std::thread::available_parallelism().map_or(1_usize, NonZeroUsize::get);
    std::thread::scope(|scope| {
        for _ in 0_usize .. workers {
            let _worker = scope.spawn(|| {
                while let Some(source) = ordered.get(next.fetch_add(1_usize, Ordering::Relaxed)) {
                    if let Err(payload) = catch_unwind(AssertUnwindSafe(|| visit(source))) {
                        panic!("visiting {}: {}", source.uri, panic_message(&*payload).0);
                    }
                }
            });
        }
    });
}

/// How many positions apart a hover sweep hovers a source; at least one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Every(pub usize);

/// One position of a corpus source as the sweep hovers it.
pub(super) struct Hovered
{
    /// Its byte offset.
    pub offset: usize,
    /// Whether it lies in a comment, which is hovered but not counted.
    pub comment: bool,
    /// The smallest node with a meaning of its own holding it; none for
    /// layout and for a comment.
    pub owner: Option<Owner>,
    /// The hover's answer, `null` for none.
    pub shown: Value,
}

/// The positions of `source` from the first, `every` apart, and the first
/// position of each name and constructor pattern, whose answers
/// [`shapes::judged`] reads for the positions they head, each hovered over a
/// fresh connection opening it whole. An `every` of one hovers every position.
///
/// # Specification
/// - requires: `source` parses under `grammar`.
/// - ensures: one entry per hovered position — each character boundary of the
///   text and its end whose rank among them is a multiple of `every`, and each
///   boundary starting the leaf of a name or of a constructor pattern — in
///   order, each with whether a comment holds it — a line comment holding the
///   newline that closes it — the owner of the written leaf holding it — none
///   for layout and comments — and the hover's answer.
/// - provides: the input of the sweep and of the hover goldens.
/// - panics: a written byte lies in no leaf, or the server faults.
///
/// # Adequacy
/// - hypothesis: L3 — the sweep counts the non-comment positions of the corpus
///   it hovers through this, and the goldens pin every answer of five sources.
/// - witness: `tests::editor::scenarios::sweeps::hovering_every_position_of_each_corpus_source_answers_without_fault`
/// - witness: `tests::editor::shapes::the_headline_sources_hover_as_their_goldens`
/// - witness: `tests::editor::scenarios::a_line_comment_holds_the_newline_closing_it_456`
#[spec(ensures: |ret| ret.len() <= source.text.chars().count().saturating_add(1)
    && (every.0 > 1 || ret.len() == source.text.chars().count().saturating_add(1)))]
pub(super) fn hovered(
    grammar: &Pbg,
    source: &Source,
    every: Every,
) -> Vec<Hovered>
{
    let owners = owners(grammar, SourceText::from(source.text.as_str()));
    let mut client = Client::initialized(Record::Dropped, Quiet::Unheld);
    let _opened = client.notify(
        Method("textDocument/didOpen"),
        &json!({ "textDocument": {
            "uri": source.uri, "languageId": "gandr", "version": 1_i32, "text": source.text,
        }}),
    );
    let text = Text(&source.text);
    let comments: Vec<(usize, usize)> = label(SourceFragment::from(source.text.as_str()))
        .into_iter()
        .filter(|token| token.lexeme == Lexeme::Space)
        .filter_map(|token| {
            let start = usize::try_from(token.start).ok()?;
            let end = usize::try_from(token.end).ok()?;
            let layout = source.text.get(start .. end)?;
            // A line comment's token stops short of the newline closing it,
            // which belongs to the comment: commenting an item moves no count.
            let closes = layout.starts_with("//")
                && source
                    .text
                    .get(end ..)
                    .is_some_and(|rest| rest.starts_with('\n'));
            (layout.starts_with("//") || layout.starts_with("/*"))
                .then_some((start, end.saturating_add(usize::from(closes))))
        })
        .collect();
    // The leaves whose first answer the shape judgement reads for the other
    // positions of their form: a name's, and a constructor pattern's.
    let heads: Vec<usize> = owners
        .iter()
        .filter(|owner| {
            owner.kind.ends_with(" name") || owner.kind == "pattern constructor_pattern"
        })
        .map(|owner| owner.leaf.0)
        .collect();
    source
        .text
        .char_indices()
        .map(|(offset, _)| offset)
        .chain([source.text.len()])
        .enumerate()
        .filter(|&(rank, offset)| {
            rank.checked_rem(every.0) == Some(0_usize) || heads.binary_search(&offset).is_ok()
        })
        .map(|(_, offset)| {
            let at = Position::of(text, Offset(offset));
            let shown = client.request(
                Method("textDocument/hover"),
                &json!({ "textDocument": { "uri": source.uri }, "position": at.json() }),
            );
            let comment = comments
                .iter()
                .any(|&(start, end)| (start .. end).contains(&offset));
            let written = !comment
                && source
                    .text
                    .get(offset ..)
                    .and_then(|rest| rest.chars().next())
                    .is_some_and(|glyph| !glyph.is_whitespace());
            let owner = written.then(|| {
                owners
                    .partition_point(|owner| owner.leaf.0 <= offset)
                    .checked_sub(1_usize)
                    .and_then(|at| owners.get(at))
                    .filter(|owner| offset < owner.leaf.1)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!("{}: byte {offset} is written but in no leaf", source.uri)
                    })
            });
            Hovered {
                offset,
                comment,
                owner,
                shown,
            }
        })
        .collect()
}

#[test]
fn fixing_a_mismatch_clears_its_diagnostic()
{
    let text = "def a : Integer ;\ndef a = 1 ;\n";
    let mut session = Session::open(
        String::from("file:///strict/mismatch.gandr"),
        Text(text),
        Typing::Assisted,
        Oracle::Keystroke,
    );
    assert_eq!(session.codes(), Vec::<Value>::new(), "the document checks");
    let one = text.rfind('1').expect("the value is written");
    session.move_to(Offset(one.saturating_add(1)));
    session.backspace();
    session.type_in(Text("\"text\""));
    assert_eq!(
        session.codes(),
        [json!("TypeMismatch")],
        "a string is not an integer"
    );
    for _ in 0_u8 .. 6_u8 {
        session.backspace();
    }
    session.type_in(Text("1"));
    assert_eq!(
        session.codes(),
        Vec::<Value>::new(),
        "the fix clears the diagnostic"
    );
    session.closes_over_streams();
}

#[test]
fn defining_a_missing_name_clears_its_diagnostic()
{
    let mut session = Session::open(
        String::from("file:///strict/missing.gandr"),
        Text("def b = a ;\n"),
        Typing::Assisted,
        Oracle::Keystroke,
    );
    assert_eq!(
        session.codes(),
        [json!("UnresolvedName")],
        "`a` is not defined"
    );
    session.move_to(Offset(0));
    session.type_in(Text("def a = 1 ;\n"));
    assert_eq!(
        session.codes(),
        Vec::<Value>::new(),
        "defining `a` clears the diagnostic"
    );
    session.closes_over_streams();
}

#[test]
fn restoring_a_semicolon_clears_its_diagnostic()
{
    let text = "def a = 1 ;\ndef b = a ;\n";
    let mut session = Session::open(
        String::from("file:///strict/semicolon.gandr"),
        Text(text),
        Typing::Assisted,
        Oracle::Keystroke,
    );
    let semicolon = text.find(';').expect("the first definition ends");
    session.move_to(Offset(semicolon.saturating_add(1)));
    session.backspace();
    assert!(
        !session.codes().is_empty(),
        "a definition without its `;` is refused"
    );
    session.type_char(Key(';'));
    assert_eq!(
        session.codes(),
        Vec::<Value>::new(),
        "the `;` clears the diagnostic"
    );
    session.closes_over_streams();
}

/// #776: an importer erased twice in one process — the first time over the
/// process's held readings and closures as it found them, the second with
/// everything the first held — answers alike at every keystroke: the same
/// diagnostics, inline completions and hovers. Every keystroke of each run
/// is also held to a fresh connection's answers.
#[test]
fn an_importer_erased_cold_and_warm_answers_alike_776()
{
    let source = corpus()
        .into_iter()
        .find(|source| {
            source
                .uri
                .ends_with("corpus/model/identity/loop-winding.gandr")
        })
        .expect("the corpus holds the winding number");
    let erased = || {
        let mut session = Session::open(
            source.uri.clone(),
            Text(&source.text),
            Typing::Assisted,
            Oracle::Keystroke,
        );
        session.erase_lines(Stride(6));
        let answers = session.answers().to_vec();
        session.closes_over_streams();
        answers
    };
    let cold = erased();
    assert!(
        cold.len() > 10_usize,
        "every keystroke is read: {}",
        cold.len()
    );
    assert_eq!(
        erased(),
        cold,
        "the warm erasure answers as the cold one did"
    );
}

/// The document the quiet scenario types into: three declarations, the last
/// naming the first.
const QUIET_SEED: &str = "def one = 1 ;\ndef mid = 2 ;\ndef two = one ;\n";

/// The document's URI.
const QUIET_URI: &str = "file:///strict/quiet.gandr";

/// The declaration the quiet scenario types on the line after the seed's.
const QUIET_DECLARATION: &str = "def three = two ;";

/// Each diagnostic notification among `messages`, as the `[code, line]` of
/// each diagnostic it publishes.
///
/// # Specification
/// trivial.
fn publications(messages: &[Value]) -> Vec<Vec<Value>>
{
    messages
        .iter()
        .filter(|message| message.get("method") == Some(&json!("textDocument/publishDiagnostics")))
        .map(|message| {
            message
                .pointer("/params/diagnostics")
                .and_then(Value::as_array)
                .map(|diagnostics| {
                    diagnostics
                        .iter()
                        .map(|diagnostic| {
                            json!([
                                diagnostic.get("code"),
                                diagnostic.pointer("/range/start/line")
                            ])
                        })
                        .collect()
                })
                .unwrap_or_default()
        })
        .collect()
}

/// A connection with [`QUIET_SEED`] open at [`QUIET_URI`], changed one
/// ranged change at a time, each at the next version.
struct Typist
{
    /// The connection.
    client: Client,
    /// The version the latest change carried.
    version: i32,
}

impl Typist
{
    /// A connection at the quiet interval `quiet`, the seed open at version 1.
    ///
    /// # Specification
    /// trivial.
    fn opened(quiet: Quiet) -> Self
    {
        let mut client = Client::initialized(Record::Dropped, quiet);
        let _opened = client.notify(
            Method("textDocument/didOpen"),
            &json!({ "textDocument": {
                "uri": QUIET_URI, "languageId": "gandr", "version": 1_i32, "text": QUIET_SEED,
            } }),
        );
        Self {
            client,
            version: 1_i32,
        }
    }

    /// Replace what lies from `start` to `end` with `text` in one ranged
    /// change, and return its publications.
    ///
    /// # Specification
    /// trivial.
    fn replace(
        &mut self,
        start: Position,
        end: Position,
        Text(text): Text<'_>,
    ) -> Vec<Vec<Value>>
    {
        self.version = self.version.saturating_add(1_i32);
        publications(&self.client.notify(
            Method("textDocument/didChange"),
            &json!({
                "textDocument": { "uri": QUIET_URI, "version": self.version },
                "contentChanges": [{
                    "range": {
                        "start": { "line": start.line, "character": start.character },
                        "end": { "line": end.line, "character": end.character },
                    },
                    "text": text,
                }],
            }),
        ))
    }

    /// Type `text` at `at`, one character a change, and return each
    /// keystroke's publications.
    ///
    /// # Specification
    /// trivial.
    fn type_at(
        &mut self,
        at: Position,
        Text(text): Text<'_>,
    ) -> Vec<Vec<Vec<Value>>>
    {
        let mut caret = at;
        text.chars()
            .map(|typed| {
                let published = self.replace(caret, caret, Text(typed.encode_utf8(&mut [0_u8; 4])));
                caret.character = caret
                    .character
                    .saturating_add(u32::try_from(typed.len_utf16()).unwrap_or(u32::MAX));
                published
            })
            .collect()
    }

    /// Let the document's quiet interval pass, and return what that
    /// publishes.
    ///
    /// # Specification
    /// trivial.
    fn lapse(&mut self) -> Vec<Vec<Value>>
    {
        publications(&self.client.lapse(&DocumentUri::from(QUIET_URI)))
    }
}

#[test]
fn typing_a_declaration_holds_its_diagnostics_until_its_terminator()
{
    let at = |line: u32, character: u32| Position { line, character };
    let seed_lines = u32::try_from(QUIET_SEED.lines().count()).expect("the seed is short");
    let declared = u32::try_from(QUIET_DECLARATION.len()).expect("the declaration is short");

    // With a zero interval, each keystroke publishes what a fresh connection
    // opening the same text does: the unfinished declaration is red from its
    // first character to its last.
    let mut unheld = Typist::opened(Quiet::Unheld);
    let today = unheld.type_at(at(seed_lines, 0), Text(QUIET_DECLARATION));
    let mut text = String::new();
    for (cut, publications) in QUIET_DECLARATION
        .char_indices()
        .map(|(offset, typed)| offset.saturating_add(typed.len_utf8()))
        .zip(&today)
    {
        let mut fresh = Client::initialized(Record::Dropped, Quiet::Default);
        let typed = QUIET_DECLARATION.get(.. cut).unwrap_or_default();
        text.clear();
        text.push_str(QUIET_SEED);
        text.push_str(typed);
        let opened = fresh.notify(
            Method("textDocument/didOpen"),
            &json!({ "textDocument": {
                "uri": QUIET_URI, "languageId": "gandr", "version": 1_i32, "text": text.as_str(),
            } }),
        );
        assert_eq!(
            *publications,
            self::publications(&opened),
            "with a zero interval, typing `{text}` publishes what opening it does"
        );
    }
    let unfinished = |code: &str| vec![vec![json!([code, seed_lines])]];
    // `d` and `de` stand last at the root: a run target naming nothing.
    let mut expected = vec![unfinished("UnresolvedName"); 2];
    expected.extend(vec![
        unfinished("MalformedForm");
        QUIET_DECLARATION.len().saturating_sub(3)
    ]);
    expected.push(vec![Vec::new()]);
    assert_eq!(
        today, expected,
        "each keystroke of the declaration is red until its `;`"
    );

    // Under the interval, nothing of the declaration under the caret
    // publishes; the `;` that ends it leaves nothing held.
    let mut quiet = Typist::opened(Quiet::Default);
    assert_eq!(
        quiet.type_at(at(seed_lines, 0), Text(QUIET_DECLARATION)),
        vec![vec![Vec::<Value>::new()]; QUIET_DECLARATION.len()],
        "the declaration under the caret publishes nothing while it is typed"
    );
    assert_eq!(
        quiet.lapse(),
        Vec::<Vec<Value>>::new(),
        "and its `;` leaves nothing held"
    );

    // A declaration left unfinished is held while the caret is in it.
    let line = seed_lines.saturating_add(1);
    assert_eq!(
        quiet.type_at(at(seed_lines, declared), Text("\n")),
        [vec![Vec::<Value>::new()]],
        "a new line after the `;` publishes nothing"
    );
    assert_eq!(
        quiet.type_at(at(line, 0), Text("def four =")),
        vec![vec![Vec::<Value>::new()]; 10],
        "an unfinished declaration under the caret publishes nothing"
    );

    // An edit two declarations above `two` refuses it on that keystroke, and
    // the caret leaving the unfinished declaration publishes its refusal.
    // `three`, which names `two`, is noted as unsettled by that refusal.
    assert_eq!(
        quiet.replace(at(0, 7), at(0, 7), Text("s")),
        [vec![
            json!(["UnresolvedName", 2_i32]),
            json!(["UnknownConstant", seed_lines]),
            json!(["MalformedForm", line]),
        ]],
        "the refusal the edit causes below publishes at once, and the declaration the caret left publishes"
    );
    assert_eq!(
        quiet.replace(at(0, 7), at(0, 8), Text("")),
        [vec![json!(["MalformedForm", line])]],
        "undoing the edit clears its refusal"
    );

    // Back in the unfinished declaration, its refusal is held again until
    // the document is quiet for the interval.
    assert_eq!(
        quiet.type_at(at(line, 10), Text(" 4")),
        vec![vec![Vec::<Value>::new()]; 2],
        "typing in the unfinished declaration holds its refusal again"
    );
    assert_eq!(
        quiet.lapse(),
        [vec![json!(["MalformedForm", line])]],
        "the interval passing publishes the held refusal"
    );
    assert_eq!(
        quiet.lapse(),
        Vec::<Vec<Value>>::new(),
        "a released refusal is published once"
    );
    assert_eq!(
        quiet.type_at(at(line, 12), Text(" ;")),
        [vec![Vec::<Value>::new()], vec![Vec::new()]],
        "typing in the declaration again holds its refusal again, and the `;` clears it"
    );
    assert_eq!(
        quiet.lapse(),
        Vec::<Vec<Value>>::new(),
        "the finished declaration holds nothing"
    );
}

/// A line comment holds the newline that closes it, so commenting an item adds
/// no position the sweep counts (#456): every position from the `//` through
/// the line's end is a comment's, and the next line's first is not.
#[test]
fn a_line_comment_holds_the_newline_closing_it_456()
{
    let text = "// a note\ndata Unit : Type { Tt : Unit; }\n";
    let source = Source {
        uri: String::from("file:///comment-line-end.gandr"),
        text: String::from(text),
    };
    let grammar = built_in().expect("the built-in grammar builds");
    let hovers = hovered(&grammar, &source, Every(1));
    let newline = text.find('\n').expect("the comment ends its line");
    let commented: Vec<usize> = hovers
        .iter()
        .filter(|hover| hover.comment)
        .map(|hover| hover.offset)
        .collect();
    assert_eq!(
        commented,
        (0_usize ..= newline).collect::<Vec<_>>(),
        "the comment holds its text and its closing newline, nothing after"
    );
}

/// The corpus sweeps and the random edit scripts. The typing and erasure
/// sweeps and the scripts visit the sample their constants state under every
/// pull-request profile and everything under the `sweeps` profile
/// (`gandr-workflow-sweep`): every source, every script from a fresh seed. A
/// sample ranks the corpus by its BLAKE3 digest under the sweep's name, holds
/// at least one source of each corpus class — `strict` and each directory
/// below `fixture` — and adds every source the change adds or modifies, so a
/// corpus edit is swept on the pull request that makes it. The hover sweep
/// prints its counts by node kind as a report and holds no ceiling on them
/// (#467).
mod sweeps
{
    use gandr_surface_dispatcher::classify;
    use gandr_surface_dispatcher::lay_out;
    use gandr_workflow_sweep::Nights;
    use gandr_workflow_sweep::Rotation;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use proptest::test_runner::RngSeed;

    use super::*;

    /// The random edit scripts each scenario generates under the `sweeps`
    /// profile, each run from a fresh seed.
    const CASES: Cases = Cases(32);

    /// The random edit scripts each scenario generates under every
    /// pull-request profile: a quarter of the whole's, drawn from
    /// [`SCRIPTS_SEED`] so every run generates the same eight.
    const SAMPLED_CASES: Cases = Cases(8);

    /// A count of random scripts a scenario generates.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Cases(u32);

    /// The seed the sampled scripts are drawn from.
    const SCRIPTS_SEED: u64 = 0x6761_6e64_7273_7765;

    /// The typing sweep's sample: sixteen sources no longer than
    /// [`TYPED_CEILING`], every keystroke held to the oracle.
    const TYPED: Sample = Sample {
        name: SampleName("typing_each_corpus_source_keeps_every_answer_faithful"),
        size: SampleSize(16),
    };

    /// The most bytes one check of a source the typing sweep's sample types
    /// may read ([`checked`]): typing costs a check per keystroke over the
    /// whole text the server judges, the source laid out after its import
    /// closure, so a source whose check reads more types for longer than the
    /// bound. The λ-calculus model's laws, half a kibibyte each over a 10 KB
    /// closure, typed for 4.5 to 6.8 s each with specifications enforced, and
    /// a 1 KB refusal over a 13 KB closure for 12.8 s. A changed source past
    /// it is typed nightly, a part of it each night; the erasure and the hover
    /// sweep visit it on the pull request within their own ceilings
    /// ([`ERASED_CEILING`], [`HOVERED_CEILING`]).
    const TYPED_CEILING: Ceiling = Ceiling(1024);

    /// How many parts the nightly typing cuts every source into, one typed a
    /// night: a sixty-fourth of typing the whole corpus each night, and of
    /// its costliest source, every keystroke within sixty-four nights. A
    /// quarter of every source typed for 317 s to 480 s on the nightly runner,
    /// a sixteenth for 139 s to 163 s and a thirty-second for 90 s, past its
    /// share of the nightly budget.
    const TYPED_NIGHTS: Nights = Nights(64);

    /// The erasure's sample: twenty-four sources, every keystroke held to the
    /// oracle.
    const ERASED: Sample = Sample {
        name: SampleName("erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful"),
        size: SampleSize(24),
    };

    /// The nights the nightly erasure takes to erase every source: a
    /// sixteenth a night. A quarter erased for 89 s to 93 s on the nightly
    /// runner, and an eighth for 60 s.
    const ERASED_NIGHTS: Nights = Nights(16);

    /// The most keystrokes a sampled erasure spends on one source. Each
    /// keystroke checks the whole text left, so erasing a source line by line
    /// costs its length squared: the 196 lines of the circle group's model
    /// took 13.7 s alone on a local machine and timed out on the Linux runner,
    /// about three times slower. A sampled erasure of a longer source deletes
    /// as many lines per keystroke as keep it to this many, and its checks to
    /// [`ERASED_BYTES`]. The `sweeps` profile erases every source line by
    /// line.
    const ERASED_KEYSTROKES: usize = 48;

    /// The most bytes a sampled erasure's checks read for one source, summed
    /// over its keystrokes: 32 KiB. A keystroke checks the text left laid out
    /// after the source's import closure ([`checked`]), so a short source
    /// over a long closure pays the closure's check at every keystroke, and
    /// the oracle a fresh session's beside it: the λ-calculus model's sources,
    /// 10 to 42 KB a check, erased for 0.5 to 2.5 s each with specifications
    /// enforced in two to nine keystrokes, and together took the macOS
    /// runner's erasure past the bound. A source whose check reads more than
    /// a 48th of this erases in fewer keystrokes, one at least.
    const ERASED_BYTES: usize = 0x8000;

    /// The most bytes one check of a source a sampled erasure visits may
    /// read: half of [`ERASED_BYTES`], since opening a source and erasing it
    /// in a single keystroke checks it twice. A changed source past it is
    /// erased under the `sweeps` and nightly profiles; of the sources before
    /// the λ-calculus model, the loop space, the open fold and the two
    /// univalence sources are.
    const ERASED_CEILING: Ceiling = Ceiling(ERASED_BYTES.div_euclid(2));

    /// The stride a run erases `source` at: one line per keystroke under the
    /// `sweeps` profile; otherwise as many lines as keep it to
    /// [`ERASED_KEYSTROKES`] keystrokes and its checks to [`ERASED_BYTES`].
    ///
    /// # Specification
    /// trivial.
    fn erased_stride(
        grammar: &Pbg,
        source: &Source,
    ) -> Stride
    {
        match gandr_workflow_sweep::Coverage::asked() {
            gandr_workflow_sweep::Coverage::Full => Stride(1),
            gandr_workflow_sweep::Coverage::Sampled => {
                let keystrokes = ERASED_BYTES
                    .checked_div(checked(grammar, source).0)
                    .unwrap_or(ERASED_KEYSTROKES)
                    .clamp(1, ERASED_KEYSTROKES);
                Stride(source.text.lines().count().div_ceil(keystrokes).max(1))
            },
        }
    }

    /// The hover sweep's sample with specifications enforced: forty-eight
    /// sources, each hovered at the positions [`hovered_every`] spaces.
    const HOVERED: Sample = Sample {
        name: SampleName("hovering_every_position_of_each_corpus_source_answers_without_fault"),
        size: SampleSize(48),
    };

    /// The nights the nightly hover sweep takes to hover every source: a
    /// sixteenth a night. A quarter hovered for 84 s to 94 s on the nightly
    /// runner, and an eighth for 68 s.
    const HOVERED_NIGHTS: Nights = Nights(16);

    /// The most a sampled hover of one source costs, counted as the positions
    /// it hovers times the bytes its check reads ([`checked`]): 4 MiB. A
    /// hover answers from the type table of the whole text the server judges,
    /// and the types it prints grow with the development that text lays out:
    /// the λ-calculus model's record, 3796 positions over a 41 KB closure,
    /// hovered for 17.3 s with specifications enforced, its 9 KB base, 5239
    /// positions, for 0.6 s. A source past it is hovered as many positions
    /// apart as keep it within.
    const HOVERED_BYTES: usize = 0x0040_0000;

    /// The most bytes one check of a source a sampled hover visits may read:
    /// 16 KiB. The first position of each name and constructor pattern is
    /// hovered however far apart the others are ([`hovered`]), so spacing
    /// bounds a long closure's cost only so far: hovered ten apart, the
    /// λ-calculus model's sources together took the macOS runner's hover sweep
    /// to 27 s, and thirty-eight apart its record still hovered for 1.4 s. A
    /// changed source past it is hovered under the `sweeps` and nightly
    /// profiles; of the sources before that model, the loop space, the open
    /// fold and the two univalence sources are.
    const HOVERED_CEILING: Ceiling = Ceiling(0x4000);

    /// How many positions apart a run hovers `source`: one under the `sweeps`
    /// profile; otherwise as few as keep its positions times its [`checked`]
    /// bytes within [`HOVERED_BYTES`].
    ///
    /// # Specification
    /// trivial.
    fn hovered_every(
        grammar: &Pbg,
        source: &Source,
    ) -> Every
    {
        match gandr_workflow_sweep::Coverage::asked() {
            gandr_workflow_sweep::Coverage::Full => Every(1),
            gandr_workflow_sweep::Coverage::Sampled => Every(
                source
                    .text
                    .chars()
                    .count()
                    .saturating_add(1)
                    .saturating_mul(checked(grammar, source).0)
                    .div_ceil(HOVERED_BYTES)
                    .max(1),
            ),
        }
    }

    /// The bytes one check of a source reads.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct Checked(usize);

    /// The bytes one check of `source` reads: the text the server judges it
    /// in, its import closure laid out before its own text, or its own text
    /// when it imports nothing. The prelude laid before every unit is not
    /// counted: its items are adopted, never judged at a keystroke.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the length of the text [`lay_out`] lays out for the path of
    ///   `source`'s URI under the root that path classifies as, past the
    ///   prelude; never less than the own text's.
    /// - provides: the size the typing ceiling, the erasure's keystrokes and
    ///   the hover's spacing bound a source's work by.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — measured by its own bytes alone, a short source over
    ///   a long closure types, erases and hovers its closure's check at every
    ///   step unbounded: the λ-calculus model's sources took each of the three
    ///   sweeps to the test bound.
    /// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `tests::editor::scenarios::sweeps::erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful`
    /// - witness: `tests::editor::scenarios::sweeps::hovering_every_position_of_each_corpus_source_answers_without_fault`
    #[spec(ensures: |ret| ret.0 >= source.text.len())]
    fn checked(
        grammar: &Pbg,
        source: &Source,
    ) -> Checked
    {
        let path = DocumentUri::from(source.uri.as_str()).path();
        Checked(
            lay_out(
                grammar,
                &path,
                classify(&path),
                SourceText::from(source.text.as_str()),
            )
            .text
            .len()
            .saturating_sub(usize::from(gandr_surface_lowering::prelude::base())),
        )
    }

    /// The bytes one check of a source may read past which a sampled sweep
    /// leaves the source to the `sweeps` profile.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Ceiling(usize);

    /// How a corpus sweep spreads its whole over the nights of the `nightly`
    /// profile.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Nightly
    {
        /// The night's slice of the sources, each visited whole.
        Slice(Nights),
        /// Every source, the night's part of each.
        Part,
    }

    /// The sources `sample` visits in this run, the longest first so the
    /// longest starts at once, and the rotation they are visited under. A
    /// sampled run under a `ceiling` draws from the sources whose check reads
    /// no more bytes than it ([`checked`]); the `sweeps` profile visits every
    /// source whole, and the `nightly` profile the night's slice of them or the
    /// night's part of each, as `nightly` says.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the rotation [`Sweep::asked`] reads, and the visited sources
    ///   sorted longest first: under [`Nightly::Slice`] what
    ///   [`Sweep::visit_rotating`] returns over its nights, under
    ///   [`Nightly::Part`] what [`Sweep::visit`] returns.
    /// - provides: the sources each corpus sweep visits.
    /// - panics: the corpus, the change or the night cannot be read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus sweep draws its sources through this; a
    ///   lost or misordered source changes what a sweep visits, which the
    ///   sample's and the rotation's own witnesses in `gandr-workflow-sweep`
    ///   pin.
    /// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `tests::editor::scenarios::sweeps::erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful`
    #[spec(ensures: |ret| ret.1.is_sorted_by(|longer, shorter| longer.text.len() >= shorter.text.len()))]
    fn visited(
        sample: Sample,
        ceiling: Option<Ceiling>,
        nightly: Nightly,
    ) -> (Rotation, Vec<Source>)
    {
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        eprintln!("{}", sweep.rotation());
        let grammar = built_in().expect("the built-in grammar builds");
        let candidates: Vec<_> = gandr_workflow_sweep::corpus::sources()
            .expect("the corpus reads")
            .into_iter()
            .filter(|source| {
                sweep.coverage() == gandr_workflow_sweep::Coverage::Full
                    || ceiling.is_none_or(|ceiling| {
                        // A source's own bytes bound its check's below, so
                        // only a short one is laid out.
                        std::fs::metadata(&source.path).is_ok_and(|meta| {
                            usize::try_from(meta.len()).is_ok_and(|own| own <= ceiling.0)
                        }) && opened(core::slice::from_ref(source))
                            .first()
                            .is_some_and(|opened| checked(&grammar, opened).0 <= ceiling.0)
                    })
            })
            .collect();
        let chosen = match nightly {
            Nightly::Slice(nights) => sweep.visit_rotating(sample, nights, &candidates),
            Nightly::Part => sweep.visit(sample, &candidates),
        };
        let mut sources = opened(&chosen);
        assert!(
            sweep.coverage() == gandr_workflow_sweep::Coverage::Full
                || sources.len() >= sample.size.0,
            "the sample is drawn: {}",
            sources.len()
        );
        sources.sort_by_key(|source| core::cmp::Reverse(source.text.len()));
        (sweep.rotation(), sources)
    }

    /// The random scripts the run generates: `sampled` from [`SCRIPTS_SEED`],
    /// or [`CASES`] from a fresh seed under the `sweeps` profile.
    ///
    /// # Specification
    /// trivial.
    fn scripts(sampled: Cases) -> ProptestConfig
    {
        match gandr_workflow_sweep::Coverage::asked() {
            gandr_workflow_sweep::Coverage::Full => ProptestConfig::with_cases(CASES.0),
            gandr_workflow_sweep::Coverage::Sampled => ProptestConfig {
                rng_seed: RngSeed::Fixed(SCRIPTS_SEED),
                ..ProptestConfig::with_cases(sampled.0)
            },
        }
    }

    /// Every source of the run typed: from its start, or under the `nightly`
    /// profile opened whole up to the night's part of [`TYPED_NIGHTS`] and
    /// typed through it, so every keystroke of every source is typed once
    /// every [`TYPED_NIGHTS`] nights.
    #[test]
    fn typing_each_corpus_source_keeps_every_answer_faithful()
    {
        let (rotation, sources) = visited(TYPED, Some(TYPED_CEILING), Nightly::Part);
        each_in_parallel(&sources, |source| {
            let part = rotation.part(gandr_workflow_sweep::Text(&source.text), TYPED_NIGHTS);
            let opening = source
                .text
                .get(.. part.start.0)
                .expect("a part starts on a line");
            let typed = source
                .text
                .get(part.start.0 .. part.end.0)
                .expect("a part ends on a line");
            let mut session = Session::open(
                source.uri.clone(),
                Text(opening),
                Typing::Assisted,
                Oracle::Line,
            );
            session.type_in(Text(typed));
            session.closes_over_streams();
        });
    }

    #[test]
    fn erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful()
    {
        let (_rotation, sources) =
            visited(ERASED, Some(ERASED_CEILING), Nightly::Slice(ERASED_NIGHTS));
        let grammar = built_in().expect("the built-in grammar builds");
        each_in_parallel(&sources, |source| {
            let mut session = Session::open(
                source.uri.clone(),
                Text(&source.text),
                Typing::Assisted,
                Oracle::Keystroke,
            );
            session.erase_lines(erased_stride(&grammar, source));
            assert!(
                session.buffer().text().0.is_empty(),
                "the document is erased"
            );
            session.closes_over_streams();
        });
    }

    #[test]
    fn hovering_every_position_of_each_corpus_source_answers_without_fault()
    {
        let whole = gandr_workflow_sweep::Coverage::asked() == gandr_workflow_sweep::Coverage::Full;
        let sources = if whole {
            let mut sources =
                opened(&gandr_workflow_sweep::corpus::sources().expect("the corpus reads"));
            sources.sort_by_key(|source| core::cmp::Reverse(source.text.len()));
            sources
        }
        else {
            visited(
                HOVERED,
                Some(HOVERED_CEILING),
                Nightly::Slice(HOVERED_NIGHTS),
            )
            .1
        };
        let grammar = built_in().expect("the built-in grammar builds");
        let positions = AtomicUsize::new(0_usize);
        let unanswered = AtomicUsize::new(0_usize);
        let by_kind: Mutex<BTreeMap<String, Coverage>> = Mutex::new(BTreeMap::new());
        each_in_parallel(&sources, |source| {
            let hovers = hovered(&grammar, source, hovered_every(&grammar, source));
            let shaped = shapes::judged(&grammar, source, &hovers);
            let text = Text(&source.text);
            let mut rows: BTreeMap<String, Coverage> = BTreeMap::new();
            for (hover, shaped) in hovers.iter().zip(shaped) {
                if hover.comment {
                    continue;
                }
                let _counted = positions.fetch_add(1_usize, Ordering::Relaxed);
                if hover.shown.is_null() {
                    let _counted = unanswered.fetch_add(1_usize, Ordering::Relaxed);
                }
                let Some(ref owner) = hover.owner
                else {
                    continue;
                };
                let mut row = Coverage {
                    positions: 1_usize,
                    ..Coverage::default()
                };
                if hover.shown.is_null() {
                    row.unanswered = 1_usize;
                }
                else {
                    if shapes::reach(text, owner, &hover.shown) == shapes::Reach::AtNode {
                        row.at_node = 1_usize;
                    }
                    else {
                        row.ancestor = 1_usize;
                    }
                    // A `?` the printer writes for an unknown stands alone; one
                    // opening a word, or a parenthesised type the action's `.`
                    // follows, `?(Seat.Dispatch). end`, is a session type's
                    // receive.
                    let receives = |rest: &str| match rest.chars().next() {
                        Some('(') => {
                            let mut depth = 0_usize;
                            let closed = rest.char_indices().find(|&(_, glyph)| {
                                if glyph == '(' {
                                    depth = depth.saturating_add(1);
                                }
                                else if glyph == ')' {
                                    depth = depth.saturating_sub(1);
                                }
                                depth == 0
                            });
                            closed.is_some_and(|(at, _)| {
                                rest.get(at + 1 ..)
                                    .is_some_and(|after| after.starts_with('.'))
                            })
                        },
                        Some(glyph) => glyph.is_alphabetic(),
                        None => false,
                    };
                    if hover.shown["contents"]["value"]
                        .as_str()
                        .is_some_and(|value| {
                            value
                                .match_indices('?')
                                .any(|(at, _)| !value.get(at + 1 ..).is_some_and(receives))
                        })
                    {
                        row.unknown = 1_usize;
                    }
                    match shaped {
                        shapes::Judged::Shaped => row.shaped = 1_usize,
                        shapes::Judged::Unshaped => row.unshaped = 1_usize,
                        shapes::Judged::Unheld => {},
                    }
                }
                rows.entry(owner.kind.clone()).or_default().add(row);
            }
            let mut by_kind = by_kind.lock().expect("no visit panicked holding the table");
            for (kind, row) in rows {
                by_kind.entry(kind).or_default().add(row);
            }
        });
        let positions = positions.into_inner();
        let unanswered = unanswered.into_inner();
        let by_kind = by_kind
            .into_inner()
            .expect("no visit panicked holding the table");
        eprintln!("{positions} corpus positions, {unanswered} answered by nothing");
        eprintln!(
            "| kind | positions | at the node ‰ | shape ‰ | by an ancestor | unanswered | `?` | \
         unshaped |"
        );
        eprintln!("| --- | --- | --- | --- | --- | --- | --- | --- |");
        for (kind, row) in &by_kind {
            let share = |count: usize| {
                count
                    .saturating_mul(1000_usize)
                    .checked_div(row.positions)
                    .unwrap_or_default()
            };
            eprintln!(
                "| {kind} | {} | {} | {} | {} | {} | {} | {} |",
                row.positions,
                share(row.at_node),
                share(row.shaped),
                row.ancestor,
                row.unanswered,
                row.unknown,
                row.unshaped
            );
        }
        let mut misses = Vec::new();
        for kind in by_kind.keys() {
            if MEANINGLESS
                .iter()
                .any(|&(meaningless, _)| meaningless == kind)
                || COUNTED.contains(&kind.as_str())
            {
                continue;
            }
            misses.push(format!("{kind}: neither counted nor meaningless"));
        }
        // A sample need not hold every kind; only the whole corpus can show a
        // row whose kind is gone.
        if whole {
            for &kind in COUNTED {
                if !by_kind.contains_key(kind) {
                    misses.push(format!("{kind}: a row for a kind the corpus no longer has"));
                }
            }
        }
        assert_eq!(misses, Vec::<String>::new(), "hover coverage by node");
    }

    proptest! {
        #![proptest_config(scripts(SAMPLED_CASES))]

        #[test]
        fn random_edits_keep_every_answer_faithful(
            seed in select(SEEDS.as_slice()),
            assisted in any::<bool>(),
            script in proptest::collection::vec(edit(), 1_usize .. 24_usize),
        ) {
            let typing = if assisted { Typing::Assisted } else { Typing::Plain };
            let mut session = Session::open(
                String::from("file:///strict/random.gandr"),
                Text(seed),
                typing,
                Oracle::Keystroke,
            );
            let opened = session.published().clone();
            for &step in &script {
                apply(&mut session, step);
            }
            while session.buffer().history() == History::Undoable {
                session.undo();
            }
            prop_assert_eq!(session.buffer().text(), Text(seed), "undoing every edit restores the text");
            prop_assert_eq!(session.published(), &opened, "and the diagnostics it opened with");
        }

        #[test]
        fn two_editors_on_their_own_buffers_each_keep_their_answers(
            seed in select(SEEDS.as_slice()),
            script in proptest::collection::vec((any::<bool>(), edit()), 1_usize .. 16_usize),
        ) {
            let mut first = Session::open_shared(
                String::from("file:///strict/diverged.gandr"),
                Text(seed),
                Typing::Assisted,
                Oracle::Keystroke,
            );
            let mut second = first.beside(Typing::Plain);
            for &(in_first, step) in &script {
                apply(if in_first { &mut first } else { &mut second }, step);
                first.verify();
                second.verify();
            }
            first.replays_over_streams();
            second.replays_over_streams();
        }
    }

    proptest! {
        #![proptest_config(scripts(SAMPLED_CASES))]
        #[test]
        fn two_editors_on_one_buffer_each_keep_their_answers(
            seed in select(SEEDS.as_slice()),
            script in proptest::collection::vec(edit(), 1_usize .. 16_usize),
        ) {
            let mut first = Session::open_shared(
                String::from("file:///strict/shared.gandr"),
                Text(seed),
                Typing::Assisted,
                Oracle::Keystroke,
            );
            let mut second = first.beside(Typing::Assisted);
            for &step in &script {
                apply(&mut first, step);
                apply(&mut second, step);
                prop_assert_eq!(first.buffer().text(), second.buffer().text(), "one buffer, two clients");
            }
            first.replays_over_streams();
            second.replays_over_streams();
        }
    }
}
