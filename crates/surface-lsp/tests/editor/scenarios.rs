//! The scenarios: the corpus typed, erased and hovered, scripted edits that
//! break and fix a document, and random edit scripts undone to where they
//! started.
//!
//! The corpus scenarios and the random scripts are sweeps, in [`sweeps`]: each
//! visits its stated sample under every pull-request profile and every source
//! and every script under the `sweeps` profile, nightly.

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

/// The corpus positions no hover answers, above which hovering has regressed:
/// the count measured when it was last changed. A position inside a
/// declaration's body that no entry holds answers nothing, so the
/// declaration's own answer is not counted there. A position inside a comment
/// is hovered but not counted: a comment is no hover target, and corpus items
/// carry comments saying what they demonstrate, so counting them would move
/// the count for documentation alone.
const UNANSWERED_CEILING: usize = 28_545;

/// The misses each node kind's hovers may hold, as [`KindFloor`] reads a row:
/// the kind, then counts of the corpus positions whose smallest meaningful
/// node is of that kind — answered by an ancestor, answered by nothing,
/// answered with a `?`, answered in another shape than the kind's
/// ([`shapes`]). Each count must not rise; the share answered at the node and
/// the share answered in shape are printed beside them and held by none.
///
/// The counts are absolute so that deleting corpus text never fails the
/// sweep: a source that shrinks takes its misses with it, where a share of
/// fewer positions can fall with every remaining position answered. A row
/// changes only with a stated cause — a change that answers or shapes a kind
/// at its own nodes lowers it, a corpus source added or extended with misses
/// raises it, and the commit moving it says which. A row whose kind answers
/// out of shape names the issue its answers wait on. A kind measured with no
/// row here and none in [`MEANINGLESS`] fails the sweep, so a new kind is
/// decided rather than counted silently, and so does a row whose kind the
/// corpus no longer has.
const KIND_FLOORS: &[KindFloor] = &[
    KindFloor("expression abort_expression", 0, 0, 7, 0),
    KindFloor("expression abort_expression name", 4, 0, 1, 0),
    KindFloor("expression access_expression", 0, 0, 0, 0),
    KindFloor("expression access_expression name", 16, 0, 0, 0),
    KindFloor("expression become_expression", 1020, 72, 36, 0),
    KindFloor("expression binary_expression", 18, 91, 2, 4), // shape: #401
    KindFloor("expression block", 375, 152, 20, 0),
    KindFloor("expression block name", 29, 8, 0, 0),
    KindFloor("expression boolean", 0, 30, 0, 0),
    KindFloor("expression break_expression", 0, 0, 0, 0),
    KindFloor("expression break_value_expression", 35, 21, 0, 0),
    KindFloor("expression call_expression", 97, 503, 134, 98), // shape: #401, `?`
    KindFloor("expression case_expression", 11, 308, 185, 12), // shape: #401
    KindFloor("expression close_expression", 70, 84, 35, 0),
    KindFloor("expression constructor", 1392, 239, 95, 0),
    KindFloor("expression continue_expression", 0, 24, 0, 0),
    KindFloor("expression double_quoted_string", 0, 83, 0, 0),
    KindFloor("expression dup_expression", 0, 5, 0, 0),
    KindFloor("expression file_descriptor", 0, 2, 0, 0),
    KindFloor("expression for_expression", 0, 8, 0, 0),
    KindFloor("expression for_expression name", 0, 1, 0, 0),
    KindFloor("expression force_expression", 0, 10, 15, 0),
    KindFloor("expression glob_expression", 0, 10, 0, 0),
    KindFloor("expression glob_expression name", 0, 8, 0, 0),
    KindFloor("expression handle_expression", 0, 132, 0, 33), // shape: #401
    KindFloor("expression handle_expression name", 141, 60, 0, 1), // shape: #401
    KindFloor("expression hole", 1, 0, 24, 0),
    KindFloor("expression host_escape", 0, 6, 0, 0),
    KindFloor("expression identifier", 2487, 1743, 167, 194), // shape: #401
    KindFloor("expression if_expression", 0, 96, 0, 0),
    KindFloor("expression instantiation_expression", 57, 34, 33, 0),
    KindFloor("expression labelled_sum_expression", 5, 0, 0, 0),
    KindFloor("expression labelled_sum_expression name", 10, 0, 0, 0),
    KindFloor("expression lambda_expression", 0, 70, 6, 0),
    KindFloor("expression lambda_expression name", 5, 17, 1, 0),
    KindFloor("expression lazy_record_expression", 0, 0, 0, 0),
    KindFloor("expression lazy_record_expression name", 18, 0, 0, 0),
    KindFloor("expression list_expression", 0, 76, 0, 0),
    KindFloor("expression list_operator", 0, 36, 0, 0),
    KindFloor("expression loop_expression", 0, 24, 0, 18), // shape: #401
    KindFloor("expression number", 24, 251, 3, 0),
    KindFloor("expression offer_expression", 0, 0, 0, 0),
    KindFloor("expression pack_expression", 0, 30, 0, 0),
    KindFloor("expression parenthesized_expression", 94, 90, 5, 0),
    KindFloor("expression pipeline", 0, 5, 0, 0),
    KindFloor("expression projection_expression", 4, 106, 1, 2), // shape: #401
    KindFloor("expression projection_expression name", 216, 561, 1, 0),
    KindFloor("expression pure_expression", 56, 160, 4, 24), // shape: #401
    KindFloor("expression redirection_operator", 0, 4, 0, 0),
    KindFloor("expression resume_expression", 9, 0, 9, 0),
    KindFloor("expression resume_expression name", 6, 0, 1, 0),
    KindFloor("expression return_expression", 48, 468, 18, 6), // shape: #401
    KindFloor("expression run_expression", 0, 0, 0, 0),
    KindFloor("expression select_expression", 18, 0, 0, 0),
    KindFloor("expression select_expression name", 37, 0, 0, 0),
    KindFloor("expression send_expression", 0, 0, 0, 0),
    KindFloor("expression shell_block", 0, 112, 0, 0),
    KindFloor("expression shell_word", 0, 229, 0, 0),
    KindFloor("expression single_quoted_string", 0, 110, 0, 0),
    KindFloor("expression string", 81, 528, 14, 0),
    KindFloor("expression subshell", 0, 10, 0, 0),
    KindFloor("expression telescope_expression", 21, 216, 8, 0),
    KindFloor("expression telescope_expression name", 13, 20, 0, 0),
    KindFloor("expression thunk_expression", 0, 122, 42, 7), // shape: #401
    KindFloor("expression typed_number", 0, 52, 0, 0),
    KindFloor("expression unary_expression", 0, 1, 0, 0),
    KindFloor("expression unit", 12, 40, 0, 0),
    KindFloor("expression variable_expansion", 0, 29, 0, 0),
    KindFloor("expression while_expression", 0, 0, 0, 0),
    KindFloor("instantiation instantiation_expression", 98, 20, 0, 0),
    KindFloor("instantiation instantiation_expression name", 0, 10, 0, 0),
    KindFloor("item circuit_declaration", 0, 78, 0, 0),
    KindFloor("item circuit_declaration name", 20, 65, 0, 0),
    KindFloor("item codata_declaration", 0, 74, 0, 0),
    KindFloor("item codata_declaration name", 5, 63, 0, 0),
    KindFloor("item data_declaration", 0, 1872, 0, 0),
    KindFloor("item data_declaration name", 27, 385, 0, 0),
    KindFloor("item def_value", 0, 919, 105, 143), // shape: #401
    KindFloor("item def_value name", 186, 664, 153, 122), // shape: #401
    KindFloor("item extern_block", 0, 142, 0, 0),
    KindFloor("item extern_block name", 0, 80, 0, 0),
    KindFloor("item import_declaration", 0, 69, 0, 0),
    KindFloor("item import_declaration name", 0, 15, 0, 0),
    KindFloor("item module_declaration", 0, 595, 0, 40), // shape: #405
    KindFloor("item module_declaration name", 52, 483, 0, 0),
    KindFloor("item operator_declaration", 0, 56, 0, 0),
    KindFloor("item rec_block", 0, 25, 0, 0),
    KindFloor("item rec_block name", 0, 9, 0, 0),
    KindFloor("item sign_declaration", 0, 1371, 0, 0),
    KindFloor("item sign_declaration name", 18, 231, 0, 0),
    KindFloor("module_member module_declaration", 0, 445, 10, 74), // shape: #401
    KindFloor("module_member module_declaration name", 1, 359, 12, 81), // shape: #401
    KindFloor("pattern cons_pattern", 0, 4, 0, 16),                // shape: #408
    KindFloor("pattern cons_pattern name", 32, 12, 0, 0),
    KindFloor("pattern constructor_pattern", 10, 43, 2, 0),
    KindFloor("pattern constructor_pattern name", 40, 131, 8, 0),
    KindFloor("pattern hole", 0, 12, 0, 0),
    KindFloor("pattern identifier", 79, 155, 2, 0),
    KindFloor("pattern labelled_sum_pattern", 0, 0, 0, 19), // shape: #408
    KindFloor("pattern labelled_sum_pattern name", 0, 0, 0, 0),
    KindFloor("pattern literal_pattern", 34, 3, 22, 0),
    KindFloor("pattern or_pattern", 0, 0, 0, 0),
    KindFloor("pattern telescope_pattern", 0, 0, 0, 0),
    KindFloor("pattern telescope_pattern name", 7, 0, 0, 0),
    KindFloor("pattern tuple_pattern", 3, 0, 0, 0),
    KindFloor("pattern wildcard", 4, 2, 0, 0),
    KindFloor("type capability_type", 0, 0, 0, 0),
    KindFloor("type capability_type name", 47, 0, 0, 0),
    KindFloor("type end_session_type", 6, 15, 0, 0),
    KindFloor("type f_type", 142, 94, 2, 12), // shape: #404
    KindFloor("type f_type name", 14, 0, 0, 0),
    KindFloor("type function_type", 8, 12, 0, 0),
    KindFloor("type labelled_sum_type", 0, 4, 0, 0),
    KindFloor("type lazy_product_type", 5, 0, 0, 0),
    KindFloor("type lazy_record_type", 19, 0, 0, 0),
    KindFloor("type mu_session_type", 0, 3, 0, 0),
    KindFloor("type mu_session_type name", 0, 4, 0, 17), // shape: #401
    KindFloor("type number", 0, 2, 0, 0),
    KindFloor("type package_type", 0, 99, 0, 0),
    KindFloor("type package_type name", 0, 11, 0, 0),
    KindFloor("type parenthesized_type", 599, 34, 2, 0),
    KindFloor("type path_type", 136, 0, 0, 0),
    KindFloor("type primitive_type", 553, 658, 0, 0),
    KindFloor("type product_type", 4, 0, 1, 6), // shape: #404
    KindFloor("type receive_session_type", 2, 0, 0, 0),
    KindFloor("type send_session_type", 2, 4, 0, 0),
    KindFloor("type static_abstraction", 0, 0, 0, 38), // shape: #404
    KindFloor("type static_abstraction name", 46, 0, 0, 0),
    KindFloor("type sum_type", 2, 3, 0, 0),
    KindFloor("type telescope_type", 6, 58, 0, 0),
    KindFloor("type type_application", 42, 83, 0, 0),
    KindFloor("type type_application name", 959, 154, 0, 0),
    KindFloor("type type_identifier", 333, 478, 0, 0),
    KindFloor("type type_path", 0, 0, 0, 8), // shape: #404
    KindFloor("type type_path name", 97, 0, 0, 0),
    KindFloor("type type_variable", 36, 129, 0, 90), // shape: #401
    KindFloor("type u_type", 22, 75, 0, 10),         // shape: #404
    KindFloor("type universe_type", 40, 116, 0, 0),
    KindFloor("type unknown_type", 8, 0, 0, 0),
    KindFloor("type value_function_type", 2, 0, 0, 4), // shape: #404
];

/// The node kinds with no meaning of their own to hover, each with why: the
/// sweep counts their positions but pins no floor on them.
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
/// - witness: `editor::editor::shapes::the_headline_sources_hover_as_their_goldens`
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
/// - witness: `editor::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
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

/// The misses one node kind's hovers may hold over the corpus, as counts of
/// positions: the kind — its form's grammar sort, then its named kind — then
/// how many positions an ancestor answers, how many nothing answers, how many
/// an answer with a `?` answers and how many an answer of another shape than
/// the kind's answers. Each count must not rise.
#[derive(Clone, Copy, Debug)]
struct KindFloor(&'static str, usize, usize, usize, usize);

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
///   parameter, a loop or a word pattern's letter — is owned by itself, as kind
///   `<sort> <form> name`, its form the form spelling it; any other tile of the
///   form its parent completes — a keyword, a delimiter, an operator — by that
///   form; any other tile, an atom such as a name, a constructor or a literal,
///   by itself; grout by itself, as kind `grout`. A kind is the sort of the
///   owning form's mold and its named kind, so a name in a pattern and a name
///   in a term are two kinds. Every leaf inside an attribute block or a module
///   member's inline `@[ … ]` — its payload's strings, numbers and names as
///   well as its own tiles — is owned by the attribute, as kind `item
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
/// - witness: `editor::editor::scenarios::sweeps::hovering_every_position_of_each_corpus_source_answers_without_fault`
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
                match parent.map(|parent| (parent, parent.label())) {
                    Some((parent, NodeLabel::Meld(form))) if rule(form) == rule(mold) => {
                        if NAMES
                            .contains(&grammar.mold(mold).expect("a tree's mold is known").label)
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
/// - witness: `editor::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
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

/// Every position of `source`, each hovered over a fresh connection opening
/// it whole.
///
/// # Specification
/// - requires: `source` parses under `grammar`.
/// - ensures: one entry per character boundary of the text and its end, in
///   order, each with whether a comment holds it, the owner of the written leaf
///   holding it — none for layout and comments — and the hover's answer.
/// - provides: the input of the sweep and of the hover goldens.
/// - panics: a written byte lies in no leaf, or the server faults.
///
/// # Adequacy
/// - hypothesis: L3 — the sweep counts every non-comment position of the corpus
///   through this, and the goldens pin every answer of five sources.
/// - witness: `editor::editor::scenarios::sweeps::hovering_every_position_of_each_corpus_source_answers_without_fault`
/// - witness: `editor::editor::shapes::the_headline_sources_hover_as_their_goldens`
#[spec(ensures: |ret| ret.len() == source.text.chars().count().saturating_add(1))]
pub(super) fn hovered(
    grammar: &Pbg,
    source: &Source,
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
            (layout.starts_with("//") || layout.starts_with("/*")).then_some((start, end))
        })
        .collect();
    source
        .text
        .char_indices()
        .map(|(offset, _)| offset)
        .chain([source.text.len()])
        .map(|offset| {
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
    for (cut, publications) in QUIET_DECLARATION
        .char_indices()
        .map(|(offset, typed)| offset.saturating_add(typed.len_utf8()))
        .zip(&today)
    {
        let mut fresh = Client::initialized(Record::Dropped, Quiet::Default);
        let typed = QUIET_DECLARATION.get(.. cut).unwrap_or_default();
        let text = format!("{QUIET_SEED}{typed}");
        let opened = fresh.notify(
            Method("textDocument/didOpen"),
            &json!({ "textDocument": {
                "uri": QUIET_URI, "languageId": "gandr", "version": 1_i32, "text": text,
            } }),
        );
        assert_eq!(
            *publications,
            self::publications(&opened),
            "with a zero interval, typing `{text}` publishes what opening it does"
        );
    }
    let unfinished = |code: &str| vec![vec![json!([code, seed_lines])]];
    let mut expected = vec![unfinished("OutOfFragment"); 2];
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

/// The corpus sweeps and the random edit scripts. Each visits the sample its
/// constant states under every pull-request profile and everything under the
/// `sweeps` profile (`gandr-workflow-sweep`): every source, every script from
/// a fresh seed. A sample ranks the corpus by its BLAKE3 digest under the
/// sweep's name, holds at least one source of each corpus class — `strict` and
/// each directory below `fixture` — and adds every source the change adds or
/// modifies, so a corpus edit is swept on the pull request that makes it.
mod sweeps
{
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use proptest::test_runner::RngSeed;

    use super::*;

    /// The random edit scripts each scenario generates under the `sweeps`
    /// profile, each run from a fresh seed.
    const CASES: u32 = 32;

    /// The random edit scripts each scenario generates under every
    /// pull-request profile: a quarter of the whole's, drawn from
    /// [`SCRIPTS_SEED`] so every run generates the same eight.
    const SAMPLED_CASES: u32 = 8;

    /// The seed the sampled scripts are drawn from.
    const SCRIPTS_SEED: u64 = 0x6761_6e64_7273_7765;

    /// The typing sweep's sample: sixteen sources no longer than
    /// [`TYPED_CEILING`], every keystroke held to the oracle.
    const TYPED: Sample = Sample {
        name: SampleName("typing_each_corpus_source_keeps_every_answer_faithful"),
        size: SampleSize(16),
    };

    /// The longest source the typing sweep's sample types, in bytes: typing
    /// costs a check per keystroke over the whole text, so a long source alone
    /// types for longer than the bound. A changed source past it is typed
    /// nightly; the erasure and the hover sweep visit it on the pull request.
    const TYPED_CEILING: Ceiling = Ceiling(1024);

    /// The erasure's sample: twenty-four sources, every keystroke held to the
    /// oracle.
    const ERASED: Sample = Sample {
        name: SampleName("erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful"),
        size: SampleSize(24),
    };

    /// The hover sweep's sample: forty-eight sources, every position hovered.
    const HOVERED: Sample = Sample {
        name: SampleName("hovering_every_position_of_each_corpus_source_answers_without_fault"),
        size: SampleSize(48),
    };

    /// The length in bytes past which a sampled sweep leaves a source to the
    /// `sweeps` profile.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Ceiling(u64);

    /// The sources `sample` visits in this run, the longest first so the
    /// longest starts at once. A sampled run draws from the sources no longer
    /// than `ceiling`; the `sweeps` profile visits every source.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the visited sources, sorted longest first.
    /// - provides: the sources each corpus sweep visits.
    /// - panics: the corpus or the change cannot be read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus sweep draws its sources through this; a
    ///   lost or misordered source changes what a sweep visits, which the
    ///   sample's own witnesses in `gandr-workflow-sweep` pin.
    /// - witness: `editor::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::sweeps::erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful`
    #[spec(ensures: |ret| ret.is_sorted_by(|longer, shorter| longer.text.len() >= shorter.text.len()))]
    fn visited(
        sample: Sample,
        ceiling: Ceiling,
    ) -> Vec<Source>
    {
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        let candidates: Vec<_> = gandr_workflow_sweep::corpus::sources()
            .expect("the corpus reads")
            .into_iter()
            .filter(|source| {
                sweep.coverage() == gandr_workflow_sweep::Coverage::Full
                    || std::fs::metadata(&source.path).is_ok_and(|meta| meta.len() <= ceiling.0)
            })
            .collect();
        let mut sources = opened(&sweep.visit(sample, &candidates));
        assert!(
            sources.len() >= sample.size.0,
            "the sample is drawn: {}",
            sources.len()
        );
        sources.sort_by_key(|source| core::cmp::Reverse(source.text.len()));
        sources
    }

    /// The random scripts the run generates: [`SAMPLED_CASES`] from
    /// [`SCRIPTS_SEED`], or [`CASES`] from a fresh seed under the `sweeps`
    /// profile.
    ///
    /// # Specification
    /// trivial.
    fn scripts() -> ProptestConfig
    {
        match gandr_workflow_sweep::Coverage::asked() {
            gandr_workflow_sweep::Coverage::Full => ProptestConfig::with_cases(CASES),
            gandr_workflow_sweep::Coverage::Sampled => ProptestConfig {
                rng_seed: RngSeed::Fixed(SCRIPTS_SEED),
                ..ProptestConfig::with_cases(SAMPLED_CASES)
            },
        }
    }

    #[test]
    fn typing_each_corpus_source_keeps_every_answer_faithful()
    {
        let sources = visited(TYPED, TYPED_CEILING);
        each_in_parallel(&sources, |source| {
            let mut session =
                Session::open(source.uri.clone(), Text(""), Typing::Assisted, Oracle::Line);
            session.type_in(Text(&source.text));
            session.closes_over_streams();
        });
    }

    #[test]
    fn erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful()
    {
        let sources = visited(ERASED, Ceiling(u64::MAX));
        each_in_parallel(&sources, |source| {
            let mut session = Session::open(
                source.uri.clone(),
                Text(&source.text),
                Typing::Assisted,
                Oracle::Keystroke,
            );
            session.erase_lines();
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
        let sources = visited(HOVERED, Ceiling(u64::MAX));
        let grammar = built_in().expect("the built-in grammar builds");
        let positions = AtomicUsize::new(0_usize);
        let unanswered = AtomicUsize::new(0_usize);
        let by_kind: Mutex<BTreeMap<String, Coverage>> = Mutex::new(BTreeMap::new());
        each_in_parallel(&sources, |source| {
            let hovers = hovered(&grammar, source);
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
                    // opening a word is a session type's receive.
                    if hover.shown["contents"]["value"]
                        .as_str()
                        .is_some_and(|value| {
                            value.match_indices('?').any(|(at, _)| {
                                !value
                                    .get(at + 1 ..)
                                    .and_then(|rest| rest.chars().next())
                                    .is_some_and(char::is_alphabetic)
                            })
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
        if unanswered > UNANSWERED_CEILING {
            misses.push(format!(
                "{unanswered} corpus positions answered by nothing, above {UNANSWERED_CEILING}"
            ));
        }
        for (kind, row) in &by_kind {
            if MEANINGLESS
                .iter()
                .any(|&(meaningless, _)| meaningless == kind)
            {
                continue;
            }
            let Some(&KindFloor(_, ancestors, unanswered, unknowns, unshaped)) =
                KIND_FLOORS.iter().find(|floor| floor.0 == kind)
            else {
                misses.push(format!("{kind}: no floor and not meaningless"));
                continue;
            };
            for (what, count, ceiling) in [
                ("answered by an ancestor", row.ancestor, ancestors),
                ("answered by nothing", row.unanswered, unanswered),
                ("answered with `?`", row.unknown, unknowns),
                ("answered in another shape", row.unshaped, unshaped),
            ] {
                if count > ceiling {
                    misses.push(format!("{kind}: {count} {what}, above {ceiling}"));
                }
            }
        }
        // A sample need not hold every kind; only the whole corpus can show a
        // floor whose kind is gone.
        if gandr_workflow_sweep::Coverage::asked() == gandr_workflow_sweep::Coverage::Full {
            for &KindFloor(kind, ..) in KIND_FLOORS {
                if !by_kind.contains_key(kind) {
                    misses.push(format!(
                        "{kind}: a floor for a kind the corpus no longer has"
                    ));
                }
            }
        }
        assert_eq!(misses, Vec::<String>::new(), "hover coverage by node");
    }

    proptest! {
        #![proptest_config(scripts())]

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
}
