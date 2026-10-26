//! One source's uncommented items, read off the molded tree.

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

use crate::comments::error::CommentError;
use crate::comments::shape::Line;
use crate::comments::shape::Span;
use crate::comments::shape::Text;
use crate::comments::shape::Yes;

/// The ledger item of a source that does not open with a comment.
const FILE_ITEM: &str = "<file>";

/// Tile labels that spell a declaration's name.
const NAME_LABELS: [&str; 3] = ["identifier", "type_identifier", "constructor"];

/// How many hex digits of the item's BLAKE3 hash a ledger line keeps.
const DIGEST_DIGITS: usize = 16;

/// One uncommented item, as the ledger and the gate name it.
///
/// # Specification
/// - provides: the ledger line `file:name:digest` (or `file:<file>`) and the
///   sentence that names the file and the item.
/// - executable: none — the line is the field the witnesses compare.
///
/// # Adequacy
/// - hypothesis: L3 — the comment verdicts name the item the ledger holds.
/// - witness: `tests::comments::judge::tests::an_uncommented_item_is_refused_by_name`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding
{
    /// `file:name:digest`, or `file:<file>`, the ledger key.
    line: String,
    /// The sentence the gate prints, naming the file and the item.
    detail: String,
}

impl Finding
{
    /// The ledger key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn line(&self) -> Line<'_>
    {
        Line(&self.line)
    }

    /// The sentence naming the file and the item.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn detail(&self) -> Line<'_>
    {
        Line(&self.detail)
    }

    /// A finding whose line and sentence are both `line`.
    ///
    /// # Specification
    /// trivial.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn from_line(line: Text<'_>) -> Self
    {
        Self {
            line: line.0.to_owned(),
            detail: line.0.to_owned(),
        }
    }
}

/// The built-in grammar the walk resolves molds under.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the grammar the parser's corpus molds against, or the builder's
///   refusal.
/// - provides: the one grammar a run resolves every mold under.
/// - fails: the built-in grammar does not build.
/// - panics: none.
///
/// # Errors
/// [`CommentError::Grammar`] when the grammar does not build.
///
/// # Adequacy
/// - hypothesis: L3 — a built grammar resolves a `def`; a swapped error variant
///   would name something other than the grammar.
/// - witness: `tests::comments::judge::tests::an_uncommented_item_is_refused_by_name`
#[spec(ensures: |ret| ret.is_ok())]
#[inline]
pub fn grammar() -> Result<Pbg, CommentError>
{
    built_in().map_err(|error| CommentError::Grammar(error.to_string()))
}

/// The first sixteen hex digits of BLAKE3 over `text`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: sixteen lowercase hex digits, the prefix of BLAKE3's hex digest
///   of `text`'s bytes.
/// - provides: the content half of a ledger line.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the same text keys the same line and a changed text a
///   different one; a truncation other than sixteen digits would change every
///   line the witnesses compare.
/// - witness: `tests::comments::judge::tests::the_key_is_the_items_content`
#[spec(ensures: |ret| ret.len() == DIGEST_DIGITS && ret.chars().all(|digit| digit.is_ascii_hexdigit()))]
#[inline]
#[must_use]
pub fn digest(text: Text<'_>) -> String
{
    blake3::hash(text.0.as_bytes())
        .to_hex()
        .as_str()
        .chars()
        .take(DIGEST_DIGITS)
        .collect()
}

/// The uncommented items of `source`, keyed under `file`.
///
/// An item is commented by a doc comment or a line comment immediately
/// before its attribute block, or by inheritance: an item on the line after
/// a commented item of the same name (a `def name = …` body after its
/// `def name : T ;` signature) carries that comment, so one comment covers a
/// run of one name. An uncommented item's line is `file:name:digest`, the
/// digest over the item's text with whitespace collapsed and comments left
/// out; the attribute block is a sibling of the item, never part of it.
///
/// # Specification
/// - requires: `file` contains no colon.
/// - ensures: one finding per uncommented top-level item, keyed by its name
///   (its kind when it has none) and its content digest, plus `file:<file>`
///   when the file has no leading comment; sorted, without repeats.
/// - provides: the debt one source owes.
/// - fails: `file` contains a colon, the parser does not commit a tree, or a
///   mold does not resolve.
/// - panics: none.
///
/// # Errors
/// [`CommentError::File`] for a colon in `file`. [`CommentError::Parse`] when
/// the parser does not commit. [`CommentError::Mold`] when a mold does not
/// resolve.
///
/// # Adequacy
/// - hypothesis: L3 — an uncommented name, a ledgered name, a stale line and a
///   file with no leading comment are distinct observations. A comment after an
///   attribute block is not a comment before it. A body inherits only from the
///   line before it and only under the same name. The key moves with the item's
///   text and with nothing else.
/// - witness: `tests::comments::judge::tests::an_uncommented_item_is_refused_by_name`
/// - witness: `tests::comments::judge::tests::a_ledgered_item_passes`
/// - witness: `tests::comments::judge::tests::a_stale_ledger_line_is_refused`
/// - witness: `tests::comments::judge::tests::a_file_without_a_leading_comment_is_refused`
/// - witness: `tests::comments::judge::tests::a_comment_after_the_attribute_block_does_not_count`
/// - witness: `tests::comments::judge::tests::a_body_inherits_its_signatures_comment`
/// - witness: `tests::comments::judge::tests::the_key_is_the_items_content`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.iter().all(|finding| finding.line.starts_with(file.0) && finding.line.contains(':'))))]
#[inline]
pub fn findings_of(
    pbg: &Pbg,
    file: Text<'_>,
    source: Text<'_>,
) -> Result<Vec<Finding>, CommentError>
{
    if file.0.contains(':') {
        return Err(CommentError::File {
            path: std::path::PathBuf::from(file.0),
            detail: "a ledger file key cannot contain ':'".to_owned(),
        });
    }
    let opens = |source: &str| {
        let mut rest = source.trim_start();
        if rest.starts_with("#!") {
            rest = rest
                .split_once('\n')
                .map_or("", |(_, after)| after)
                .trim_start();
        }
        rest.starts_with("//") || rest.starts_with("/*")
    };
    let parsed = parse(pbg, SourceText::from(source.0)).map_err(|error| CommentError::Parse {
        file: file.0.to_owned(),
        detail: error.to_string(),
    })?;
    let tree = parsed.tree();
    let leading = |tree: &SyntaxTree<'_>, at: NodeIndex| {
        for child in tree.children(at) {
            let Some(node) = tree.node(child)
            else {
                continue;
            };
            match node.label() {
                NodeLabel::Doc => return true,
                NodeLabel::Space
                    if tree
                        .fragment(child)
                        .is_some_and(|text| <&str>::from(text).trim_start().starts_with("//")) =>
                {
                    return true;
                },
                NodeLabel::Space => {},
                NodeLabel::Wald
                | NodeLabel::Meld(_)
                | NodeLabel::Tile(_)
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. } => return false,
            }
        }
        false
    };
    let blank = |source: &str, end: usize, start: usize| {
        if start < end {
            return true;
        }
        let Some(gap) = source.get(end .. start)
        else {
            return true;
        };
        let mut after_newline = false;
        for character in gap.chars() {
            if character == '\n' {
                if after_newline {
                    return true;
                }
                after_newline = true;
            }
            else if !character.is_whitespace() {
                after_newline = false;
            }
        }
        false
    };
    let sibling = |source: &str, tree: &SyntaxTree<'_>, anchor: NodeIndex| {
        let Some(held) = tree.node(anchor)
        else {
            return false;
        };
        let start = usize::from(held.span().start());
        let mut previous_end = 0_usize;
        let mut saw_comment = false;
        for child in tree.children(tree.root()) {
            if child == anchor {
                break;
            }
            let Some(node) = tree.node(child)
            else {
                continue;
            };
            let comment = matches!(node.label(), NodeLabel::Doc)
                || matches!(node.label(), NodeLabel::Space)
                    && tree
                        .fragment(child)
                        .is_some_and(|text| <&str>::from(text).trim_start().starts_with("//"));
            if comment {
                previous_end = usize::from(node.span().end());
                saw_comment = true;
            }
            else if !matches!(node.label(), NodeLabel::Space) {
                saw_comment = false;
            }
        }
        saw_comment && !blank(source, previous_end, start)
    };
    let mut found = Vec::new();
    if !opens(source.0) {
        found.push(Finding {
            line: format!("{file}:{FILE_ITEM}", file = file.0),
            detail: format!("{file}: no leading comment", file = file.0),
        });
    }
    // Every space and doc comment in the tree, by start: an item's text is
    // its span with these read as one space each.
    let mut quiet: Vec<Span> = tree
        .positions()
        .filter_map(|position| {
            let node = tree.node(position)?;
            matches!(node.label(), NodeLabel::Doc | NodeLabel::Space).then(|| Span {
                start: usize::from(node.span().start()),
                end: usize::from(node.span().end()),
            })
        })
        .collect();
    quiet.sort_unstable();
    // The previous item's name, where it ends, and whether it is commented.
    let mut previous: Option<(String, usize, bool)> = None;
    let mut attributes: Vec<NodeIndex> = Vec::new();
    for child in tree.children(tree.root()) {
        let Some(node) = tree.node(child)
        else {
            continue;
        };
        let (NodeLabel::Meld(mold) | NodeLabel::Tile(mold)) = node.label()
        else {
            continue;
        };
        let kind = pbg.named_kind(mold).map_err(|error| CommentError::Mold {
            file: file.0.to_owned(),
            detail: error.to_string(),
        })?;
        // A `pub` mark is one tile before the item it exports: the comment
        // before it comments the item, as one before an attribute block does.
        if kind.0 == "attribute_block" || kind.0 == "pub_declaration" {
            attributes.push(child);
            continue;
        }
        if matches!(node.label(), NodeLabel::Tile(_)) {
            continue;
        }
        let anchor = attributes.first().copied().unwrap_or(child);
        attributes.clear();
        let start = tree
            .node(anchor)
            .map_or(0_usize, |held| usize::from(held.span().start()));
        let name = item_name(pbg, file, tree, child)?.unwrap_or_else(|| kind.0.to_owned());
        let inherited = previous
            .as_ref()
            .is_some_and(|&(ref held, end, commented)| {
                commented
                    && *held == name
                    && on_next_line(source, Span {
                        start: end,
                        end: start,
                    })
                    .0
            });
        let commented = inherited || leading(tree, anchor) || sibling(source.0, tree, anchor);
        let end = usize::from(node.span().end());
        if !commented {
            let held = Span {
                start: usize::from(node.span().start()),
                end,
            };
            let key = digest(Text(&item_text(source, held, &quiet)));
            found.push(Finding {
                line: format!("{file}:{name}:{key}", file = file.0),
                detail: format!(
                    "{file}: {name} ({key}) has no comment before its attribute block",
                    file = file.0
                ),
            });
        }
        previous = Some((name, end, commented));
    }
    found.sort_by(|left, right| left.line.cmp(&right.line));
    found.dedup_by(|left, right| left.line == right.line);
    Ok(found)
}

/// The name the item at `at` declares, when one of its tiles spells one.
///
/// # Specification
/// - requires: `at` is a position in `tree`, molded under `pbg`.
/// - ensures: the text of the item's first non-empty direct tile whose mold is
///   labelled as a name, or nothing when no tile is.
/// - provides: the name half of a ledger line and the key of a name run.
/// - fails: a tile's mold does not resolve under `pbg`.
/// - panics: none.
///
/// # Errors
/// [`CommentError::Mold`] when a tile's mold does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — an uncommented `def` is named by its identifier, and a
///   body is matched to its signature by that name.
/// - witness: `tests::comments::judge::tests::an_uncommented_item_is_refused_by_name`
/// - witness: `tests::comments::judge::tests::a_body_inherits_its_signatures_comment`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |name| name.as_ref().is_none_or(|text| !text.is_empty())))]
fn item_name(
    pbg: &Pbg,
    file: Text<'_>,
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Result<Option<String>, CommentError>
{
    for child in tree.children(at) {
        let Some(node) = tree.node(child)
        else {
            continue;
        };
        let NodeLabel::Tile(mold) = node.label()
        else {
            continue;
        };
        let defined = pbg.mold(mold).map_err(|error| CommentError::Mold {
            file: file.0.to_owned(),
            detail: error.to_string(),
        })?;
        if !NAME_LABELS.contains(&defined.label) {
            continue;
        }
        let Some(text) = tree.fragment(child)
        else {
            continue;
        };
        let text = <&str>::from(text);
        if !text.is_empty() {
            return Ok(Some(text.to_owned()));
        }
    }
    Ok(None)
}

/// The text of an item spanning `held`: its source with every space and
/// comment read as one space, every run of whitespace one space.
///
/// The parser hangs an item's inner spaces and comments wherever its layout
/// puts them, not always under the item's node, so the text is read off the
/// span and the tree's quiet spans rather than off the item's leaves.
///
/// # Specification
/// - requires: `quiet` is sorted by start and holds the spans of the tree's
///   space and doc-comment nodes.
/// - ensures: `source` over `held`, each part of a quiet span inside `held`
///   read as one space, then every run of whitespace collapsed to one space and
///   the ends trimmed.
/// - provides: the text the content digest is taken over.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — re-spacing an item and putting a comment inside it leave
///   its key alone, and changing a token moves it.
/// - witness: `tests::comments::judge::tests::the_key_is_the_items_content`
#[spec(ensures: |ret| ret.trim() == ret.as_str() && !ret.contains("  ") && !ret.contains('\n'))]
fn item_text(
    source: Text<'_>,
    held: Span,
    quiet: &[Span],
) -> String
{
    let mut spelled = String::new();
    let mut cursor = held.start;
    for &Span {
        start: from,
        end: to,
    } in quiet
    {
        if from == to || to <= cursor || from >= held.end {
            continue;
        }
        let from = from.max(cursor);
        spelled.push_str(source.0.get(cursor .. from).unwrap_or_default());
        spelled.push(' ');
        cursor = to.min(held.end);
    }
    spelled.push_str(source.0.get(cursor .. held.end).unwrap_or_default());
    let mut collapsed = String::with_capacity(spelled.len());
    for word in spelled.split_whitespace() {
        if !collapsed.is_empty() {
            collapsed.push(' ');
        }
        collapsed.push_str(word);
    }
    collapsed
}

/// Whether the text from `gap.end` begins on the line after the text that
/// ends at `gap.start`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: yes exactly when the stretch from the last non-whitespace byte
///   before `gap.start` to the first non-whitespace byte from `gap.end` is
///   whitespace holding exactly one line break.
/// - provides: the adjacency a body needs to inherit its signature's comment.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a body on the next line inherits and a body after a blank
///   line does not.
/// - witness: `tests::comments::judge::tests::a_body_inherits_its_signatures_comment`
#[spec(ensures: |ret| !ret.0 || source.0.get(.. gap.start).is_some() && source.0.get(gap.end ..).is_some())]
fn on_next_line(
    source: Text<'_>,
    gap: Span,
) -> Yes
{
    let (Some(before), Some(after)) = (source.0.get(.. gap.start), source.0.get(gap.end ..))
    else {
        return Yes(false);
    };
    let from = before.trim_end().len();
    let to = source.0.len().saturating_sub(after.trim_start().len());
    Yes(source.0.get(from .. to).is_some_and(|stretch| {
        stretch.chars().all(char::is_whitespace)
            && stretch
                .split_once('\n')
                .is_some_and(|(_, rest)| !rest.contains('\n'))
    }))
}

#[cfg(test)]
mod tests
{
    use super::digest;
    use super::findings_of;
    use super::grammar;
    use crate::comments::ledger::discrepancies;
    use crate::comments::shape::Text;

    /// # Specification
    /// trivial.
    fn lines(source: Text<'_>) -> Vec<String>
    {
        let pbg = grammar().expect("the built-in grammar builds");
        findings_of(&pbg, Text("sample.gandr"), source)
            .expect("the source commits a tree")
            .into_iter()
            .map(|finding| finding.line().0.to_owned())
            .collect()
    }

    /// The ledger line of an uncommented `name` whose collapsed text is
    /// `text`.
    ///
    /// # Specification
    /// trivial.
    fn key(
        name: Text<'_>,
        text: Text<'_>,
    ) -> String
    {
        format!("sample.gandr:{}:{}", name.0, digest(text))
    }

    #[test]
    fn an_uncommented_item_is_refused_by_name()
    {
        let bare = key(Text("bare"), Text("def bare = 1;"));
        let owed = lines(Text("// what the file shows\n\ndef bare = 1;\n"));
        assert_eq!(
            owed,
            [bare.as_str()],
            "the blank line leaves `bare` uncommented, and the gate names it with its digest"
        );
        let pbg = grammar().expect("the built-in grammar builds");
        let found = findings_of(
            &pbg,
            Text("sample.gandr"),
            Text("// what the file shows\n\ndef bare = 1;\n"),
        )
        .expect("the source commits a tree");
        let refused = discrepancies(&found, Text(""));
        assert!(
            refused.iter().any(|row| row.line().0 == bare),
            "an empty ledger refuses `bare` by name"
        );
    }

    #[test]
    fn a_ledgered_item_passes()
    {
        let pbg = grammar().expect("the built-in grammar builds");
        let found = findings_of(
            &pbg,
            Text("sample.gandr"),
            Text("// what the file shows\n\ndef bare = 1;\n"),
        )
        .expect("the source commits a tree");
        let ledger = format!(
            "# key shape\n{}\n",
            key(Text("bare"), Text("def bare = 1;"))
        );
        let refused = discrepancies(&found, Text(&ledger));
        assert!(
            refused.is_empty(),
            "a ledger line for `bare` is not a refusal, and the header is not a line"
        );
    }

    #[test]
    fn a_stale_ledger_line_is_refused()
    {
        let pbg = grammar().expect("the built-in grammar builds");
        let found = findings_of(&pbg, Text("sample.gandr"), Text("// kept\ndef kept = 1;\n"))
            .expect("the source commits a tree");
        assert!(found.is_empty(), "a commented item owes nothing");
        let gone = key(Text("gone"), Text("def gone = 1;"));
        let refused = discrepancies(&found, Text(&format!("{gone}\n")));
        assert!(
            refused
                .iter()
                .any(|row| row.is_stale().0 && row.line().0 == gone),
            "a ledger line the source no longer owes is refused"
        );
    }

    #[test]
    fn a_file_without_a_leading_comment_is_refused()
    {
        let source = Text("def first = 1;\n\n// second\ndef second = 1;\n");
        let owed = lines(source);
        assert_eq!(
            owed,
            [
                "sample.gandr:<file>".to_owned(),
                key(Text("first"), Text("def first = 1;")),
            ],
            "a source that opens on an item has no leading comment, and the later item's own \
             comment is not the file's"
        );
        let pbg = grammar().expect("the built-in grammar builds");
        let found =
            findings_of(&pbg, Text("sample.gandr"), source).expect("the source commits a tree");
        let ledger = format!("{}\n", key(Text("first"), Text("def first = 1;")));
        let refused = discrepancies(&found, Text(&ledger));
        assert!(
            refused
                .iter()
                .any(|row| row.line().0 == "sample.gandr:<file>" && !row.is_stale().0),
            "the file finding is refused by name when the ledger omits it"
        );
    }

    #[test]
    fn a_comment_after_the_attribute_block_does_not_count()
    {
        let before = lines(Text("// shown\n@[ checks ]\ndef shown = 1;\n"));
        assert!(
            before.is_empty(),
            "a comment immediately before the attribute block comments the item"
        );
        let after = lines(Text("@[ checks ]\n// late\ndef late = 1;\n"));
        assert_eq!(
            after,
            [
                "sample.gandr:<file>".to_owned(),
                key(Text("late"), Text("def late = 1;")),
            ],
            "a comment after the attribute block is not before it, and a source that opens on an \
             attribute block has no leading comment"
        );
    }

    #[test]
    fn a_body_inherits_its_signatures_comment()
    {
        assert!(
            lines(Text(
                "// file\n\n// counted\ndef counted : Integer ;\ndef counted = 1 ;\n"
            ))
            .is_empty(),
            "a body on the line after its commented signature carries that comment"
        );
        assert_eq!(
            lines(Text(
                "// file\n\n// counted\ndef counted : Integer ;\n\ndef counted = 1 ;\n"
            )),
            [key(Text("counted"), Text("def counted = 1 ;"))],
            "a blank line ends the run, so the body owes its own comment"
        );
        assert_eq!(
            lines(Text(
                "// file\n\n// counted\ndef counted : Integer ;\ndef other = 1 ;\n"
            )),
            [key(Text("other"), Text("def other = 1 ;"))],
            "an item of another name on the next line does not inherit"
        );
        let mut both = lines(Text(
            "// file\n\ndef counted : Integer ;\ndef counted = 1 ;\n",
        ));
        both.sort();
        let mut expected = vec![
            key(Text("counted"), Text("def counted : Integer ;")),
            key(Text("counted"), Text("def counted = 1 ;")),
        ];
        expected.sort();
        assert_eq!(
            both, expected,
            "an uncommented signature leaves nothing to inherit, and its two items are two \
             lines told apart by their digests"
        );
    }

    #[test]
    fn the_key_is_the_items_content()
    {
        let bare = key(Text("bare"), Text("def bare = 1;"));
        let alone = lines(Text("// file\n\ndef bare = 1;\n"));
        assert_eq!(
            alone,
            [bare.as_str()],
            "the digest is over the item's collapsed text"
        );
        let moved = lines(Text(
            "// file\n\n// other\ndef other = 2;\n\ndef bare = 1;\n",
        ));
        assert_eq!(
            moved,
            [bare.as_str()],
            "an edit elsewhere leaves the key alone"
        );
        let mut reordered = lines(Text("// file\n\ndef second = 2;\n\ndef bare = 1;\n"));
        let mut ordered = lines(Text("// file\n\ndef bare = 1;\n\ndef second = 2;\n"));
        reordered.sort();
        ordered.sort();
        assert_eq!(
            reordered, ordered,
            "reordering items leaves every key alone"
        );
        let respaced = lines(Text("// file\n\ndef   bare\n  =\n 1;\n"));
        assert_eq!(
            respaced,
            [bare.as_str()],
            "whitespace collapses before the digest"
        );
        let annotated = lines(Text("// file\n\n@[ checks ]\ndef bare = 1;\n"));
        assert_eq!(
            annotated,
            [bare.as_str()],
            "the attribute block is not the item's text"
        );
        let remarked = lines(Text("// file\n\ndef bare = // one\n 1;\n"));
        assert_eq!(
            remarked,
            [bare.as_str()],
            "a comment inside the item is not its text"
        );
        let edited = lines(Text("// file\n\ndef bare = 2;\n"));
        assert_eq!(
            edited,
            [key(Text("bare"), Text("def bare = 2;"))],
            "an edited item keys a new line, so its ledger line goes stale"
        );
        assert_ne!(edited, alone, "a changed token moves the digest");
    }
}
