//! One source's uncommented items, read off the molded tree.

use alloc::collections::BTreeSet;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

use crate::error::CommentError;
use crate::shape::Line;
use crate::shape::Text;

/// The ledger item of a source that does not open with a comment.
const FILE_ITEM: &str = "<file>";

/// Tile labels that spell a declaration's name.
const NAME_LABELS: [&str; 3] = ["identifier", "type_identifier", "constructor"];

/// One uncommented item, as the ledger and the gate name it.
///
/// # Specification
/// - provides: the ledger line `file:item` and the sentence that names both.
/// - executable: none — the line is the field the witnesses compare.
///
/// # Adequacy
/// - hypothesis: L3 — the comment verdicts name the item the ledger holds.
/// - witness: `comments::judge::tests::an_uncommented_item_is_refused_by_name`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding
{
    /// `file:item`, the ledger key.
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
/// - witness: `comments::judge::tests::an_uncommented_item_is_refused_by_name`
#[spec(ensures: |ret| ret.is_ok())]
#[inline]
pub fn grammar() -> Result<Pbg, CommentError>
{
    built_in().map_err(|error| CommentError::Grammar(error.to_string()))
}

/// The uncommented items of `source`, keyed under `file`.
///
/// # Specification
/// - requires: `file` contains no colon.
/// - ensures: one finding per uncommented top-level item, plus one when the
///   file has no leading comment; each line is `file:item`.
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
///   attribute block is not a comment before it.
/// - witness: `comments::judge::tests::an_uncommented_item_is_refused_by_name`
/// - witness: `comments::judge::tests::a_ledgered_item_passes`
/// - witness: `comments::judge::tests::a_stale_ledger_line_is_refused`
/// - witness: `comments::judge::tests::a_file_without_a_leading_comment_is_refused`
/// - witness: `comments::judge::tests::a_comment_after_the_attribute_block_does_not_count`
/// - witness: `comments::judge::tests::a_repeated_name_keeps_its_first_line`
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
    let owed = |file: &str, item: &str, detail: &str| Finding {
        line: format!("{file}:{item}"),
        detail: format!("{file}: {detail}"),
    };
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
                | NodeLabel::Doc => return true,
                | NodeLabel::Space
                    if tree
                        .fragment(child)
                        .is_some_and(|text| <&str>::from(text).trim_start().starts_with("//")) =>
                {
                    return true;
                },
                | NodeLabel::Space => {},
                | NodeLabel::Wald
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
        found.push(owed(file.0, FILE_ITEM, "no leading comment"));
    }
    let mut seen = BTreeSet::new();
    let mut item_key = |tree: &SyntaxTree<'_>,
                        at: NodeIndex,
                        kind: &str,
                        start: usize|
     -> Result<String, CommentError> {
        let mut name = String::new();
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
                file: String::new(),
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
            if text.is_empty() {
                continue;
            }
            text.clone_into(&mut name);
            break;
        }
        if name.is_empty() {
            return Ok(format!("{kind}@{start}"));
        }
        if seen.insert(name.clone()) {
            Ok(name)
        }
        else {
            Ok(format!("{name}@{start}"))
        }
    };
    let mut attributes: Vec<NodeIndex> = Vec::new();
    for child in tree.children(tree.root()) {
        let Some(node) = tree.node(child)
        else {
            continue;
        };
        let NodeLabel::Meld(mold) = node.label()
        else {
            continue;
        };
        let kind = pbg.named_kind(mold).map_err(|error| CommentError::Mold {
            file: file.0.to_owned(),
            detail: error.to_string(),
        })?;
        if kind.0 == "attribute_block" {
            attributes.push(child);
            continue;
        }
        let anchor = attributes.first().copied().unwrap_or(child);
        let commented = leading(tree, anchor) || sibling(source.0, tree, anchor);
        let key = item_key(tree, child, kind.0, usize::from(node.span().start()))?;
        attributes.clear();
        if commented {
            continue;
        }
        found.push(owed(
            file.0,
            &key,
            &format!("{key} has no comment before its attribute block"),
        ));
    }
    found.sort_by(|left, right| left.line.cmp(&right.line));
    Ok(found)
}

#[cfg(test)]
mod tests
{
    use super::findings_of;
    use super::grammar;
    use crate::ledger::discrepancies;
    use crate::shape::Text;

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

    #[test]
    fn an_uncommented_item_is_refused_by_name()
    {
        let owed = lines(Text("// what the file shows\n\ndef bare = 1;\n"));
        assert_eq!(
            owed,
            ["sample.gandr:bare".to_owned()],
            "the blank line leaves `bare` uncommented, and the gate names it"
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
            refused
                .iter()
                .any(|row| row.line().0 == "sample.gandr:bare"),
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
        let refused = discrepancies(&found, Text("sample.gandr:bare\n"));
        assert!(
            refused.is_empty(),
            "a ledger line for `bare` is not a refusal"
        );
    }

    #[test]
    fn a_stale_ledger_line_is_refused()
    {
        let pbg = grammar().expect("the built-in grammar builds");
        let found = findings_of(&pbg, Text("sample.gandr"), Text("// kept\ndef kept = 1;\n"))
            .expect("the source commits a tree");
        assert!(found.is_empty(), "a commented item owes nothing");
        let refused = discrepancies(&found, Text("sample.gandr:gone\n"));
        assert!(
            refused
                .iter()
                .any(|row| row.is_stale().0 && row.line().0 == "sample.gandr:gone"),
            "a ledger line the source no longer owes is refused"
        );
    }

    #[test]
    fn a_file_without_a_leading_comment_is_refused()
    {
        let owed = lines(Text("def first = 1;\n\n// second\ndef second = 1;\n"));
        assert!(
            owed.contains(&"sample.gandr:<file>".to_owned()),
            "a source that opens on an item has no leading comment"
        );
        assert!(
            !owed.contains(&"sample.gandr:second".to_owned()),
            "the later item's own comment is not the file's"
        );
        let pbg = grammar().expect("the built-in grammar builds");
        let found = findings_of(
            &pbg,
            Text("sample.gandr"),
            Text("def first = 1;\n\n// second\ndef second = 1;\n"),
        )
        .expect("the source commits a tree");
        let refused = discrepancies(&found, Text("sample.gandr:first\n"));
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
        assert!(
            after.contains(&"sample.gandr:late".to_owned()),
            "a comment after the attribute block is not before it"
        );
        assert!(
            after.contains(&"sample.gandr:<file>".to_owned()),
            "a source that opens on an attribute block has no leading comment"
        );
    }

    #[test]
    fn a_repeated_name_keeps_its_first_line()
    {
        let owed = lines(Text("def counted : Integer ;\ndef counted = 1 ;\n"));
        assert!(
            owed.iter().any(|line| line == "sample.gandr:counted"),
            "the first `counted` keeps the bare name"
        );
        assert!(
            owed.iter()
                .any(|line| line.starts_with("sample.gandr:counted@")),
            "the later `counted` carries its start byte"
        );
    }
}
