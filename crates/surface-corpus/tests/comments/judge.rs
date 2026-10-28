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
pub const FILE_ITEM: &str = "<file>";

/// The kind column of an uncommented item's ledger line.
const UNCOMMENTED: &str = "uncommented";

/// Tile labels that spell a declaration's name.
const NAME_LABELS: [&str; 3] = ["identifier", "type_identifier", "constructor"];

/// How many hex digits of the item's BLAKE3 hash a ledger line keeps.
const DIGEST_DIGITS: usize = 16;

/// Block keywords whose members are items, each its own meld.
const ITEM_BLOCKS: [&str; 2] = ["module", "rec"];

/// Block keywords whose members are runs of the block's own tiles, each
/// ended by `;`.
const TILE_BLOCKS: [&str; 3] = ["data", "codata", "theory"];

/// One finding, as the ledger and the gate name it: an uncommented item, or
/// a comment outside the shape (`prose.rs`).
///
/// # Specification
/// - provides: the ledger line `key kind`, the key `file:name:digest` (or
///   `file:<file>`), the kind `uncommented` or `unshaped:<rule>`, and the
///   sentence that names the file and the item.
/// - executable: none — the line is the field the witnesses compare.
///
/// # Adequacy
/// - hypothesis: L3 — the comment verdicts name the item the ledger holds.
/// - witness: `tests::comments::judge::tests::an_uncommented_item_is_refused_by_name`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding
{
    /// `key kind`, the ledger line.
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

    /// The finding that the comment keyed `key` breaks the shape's `rule`,
    /// the gate printing the key and `told`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn unshaped(
        key: String,
        rule: Text<'_>,
        told: Text<'_>,
    ) -> Self
    {
        let detail = format!("{key}: {told}", told = told.0);
        let mut line = key;
        line.push_str(" unshaped:");
        line.push_str(rule.0);
        Self { line, detail }
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

/// The uncommented items and block members of `source`, keyed under `file`.
///
/// An item is commented by a doc comment or a line comment immediately
/// before its attribute block, or by inheritance: an item on the line after
/// a commented item of the same name (a `def name = …` body after its
/// `def name : T ;` signature) carries that comment, so one comment covers a
/// run of one name. An uncommented item's line is `file:name:digest`, the
/// digest over the item's text with whitespace collapsed and comments left
/// out; the attribute block is a sibling of the item, never part of it.
///
/// The members of a `module` or `rec` block are items judged the same way,
/// and the members of a `data`, `codata` or `theory` block (a constructor,
/// an observation, a sort, an operation, a rule) are commented by a comment
/// immediately before them. A member's line is `file:block.member:digest`,
/// the block named by its path from the top level.
///
/// # Specification
/// - requires: `file` contains no colon.
/// - ensures: one finding per uncommented item or block member, at any depth,
///   keyed by its qualified name (its kind or keyword when it has none) and its
///   content digest, plus `file:<file>` when the file has no leading comment;
///   sorted, without repeats.
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
///   text and with nothing else. A commented block leaves its members owing
///   their own comments, and a member is named under its block.
/// - witness: `tests::comments::judge::tests::an_uncommented_item_is_refused_by_name`
/// - witness: `tests::comments::judge::tests::a_ledgered_item_passes`
/// - witness: `tests::comments::judge::tests::a_stale_ledger_line_is_refused`
/// - witness: `tests::comments::judge::tests::a_file_without_a_leading_comment_is_refused`
/// - witness: `tests::comments::judge::tests::a_comment_after_the_attribute_block_does_not_count`
/// - witness: `tests::comments::judge::tests::a_body_inherits_its_signatures_comment`
/// - witness: `tests::comments::judge::tests::the_key_is_the_items_content`
/// - witness: `tests::comments::judge::tests::every_tile_member_owes_its_own_comment`
/// - witness: `tests::comments::judge::tests::every_item_member_owes_its_own_comment`
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
    let mut found = Vec::new();
    if !opens(source.0) {
        found.push(Finding {
            line: format!("{file}:{FILE_ITEM} {UNCOMMENTED}", file = file.0),
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
    let walk = Walk {
        pbg,
        file,
        source,
        tree,
        quiet,
    };
    let mut pending = vec![Pending {
        parent: tree.root(),
        children: tree.children(tree.root()).collect(),
        block: None,
        tiles: Yes(false),
    }];
    while let Some(next) = pending.pop() {
        if next.tiles.0 {
            let block = next.block.as_deref().unwrap_or_default();
            walk.tile_members(&next.children, Text(block), &mut found)?;
        }
        else {
            walk.items(&next, &mut found, &mut pending)?;
        }
    }
    found.sort_by(|left, right| left.line.cmp(&right.line));
    found.dedup_by(|left, right| left.line == right.line);
    Ok(found)
}

/// One source under judgement: the grammar its molds resolve under, its
/// ledger key, its text, its tree, and the spans an item's text reads as
/// spaces.
struct Walk<'walk, 'tree>
{
    /// The grammar every mold resolves under.
    pbg: &'walk Pbg,
    /// The ledger key of the source.
    file: Text<'walk>,
    /// The source text.
    source: Text<'walk>,
    /// The committed tree.
    tree: &'walk SyntaxTree<'tree>,
    /// Every space and doc-comment span, sorted by start.
    quiet: Vec<Span>,
}

/// A run of items or members still to judge: the top level, or a block's
/// body.
struct Pending
{
    /// The node whose children the run is.
    parent: NodeIndex,
    /// The run itself.
    children: Vec<NodeIndex>,
    /// The block's qualified name; nothing at the top level.
    block: Option<String>,
    /// Whether the run is a block of tiles (`data`, `codata`, `theory`)
    /// rather than of items.
    tiles: Yes,
}

impl Walk<'_, '_>
{
    /// The refusal for a mold that does not resolve.
    ///
    /// # Specification
    /// trivial.
    fn unresolved(
        &self,
        detail: String,
    ) -> CommentError
    {
        CommentError::Mold {
            file: self.file.0.to_owned(),
            detail,
        }
    }

    /// The label of the tile at `at`, or nothing when `at` is not a tile.
    ///
    /// # Specification
    /// trivial.
    fn tile_label(
        &self,
        at: NodeIndex,
    ) -> Result<Option<Text<'static>>, CommentError>
    {
        let Some(NodeLabel::Tile(mold)) = self.tree.node(at).map(gandr_surface_syntax::Node::label)
        else {
            return Ok(None);
        };
        let defined = self
            .pbg
            .mold(mold)
            .map_err(|error| self.unresolved(error.to_string()))?;
        Ok(Some(Text(defined.label)))
    }

    /// The bytes the node at `at` covers, empty at the start when `at` is no
    /// node.
    ///
    /// # Specification
    /// trivial.
    fn span(
        &self,
        at: NodeIndex,
    ) -> Span
    {
        self.tree
            .node(at)
            .map_or(Span { start: 0, end: 0 }, |node| Span {
                start: usize::from(node.span().start()),
                end: usize::from(node.span().end()),
            })
    }

    /// Whether the node at `at` is a doc comment or a line comment.
    ///
    /// # Specification
    /// trivial.
    fn is_comment(
        &self,
        at: NodeIndex,
    ) -> Yes
    {
        Yes(self.tree.node(at).is_some_and(|node| {
            matches!(node.label(), NodeLabel::Doc)
                || matches!(node.label(), NodeLabel::Space)
                    && self
                        .tree
                        .fragment(at)
                        .is_some_and(|text| <&str>::from(text).trim_start().starts_with("//"))
        }))
    }

    /// Whether the item at `at` opens on a comment of its own, before any of
    /// its tiles.
    ///
    /// # Specification
    /// trivial.
    fn leading(
        &self,
        at: NodeIndex,
    ) -> Yes
    {
        for child in self.tree.children(at) {
            let Some(node) = self.tree.node(child)
            else {
                continue;
            };
            if self.is_comment(child).0 {
                return Yes(true);
            }
            if !matches!(node.label(), NodeLabel::Space) {
                return Yes(false);
            }
        }
        Yes(false)
    }

    /// Whether a comment among `parent`'s children runs up to `anchor`, no
    /// blank line and no other node between them.
    ///
    /// # Specification
    /// trivial.
    fn sibling(
        &self,
        parent: NodeIndex,
        anchor: NodeIndex,
    ) -> Yes
    {
        let start = self.span(anchor).start;
        let mut previous_end = 0_usize;
        let mut saw_comment = false;
        for child in self.tree.children(parent) {
            if child == anchor {
                break;
            }
            let Some(node) = self.tree.node(child)
            else {
                continue;
            };
            if self.is_comment(child).0 {
                previous_end = usize::from(node.span().end());
                saw_comment = true;
            }
            else if !matches!(node.label(), NodeLabel::Space) {
                saw_comment = false;
            }
        }
        Yes(saw_comment
            && !blank(self.source, Span {
                start: previous_end,
                end: start,
            })
            .0)
    }

    /// The first child of `at` past its comments, its attribute tiles and its
    /// `pub` mark, with that child's tile label when it is a tile.
    ///
    /// # Specification
    /// trivial.
    fn head(
        &self,
        at: NodeIndex,
    ) -> Result<Option<(NodeIndex, Option<Text<'static>>)>, CommentError>
    {
        let mut depth = 0_usize;
        for child in self.tree.children(at) {
            let Some(node) = self.tree.node(child)
            else {
                continue;
            };
            if matches!(node.label(), NodeLabel::Doc | NodeLabel::Space) {
                continue;
            }
            let label = self.tile_label(child)?;
            match label.map(|held| held.0) {
                Some("@[") => depth = depth.saturating_add(1),
                Some("[") if depth > 0 => depth = depth.saturating_add(1),
                Some("]") if depth > 0 => depth = depth.saturating_sub(1),
                _ if depth > 0 => {},
                Some("pub") => {},
                _ => return Ok(Some((child, label))),
            }
        }
        Ok(None)
    }

    /// Judge the run of items `next`, and queue on `pending` the body of
    /// every block among them.
    ///
    /// # Specification
    /// trivial.
    fn items(
        &self,
        next: &Pending,
        found: &mut Vec<Finding>,
        pending: &mut Vec<Pending>,
    ) -> Result<(), CommentError>
    {
        let prefix = next
            .block
            .as_ref()
            .map_or_else(String::new, |held| format!("{held}."));
        // The previous item's name, where it ends, and whether it is commented.
        let mut previous: Option<(String, usize, bool)> = None;
        let mut attributes: Vec<NodeIndex> = Vec::new();
        for &child in &next.children {
            let Some(node) = self.tree.node(child)
            else {
                continue;
            };
            let (NodeLabel::Meld(mold) | NodeLabel::Tile(mold)) = node.label()
            else {
                continue;
            };
            let kind = self
                .pbg
                .named_kind(mold)
                .map_err(|error| self.unresolved(error.to_string()))?;
            // A `pub` mark is one tile before the item it exports: the comment
            // before it comments the item, as one before an attribute block
            // does.
            if kind.0 == "attribute_block" || kind.0 == "pub_declaration" {
                attributes.push(child);
                continue;
            }
            if matches!(node.label(), NodeLabel::Tile(_)) {
                continue;
            }
            let anchor = attributes.first().copied().unwrap_or(child);
            attributes.clear();
            let start = self.span(anchor).start;
            let own = item_name(self.pbg, self.file, self.tree, child)?
                .unwrap_or_else(|| kind.0.to_owned());
            let inherited = previous
                .as_ref()
                .is_some_and(|&(ref held, end, commented)| {
                    commented
                        && *held == own
                        && on_next_line(self.source, Span {
                            start: end,
                            end: start,
                        })
                        .0
                });
            let commented =
                inherited || self.leading(anchor).0 || self.sibling(next.parent, anchor).0;
            let end = usize::from(node.span().end());
            if !commented {
                // A member's attribute tiles sit inside it; its text starts
                // past them, as an item's starts past its attribute block.
                let text_start = self.head(child)?.map_or_else(
                    || usize::from(node.span().start()),
                    |(first, _)| self.span(first).start,
                );
                let held = Span {
                    start: text_start,
                    end,
                };
                let key = digest(Text(&item_text(self.source, held, &self.quiet)));
                found.push(Finding {
                    line: format!(
                        "{file}:{prefix}{own}:{key} {UNCOMMENTED}",
                        file = self.file.0
                    ),
                    detail: format!(
                        "{file}: {prefix}{own} ({key}) has no comment before its attribute block",
                        file = self.file.0
                    ),
                });
            }
            if let Some((children, tiles)) = self.block(child)? {
                pending.push(Pending {
                    parent: child,
                    children,
                    block: Some(format!("{prefix}{own}")),
                    tiles,
                });
            }
            previous = Some((own, end, commented));
        }
        Ok(())
    }

    /// The body of the item at `at` when it is a block, and whether it is a
    /// block of tiles.
    ///
    /// # Specification
    /// trivial.
    fn block(
        &self,
        at: NodeIndex,
    ) -> Result<Option<(Vec<NodeIndex>, Yes)>, CommentError>
    {
        let Some((_, Some(keyword))) = self.head(at)?
        else {
            return Ok(None);
        };
        let tiles = TILE_BLOCKS.contains(&keyword.0);
        if !tiles && !ITEM_BLOCKS.contains(&keyword.0) {
            return Ok(None);
        }
        let children: Vec<NodeIndex> = self.tree.children(at).collect();
        let mut open = None;
        let mut close = None;
        for (place, &child) in children.iter().enumerate() {
            match self.tile_label(child)?.map(|held| held.0) {
                Some("{") if open.is_none() => open = Some(place),
                Some("}") => close = Some(place),
                _ => {},
            }
        }
        let (Some(open), Some(close)) = (open, close)
        else {
            return Ok(None);
        };
        let body = children
            .get(open.saturating_add(1) .. close)
            .unwrap_or_default()
            .to_vec();
        Ok(Some((body, Yes(tiles))))
    }

    /// Judge the members of a block of tiles, each the run of `body` up to a
    /// `;` or a closing brace outside any inner brace.
    ///
    /// # Specification
    /// trivial.
    fn tile_members(
        &self,
        body: &[NodeIndex],
        block: Text<'_>,
        found: &mut Vec<Finding>,
    ) -> Result<(), CommentError>
    {
        let mut comment_end: Option<usize> = None;
        let mut member: Vec<NodeIndex> = Vec::new();
        let mut commented = false;
        let mut depth = 0_usize;
        for &child in body {
            let Some(node) = self.tree.node(child)
            else {
                continue;
            };
            if self.is_comment(child).0 {
                if member.is_empty() {
                    comment_end = Some(usize::from(node.span().end()));
                }
                continue;
            }
            if matches!(node.label(), NodeLabel::Space) {
                continue;
            }
            if member.is_empty() {
                let start = usize::from(node.span().start());
                commented = comment_end.is_some_and(|end| {
                    !blank(self.source, Span {
                        start: end,
                        end: start,
                    })
                    .0
                });
            }
            member.push(child);
            let ends = match self.tile_label(child)?.map(|held| held.0) {
                Some("{") => {
                    depth = depth.saturating_add(1);
                    false
                },
                Some("}") => {
                    depth = depth.saturating_sub(1);
                    depth == 0
                },
                Some(";") => depth == 0,
                _ => false,
            };
            if ends {
                if !commented {
                    self.tile_member(&member, block, found)?;
                }
                member.clear();
                comment_end = None;
            }
        }
        if !member.is_empty() && !commented {
            self.tile_member(&member, block, found)?;
        }
        Ok(())
    }

    /// The finding of the uncommented member of `block` whose nodes are
    /// `member`, past its comments and spaces; nothing for a lone `;`.
    ///
    /// # Specification
    /// trivial.
    fn tile_member(
        &self,
        member: &[NodeIndex],
        block: Text<'_>,
        found: &mut Vec<Finding>,
    ) -> Result<(), CommentError>
    {
        let (Some(&first), Some(&last)) = (member.first(), member.last())
        else {
            return Ok(());
        };
        let lead = self.tile_label(first)?;
        if lead.is_some_and(|held| held.0 == ";") {
            return Ok(());
        }
        let own = self.member_name(member, lead)?;
        let held = Span {
            start: self.span(first).start,
            end: self.span(last).end,
        };
        let key = digest(Text(&item_text(self.source, held, &self.quiet)));
        found.push(Finding {
            line: format!(
                "{file}:{block}.{own}:{key} {UNCOMMENTED}",
                file = self.file.0,
                block = block.0
            ),
            detail: format!(
                "{file}: {block}.{own} ({key}) has no comment before it",
                file = self.file.0,
                block = block.0
            ),
        });
        Ok(())
    }

    /// The name a block member spells: its leading name, the name after its
    /// keyword (`sort S`, `oper get`, `rule putGet`), its keyword when no name
    /// follows it, else its first name.
    ///
    /// # Specification
    /// trivial.
    fn member_name(
        &self,
        member: &[NodeIndex],
        lead: Option<Text<'static>>,
    ) -> Result<String, CommentError>
    {
        let spelled = |at: NodeIndex| {
            self.tree
                .fragment(at)
                .map(|text| <&str>::from(text).to_owned())
                .filter(|text| !text.is_empty())
        };
        let mut names = Vec::new();
        for &child in member {
            let label = self.tile_label(child)?;
            names.push(
                label
                    .filter(|held| NAME_LABELS.contains(&held.0))
                    .and_then(|_| spelled(child)),
            );
        }
        if let Some(name) = names.first().cloned().flatten() {
            return Ok(name);
        }
        let lead = lead.map(|held| held.0);
        if let Some(keyword) = lead.filter(|held| held.chars().all(char::is_alphabetic)) {
            return Ok(names
                .get(1)
                .cloned()
                .flatten()
                .unwrap_or_else(|| keyword.to_owned()));
        }
        Ok(names
            .into_iter()
            .flatten()
            .next()
            .unwrap_or_else(|| lead.unwrap_or("member").to_owned()))
    }
}

/// Whether the stretch of `source` from `gap.start` to `gap.end` holds a
/// blank line, or does not run forward.
///
/// # Specification
/// trivial.
fn blank(
    source: Text<'_>,
    gap: Span,
) -> Yes
{
    if gap.end < gap.start {
        return Yes(true);
    }
    let Some(stretch) = source.0.get(gap.start .. gap.end)
    else {
        return Yes(true);
    };
    let mut after_newline = false;
    for character in stretch.chars() {
        if character == '\n' {
            if after_newline {
                return Yes(true);
            }
            after_newline = true;
        }
        else if !character.is_whitespace() {
            after_newline = false;
        }
    }
    Yes(false)
}

/// The name the item at `at` declares, when one of its tiles spells one.
///
/// # Specification
/// - requires: `at` is a position in `tree`, molded under `pbg`.
/// - ensures: the text of the item's first non-empty direct tile, outside an
///   attribute's `@[ … ]`, whose mold is labelled as a name, or nothing when no
///   tile is.
/// - provides: the name half of a ledger line and the key of a name run.
/// - fails: a tile's mold does not resolve under `pbg`.
/// - panics: none.
///
/// # Errors
/// [`CommentError::Mold`] when a tile's mold does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — an uncommented `def` is named by its identifier, a body
///   is matched to its signature by that name, and a module member is named by
///   its identifier, not by its attribute's.
/// - witness: `tests::comments::judge::tests::an_uncommented_item_is_refused_by_name`
/// - witness: `tests::comments::judge::tests::a_body_inherits_its_signatures_comment`
/// - witness: `tests::comments::judge::tests::every_item_member_owes_its_own_comment`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |name| name.as_ref().is_none_or(|text| !text.is_empty())))]
fn item_name(
    pbg: &Pbg,
    file: Text<'_>,
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Result<Option<String>, CommentError>
{
    let mut depth = 0_usize;
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
        match defined.label {
            "@[" => depth = depth.saturating_add(1),
            "[" if depth > 0 => depth = depth.saturating_add(1),
            "]" if depth > 0 => depth = depth.saturating_sub(1),
            _ => {},
        }
        if depth > 0 || !NAME_LABELS.contains(&defined.label) {
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
        format!("sample.gandr:{}:{} uncommented", name.0, digest(text))
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
        let refused = discrepancies(&found, Text("")).expect("the ledger reads");
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
        let refused = discrepancies(&found, Text(&ledger)).expect("the ledger reads");
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
        let refused = discrepancies(&found, Text(&format!("{gone}\n"))).expect("the ledger reads");
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
                "sample.gandr:<file> uncommented".to_owned(),
                key(Text("first"), Text("def first = 1;")),
            ],
            "a source that opens on an item has no leading comment, and the later item's own \
             comment is not the file's"
        );
        let pbg = grammar().expect("the built-in grammar builds");
        let found =
            findings_of(&pbg, Text("sample.gandr"), source).expect("the source commits a tree");
        let ledger = format!("{}\n", key(Text("first"), Text("def first = 1;")));
        let refused = discrepancies(&found, Text(&ledger)).expect("the ledger reads");
        assert!(
            refused
                .iter()
                .any(|row| row.line().0 == "sample.gandr:<file> uncommented" && !row.is_stale().0),
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
                "sample.gandr:<file> uncommented".to_owned(),
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

    #[test]
    fn every_tile_member_owes_its_own_comment()
    {
        let mut owed = lines(Text(concat!(
            "// file\n\n",
            "// the naturals\n",
            "data Nat : Type {\n",
            "  // the base\n",
            "  Zero : Nat;\n",
            "  Succ : (n : Nat) --> Nat;\n",
            "\n",
            "  // a comment cut off by a blank line\n",
            "\n",
            "  rule Succ(Zero) <=> Zero;\n",
            "}\n\n",
            "// a theory\n",
            "theory T {\n",
            "  /// the carrier\n",
            "  sort S : Type+;\n",
            "  oper get : (k : S) --> S;\n",
            "  rule g : get(k) <=> k;\n",
            "}\n\n",
            "// a stream\n",
            "codata Stream(a : Type) : Type[-] {\n",
            "  head : a;\n",
            "  /// what follows\n",
            "  tail : Stream(a);\n",
            "}\n",
        )));
        owed.sort();
        let mut expected = vec![
            key(Text("Nat.Succ"), Text("Succ : (n : Nat) --> Nat;")),
            key(Text("Nat.rule"), Text("rule Succ(Zero) <=> Zero;")),
            key(Text("T.get"), Text("oper get : (k : S) --> S;")),
            key(Text("T.g"), Text("rule g : get(k) <=> k;")),
            key(Text("Stream.head"), Text("head : a;")),
        ];
        expected.sort();
        assert_eq!(
            owed, expected,
            "each commented block still owes a comment per member: a constructor by its name, \
             a sort, operation or rule by the name after its keyword, an unnamed rule by its \
             keyword, and a comment ended by a blank line covers nothing"
        );
    }

    #[test]
    fn every_item_member_owes_its_own_comment()
    {
        let mut owed = lines(Text(concat!(
            "// file\n\n",
            "// a module\n",
            "module M {\n",
            "  /// one\n",
            "  @[ checks ]\n",
            "  def one = 1;\n",
            "  def two = 2;\n",
            "  @[ checks ]\n",
            "  def three = 3;\n",
            "}\n\n",
            "// a rec block\n",
            "rec {\n",
            "  data Rose : Type {\n",
            "    Node : Rose;\n",
            "  }\n",
            "}\n",
        )));
        owed.sort();
        let mut expected = vec![
            key(Text("M.two"), Text("def two = 2;")),
            key(Text("M.three"), Text("def three = 3;")),
            key(
                Text("rec_block.Rose"),
                Text("data Rose : Type { Node : Rose; }"),
            ),
            key(Text("rec_block.Rose.Node"), Text("Node : Rose;")),
        ];
        expected.sort();
        assert_eq!(
            owed, expected,
            "a module's members are items named under it, by their own name and text rather \
             than their attribute's, and a block inside a block names its members by the path"
        );
    }
}
