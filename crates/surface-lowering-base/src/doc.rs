//! Documentation: what a declaration's `///` lines and `doc("…")` entries,
//! and a source's `//!` lines, say, read into one text, and the names that
//! text links to.
//!
//! # Both spellings are one attribute
//!
//! The parser groups a run of `///` lines, and a `doc("…")` entry of an
//! attribute block, under the form they document as one
//! [`NodeLabel::Doc`] node, which reaches no digest. This module reads either
//! spelling into the same [`Documentation`]: a `///` line contributes the text
//! after its slashes, less one leading space, and an entry contributes its
//! string's decoded content. Pieces join in source order, one line break
//! between them, so moving a sentence between the two spellings leaves the
//! text as it was.
//!
//! # A link is checked where it is written
//!
//! `[name]`, or `` [`name`] ``, inside documentation is a link to the name it
//! holds, read as rustdoc reads an intra-doc link: a bracketed run followed by
//! `(`, `[` or `:` is a Markdown link or reference instead, and brackets inside
//! a code span are text. The lowering resolves every link against the names
//! the module declares, so a rename or a deletion breaks the link at its own
//! span rather than leaving stale prose.
//!
//! # Documentation: one text, its links checked
//!
//! A declaration's documentation is every `NodeLabel::Doc` the parser grouped
//! inside the attribute blocks that decorate it or before its name: `///` runs
//! and `doc("…")` entries alike, in source order. A run reads as its lines with
//! the `///` and one following space removed, joined by line breaks; an entry
//! reads as its string literal decoded; the pieces join by line breaks.
//! `LoweredModule::documentation` answers it under the content identity of the
//! declaration form, the key the attribute table uses, and the parser keeps
//! documentation out of that identity, so documenting a declaration re-keys
//! nothing. A module form is documented the same way and answers under its
//! own key, a nested module's included; its members keep their own.
//! Documentation inside a body, before a constructor say, is not read.
//!
//! A link is a bracketed name, `[name]` or ``[`name`]``, a dotted path
//! included, as an intra-doc link is in rustdoc: a bracket pair followed by
//! `(`, `[` or `:` is a Markdown link or reference instead, and a bracket
//! inside a code span is text. A link resolves as a name written in the source
//! does, as a declared path, any declared name, a module or a constructor, and
//! one nothing answers refuses its declaration as `UnresolvedDocLink` at the
//! linked name, so renaming or deleting a declaration breaks the documentation
//! that names it where the link is written. A module is no declaration, so a
//! broken link in its documentation refuses its first member, as a module's
//! refused attribute does; a module with no member has none to refuse.
//!
//! A link that names a declaration keeps it as its target
//! ([`Documentation::targets`]): the lowering reads the name where the
//! documentation stands, in the documented form's module and then around it.
//! The hover and `gandr doc` follow the target to write a Markdown reference
//! line, `[name]: <file URI>#L<line>`, so a reader follows `[name]` to the
//! declaration. A link to a module, a constructor or a built-in name keeps no
//! target, and reads as text.
//!
//! A reference leaves the prose for the footer of its run. The footer is the
//! run of lines `[label]: target` that ends a `///` run, a `//!` run or the
//! string of a `doc("…")` entry. A link to a label the footer defines
//! resolves to that line, and the lowering looks for no declaration. A
//! reference line with prose after it is no footer. A link to its label
//! resolves as any other link does.
//!
//! A source documents itself with `//!` lines, which the parser groups as it
//! groups `///` lines and leaves with the node they stand in. A run standing
//! at a root is the source's own: it reads as a `///` run does and is filed
//! under the source, every run of one source joined in source order, and
//! `LoweredModule::source_documentation` answers it, as an import's hover
//! does beside the file it reads. A broken link in it refuses the source's
//! first declaration, as a module's does its first member. A `//!` run inside
//! a form is not read.
//!
//! A source is keyed by its place in the unit because a file writes no form
//! of its own to key by. The alternative was filing a source's documentation
//! under its first declaration's key, which would merge it with that
//! declaration's own and lose it from a source declaring nothing. Reversal:
//! when a source gains a content identity, as a module form per file would
//! give it, its documentation is filed under that key.
//!
//! The alternative was storing documentation as an attribute entry with a text
//! payload. It was declined because an entry's payload is minted into the core
//! arena and the attribute table carries no source borrow, while a link names
//! the source it was written in. A broken link refuses its declaration because
//! the lowering has no warning severity; reversal: when diagnostics carry a
//! severity, a broken link is a warning and the declaration lowers.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Shape;
use crate::form::shape_of;
use crate::lower::parse_literal;
use crate::resolve::SurfaceName;

/// The opening of a documentation line.
const DOC_LINE: &str = "///";

/// The opening of an inner documentation line, a source's own.
pub const INNER_DOC_LINE: &str = "//!";

quenchant_shape::reason_enum! {
    /// Why a documentation node carries no entry's string.
    pub mod entry {
        /// The node is not a `doc("…")` entry.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node is a run of `///` or `//!` lines.
            Lines,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration form has no documentation.
    pub mod documentation {
        /// Nothing documents the form.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The form wrote neither `///` lines nor a `doc("…")` entry.
            Undocumented,
        }
    }
}

/// The text a declaration's documentation says.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DocumentationText(String);

impl AsRef<str> for DocumentationText
{
    /// The text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// One link documentation writes: the name it holds and where it stands.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DocLink<'source>
{
    /// The name between the brackets.
    name: SurfaceName<'source>,
    /// The bytes of the name in the source.
    span: ByteSpan,
}

impl<'source> DocLink<'source>
{
    /// The name between the brackets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> SurfaceName<'source>
    {
        self.name
    }

    /// The bytes of the name in the source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }
}

/// A link that resolves to a declaration: the name the link writes and the
/// admission position of the declaration it names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinkTarget<'source>
{
    /// The name between the brackets.
    name: SurfaceName<'source>,
    /// The declaration the name resolves to.
    constant: ConstantIndex,
}

impl<'source> LinkTarget<'source>
{
    /// The name between the brackets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> SurfaceName<'source>
    {
        self.name
    }

    /// The declaration the name resolves to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }
}

/// A declaration form's documentation: the text of every piece written for
/// it, in source order, the names that text links to, and the declaration
/// each name resolves to.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Documentation<'source>
{
    /// The pieces' text, one line break between pieces.
    text: DocumentationText,
    /// Every link the pieces write, in source order.
    links: Vec<DocLink<'source>>,
    /// Each linked name that resolves to a declaration, once, in the order
    /// the links first write it.
    targets: Vec<LinkTarget<'source>>,
}

impl<'source> Documentation<'source>
{
    /// The pieces' text, one line break between pieces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn text(&self) -> &DocumentationText
    {
        &self.text
    }

    /// Every link the pieces write, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn links(&self) -> &[DocLink<'source>]
    {
        &self.links
    }

    /// Each linked name that resolves to a declaration, once, in the order
    /// the links first write it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn targets(&self) -> &[LinkTarget<'source>]
    {
        &self.targets
    }

    /// How many links the pieces write so far: the mark a later piece's links
    /// start after.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn link_count(&self) -> LinkCount
    {
        LinkCount(self.links.len())
    }

    /// The links the pieces write from the mark `from` on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn links_from(
        &self,
        from: LinkCount,
    ) -> &[DocLink<'source>]
    {
        self.links.get(from.0 ..).unwrap_or_default()
    }

    /// Keep that the linked name `name` resolves to the declaration admitted
    /// at `constant`, after the targets kept already.
    ///
    /// # Specification
    /// - requires: `name` is the name of one of the links, and no target of
    ///   `name` is kept yet.
    /// - ensures: the target is the last one kept.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name linked twice keeps one target.
    /// - witness: `gandr-surface-lowering::lower::tests::a_link_keeps_the_declaration_it_resolves_to_4963`
    #[inline]
    #[spec(ensures: self.targets.last().is_some_and(|target| target.name == name && target.constant == constant))]
    pub fn target(
        &mut self,
        name: SurfaceName<'source>,
        constant: ConstantIndex,
    )
    {
        self.targets.push(LinkTarget { name, constant });
    }
}

/// A count of the links a documentation writes, the mark the links of a
/// later piece start after.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinkCount(usize);

/// Read the documentation node at `at` onto `into`.
///
/// # Specification
/// - requires: `at` is a [`NodeLabel::Doc`] node of `tree`, molded under `pbg`.
/// - ensures: a node holding a string form is a `doc("…")` entry and
///   contributes the string's decoded content; any other contributes each of
///   its `///` or `//!` lines, the text after the opening less one leading
///   space, one line break between lines. The piece follows `into`'s text after
///   one line break when that text is not empty. Every link the piece writes
///   joins `into`'s links with its source span, except a link to a label the
///   piece's own footer defines ([`footer_labels`]).
/// - provides: the one reading both documentation spellings share.
/// - fails: [`LoweringRefusal::MalformedLiteral`] for an entry whose string
///   does not decode; [`LoweringRefusal::UnknownMold`] for a mold `pbg` does
///   not hold. `into` is unchanged on failure.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — `///` lines, `//!` lines and the equivalent entry read to
///   equal documentation, two pieces join with one line break, and a link in
///   each spelling is found at its exact span. The body writes `into` only
///   after its last refusal and only by appending, so the predicate checks the
///   text and link counts against the ones captured on entry rather than
///   copying the documentation read so far; the witnesses assert the joined
///   text.
/// - witness: `doc::tests::both_spellings_read_to_one_text`
/// - witness: `doc::tests::links_are_found_where_they_are_written`
/// - witness: `doc::tests::a_footer_line_answers_its_label`
#[spec(
    captures: before = (into.text.0.len(), into.links.len()),
    ensures: |ret| match ret {
        | Ok(()) => into.text.0.len() >= before.0 && into.links.len() >= before.1,
        | Err(_) => into.text.0.len() == before.0 && into.links.len() == before.1,
    },
)]
#[inline]
pub fn read_doc<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    at: NodeIndex,
    into: &mut Documentation<'source>,
) -> Result<(), LoweringRefusal<'source>>
{
    let mut lines: Vec<&'source str> = Vec::new();
    let mut links: Vec<DocLink<'source>> = Vec::new();
    let mut entry: Maybe<String, entry::Absent> = Maybe::Absent(entry::Absent::Lines);
    for child in tree.children(at) {
        let (Some(node), Some(written)) = (tree.node(child), tree.fragment(child))
        else {
            continue;
        };
        let written: &'source str = written.into();
        let span = node.span();
        if let NodeLabel::Meld(_) = node.label()
            && let Shape::Form {
                former: Former::Text,
                ..
            } = shape_of(pbg, node)?
        {
            let Maybe::Present(Literal::Text(literal)) =
                parse_literal(Former::Text, SourceFragment::from(written))
            else {
                return Err(LoweringRefusal::MalformedLiteral {
                    span,
                    form: FormName::STRING,
                });
            };
            entry = Maybe::Present(String::from(literal.as_ref()));
            scan_links(SourceFragment::from(written), span.start(), &mut links);
            continue;
        }
        let Some(line) = written
            .strip_prefix(DOC_LINE)
            .or_else(|| written.strip_prefix(INNER_DOC_LINE))
        else {
            continue;
        };
        if node.label() != NodeLabel::Space {
            continue;
        }
        let opened = written.len().saturating_sub(line.len());
        let (line, skipped) = line
            .strip_prefix(' ')
            .map_or((line, opened), |rest| (rest, opened.saturating_add(1)));
        lines.push(line);
        let start = ByteOffset::from(usize::from(span.start()).saturating_add(skipped));
        scan_links(SourceFragment::from(line), start, &mut links);
    }
    let text = DocumentationText(match entry {
        Maybe::Present(content) => content,
        Maybe::Absent(_) => lines.join("\n"),
    });
    let footer = footer_labels(&text);
    links.retain(|link| !footer.contains(&link.name));
    if !into.text.0.is_empty() {
        into.text.0.push('\n');
    }
    into.text.0.push_str(&text.0);
    into.links.append(&mut links);

    Ok(())
}

/// The labels the footer of `text` defines. The footer is the run of lines
/// that ends `text`, each a reference line `[label]: target`. Blank lines
/// between and after the reference lines belong to the footer too.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each label of a reference line in the footer, its backticks
///   removed; nothing for a reference line that prose follows.
/// - provides: the names a link resolves to without a declaration.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a footer after a blank line, a backticked label, a
///   reference line with prose after it and a run with no footer each read to
///   their exact labels.
/// - witness: `doc::tests::a_footer_line_answers_its_label`
#[spec(ensures: |ret| ret.iter().all(|label| !label.as_ref().is_empty()))]
fn footer_labels(text: &DocumentationText) -> BTreeSet<SurfaceName<'_>>
{
    let mut labels = BTreeSet::new();
    for line in text.0.lines().rev() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let Some(label) = line
            .strip_prefix('[')
            .and_then(|rest| rest.split_once("]:"))
            .map(|(label, _)| label)
        else {
            break;
        };
        let label = label
            .strip_prefix('`')
            .and_then(|quoted| quoted.strip_suffix('`'))
            .unwrap_or(label);
        if label.is_empty() {
            break;
        }
        let _fresh = labels.insert(SurfaceName::from(label));
    }
    labels
}

/// Push every link `written` holds onto `links`, `written` standing at `start`
/// in the source.
///
/// # Specification
/// - requires: `written` is the source text at `start`.
/// - ensures: a link is a `[`, an optional backtick, a name, the matching
///   backtick and a `]` not followed by `(`, `[` or `:`, outside a code span; a
///   name is a letter or `_` followed by letters, digits, `_` and `.` between
///   segments. Each is pushed with the span of its name alone, in source order;
///   nothing else is.
/// - provides: the recognition of an intra-doc link.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a bare and a backticked link, a Markdown link, a
///   reference, a bracket inside a code span, a bracketed non-name and a name
///   with an underscore beside one with a hyphen each separate a link from
///   text.
/// - witness: `doc::tests::links_are_found_where_they_are_written`
#[spec(captures: before = links.len(), ensures: links.len() >= before)]
fn scan_links<'source>(
    written: SourceFragment<'source>,
    start: ByteOffset,
    links: &mut Vec<DocLink<'source>>,
)
{
    let text: &'source str = written.into();
    let bytes = text.as_bytes();
    let is_name = |name: &str| {
        !name.is_empty()
            && name.split('.').all(|segment| {
                let mut characters = segment.chars();
                characters
                    .next()
                    .is_some_and(|first| first.is_alphabetic() || first == '_')
                    && characters.all(|rest| rest.is_alphanumeric() || rest == '_')
            })
    };
    let mut in_code = false;
    let mut at = 0_usize;
    while let Some(&byte) = bytes.get(at) {
        match byte {
            b'`' => {
                in_code = !in_code;
                at = at.saturating_add(1);
            },
            b'[' if !in_code => {
                let Some(close) = text
                    .get(at ..)
                    .and_then(|rest| rest.find(']'))
                    .map(|offset| at.saturating_add(offset))
                else {
                    return;
                };
                let inner_start = at.saturating_add(1);
                let inner = text.get(inner_start .. close).unwrap_or_default();
                let (name, offset) = inner
                    .strip_prefix('`')
                    .and_then(|quoted| quoted.strip_suffix('`'))
                    .map_or((inner, inner_start), |quoted| {
                        (quoted, inner_start.saturating_add(1))
                    });
                let follows = bytes.get(close.saturating_add(1)).copied();
                if is_name(name) && !matches!(follows, Some(b'(' | b'[' | b':')) {
                    let first = usize::from(start).saturating_add(offset);
                    let last = first.saturating_add(name.len());
                    if let Ok(span) = ByteSpan::new(ByteOffset::from(first), ByteOffset::from(last))
                    {
                        links.push(DocLink {
                            name: SurfaceName::from(name),
                            span,
                        });
                    }
                }
                at = close.saturating_add(1);
            },
            _ => at = at.saturating_add(1),
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::NodeIndex;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceText;
    use gandr_surface_syntax::SyntaxTree;

    use super::Documentation;
    use super::read_doc;

    /// The grammar every test parses under.
    ///
    /// # Specification
    /// trivial.
    fn grammar() -> Pbg
    {
        built_in().unwrap()
    }

    /// Every documentation node of `tree`, in ascending position order.
    ///
    /// # Specification
    /// trivial.
    fn docs(tree: &SyntaxTree<'_>) -> Vec<NodeIndex>
    {
        tree.positions()
            .filter(|&position| {
                tree.node(position)
                    .is_some_and(|node| node.label() == NodeLabel::Doc)
            })
            .collect()
    }

    /// The documentation every documentation node of `source` reads to.
    ///
    /// # Specification
    /// trivial.
    fn read(source: SourceText<'static>) -> (Documentation<'static>, Vec<String>)
    {
        let pbg = grammar();
        let tree = gandr_surface_parser::parse(&pbg, source)
            .unwrap()
            .into_tree();
        let mut documentation = Documentation::default();
        for at in docs(&tree) {
            read_doc(&pbg, &tree, at, &mut documentation).unwrap();
        }
        let links = documentation
            .links()
            .iter()
            .map(|link| {
                let span = link.span();
                let spanned = source
                    .as_ref()
                    .get(usize::from(span.start()) .. usize::from(span.end()))
                    .unwrap();
                format!("{}={spanned}", link.name())
            })
            .collect();
        (documentation, links)
    }

    #[test]
    fn both_spellings_read_to_one_text()
    {
        let (lines, _) = read(SourceText::from(include_str!(
            "doc/fixtures/both-spellings-read-to-one-text-1.gandr"
        )));
        let (entry, _) = read(SourceText::from(
            "@[ doc(\"Squares\\nits argument.\") ] def square = 1 ;",
        ));
        assert_eq!(lines.text().as_ref(), "Squares\nits argument.");
        assert_eq!(
            lines.text(),
            entry.text(),
            "a `///` run and the equivalent entry read to one text"
        );
        let (inner, inner_links) = read(SourceText::from(include_str!(
            "doc/fixtures/both-spellings-read-to-one-text-2.gandr"
        )));
        assert_eq!(
            inner.text().as_ref(),
            "Squares\nits [argument].",
            "a `//!` run reads as a `///` run does, a tight line kept whole"
        );
        assert_eq!(
            inner_links,
            ["argument=argument"],
            "a link in a `//!` line spans its name"
        );
        let (joined, _) = read(SourceText::from(include_str!(
            "doc/fixtures/both-spellings-read-to-one-text-3.gandr"
        )));
        assert_eq!(
            joined.text().as_ref(),
            "First.\nSecond.",
            "pieces join in source order, one line break between them"
        );
        let (unspaced, _) = read(SourceText::from(include_str!(
            "doc/fixtures/both-spellings-read-to-one-text-4.gandr"
        )));
        assert_eq!(
            unspaced.text().as_ref(),
            "Tight.",
            "a line without a leading space keeps its first character"
        );
    }

    #[test]
    fn links_are_found_where_they_are_written()
    {
        let (_, links) = read(SourceText::from(include_str!(
            "doc/fixtures/links-are-found-where-they-are-written-1.gandr"
        )));
        assert_eq!(links, ["first=first", "second=second"]);
        let (_, entry) = read(SourceText::from(
            "@[ doc(\"Uses [M.inner].\") ] def x = 1 ;",
        ));
        assert_eq!(
            entry,
            ["M.inner=M.inner"],
            "a link inside an entry's string spans its name in the source"
        );
        let (_, mixed) = read(SourceText::from(include_str!(
            "doc/fixtures/links-are-found-where-they-are-written-2.gandr"
        )));
        assert_eq!(
            mixed,
            ["snake_case=snake_case"],
            "an underscore continues a name and a hyphen ends one"
        );
    }

    #[test]
    fn a_footer_line_answers_its_label()
    {
        let (_, footed) = read(SourceText::from(include_str!(
            "doc/fixtures/a-footer-line-answers-its-label-1.gandr"
        )));
        assert_eq!(
            footed,
            ["other=other"],
            "a label the footer defines needs no declaration, and another link still does"
        );
        let (_, early) = read(SourceText::from(include_str!(
            "doc/fixtures/a-footer-line-answers-its-label-2.gandr"
        )));
        assert_eq!(
            early,
            ["guide=guide"],
            "a reference line with prose after it is no footer"
        );
        let (_, entry) = read(SourceText::from(
            "@[ doc(\"See [guide].\\n\\n[guide]: https://example.org\") ] def x = 1 ;",
        ));
        assert!(
            entry.is_empty(),
            "an entry's string has a footer too: {entry:?}"
        );
    }
}
