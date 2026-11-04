//! A package's documentation as Markdown: one page per source, and an index
//! naming each source by the first sentence of its own documentation.
//!
//! # A page is the hover of each public declaration
//!
//! [`page`] judges a source laid out over its import closure, as an editor's
//! copy is judged, and reads it as a hover does. The page opens with the
//! source's path as its title and its own `//!` documentation. Then comes each
//! public declaration the source writes, in source order, a declaration being
//! public when `pub` is written before its head. Each has a heading naming it,
//! then the block a hover on its name shows: the fenced `gandr` block with the
//! name and its type, or the declaration as written for a theory or a module,
//! then a refusal, a deprecation and the `///` documentation, each after a
//! blank line, and a reference line per declaration the documentation links.
//! Both come from one function, so a page and a hover never differ. A link
//! leads to the file of the declaring source, not to another page.
//! The types are spelled as the editor spells them by default: sugared, in
//! Unicode.
//!
//! The alternative was a printer of its own over the lowering's declarations:
//! it would print each signature a second way, beside the hover's, and the two
//! would drift. A page returns to its own printer when it shows what a hover
//! does not, such as the body of a definition.
//!
//! [`index`] lists the pages under the package's name, each linked by its path
//! beside its summary. Pages are Markdown alone, so the documentation needs no
//! renderer; links between pages, doctests and an HTML site are later stages.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::DiscardingCheckpointStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::Unshadowed;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::lay_out_shadowed;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Spelling;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_session::ClosureSlot;
use gandr_surface_session::Session;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::hover::Quoted;
use crate::hover::Style;
use crate::hover::declared;
use crate::hover::hovering_laid;
use crate::markup::Markup;
use crate::reading::Reading;
use crate::reading::Written;
use crate::recheck::grammar;

/// The style a page spells its types in: the editor's default, sugared and
/// in Unicode, in Markdown.
const PAGE: Style = Style {
    form: Form::Sugared,
    spelling: Spelling::Unicode,
    markup: Markup::Markdown,
};

/// One source's documentation page.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Page
{
    /// The page, as Markdown.
    pub markdown: String,
    /// The first sentence of the source's own documentation, or nothing when
    /// it has none.
    pub summary: String,
}

/// One row of an index: where a source's page is, relative to the index, and
/// its summary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry
{
    /// The page's path relative to the index, as the link writes it.
    pub page: PathBuf,
    /// The source's path relative to the package, as the link reads.
    pub source: PathBuf,
    /// The page's summary.
    pub summary: String,
}

/// Why a source has no page.
#[derive(Debug, Eq, PartialEq)]
pub enum Unpaged
{
    /// The source could not be read, for this reason.
    Unread(String),
    /// The built-in grammar did not build, for this reason.
    Unbuilt(String),
    /// The source did not parse.
    Unparsed,
    /// The session faulted judging the source, for this reason.
    Faulted(String),
}

impl core::fmt::Display for Unpaged
{
    /// The reason as a sentence fragment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Unread(ref why) => write!(f, "the source could not be read: {why}"),
            Self::Unbuilt(ref why) => write!(f, "the built-in grammar did not build: {why}"),
            Self::Unparsed => f.write_str("the source did not parse"),
            Self::Faulted(ref fault) => write!(f, "the source did not judge: {fault}"),
        }
    }
}

impl core::error::Error for Unpaged
{
}

/// The documentation page of the source at `path`, titled `title`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `# ` and `title` in backquotes; then the source's own
///   documentation after a blank line when it has any; then, for each
///   declaration a form of the source's own writes whose head `pub` precedes,
///   in source order, a blank line, `## ` and its name in backquotes, a blank
///   line, and the block the hover on its name shows in the sugared Unicode
///   form; a final newline. The summary is [`summary`] of the own
///   documentation, empty when it has none.
/// - provides: one page of `gandr doc`.
/// - fails: [`Unpaged`] when the source could not be read, the grammar did not
///   build, the text did not parse, or the session faulted judging it.
/// - panics: none.
///
/// # Errors
/// [`Unpaged`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a source with its own documentation, a documented and an
///   undocumented public definition, a private one and a public theory is
///   asserted at its exact page, each block equal to the hover on its name.
/// - witness: `doc::tests::a_page_holds_each_public_declaration_s_hover`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |page| page.markdown.starts_with("# `") && page.markdown.ends_with('\n')))]
#[inline]
pub fn page(
    path: &Path,
    title: &Path,
) -> Result<Page, Unpaged>
{
    let written =
        std::fs::read_to_string(path).map_err(|error| Unpaged::Unread(error.to_string()))?;
    let text = SourceText::from(written.as_str());
    let grammar = grammar().map_err(|fault| Unpaged::Unbuilt(fault.to_string()))?;
    let root = classify(path);
    let mut session = Session::new(
        grammar.clone(),
        root,
        DiscardingCheckpointStore,
        InMemoryBlockStore::default(),
        BackendArtifact::from(b"gandr doc".as_slice()),
    );
    let laid = lay_out_shadowed(grammar, path, root, text, &Unshadowed);
    let slot = ClosureSlot::new();
    let judged = session
        .judge_unit_reading(
            SourceText::from(laid.text.as_str()),
            &laid.unit,
            laid.base,
            &slot,
            |_tree| {},
        )
        .map(|_submission| ())
        .map_err(|fault| Unpaged::Faulted(fault.to_string()));
    judged?;
    let hovering = hovering_laid(text, path, &session, (&Maybe::Present(laid), None));
    let reading = Reading::of(text);
    let Maybe::Present(declarations) = reading.declarations()
    else {
        return Err(Unpaged::Unparsed);
    };
    let table = hovering.table();
    let own = match table.source_documentation(table.own_source()) {
        Maybe::Present(written) => String::from(written.as_ref()),
        Maybe::Absent(_) => String::new(),
    };
    let index = LineIndex::new(<&str>::from(text).into());
    let quoted = Quoted::new(text, &index, reading.spans());
    let mut markdown = format!("# `{}`\n", title.display());
    if !own.is_empty() {
        markdown.push('\n');
        markdown.push_str(&own);
        markdown.push('\n');
    }
    for declaration in declarations {
        let head = usize::from(declaration.head.start.byte(&index));
        let public = <&str>::from(text)
            .get(.. head)
            .and_then(|before| before.trim_end().strip_suffix("pub"))
            .is_some_and(|before| before.is_empty() || before.ends_with(char::is_whitespace));
        if declaration.written != Written::Form || !public {
            continue;
        }
        let shown = declared(
            &session,
            &hovering,
            declaration,
            declaration.symbol.selection_range,
            &quoted,
            PAGE,
        );
        let _written = write!(
            markdown,
            "\n## `{}`\n\n{}\n",
            declaration.symbol.name, shown.contents.value
        );
    }
    Ok(Page {
        summary: summary(SourceText::from(own.as_str())),
        markdown,
    })
}

/// The first sentence of `documentation`: its first paragraph, its lines
/// joined by spaces, up to and including the first full stop that ends a
/// word.
///
/// # Specification
/// - requires: nothing.
/// - ensures: empty for empty documentation; otherwise a prefix of the first
///   paragraph with its line breaks read as spaces, ending at the first `.`
///   followed by a space or the paragraph's end, or the whole paragraph when no
///   such stop is in it.
/// - provides: the sentence an index names a source by.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a two-sentence paragraph, a sentence over two lines with
///   a dotted name in it, a paragraph without a stop and empty documentation
///   are asserted at their exact sentences.
/// - witness: `doc::tests::a_summary_is_the_first_sentence`
#[spec(ensures: |ret| ret.is_empty() == <&str>::from(documentation).trim().is_empty())]
fn summary(documentation: SourceText<'_>) -> String
{
    let paragraph = <&str>::from(documentation)
        .trim()
        .split("\n\n")
        .next()
        .unwrap_or_default()
        .split('\n')
        .map(str::trim)
        .collect::<Vec<_>>()
        .join(" ");
    let end = paragraph
        .match_indices(". ")
        .next()
        .map_or(paragraph.len(), |(stop, _)| stop.saturating_add(1));
    String::from(paragraph.get(.. end).unwrap_or(&paragraph))
}

/// The index of a package named `package`: its title, then one line per
/// entry linking its page by its source's path, then its summary.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `# ` and `package` in backquotes, a blank line, then for each
///   entry in order `- [`source`](page)`, then ` — ` and its summary when it
///   has one, each on its own line.
/// - provides: the index page of `gandr doc`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a package of a summarised and an unsummarised source is
///   asserted at its exact index.
/// - witness: `doc::tests::an_index_links_each_page_by_its_source`
#[spec(ensures: |ret| ret.starts_with("# `") && ret.lines().count() == entries.len().saturating_add(2))]
#[inline]
#[must_use]
pub fn index(
    package: &Path,
    entries: &[Entry],
) -> String
{
    let mut markdown = format!("# `{}`\n\n", package.display());
    for entry in entries {
        let _written = write!(
            markdown,
            "- [`{}`]({})",
            entry.source.display(),
            entry.page.display()
        );
        if !entry.summary.is_empty() {
            markdown.push_str(" — ");
            markdown.push_str(&entry.summary);
        }
        markdown.push('\n');
    }
    markdown
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_syntax::SourceText;

    use super::Entry;
    use super::index;
    use super::page;
    use super::summary;

    #[test]
    fn a_page_holds_each_public_declaration_s_hover()
    {
        let directory = std::env::temp_dir().join(format!("gandr-doc-page-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let path = directory.join("small.gandr");
        std::fs::write(
            &path,
            "//! A small source, for its page. It says little.\n//!\n//! Its second \
             paragraph.\n\n/// Kept to the source.\ndef hidden = 1 ;\n/// The answer, said \
             once, unlike [hidden].\npub def answer = 42 ;\npub def plain : String ;\n/// A sort, \
             alone.\npub theory Lone where {\n  sort N : Type;\n}\n",
        )
        .expect("the source is written");
        let paged = page(&path, Path::new("small.gandr")).expect("the source has a page");
        let _cleared = std::fs::remove_dir_all(&directory);
        let uri = crate::protocol::DocumentUri::of_path(&path).expect("the path is absolute");
        assert_eq!(paged.summary, "A small source, for its page.");
        assert_eq!(
            paged.markdown,
            format!(
                "# `small.gandr`\n\nA small source, for its page. It says little.\n\nIts second \
                 paragraph.\n\n## `answer`\n\n```gandr\nanswer : Integer\n```\n\nThe answer, said \
                 once, unlike [hidden].\n\n[hidden]: {uri}#L6\n\n## `plain`\n\n```gandr\nplain : \
                 String\n```\n\n## `Lone`\n\n```gandr\ntheory Lone where {{\n  sort N : \
                 Type;\n}}\n```\n\nA sort, alone.\n"
            ),
            "the private `hidden` has no section, each block is the hover's, and a link \
             writes its reference line"
        );
    }

    #[test]
    fn a_summary_is_the_first_sentence()
    {
        let read = |text: &str| summary(SourceText::from(text));
        assert_eq!(read("One. Two."), "One.");
        assert_eq!(
            read("The `std.cost` effect,\nover two lines. Then more."),
            "The `std.cost` effect, over two lines."
        );
        assert_eq!(read("No stop here\n\nA second paragraph."), "No stop here");
        assert_eq!(read(""), "");
    }

    #[test]
    fn an_index_links_each_page_by_its_source()
    {
        let entries = [
            Entry {
                page: PathBuf::from("src/a.md"),
                source: PathBuf::from("src/a.gandr"),
                summary: String::from("The first."),
            },
            Entry {
                page: PathBuf::from("b.md"),
                source: PathBuf::from("b.gandr"),
                summary: String::new(),
            },
        ];
        assert_eq!(
            index(Path::new("std"), &entries),
            "# `std`\n\n- [`src/a.gandr`](src/a.md) — The first.\n- [`b.gandr`](b.md)\n"
        );
    }
}
