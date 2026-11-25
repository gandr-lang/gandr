//! A package's documentation as a static HTML site: an index, a page per
//! source and per public item, an index of every item, a source view and a
//! search over the items.
//!
//! # The site is the hover, rendered
//!
//! [`site`] takes each source as [`crate::doc::read`] reads it for the site,
//! so the block on an item's page is the hover on its name, written as
//! [`Markup::Site`] writes it: each run in the class of its role, which
//! `gandr.css` colours. The documentation prose is `CommonMark`, which
//! `pulldown-cmark` renders. The hover's HTML passes through it unchanged, and
//! a fenced `gandr` block in the prose takes the colours a backquoted fragment
//! takes: its roles when it lexes and parses clean, and the code style alone
//! otherwise. The source view writes the whole source under the editor's
//! spans, beside a column of line numbers that an item page links to.
//!
//! Every file is static, so a reader opens `index.html` from disk with no
//! server. The search is a script over `search.js`, which lists each item's
//! name, kind, page and summary. The script and the stylesheet are strings in
//! the binary, written beside the pages. Each page is written into its own
//! contents, so no page is built twice.
//!
//! - Alternatives: a renderer of its own for the prose, which would restate the
//!   many edge cases of `CommonMark`; `comrak`, larger and with two cross-site
//!   scripting advisories of 2021; a search on a server, which a site read from
//!   disk cannot reach.
//! - Reversal: a high-risk advisory against `pulldown-cmark` outside an option
//!   the site keeps off, or an unmaintained mark, moves the prose to another
//!   `CommonMark` renderer.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_syntax::SourceText;
use pulldown_cmark::CodeBlockKind;
use pulldown_cmark::Event;
use pulldown_cmark::Options;
use pulldown_cmark::Parser;
use pulldown_cmark::Tag;
use pulldown_cmark::TagEnd;

use crate::doc::Kind;
use crate::doc::Source;
use crate::doc::Unpaged;
use crate::doc::read;
use crate::fragment::coloured;
use crate::markup::Code;
use crate::markup::Markup;
use crate::markup::escape;

/// The site's stylesheet.
const STYLE: &str = include_str!("site/gandr.css");

/// The site's search script.
const SEARCH: &str = include_str!("site/gandr-search.js");

/// The directory the source view is written under.
const VIEW: &str = "source";

/// One source of a package, read for the site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sourced
{
    /// The source's path relative to the package.
    path: PathBuf,
    /// What the source reads, each hover in [`Markup::Site`].
    read: Source,
}

/// The source at `path`, read for the site under the name `relative`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the source as [`read`] reads it in [`Markup::Site`], at
///   `relative`.
/// - provides: one source of [`site`].
/// - fails: [`Unpaged`], as [`read`] fails.
/// - panics: none.
/// - executable: none — the source is read from disk, which the witness writes
///   and reads back through the site.
///
/// # Errors
/// [`Unpaged`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`site`].
/// - witness: `site::tests::a_site_writes_each_page_the_search_and_the_source_view`
#[inline]
pub fn sourced(
    path: &Path,
    relative: PathBuf,
) -> Result<Sourced, Unpaged>
{
    Ok(Sourced {
        path: relative,
        read: read(path, Markup::Site)?,
    })
}

/// One file of the site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct File
{
    /// Its path relative to the site's directory.
    pub path: PathBuf,
    /// Its contents.
    pub contents: String,
}

/// One item of the package, where the site writes it.
struct Placed<'site>
{
    /// The item's name.
    name: &'site str,
    /// What it declares.
    kind: Kind,
    /// The first sentence of its documentation.
    summary: &'site str,
    /// The path of its page.
    page: PathBuf,
    /// The source it is declared in.
    source: &'site Path,
}

/// The site of the package named `package` over `sources`.
///
/// # Specification
/// - requires: each source's items read in [`Markup::Site`].
/// - ensures: for each source at `<path>.gandr`, in order, `<path>.html`, its
///   page; then `<path>/<item>.html` for each item, its page, where `<item>` is
///   the item's name with each character outside letters, digits, `.`, `-` and
///   `_` read as `_`, and a second item of the same name in the source taking
///   `-2`, a third `-3`; then `source/<path>.html`, its view. Then
///   `index.html`, `all.html`, `search.js`, `gandr.css` and `gandr-search.js`.
///   Every page links the stylesheet and the scripts by a path relative to it.
/// - provides: every file `gandr doc` writes for a site.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a package of a documented source with an item with a
///   fenced block in its documentation, nested two directories down, and a
///   source with two public items of one name, is asserted at its paths, its
///   links, its search index and its coloured blocks; a wrong relative path, a
///   lost item or an unescaped name changes them.
/// - witness: `site::tests::a_site_writes_each_page_the_search_and_the_source_view`
#[spec(ensures: |ret| ret.len() == sources.iter().map(|sourced| sourced.read.items.len().saturating_add(2)).sum::<usize>().saturating_add(5))]
#[inline]
#[must_use]
pub fn site(
    package: &Path,
    sources: &[Sourced],
) -> Vec<File>
{
    let package = package.to_string_lossy();
    let package = SourceText::from(package.as_ref());
    let mut files = Vec::new();
    let mut placed = Vec::new();
    let mut rows = String::new();
    let mut name = String::new();
    let mut counts: BTreeMap<String, u32> = BTreeMap::new();
    for sourced in sources {
        let title = sourced.path.to_string_lossy();
        let title = SourceText::from(title.as_ref());
        let page = sourced.path.with_extension("html");
        let view = Path::new(VIEW).join(&page);
        let first = files.len();
        rows.clear();
        counts.clear();
        for item in &sourced.read.items {
            name.clear();
            slug(&mut name, SourceText::from(item.name.as_str()));
            let count = counts.get_mut(name.as_str()).map_or(1, |seen| {
                *seen = seen.saturating_add(1);
                *seen
            });
            if count == 1 {
                counts.insert(name.clone(), 1);
            }
            else {
                let _written = write!(name, "-{count}");
            }
            name.push_str(".html");
            let at = sourced.path.with_extension("").join(&name);
            rows.push_str("<tr><td class=\"kind\">");
            rows.push_str(item.kind.0);
            rows.push_str("</td><td><a href=\"");
            link(&mut rows, &page, &at);
            rows.push_str("\"><code>");
            escape(&mut rows, SourceText::from(item.name.as_str()));
            rows.push_str("</code></a></td><td>");
            inline(&mut rows, SourceText::from(item.summary.as_str()));
            rows.push_str("</td></tr>\n");
            let mut contents = String::new();
            open(
                &mut contents,
                package,
                SourceText::from(item.name.as_str()),
                &at,
            );
            let _written = write!(
                contents,
                "<h1><span class=\"kind\">{}</span> <code>",
                item.kind.0
            );
            escape(&mut contents, SourceText::from(item.name.as_str()));
            contents.push_str("</code></h1>\n<p class=\"where\">In <a href=\"");
            link(&mut contents, &at, &page);
            contents.push_str("\"><code>");
            escape(&mut contents, title);
            contents.push_str("</code></a> · <a href=\"");
            link(&mut contents, &at, &view);
            let _written = writeln!(contents, "#L{}\">source</a></p>", item.line.0);
            render(&mut contents, SourceText::from(item.shown.as_str()));
            close(&mut contents, &at);
            placed.push(Placed {
                name: &item.name,
                kind: item.kind,
                summary: &item.summary,
                page: at.clone(),
                source: &sourced.path,
            });
            files.push(File { path: at, contents });
        }
        let mut contents = String::new();
        open(&mut contents, package, title, &page);
        contents.push_str("<h1><code>");
        escape(&mut contents, title);
        contents.push_str("</code></h1>\n<p class=\"where\"><a href=\"");
        link(&mut contents, &page, &view);
        contents.push_str("\">source</a></p>\n");
        render(&mut contents, SourceText::from(sourced.read.own.as_str()));
        if !rows.is_empty() {
            contents.push_str("<h2>Items</h2>\n<table class=\"items\">\n");
            contents.push_str(&rows);
            contents.push_str("</table>\n");
        }
        close(&mut contents, &page);
        files.insert(first, File {
            path: page,
            contents,
        });
        let mut contents = String::new();
        open(&mut contents, package, title, &view);
        contents.push_str("<h1><code>");
        escape(&mut contents, title);
        contents.push_str("</code></h1>\n");
        source_view(&mut contents, &sourced.read);
        close(&mut contents, &view);
        files.push(File {
            path: view,
            contents,
        });
    }
    let index = Path::new("index.html");
    let mut contents = String::new();
    open(&mut contents, package, package, index);
    contents.push_str("<h1><code>");
    escape(&mut contents, package);
    contents.push_str(
        "</code></h1>\n<p><a href=\"all.html\">All items</a></p>\n<table class=\"items\">\n",
    );
    for sourced in sources {
        contents.push_str("<tr><td><a href=\"");
        link(&mut contents, index, &sourced.path.with_extension("html"));
        contents.push_str("\"><code>");
        escape(
            &mut contents,
            SourceText::from(sourced.path.to_string_lossy().as_ref()),
        );
        contents.push_str("</code></a></td><td>");
        inline(
            &mut contents,
            SourceText::from(sourced.read.summary.as_str()),
        );
        contents.push_str("</td></tr>\n");
    }
    contents.push_str("</table>\n");
    close(&mut contents, index);
    files.push(File {
        path: index.to_path_buf(),
        contents,
    });
    placed.sort_by(|left, right| {
        left.name
            .to_lowercase()
            .cmp(&right.name.to_lowercase())
            .then_with(|| left.name.cmp(right.name))
    });
    let all = Path::new("all.html");
    let mut contents = String::new();
    let mut search = String::from("window.gandrItems = [");
    open(&mut contents, package, SourceText::from("All items"), all);
    contents.push_str("<h1>All items</h1>\n<table class=\"items\">\n");
    for (at, item) in placed.iter().enumerate() {
        let page = item.page.to_string_lossy();
        let _written = write!(
            contents,
            "<tr><td class=\"kind\">{}</td><td><a href=\"",
            item.kind.0
        );
        link(&mut contents, all, &item.page);
        contents.push_str("\"><code>");
        escape(&mut contents, SourceText::from(item.name));
        contents.push_str("</code></a></td><td><a href=\"");
        link(&mut contents, all, &item.source.with_extension("html"));
        contents.push_str("\"><code>");
        escape(
            &mut contents,
            SourceText::from(item.source.to_string_lossy().as_ref()),
        );
        contents.push_str("</code></a></td></tr>\n");
        if at > 0 {
            search.push(',');
        }
        search.push('[');
        for (field, text) in [item.name, item.kind.0, page.as_ref(), item.summary]
            .into_iter()
            .enumerate()
        {
            if field > 0 {
                search.push(',');
            }
            json(&mut search, SourceText::from(text));
        }
        search.push(']');
    }
    contents.push_str("</table>\n");
    close(&mut contents, all);
    files.push(File {
        path: all.to_path_buf(),
        contents,
    });
    search.push_str("];\n");
    files.push(File {
        path: PathBuf::from("search.js"),
        contents: search,
    });
    files.push(File {
        path: PathBuf::from("gandr.css"),
        contents: String::from(STYLE),
    });
    files.push(File {
        path: PathBuf::from("gandr-search.js"),
        contents: String::from(SEARCH),
    });
    files
}

/// Append `text` to `out` as a JSON string: in double quotes, with `"`, `\`
/// and each control character escaped.
///
/// # Specification
/// trivial.
fn json(
    out: &mut String,
    text: SourceText<'_>,
)
{
    out.push('"');
    for character in <&str>::from(text).chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            control if u32::from(control) < 0x20 => {
                let _written = write!(out, "\\u{:04x}", u32::from(control));
            },
            _ => out.push(character),
        }
    }
    out.push('"');
}

/// Append `name` as a file name to `out`: each character outside letters,
/// digits, `.`, `-` and `_` read as `_`.
///
/// # Specification
/// trivial.
fn slug(
    out: &mut String,
    name: SourceText<'_>,
)
{
    out.extend(<&str>::from(name).chars().map(|character| {
        if character.is_alphanumeric() || matches!(character, '.' | '-' | '_') {
            character
        }
        else {
            '_'
        }
    }));
}

/// Append to `out` the path of `to` relative to the directory of `from`, both
/// relative to the site's directory, with `/` between its components.
///
/// # Specification
/// trivial.
fn link(
    out: &mut String,
    from: &Path,
    to: &Path,
)
{
    root(out, from);
    for (at, part) in to.components().enumerate() {
        if at > 0 {
            out.push('/');
        }
        out.push_str(&part.as_os_str().to_string_lossy());
    }
}

/// Append to `out` the path from the directory of `page` back to the site's
/// directory: one `../` for each directory above `page`.
///
/// # Specification
/// trivial.
fn root(
    out: &mut String,
    page: &Path,
)
{
    for _ in 1 .. page.components().count() {
        out.push_str("../");
    }
}

/// Append to `out` the opening of the page titled `title` of the package named
/// `package`, written at `page`: the stylesheet, then a header of the package's
/// index, the item index and the search.
///
/// # Specification
/// trivial.
fn open(
    out: &mut String,
    package: SourceText<'_>,
    title: SourceText<'_>,
    page: &Path,
)
{
    out.push_str("<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>");
    escape(out, title);
    out.push_str(" — ");
    escape(out, package);
    out.push_str("</title>\n<link rel=\"stylesheet\" href=\"");
    root(out, page);
    out.push_str("gandr.css\">\n</head>\n<body data-root=\"");
    root(out, page);
    out.push_str("\">\n<header>\n<a class=\"package\" href=\"");
    root(out, page);
    out.push_str("index.html\">");
    escape(out, package);
    out.push_str("</a>\n<a href=\"");
    root(out, page);
    out.push_str("all.html\">All items</a>\n<input id=\"search\" type=\"search\" placeholder=\"Search the items\" autocomplete=\"off\">\n<ul id=\"results\"></ul>\n</header>\n<main>\n");
}

/// Append to `out` the close of the page written at `page`: the scripts.
///
/// # Specification
/// trivial.
fn close(
    out: &mut String,
    page: &Path,
)
{
    out.push_str("</main>\n<script src=\"");
    root(out, page);
    out.push_str("search.js\"></script>\n<script src=\"");
    root(out, page);
    out.push_str("gandr-search.js\"></script>\n</body>\n</html>\n");
}

/// Append `markdown` to `out` as HTML: `CommonMark` with tables and
/// strikethrough, its HTML kept, and each fenced `gandr` block written as a
/// coloured block.
///
/// # Specification
/// - requires: nothing; any text is admitted.
/// - ensures: the HTML that `pulldown-cmark` writes for `markdown`, but for
///   each fenced block whose info string is `gandr`, which is `<pre><code>`
///   with its text under the roles [`coloured`] gives it, or uncoloured when it
///   gives none.
/// - provides: the prose of every page.
/// - fails: never.
/// - panics: none.
/// - executable: none — the HTML is the renderer's, and stating it would render
///   the text again.
///
/// # Adequacy
/// - hypothesis: L3 — as the site's witness, whose documentation holds a fenced
///   `gandr` block and a paragraph.
/// - witness: `site::tests::a_site_writes_each_page_the_search_and_the_source_view`
fn render(
    out: &mut String,
    markdown: SourceText<'_>,
)
{
    let mut fenced: Option<String> = None;
    let events = Parser::new_ext(
        markdown.into(),
        Options::ENABLE_TABLES | Options::ENABLE_STRIKETHROUGH,
    )
    .filter_map(|event| match (fenced.as_mut(), event) {
        (None, Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(ref language))))
            if language.as_ref() == "gandr" =>
        {
            fenced = Some(String::new());
            None
        },
        (Some(text), Event::Text(ref more)) => {
            text.push_str(more);
            None
        },
        (Some(_), Event::End(TagEnd::CodeBlock)) => {
            let text = fenced.take().unwrap_or_default();
            let mut code = Code::new(Markup::Site);
            let spans = coloured(SourceText::from(text.as_str())).unwrap_or_default();
            code.quoted(
                SourceText::from(text.as_str()),
                ByteOffset::from(0_usize),
                &spans,
            );
            let mut block = code.block();
            block.push('\n');
            Some(Event::Html(block.into()))
        },
        (Some(_), _) => None,
        (None, event) => Some(event),
    });
    pulldown_cmark::html::push_html(out, events);
}

/// Append `markdown`, one paragraph, to `out` as inline HTML: [`render`]
/// without the paragraph's tags.
///
/// # Specification
/// trivial.
fn inline(
    out: &mut String,
    markdown: SourceText<'_>,
)
{
    let start = out.len();
    render(out, markdown);
    let rendered = out.get(start ..).unwrap_or_default().trim_end();
    let (cut, length) = rendered
        .strip_prefix("<p>")
        .and_then(|inner| inner.strip_suffix("</p>"))
        .map_or((0, rendered.len()), |inner| (3, inner.len()));
    out.replace_range(start .. start.saturating_add(cut), "");
    out.truncate(start.saturating_add(length));
}

/// Append to `out` the source view of `read`: a column of line numbers, each
/// an anchor `L<n>`, beside the whole text under the editor's spans.
///
/// # Specification
/// trivial.
fn source_view(
    out: &mut String,
    read: &Source,
)
{
    out.push_str("<div class=\"view\">\n<pre class=\"lines\">");
    for line in 1 ..= read.text.lines().count().max(1) {
        let _written = writeln!(out, "<a id=\"L{line}\" href=\"#L{line}\">{line}</a>");
    }
    out.push_str("</pre>\n");
    let mut code = Code::new(Markup::Site);
    code.quoted(
        SourceText::from(read.text.as_str()),
        ByteOffset::from(0_usize),
        &read.spans,
    );
    out.push_str(&code.block());
    out.push_str("\n</div>\n");
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use super::Sourced;
    use super::site;
    use super::sourced;
    use crate::doc::Item;
    use crate::doc::Kind;
    use crate::doc::Lineno;
    use crate::doc::Source;

    #[test]
    fn a_site_writes_each_page_the_search_and_the_source_view()
    {
        let directory = std::env::temp_dir().join(format!("gandr-doc-site-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let path = directory.join("a.gandr");
        std::fs::write(
            &path,
            "//! The source `a`. It says little.\n\n/// The answer, said once.\n///\n/// \
             ```gandr\n/// answer\n/// ```\npub def answer = 42 ;\ndef hidden = 1 ;\n",
        )
        .expect("the source is written");
        let read = sourced(&path, PathBuf::from("src/a.gandr")).expect("the source is read");
        let _cleared = std::fs::remove_dir_all(&directory);
        let twice = |line: u32| Item {
            name: String::from("x<y"),
            kind: Kind("function"),
            line: Lineno(line),
            shown: String::from("<pre><code>x</code></pre>"),
            summary: String::from("Takes `x` & more."),
        };
        let made = Sourced {
            path: PathBuf::from("b.gandr"),
            read: Source {
                own: String::new(),
                summary: String::new(),
                items: Vec::from([twice(1), twice(2)]),
                text: String::from(include_str!(
                    "site/unformatted/a-site-writes-each-page-the-search-and-the-source-view-made.gandr"
                )),
                spans: Vec::new(),
            },
        };
        let files = site(Path::new("pkg"), &[read, made]);
        assert_eq!(
            files
                .iter()
                .map(|file| file.path.to_string_lossy().into_owned())
                .collect::<Vec<_>>(),
            [
                "src/a.html",
                "src/a/answer.html",
                "source/src/a.html",
                "b.html",
                "b/x_y.html",
                "b/x_y-2.html",
                "source/b.html",
                "index.html",
                "all.html",
                "search.js",
                "gandr.css",
                "gandr-search.js",
            ],
            "each source writes its page, its items in order, a second name taking `-2`, then its view"
        );
        let file = |path: &str| {
            files
                .iter()
                .find(|file| file.path == Path::new(path))
                .map(|file| file.contents.as_str())
                .expect("the file is written")
        };
        let answer = file("src/a/answer.html");
        assert!(
            answer.contains("<link rel=\"stylesheet\" href=\"../../gandr.css\">")
                && answer.contains("<a href=\"../../source/src/a.html#L8\">source</a>")
                && answer.contains("<a href=\"../../src/a.html\"><code>src/a.gandr</code></a>"),
            "an item page two directories down links back by `../../`: {answer}"
        );
        assert!(
            answer.contains(
                "<pre><code><span class=\"hl-functionDef\">answer</span> : <span \
                 class=\"hl-typeBuiltin\">Integer</span></code></pre>"
            ),
            "the item's block is the hover in the site's classes: {answer}"
        );
        assert!(
            answer.contains("<p>The answer, said once.</p>\n<pre><code><span class=\"hl-"),
            "the fenced `gandr` block in the documentation is coloured: {answer}"
        );
        let page = file("src/a.html");
        assert!(
            page.contains("<p>The source <code>")
                && page.contains(
                    "<td class=\"kind\">function</td><td><a \
                     href=\"../src/a/answer.html\"><code>answer</code></a></td><td>The answer, \
                     said once.</td>"
                )
                && !page.contains("hidden"),
            "a source page renders its own documentation and lists its public items: {page}"
        );
        assert!(
            file("b/x_y.html").contains("<code>x&lt;y</code>")
                && file("b.html").contains("<td>Takes <code>x</code> &amp; more.</td>"),
            "a name and a summary are escaped"
        );
        let view = file("source/b.html");
        assert!(
            view.contains(
                "<a id=\"L1\" href=\"#L1\">1</a>\n<a id=\"L2\" href=\"#L2\">2</a>\n</pre>"
            ) && view.contains("<pre><code>one\ntwo\n</code></pre>"),
            "the view numbers each line beside the text: {view}"
        );
        assert_eq!(
            file("search.js"),
            "window.gandrItems = [[\"answer\",\"function\",\"src/a/answer.html\",\"The answer, said \
             once.\"],[\"x<y\",\"function\",\"b/x_y.html\",\"Takes `x` & \
             more.\"],[\"x<y\",\"function\",\"b/x_y-2.html\",\"Takes `x` & more.\"]];\n",
            "the search lists every item by name, its kind, its page and its summary"
        );
        let all = file("all.html");
        assert!(
            all.find("answer") < all.find("x&lt;y"),
            "the item index is in name order"
        );
    }
}
