//! How a hover writes gandr text: a fenced `gandr` block, or HTML coloured
//! by the highlighter's roles where the client renders it.
//!
//! # A hover is coloured by the roles its tokens are coloured by
//!
//! A client announces, at `initialize`, the HTML tags its markdown renderer
//! keeps (`general.markdown.allowedTags`). When they include `span`, `pre` and
//! `code`, every piece of gandr text a hover shows — the type in its block,
//! the name or the written text before it, the type a term was checked
//! against, a checked fill's text in a proposal's note — is written as
//! `<pre><code>` (or `<code>` inline), each run the highlighter classifies
//! wrapped in `<span style="color:var(--vscode-gandr-hover-<role>);">`, the
//! rest HTML-escaped. The roles are the ones the semantic tokens carry: text
//! read from the document takes the spans its [`crate::reading::Reading`]
//! holds over that range, so a name hovers in the colour it has in the editor;
//! text the printer wrote is parsed in a host declaration (`def h : <type> ;`
//! for a type, `def h = <term> ;` for a term) and takes the spans the same
//! role table gives it there. Text the parser does not read is written
//! escaped and uncoloured. A client that keeps none of those tags reads the
//! fenced `gandr` block the hover always wrote, byte for byte, and colours it
//! with its own grammar for the fence's language, if it has one.
//!
//! The colour is a CSS variable, not a colour: VS Code's sanitizer keeps a
//! `style` attribute that names one of its own theme variables, and an
//! extension contributes the colour behind each (`gandr.hover.<role>`, whose
//! variable is `--vscode-gandr-hover-<role>`) with a default per theme kind.
//!
//! - Alternatives: a `TextMate` grammar generated from the role table, which VS
//!   Code would apply to the fenced block — a second classifier whose regular
//!   expressions approximate the molder and drift from it at every grammar
//!   change; `<span data-token-type>` markup as the protocol's issue 1056
//!   proposes, which no client renders yet.
//! - Reversal: when the protocol specifies semantic markup for hover content,
//!   the server writes that instead and the extension's colours retire.

use alloc::format;
use alloc::string::String;

use anodized::spec;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_syntax::SourceText;

use crate::recheck::grammar;
use crate::recheck::roles;

/// The tags a client's markdown renderer keeps for the server to write HTML.
const TAGS: [&str; 3] = ["span", "pre", "code"];

/// What a hover is written in.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Markup
{
    /// Markdown alone: gandr text in a fenced `gandr` block.
    #[default]
    Markdown,
    /// Markdown with HTML: gandr text in `<pre><code>`, coloured by role.
    Html,
}

impl Markup
{
    /// The markup a client keeping the HTML `tags` reads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Markup::Html`] exactly when `tags` holds each of `span`,
    ///   `pre` and `code`.
    /// - provides: the reading of `general.markdown.allowedTags`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three tags among others, each one missing, and
    ///   none are asserted at their markup.
    /// - witness: `markup::tests::html_needs_every_tag_it_writes`
    #[spec(ensures: |ret| (ret == Self::Html) == TAGS.iter().all(|wanted| tags.iter().any(|tag| tag == wanted)))]
    #[must_use]
    pub fn of(tags: &[String]) -> Self
    {
        if TAGS
            .iter()
            .all(|wanted| tags.iter().any(|tag| tag == wanted))
        {
            Self::Html
        }
        else {
            Self::Markdown
        }
    }

    /// What a block of gandr text opens with.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub const fn opener(self) -> Opener
    {
        Opener(match self {
            Self::Markdown => "```gandr\n",
            Self::Html => "<pre><code>",
        })
    }
}

/// The text a block of gandr text opens with in one markup.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Opener(pub &'static str);

/// Where printed text stands for the highlighter to classify it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Host
{
    /// A type: `def h : <text> ;`.
    Type,
    /// A signature's tail, `: <type>`: `def h <text> ;`.
    Signature,
    /// A term: `def h = <text> ;`.
    Term,
}

impl Host
{
    /// `text` hosted as the declaration this host is, and the offset `text`
    /// starts at inside it.
    ///
    /// # Specification
    /// trivial.
    fn host(
        self,
        text: SourceText<'_>,
    ) -> (String, ByteOffset)
    {
        let (before, after) = match self {
            Self::Type => ("def h : ", " ;"),
            Self::Signature => ("def h ", " ;"),
            Self::Term => ("def h = ", " ;"),
        };
        (
            format!("{before}{}{after}", <&str>::from(text)),
            ByteOffset::from(before.len()),
        )
    }
}

/// The CSS variable suffix a role is coloured by.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Variable(&'static str);

/// The CSS variable suffix of `role`: `gandr.hover.<suffix>` is the colour an
/// extension contributes for it. None for [`HlRole::Other`], which the
/// semantic tokens leave uncoloured too.
///
/// # Specification
/// trivial.
const fn colour(role: HlRole) -> Option<Variable>
{
    Some(Variable(match role {
        HlRole::Keyword => "keyword",
        HlRole::Operator => "operator",
        HlRole::FunctionDef => "functionDef",
        HlRole::FunctionCall => "functionCall",
        HlRole::VariableDef => "variableDef",
        HlRole::VariableParam => "variableParam",
        HlRole::Member => "member",
        HlRole::Variable => "variable",
        HlRole::Constructor => "constructor",
        HlRole::Type => "type",
        HlRole::TypeBuiltin => "typeBuiltin",
        HlRole::TypeVariable => "typeVariable",
        HlRole::Number => "number",
        HlRole::Boolean => "boolean",
        HlRole::Character => "character",
        HlRole::StringLit => "stringLit",
        HlRole::Escape => "escape",
        HlRole::Comment => "comment",
        HlRole::Hole => "hole",
        HlRole::Label => "label",
        HlRole::Path => "path",
        HlRole::Directive => "directive",
        HlRole::Other => return None,
    }))
}

/// A piece of gandr text being written in one markup.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Code
{
    /// The markup it is written in.
    markup: Markup,
    /// What is written so far, escaped and coloured for the markup.
    written: String,
}

impl Code
{
    /// An empty piece of text in `markup`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub const fn new(markup: Markup) -> Self
    {
        Self {
            markup,
            written: String::new(),
        }
    }

    /// Append `text`, the document's text from byte `at`, coloured by the
    /// highlighter `spans` over the document that fall inside it.
    ///
    /// # Specification
    /// - requires: `spans` are sorted and disjoint, as a reading holds them.
    /// - ensures: `text` appended as [`Code::paint`] writes it under the spans
    ///   inside `at .. at + text.len()`, shifted to `text`.
    /// - provides: the document's own colours for the text a hover quotes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — what is written is private, and stating it would
    ///   repeat the painting this call does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hovered name and binder are coloured as the
    ///   editor's tokens colour them.
    /// - witness: `markup::tests::quoted_and_printed_text_take_their_roles`
    pub fn quoted(
        &mut self,
        text: SourceText<'_>,
        at: ByteOffset,
        spans: &[HlSpan],
    )
    {
        let at = usize::from(at);
        let end = at.saturating_add(<&str>::from(text).len());
        let inside = spans.iter().filter_map(|span| {
            let (start, stop) = (
                usize::from(span.range.start()),
                usize::from(span.range.end()),
            );
            (start >= at && stop <= end)
                .then(|| (start.saturating_sub(at), stop.saturating_sub(at), span.role))
        });
        self.paint(text, inside);
    }

    /// Append `text`, which the printer wrote, coloured by the spans the
    /// highlighter gives it standing in `host`.
    ///
    /// # Specification
    /// - requires: nothing; any text is admitted.
    /// - ensures: `text` appended as [`Code::paint`] writes it under the spans
    ///   of the host declaration that fall inside `text`, shifted to it; none
    ///   when the grammar did not build or the host did not parse.
    /// - provides: the colours of printed text, from the same classifier the
    ///   semantic tokens use.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — what is written is private, and stating it would
    ///   parse and highlight the host again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a printed signature is coloured by role, its colon
    ///   uncoloured as the editor leaves it, and the markdown text is the
    ///   printed text itself.
    /// - witness: `markup::tests::quoted_and_printed_text_take_their_roles`
    pub fn printed(
        &mut self,
        text: SourceText<'_>,
        host: Host,
    )
    {
        if self.markup == Markup::Markdown {
            self.written.push_str(text.into());
            return;
        }
        let (hosted, at) = host.host(text);
        let spans = match (grammar(), roles()) {
            (Ok(grammar), Ok(roles)) => parse(grammar, SourceText::from(hosted.as_str()))
                .ok()
                .and_then(|parsed| roles.highlight(&parsed.into_tree()).ok())
                .unwrap_or_default(),
            _ => alloc::vec::Vec::new(),
        };
        self.quoted(text, at, &spans);
    }

    /// Append `text` uncoloured.
    ///
    /// # Specification
    /// trivial.
    pub fn plain(
        &mut self,
        text: SourceText<'_>,
    )
    {
        self.paint(text, core::iter::empty());
    }

    /// Append `text`, each of `runs` — its start, its end and its role, in
    /// `text`'s bytes, sorted — in its role's colour.
    ///
    /// # Specification
    /// - requires: nothing; a run overlapping an earlier one or off a character
    ///   boundary is dropped.
    /// - ensures: in markdown, `text` itself; in HTML, `text` with `&`, `<` and
    ///   `>` escaped, each kept run of a role other than [`HlRole::Other`]
    ///   inside one `span` coloured by its role's variable; an `Other` run is
    ///   uncoloured, as the editor gives it no token.
    /// - provides: the one writer every quoted and printed piece goes through.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — what is written is private; the witnesses read it
    ///   through the block it closes into.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the quoted and printed witnesses.
    /// - witness: `markup::tests::quoted_and_printed_text_take_their_roles`
    /// - witness: `markup::tests::plain_text_is_escaped_and_uncoloured`
    fn paint(
        &mut self,
        text: SourceText<'_>,
        runs: impl Iterator<Item = (usize, usize, HlRole)>,
    )
    {
        let text = <&str>::from(text);
        if self.markup == Markup::Markdown {
            self.written.push_str(text);
            return;
        }
        let mut cursor = 0_usize;
        for (start, end, role) in runs {
            let (Some(before), Some(run), Some(Variable(colour))) = (
                text.get(cursor .. start),
                text.get(start .. end),
                colour(role),
            )
            else {
                continue;
            };
            escape(&mut self.written, SourceText::from(before));
            self.written
                .push_str("<span style=\"color:var(--vscode-gandr-hover-");
            self.written.push_str(colour);
            self.written.push_str(");\">");
            escape(&mut self.written, SourceText::from(run));
            self.written.push_str("</span>");
            cursor = end;
        }
        escape(
            &mut self.written,
            SourceText::from(text.get(cursor ..).unwrap_or_default()),
        );
    }

    /// The text as a block: a fenced `gandr` block, or `<pre><code>`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn block(self) -> String
    {
        match self.markup {
            Markup::Markdown => format!("```gandr\n{}\n```", self.written),
            Markup::Html => format!("<pre><code>{}</code></pre>", self.written),
        }
    }

    /// The text inline in a paragraph: between backticks, or in `<code>`
    /// with the markdown's own punctuation escaped too, so the paragraph
    /// around it reads none of it as emphasis or a link.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn inline(self) -> String
    {
        match self.markup {
            Markup::Markdown => format!("`{}`", self.written),
            Markup::Html => {
                let mut inline = String::from("<code>");
                let mut tag = false;
                for character in self.written.chars() {
                    match character {
                        '<' => {
                            tag = true;
                            inline.push(character);
                        },
                        '>' => {
                            tag = false;
                            inline.push(character);
                        },
                        _ if tag => inline.push(character),
                        '*' => inline.push_str("&#42;"),
                        '_' => inline.push_str("&#95;"),
                        '`' => inline.push_str("&#96;"),
                        '\\' => inline.push_str("&#92;"),
                        '[' => inline.push_str("&#91;"),
                        ']' => inline.push_str("&#93;"),
                        '~' => inline.push_str("&#126;"),
                        '|' => inline.push_str("&#124;"),
                        '!' => inline.push_str("&#33;"),
                        _ => inline.push(character),
                    }
                }
                inline.push_str("</code>");
                inline
            },
        }
    }
}

/// Push `text` onto `out` with `&`, `<` and `>` escaped.
///
/// # Specification
/// trivial.
fn escape(
    out: &mut String,
    text: SourceText<'_>,
)
{
    for character in <&str>::from(text).chars() {
        match character {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            _ => out.push(character),
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::ByteRange;
    use gandr_surface_render_remote::HlRole;
    use gandr_surface_render_remote::HlSpan;
    use gandr_surface_syntax::SourceText;

    use super::Code;
    use super::Host;
    use super::Markup;

    #[test]
    fn html_needs_every_tag_it_writes()
    {
        let tags = |names: &[&str]| {
            names
                .iter()
                .map(|&name| String::from(name))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            Markup::of(&tags(&["p", "span", "pre", "code", "a"])),
            Markup::Html
        );
        for missing in ["span", "pre", "code"] {
            let kept: Vec<&str> = ["span", "pre", "code"]
                .into_iter()
                .filter(|&tag| tag != missing)
                .collect();
            assert_eq!(
                Markup::of(&tags(&kept)),
                Markup::Markdown,
                "without `{missing}` the hover stays markdown"
            );
        }
        assert_eq!(Markup::of(&[]), Markup::Markdown);
    }

    #[test]
    fn quoted_and_printed_text_take_their_roles()
    {
        let span = |start: usize, end: usize, role| HlSpan {
            range: ByteRange::new(start.into(), end.into()).expect("an ordered range"),
            role,
        };
        let mut code = Code::new(Markup::Html);
        code.quoted(SourceText::from("x"), ByteOffset::from(10_usize), &[
            span(4, 7, HlRole::Keyword),
            span(10, 11, HlRole::VariableParam),
        ]);
        code.printed(SourceText::from(" : Integer"), Host::Signature);
        assert_eq!(
            code.block(),
            "<pre><code><span style=\"color:var(--vscode-gandr-hover-variableParam);\">x</span> : \
             <span style=\"color:var(--vscode-gandr-hover-typeBuiltin);\">Integer</span></code></pre>"
        );
        let mut markdown = Code::new(Markup::Markdown);
        markdown.quoted(SourceText::from("x"), ByteOffset::from(10_usize), &[span(
            10,
            11,
            HlRole::VariableParam,
        )]);
        markdown.printed(SourceText::from(" : Integer"), Host::Signature);
        assert_eq!(markdown.block(), "```gandr\nx : Integer\n```");
    }

    #[test]
    fn plain_text_is_escaped_and_uncoloured()
    {
        let mut code = Code::new(Markup::Html);
        code.plain(SourceText::from("<a & b>"));
        assert_eq!(code.block(), "<pre><code>&lt;a &amp; b&gt;</code></pre>");
        let mut inline = Code::new(Markup::Html);
        inline.plain(SourceText::from("a * b_c"));
        assert_eq!(inline.inline(), "<code>a &#42; b&#95;c</code>");
    }
}
