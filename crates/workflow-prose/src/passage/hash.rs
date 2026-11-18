//! The `#` comments of a task, a script, a workflow, a manifest, and a list
//! or a configuration that a tool reads.
//!
//! A `#` comment is prose, and it meets the rules of every comment. The reader
//! cuts each run of whole-line `#` comments into paragraphs, as
//! [`super::comments`] cuts a run of `//` lines. A paragraph ends at a blank
//! comment line, at a line of code and at each line that the reader leaves
//! out.
//!
//! # Boundaries
//!
//! The reader names each line that it leaves out by its marks, never by a
//! guess:
//!
//! - a shebang on the first line;
//! - a directive that a tool reads: `# shellcheck`, `# vim:`, `#
//!   yaml-language-server:`, the `#:` line of a TOML tool, such as `#:schema`,
//!   and a Dockerfile's `# syntax=`, `# escape=` and `# check=`;
//! - the body of a heredoc, whose lines are data of the script;
//! - a list item and a footer line `[label]: target`, as in a gandr comment;
//! - an indented line, which a table, a synopsis or a list item's continuation
//!   lays out by hand;
//! - a table row, which opens with `|`;
//! - a line of two or more `#` marks, which heads a section or rules it off;
//! - commented-out code: a line whose first token is the file's own syntax, in
//!   a form that [`Syntax`] names. The reader counts these lines.
//!
//! A TOML string, a YAML block and a Dockerfile's `RUN` hold scripts too. So
//! the reader reads their heredocs and their commented-out shell lines as it
//! reads a script's.
//!
//! A comment after code on the same line stays unread. Only the language's
//! own lexer finds where such a comment starts. The tree holds about 190 words
//! of them, all in YAML.

use super::Line;
use super::Paragraph;
use super::Passage;
use super::Source;
use super::Text;
use super::footer_label;

/// The syntax that a file of `#` comments is written in.
///
/// # Specification
/// - provides: the files that [`comments`] reads, and the forms of
///   commented-out code that it leaves out of each.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Syntax
{
    /// TOML: a manifest, a task file or the configuration of a tool.
    Toml,
    /// A shell script: bash or POSIX `sh`.
    Shell,
    /// YAML: a workflow or the configuration of a tool.
    Yaml,
    /// A jq program.
    Jq,
    /// A Python script.
    Python,
    /// An awk program.
    Awk,
    /// A Dockerfile: the build of an image.
    Docker,
    /// A list or a configuration that a tool reads, one entry to a line, with
    /// no code form of its own.
    Plain,
}

/// Whether a file of a syntax holds shell scripts.
///
/// # Specification
/// - provides: the files whose heredocs and commented-out shell lines the
///   reader reads as a script's.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Embeds
{
    /// A shell script, or a file whose TOML strings, YAML blocks or `RUN`
    /// instructions hold one.
    Shell,
    /// No script.
    Nothing,
}

/// What the reader makes of one comment line's text.
///
/// # Specification
/// - provides: the three ways that a comment line feeds or ends a paragraph.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kept
{
    /// Prose, which the open paragraph takes.
    Prose,
    /// A line that holds no prose by its marks, which ends the paragraph.
    Out,
    /// Commented-out code, which ends the paragraph and counts.
    Code,
}

impl Syntax
{
    /// The syntax of the file at `path`, whose first line `first` reads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: by the name, Docker for `Dockerfile` and `*.Dockerfile`; by
    ///   the extension, TOML for `.toml`, a shell for `.bash` and `.sh`, YAML
    ///   for `.yml` and `.yaml`, jq for `.jq`, Python for `.py`, awk for
    ///   `.awk`, and plain for `.txt` and `.tsv`. A file with no extension
    ///   takes the syntax of its shebang: a shell for `bash`, `sh` or `dash`,
    ///   Python for `python` and awk for an awk, directly or through `env`.
    ///   With no shebang, it is plain. Every other file has none, as has a file
    ///   with no extension that `first` cannot read. Only a file with no
    ///   extension calls `first`.
    /// - provides: the files whose `#` comments the check reads.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the match is the clause.
    ///
    /// # Cost
    /// - allocation: the first line that `first` reads for a file with no
    ///   extension, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each name and extension, a dotfile with an extension,
    ///   a script with a bash, an `sh`, a Python and an awk shebang, a script
    ///   of another interpreter, a dotfile with no shebang and a markdown file;
    ///   a file with an extension that calls `first`, or a missed shebang,
    ///   changes the syntax.
    /// - witness: `passage::hash::tests::a_file_takes_its_syntax_by_its_extension_or_its_shebang`
    #[inline]
    #[must_use]
    pub fn of<First>(
        path: Text<'_>,
        first: First,
    ) -> Option<Self>
    where
        First: FnOnce() -> Option<String>,
    {
        let name = path.0.rsplit('/').next().unwrap_or(path.0);
        if name == "Dockerfile" {
            return Some(Self::Docker);
        }
        match name.rsplit_once('.') {
            Some((stem, extension)) if !stem.is_empty() => match extension {
                "toml" => Some(Self::Toml),
                "bash" | "sh" => Some(Self::Shell),
                "yml" | "yaml" => Some(Self::Yaml),
                "jq" => Some(Self::Jq),
                "py" => Some(Self::Python),
                "awk" => Some(Self::Awk),
                "Dockerfile" => Some(Self::Docker),
                "txt" | "tsv" => Some(Self::Plain),
                _ => None,
            },
            _ => {
                let line = first()?;
                if line.starts_with("#!") {
                    Self::of_shebang(Text(&line))
                }
                else {
                    Some(Self::Plain)
                }
            },
        }
    }

    /// The syntax that the shebang `line` names, if it is one.
    ///
    /// # Specification
    /// trivial.
    fn of_shebang(line: Text<'_>) -> Option<Self>
    {
        let mut words = line.0.strip_prefix("#!")?.split_whitespace();
        let mut program = words.next()?.rsplit('/').next()?;
        if program == "env" {
            program = words.find(|word| !word.starts_with('-'))?;
        }
        match program {
            "bash" | "sh" | "dash" => Some(Self::Shell),
            _ if program.starts_with("python") => Some(Self::Python),
            _ if program.ends_with("awk") => Some(Self::Awk),
            _ => None,
        }
    }

    /// Whether a file of this syntax holds shell scripts.
    ///
    /// # Specification
    /// trivial.
    const fn embeds(self) -> Embeds
    {
        match self {
            Self::Shell | Self::Toml | Self::Yaml | Self::Docker => Embeds::Shell,
            Self::Jq | Self::Python | Self::Awk | Self::Plain => Embeds::Nothing,
        }
    }

    /// Whether the comment text `text` opens with a form of this syntax, so
    /// that the line is commented-out code.
    ///
    /// # Specification
    /// - requires: `text` is a comment line's text, its marker, the space after
    ///   it and the trailing space removed.
    /// - ensures: [`Kept::Code`] for a form that [`shell()`] names in a file
    ///   that holds shell scripts; for a form that [`toml()`] names in a TOML
    ///   file, that [`yaml()`] names in a YAML file, that [`jq()`] names in a
    ///   jq program, that [`python()`] names in a Python script, that [`awk()`]
    ///   names in an awk program and that [`docker()`] names in a Dockerfile;
    ///   [`Kept::Prose`] for any other text, and for every text of a plain
    ///   file.
    /// - provides: the one test that sets commented-out code apart from prose.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the forms are the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each form of each syntax beside a prose line that
    ///   opens with the same word; a prose line read as code, or a form read as
    ///   prose, changes the passages and the count.
    /// - witness: `passage::hash::tests::commented_out_code_is_counted_and_prose_beside_it_is_read`
    fn code(
        self,
        text: Text<'_>,
    ) -> Kept
    {
        let own = match self {
            Self::Shell | Self::Plain => Kept::Prose,
            Self::Toml => toml(text),
            Self::Yaml => yaml(text),
            Self::Jq => jq(text),
            Self::Python => python(text),
            Self::Awk => awk(text),
            Self::Docker => docker(text),
        };
        match (own, self.embeds()) {
            (Kept::Prose, Embeds::Shell) => shell(text),
            _ => own,
        }
    }
}

/// The prose paragraphs of one file, and the count of its lines of
/// commented-out code.
///
/// # Specification
/// - provides: what a reader takes from one file: [`comments`] for `#`
///   comments, and the markdown reader with no code lines.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Paragraphs
{
    /// The prose paragraphs, each one passage.
    pub passages: Vec<Passage>,
    /// The lines of commented-out code that the reader leaves out.
    pub code: usize,
}

/// The names that open a directive which a tool reads, after `# `: a name
/// that ends in `:` or `=` opens the first word, and any other name is the
/// whole first word, with a `key=value` word after it.
const DIRECTIVES: [&str; 6] = [
    "shellcheck",
    "vim:",
    "yaml-language-server:",
    "syntax=",
    "escape=",
    "check=",
];

/// The `#` comment paragraphs of `text`, the file at `path`, written in
/// `syntax`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one passage per paragraph of consecutive whole-line `#` comments,
///   a paragraph ending at a blank comment line, a line that is not a comment
///   and each line that the module's list leaves out; each passage starts on
///   its first line; `code` counts the lines of commented-out code that a form
///   of [`Syntax`] names.
/// - provides: the `#` comments that the sentence rules read under the base.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Cost
/// - allocation: the passages, growth within the file's comments
///
/// # Adequacy
/// - hypothesis: L3 — a run of paragraphs that blank lines and code split, and
///   one hand-written source for each skip, each beside a prose line that the
///   reader keeps; a skip read as prose, or a prose line left out, changes the
///   passages.
/// - witness: `passage::hash::tests::a_comment_run_splits_at_its_blank_lines_and_its_code`
/// - witness: `passage::hash::tests::a_shebang_and_a_directive_hold_no_prose`
/// - witness: `passage::hash::tests::a_heredoc_s_body_is_data_of_the_script`
/// - witness: `passage::hash::tests::a_list_a_table_an_indented_line_and_a_heading_hold_no_prose`
/// - witness: `passage::hash::tests::commented_out_code_is_counted_and_prose_beside_it_is_read`
/// - witness: `passage::hash::tests::a_comment_after_code_stays_unread`
#[inline]
#[must_use]
pub fn comments(
    path: Text<'_>,
    text: Text<'_>,
    syntax: Syntax,
) -> Paragraphs
{
    let mut paragraph = Paragraph::new(path, Source::Hash);
    let mut code: usize = 0;
    let mut heredoc: Option<Text<'_>> = None;
    for (index, raw) in text.0.lines().enumerate() {
        let line = raw.trim();
        if let Some(word) = heredoc {
            if line == word.0 {
                heredoc = None;
            }
            paragraph.close();
            continue;
        }
        let Some(comment) = line.strip_prefix('#')
        else {
            paragraph.close();
            if syntax.embeds() == Embeds::Shell {
                heredoc = opened(Text(line));
            }
            continue;
        };
        let shebang = index == 0 && comment.starts_with('!');
        let marked = comment.starts_with([':', '#']);
        let comment = comment.strip_prefix(' ').unwrap_or(comment);
        let indented = comment.starts_with([' ', '\t']);
        let kept = if shebang || marked || indented {
            Kept::Out
        }
        else {
            match held_out(Text(comment)) {
                Kept::Prose => syntax.code(Text(comment)),
                out @ (Kept::Out | Kept::Code) => out,
            }
        };
        match kept {
            Kept::Prose => paragraph.push(Line(index.saturating_add(1)), Text(comment)),
            Kept::Out => paragraph.close(),
            Kept::Code => {
                paragraph.close();
                code = code.saturating_add(1);
            },
        }
    }
    paragraph.close();
    Paragraphs {
        passages: paragraph.passages,
        code,
    }
}

/// Whether the comment text `text`, its marker and one space removed, holds
/// no prose by its marks: a blank, a list item, a table row, a footer line or
/// a directive.
///
/// # Specification
/// trivial.
fn held_out(text: Text<'_>) -> Kept
{
    let text = text.0;
    let mut words = text.split_whitespace();
    let first = words.next().unwrap_or_default();
    let keyed = words.next().is_some_and(|word| word.contains('='));
    let numbered = first.strip_suffix('.').is_some_and(|number| {
        !number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())
    });
    let directive = DIRECTIVES.into_iter().any(|name| {
        if name.ends_with([':', '=']) {
            first.starts_with(name)
        }
        else {
            first == name && keyed
        }
    });
    let out = text.is_empty()
        || text == "-"
        || text.starts_with("- ")
        || text.starts_with("* ")
        || text.starts_with('|')
        || numbered
        || footer_label(Text(text)).is_some()
        || directive;
    if out { Kept::Out } else { Kept::Prose }
}

/// The word that ends the heredoc which the code line `line` opens, if it
/// opens one: `<<WORD`, `<<-WORD`, `<<'WORD'` or `<<"WORD"`, never the
/// here-string `<<<`.
///
/// # Specification
/// trivial.
fn opened(line: Text<'_>) -> Option<Text<'_>>
{
    let mut rest = line.0;
    while let Some((_, after)) = rest.split_once("<<") {
        if let Some(string) = after.strip_prefix('<') {
            rest = string;
            continue;
        }
        let after = after.strip_prefix('-').unwrap_or(after).trim_start();
        let (quote, word) = after
            .strip_prefix(['\'', '"'])
            .map_or((None, after), |quoted| (after.chars().next(), quoted));
        let end = word
            .find(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
            .unwrap_or(word.len());
        let (name, tail) = word.split_at_checked(end)?;
        let closed = quote.is_none_or(|quote| tail.starts_with(quote));
        if closed
            && name
                .starts_with(|character: char| character.is_ascii_alphabetic() || character == '_')
        {
            return Some(Text(name));
        }
        rest = word;
    }
    None
}

/// The name `name`, if it is a shell variable's name: a letter or `_`, then
/// letters, digits and `_`.
///
/// # Specification
/// trivial.
fn variable(name: Text<'_>) -> Option<Text<'_>>
{
    let valid = name
        .0
        .starts_with(|character: char| character.is_ascii_alphabetic() || character == '_')
        && name
            .0
            .chars()
            .all(|character| character.is_ascii_alphanumeric() || character == '_');
    valid.then_some(name)
}

/// Whether `text` opens with a shell form: an assignment to a quoted, an
/// expanded, a numeric or an empty value; an expansion, a test or an
/// arithmetic form; a word, a brace or a parenthesis that stands alone and
/// closes or opens a block; a conditional or a loop that ends where its body
/// opens, and a `case` head of three words; or a function's head.
///
/// # Specification
/// trivial.
fn shell(text: Text<'_>) -> Kept
{
    let text = text.0;
    let alone = [
        "fi", "done", "esac", "then", "do", "else", "{", "}", "(", ")",
    ];
    let first = text.split_whitespace().next().unwrap_or_default();
    let assigned = first.split_once('=').is_some_and(|(name, value)| {
        variable(Text(name)).is_some()
            && value.chars().next().is_none_or(|start| {
                matches!(start, '"' | '\'' | '$' | '(') || start.is_ascii_digit()
            })
    });
    let conditional = matches!(first, "if" | "elif" | "while" | "until" | "for")
        && (text.ends_with("; then") || text.ends_with("; do"));
    let cased =
        first == "case" && text.ends_with(" in") && text.split_whitespace().take(4).count() == 3;
    let code = alone.contains(&text)
        || ["$(", "${", "[[ ", "(( "]
            .into_iter()
            .any(|form| text.starts_with(form))
        || assigned
        || conditional
        || cased
        || text.ends_with("() {");
    if code { Kept::Code } else { Kept::Prose }
}

/// Whether `text` opens with a TOML form: a table's header alone, or a key
/// set to a literal value.
///
/// # Specification
/// trivial.
fn toml(text: Text<'_>) -> Kept
{
    let text = text.0;
    let keyed = |key: &str| {
        !key.is_empty()
            && key.chars().all(|character| {
                character.is_ascii_alphanumeric() || matches!(character, '_' | '-' | '.' | '"')
            })
    };
    let header = |inner: &str| {
        let inner = inner
            .strip_prefix('[')
            .and_then(|rest| rest.strip_suffix(']'))
            .unwrap_or(inner);
        keyed(inner)
    };
    let assignment = || {
        text.split_once('=').is_some_and(|(key, value)| {
            let value = value.trim_start();
            let numeric = value
                .strip_prefix(['-', '+'])
                .unwrap_or(value)
                .starts_with(|start: char| start.is_ascii_digit());
            let word = ["true", "false", "inf", "nan"].into_iter().any(|word| {
                value
                    .strip_prefix(word)
                    .is_some_and(|rest| rest.is_empty() || rest.starts_with([' ', ',']))
            });
            keyed(key.trim()) && (value.starts_with(['"', '\'', '[', '{']) || numeric || word)
        })
    };
    let code = text
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
        .map_or_else(assignment, header);
    if code { Kept::Code } else { Kept::Prose }
}

/// Whether `text` opens with a YAML form: a lower-case key alone, or a
/// lower-case key with one word for its value.
///
/// # Specification
/// trivial.
fn yaml(text: Text<'_>) -> Kept
{
    let code = text.0.split_once(':').is_some_and(|(key, value)| {
        let keyed = key.starts_with(|start: char| start.is_ascii_lowercase())
            && key.chars().all(|character| {
                character.is_ascii_alphanumeric() || matches!(character, '_' | '-')
            });
        let valued = value.is_empty()
            || (value.starts_with(' ') && value.split_whitespace().take(2).count() == 1);
        keyed && valued
    });
    if code { Kept::Code } else { Kept::Prose }
}

/// Whether `text` opens with a jq form: a definition's head, whose name ends
/// with `:` or opens its parameters, or a path that a pipe or an index
/// follows or that stands alone.
///
/// # Specification
/// trivial.
fn jq(text: Text<'_>) -> Kept
{
    let text = text.0;
    let defined = text
        .strip_prefix("def ")
        .and_then(|rest| rest.split_whitespace().next())
        .is_some_and(|name| {
            name.starts_with(|start: char| start.is_ascii_alphabetic() || start == '_')
                && (name.ends_with(':') || name.contains('('))
        });
    let path = text.strip_prefix('.').is_some_and(|rest| {
        let end = rest
            .find(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
            .unwrap_or(rest.len());
        rest.split_at_checked(end).is_some_and(|(name, tail)| {
            variable(Text(name)).is_some()
                && (tail.is_empty() || tail.starts_with(" |") || tail.starts_with('['))
        })
    });
    if defined || path {
        Kept::Code
    }
    else {
        Kept::Prose
    }
}

/// Whether `text` opens with a Python form: a function's or a class's head,
/// or an import.
///
/// # Specification
/// trivial.
fn python(text: Text<'_>) -> Kept
{
    let text = text.0;
    let mut words = text.split_whitespace();
    let code = match words.next() {
        Some("def" | "class") => words.next().is_some_and(|name| {
            name.starts_with(|start: char| start.is_ascii_alphabetic() || start == '_')
                && (name.contains('(') || name.ends_with(':'))
        }),
        Some("import") => words.next().is_some() && words.next().is_none(),
        Some("from") => text.contains(" import "),
        _ => false,
    };
    if code { Kept::Code } else { Kept::Prose }
}

/// Whether `text` opens with an awk form: a `BEGIN` or an `END` block, a
/// function's head, a pattern that opens its action, a brace alone, or a
/// print of a field or a string.
///
/// # Specification
/// trivial.
fn awk(text: Text<'_>) -> Kept
{
    let text = text.0;
    let mut words = text.split_whitespace();
    let first = words.next().unwrap_or_default();
    let second = words.next();
    let keyword = matches!(first, "BEGIN" | "END" | "BEGINFILE" | "ENDFILE")
        && second.is_none_or(|word| word == "{");
    let block = keyword
        || ["BEGIN{", "END{"]
            .into_iter()
            .any(|form| first.starts_with(form));
    let function = first == "function" && second.is_some_and(|name| name.contains('('));
    let pattern = text.starts_with(['/', '$', '!', '(']) && text.ends_with('{');
    let printed = matches!(first, "print" | "printf")
        && second.is_none_or(|word| word.starts_with(['$', '"']));
    let code = block || function || pattern || printed || text == "{" || text == "}";
    if code { Kept::Code } else { Kept::Prose }
}

/// The instructions of a Dockerfile.
const INSTRUCTIONS: [&str; 18] = [
    "ADD",
    "ARG",
    "CMD",
    "COPY",
    "ENTRYPOINT",
    "ENV",
    "EXPOSE",
    "FROM",
    "HEALTHCHECK",
    "LABEL",
    "MAINTAINER",
    "ONBUILD",
    "RUN",
    "SHELL",
    "STOPSIGNAL",
    "USER",
    "VOLUME",
    "WORKDIR",
];

/// Whether `text` opens with a Dockerfile form: an instruction's keyword in
/// capitals, then its arguments.
///
/// # Specification
/// trivial.
fn docker(text: Text<'_>) -> Kept
{
    let code = text
        .0
        .split_once(' ')
        .is_some_and(|(first, _)| INSTRUCTIONS.contains(&first));
    if code { Kept::Code } else { Kept::Prose }
}

#[cfg(test)]
mod tests
{
    use super::Line;
    use super::Syntax;
    use super::Text;
    use super::comments;
    use crate::passage::Source;

    /// The passages that the reader takes from a text, each by its line, and
    /// the count of its code lines.
    #[derive(Debug, Eq, PartialEq)]
    struct Taken
    {
        /// Each passage's first line and text.
        passages: Vec<(Line, String)>,
        /// The lines of commented-out code.
        code: usize,
    }

    /// What the reader takes from `text` in `syntax`, each passage checked as
    /// a `#` comment of its file.
    ///
    /// # Specification
    /// trivial.
    fn read(
        text: Text<'_>,
        syntax: Syntax,
    ) -> Taken
    {
        let read = comments(Text("a/file"), text, syntax);
        assert!(
            read.passages
                .iter()
                .all(|passage| passage.source == Source::Hash && passage.path == "a/file"),
            "each passage is a `#` comment of its file"
        );
        Taken {
            passages: read
                .passages
                .iter()
                .map(|passage| (passage.line, passage.text.clone()))
                .collect(),
            code: read.code,
        }
    }

    /// The passages `expected` names, owned.
    ///
    /// # Specification
    /// trivial.
    fn pairs(expected: &[(Line, Text<'_>)]) -> Vec<(Line, String)>
    {
        expected
            .iter()
            .map(|&(line, text)| (line, text.0.to_owned()))
            .collect()
    }

    #[test]
    fn a_file_takes_its_syntax_by_its_extension_or_its_shebang()
    {
        let unread = || -> Option<String> { panic!("a file with an extension reads no line") };
        for (path, syntax) in [
            ("Cargo.toml", Syntax::Toml),
            (".config/a.bash", Syntax::Shell),
            ("a/b.sh", Syntax::Shell),
            (".github/workflows/a.yml", Syntax::Yaml),
            (".coderabbit.yaml", Syntax::Yaml),
            ("a/b.jq", Syntax::Jq),
            ("a/parse.py", Syntax::Python),
            (".config/coverage/merge.awk", Syntax::Awk),
            (".github/docker/ci.Dockerfile", Syntax::Docker),
            ("a/Dockerfile", Syntax::Docker),
            (".config/dead-weight/kept.txt", Syntax::Plain),
            ("a/owed.tsv", Syntax::Plain),
        ] {
            assert_eq!(Syntax::of(Text(path), unread), Some(syntax), "{path}");
        }
        for path in ["README.md", "a/b.json", "a/c.rs"] {
            assert_eq!(
                Syntax::of(Text(path), unread),
                None,
                "{path} holds no `#` comments"
            );
        }
        for (first, syntax) in [
            ("#!/usr/bin/env bash", Some(Syntax::Shell)),
            ("#!/bin/sh", Some(Syntax::Shell)),
            ("#!/usr/bin/env -S python3 -u", Some(Syntax::Python)),
            ("#!/usr/bin/awk -f", Some(Syntax::Awk)),
            ("#!/usr/bin/env node", None),
            ("# The names of a home directory.", Some(Syntax::Plain)),
        ] {
            assert_eq!(
                Syntax::of(Text(".config/local-paths/placeholders"), || Some(
                    first.to_owned()
                )),
                syntax,
                "{first}"
            );
        }
        assert_eq!(
            Syntax::of(Text(".gitignore"), || Some("/target".to_owned())),
            Some(Syntax::Plain),
            "a dotfile with no extension and no shebang is plain"
        );
        assert_eq!(
            Syntax::of(Text("a/unreadable"), || None),
            None,
            "a file with no extension that cannot be read has no syntax"
        );
    }

    #[test]
    fn a_comment_run_splits_at_its_blank_lines_and_its_code()
    {
        let text = "set -e\n# The first paragraph\n#   \n# The second paragraph\n    # wraps \
                    here, indented with its code.\n#\n# The third.\nexit 0 # after code\n# Last.\n";
        assert_eq!(read(Text(text), Syntax::Shell), Taken {
            passages: pairs(&[
                (Line(2), Text("The first paragraph")),
                (
                    Line(4),
                    Text("The second paragraph wraps here, indented with its code.")
                ),
                (Line(7), Text("The third.")),
                (Line(9), Text("Last.")),
            ]),
            code: 0,
        });
    }

    #[test]
    fn a_shebang_and_a_directive_hold_no_prose()
    {
        let text = "#!/usr/bin/env bash\n# shellcheck disable=SC2034\n# vim: set ft=sh\n# \
                    yaml-language-server: $schema=x.json\n#:schema https://x/schema.json\n# The \
                    script reads its base.\n";
        assert_eq!(read(Text(text), Syntax::Shell), Taken {
            passages: pairs(&[(Line(6), Text("The script reads its base."))]),
            code: 0,
        });
        let named = "# shellcheck reads each script.\n# Run shellcheck over the scripts.\n# The \
                     vim editor reads a modeline.\n";
        assert_eq!(
            read(Text(named), Syntax::Shell).passages,
            pairs(&[(
                Line(1),
                Text(
                    "shellcheck reads each script. Run shellcheck over the scripts. The vim \
                     editor reads a modeline."
                )
            )]),
            "a directive's name opens a directive only as the first word, and `shellcheck` only \
             with a `key=value` word after it"
        );
    }

    #[test]
    fn a_heredoc_s_body_is_data_of_the_script()
    {
        let text = "cat <<'EOF' > a.md\n# A heading of the page\nEOF\n# The prose after it.\ncat \
                    <<-END\n\t# Data too.\n\tEND\nwc -l <<< \"$x\"\n# A here-string opens no \
                    heredoc.\n";
        assert_eq!(
            read(Text(text), Syntax::Shell).passages,
            pairs(&[
                (Line(4), Text("The prose after it.")),
                (Line(9), Text("A here-string opens no heredoc.")),
            ])
        );
        let task = "run = '''\ncat <<EOF\n# Data of the task's script.\nEOF\n# A comment of the \
                    task's script.\n'''\n";
        assert_eq!(
            read(Text(task), Syntax::Toml).passages,
            pairs(&[(Line(5), Text("A comment of the task's script."))]),
            "a TOML string holds a script"
        );
        let shift = "x = 1 << y\n# A shift opens no heredoc.\ny\n";
        assert_eq!(
            read(Text(shift), Syntax::Python).passages,
            pairs(&[(Line(2), Text("A shift opens no heredoc."))]),
            "a Python shift opens no heredoc"
        );
    }

    #[test]
    fn a_list_a_table_an_indented_line_and_a_heading_hold_no_prose()
    {
        let text = "# The lead.\n# - an item\n#   continued\n# 1. numbered\n# * starred\n# | a \
                    | b |\n#   tool --flag   a synopsis\n## A heading\n#####\n# [label]: \
                    https://x \"Title\"\n# The close.\n";
        assert_eq!(read(Text(text), Syntax::Toml), Taken {
            passages: pairs(&[(Line(1), Text("The lead.")), (Line(11), Text("The close."))]),
            code: 0,
        });
    }

    #[test]
    fn commented_out_code_is_counted_and_prose_beside_it_is_read()
    {
        for (syntax, code, prose) in [
            (
                Syntax::Shell,
                "if [[ -z $x ]]; then",
                "if the base is empty, then the run stops.",
            ),
            (
                Syntax::Shell,
                "base=$(git merge-base a b)",
                "BASE=<rev> names the base.",
            ),
            (Syntax::Shell, "done", "done when the queue empties."),
            (
                Syntax::Shell,
                "${#names[@]}",
                "then the next run reads the cache.",
            ),
            (
                Syntax::Shell,
                "case $x in",
                "case by case, the run reads in.",
            ),
            (Syntax::Shell, "case \"$1\" in", "case in"),
            (
                Syntax::Shell,
                "main() {",
                "while any obligation stays open.",
            ),
            (
                Syntax::Toml,
                "fn_args_layout = \"Vertical\"",
                "warn = add a table of contents.",
            ),
            (Syntax::Toml, "[profile.release]", "[a] stands in prose."),
            (Syntax::Toml, "jobs = 4", "jobs = the count of workers."),
            (
                Syntax::Toml,
                "x=\"$y\"",
                "GANDR_NIGHT=<day> replays another night.",
            ),
            (
                Syntax::Yaml,
                "runs-on: ubuntu-latest",
                "base: the runner rebases it.",
            ),
            (Syntax::Yaml, "steps:", "Usage: run it."),
            (
                Syntax::Jq,
                "def rows: .[];",
                "def is the word for a definition.",
            ),
            (
                Syntax::Jq,
                ".changed | length",
                ".config/x holds the paths.",
            ),
            (
                Syntax::Python,
                "def main(argv):",
                "def and class open a definition.",
            ),
            (
                Syntax::Python,
                "import json",
                "import the parse from the cache.",
            ),
            (
                Syntax::Python,
                "from x import y",
                "from the cache, the run reads the parse.",
            ),
            (
                Syntax::Awk,
                "BEGIN { FS = \"\\t\" }",
                "BEGIN and END frame the program.",
            ),
            (Syntax::Awk, "/^## / {", "/ opens a pattern."),
            (Syntax::Awk, "print $1, $2", "print the fields in order."),
            (
                Syntax::Docker,
                "RUN apt-get update",
                "Run the build in a cache.",
            ),
            (
                Syntax::Docker,
                "x=\"$y\"",
                "From the base image, the build runs.",
            ),
        ] {
            let text = format!("# {code}\n# {prose}\n");
            assert_eq!(
                read(Text(&text), syntax),
                Taken {
                    passages: pairs(&[(Line(2), Text(prose))]),
                    code: 1,
                },
                "{syntax:?}: `{code}` is code and `{prose}` is prose"
            );
        }
        assert_eq!(
            read(
                Text("# jobs = 4\n# The list holds no code.\n"),
                Syntax::Plain
            ),
            Taken {
                passages: pairs(&[(Line(1), Text("jobs = 4 The list holds no code."))]),
                code: 0,
            },
            "a plain file holds no code form"
        );
    }

    #[test]
    fn a_comment_after_code_stays_unread()
    {
        let text = "steps:\n  - run: make # builds the tree\n# The steps run in order.\n";
        assert_eq!(read(Text(text), Syntax::Yaml), Taken {
            passages: pairs(&[(Line(3), Text("The steps run in order."))]),
            code: 0,
        });
    }
}
