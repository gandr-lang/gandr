//! The citations of one source: the key lines of its References section, the
//! DOI and arXiv locators of its documentation, and the lines refused.
//!
//! A crate source is `crates/<crate>/README.md` or
//! `crates/<crate>/src/<module>.rs`. A corpus source is
//! `corpus/<subject>/<name>.gandr`. A module is the path of its source under
//! `src/`: `lib.rs` and `main.rs` are the root, written as the empty string,
//! and `a/b.rs` and `a/b/mod.rs` are `a::b`.
//!
//! The documentation of a module source is its `//!` and `///` lines. A
//! block ends where a line of another kind starts. The documentation of a
//! README is each line outside a code fence. A corpus source has no key
//! lines: its citations are the locators of its comments, a line at a time.
//!
//! A References section runs from its heading to the next heading: `#` in a
//! module, `##` in a README, and never in a `///` block. An entry runs from
//! its `- ` line through the indented lines under it. A key line is
//! ``- `<key>` — <role>: <what it decides>``. The formatter can wrap a key
//! line after the key, after the dash or after the role, and the indented
//! line under it holds the rest.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// The dash between the key of a key line and its role.
const DASH: &str = " — ";

/// The roles of a key line.
const ROLES: [&str; 6] = [
    "newest",
    "dependency",
    "anchor",
    "exemplar",
    "lineage",
    "background",
];

/// The count of the ASCII digits at the start of `bytes`.
///
/// # Specification
/// trivial.
fn digits(bytes: &[u8]) -> usize
{
    bytes
        .iter()
        .take_while(|byte| byte.is_ascii_digit())
        .count()
}

/// The length of the DOI at the start of `bytes`, with the punctuation after
/// it: `10.`, four digits or more, `/`, and each byte up to a bracket, a
/// space, `<`, `>`, a backtick, a quote, a brace or `|`.
///
/// # Specification
/// - ensures: the length of the longest such DOI, or none.
/// - panics: none.
fn doi_at(bytes: &[u8]) -> Option<usize>
{
    let rest = bytes.strip_prefix(b"10.")?;
    let count = digits(rest);
    if count < 4 {
        return None;
    }
    let rest = rest.get(count ..)?.strip_prefix(b"/")?;
    let tail = rest
        .iter()
        .take_while(|byte| !byte.is_ascii_whitespace() && !b"[]<>`\"{}|".contains(byte))
        .count();
    (tail > 0).then_some(bytes.len().saturating_sub(rest.len()).saturating_add(tail))
}

/// The identifier and the length of the arXiv locator at the start of
/// `bytes`, in lower case: `arxiv`, then `.org/abs/`, `.org/pdf/`, `:` and
/// any space, or a space; then `YYMM.NNNN` with a fifth digit, or an archive
/// with its subject class and `/YYMMNNN`.
///
/// # Specification
/// - ensures: the identifier and the length of the locator, or none.
/// - panics: none.
fn arxiv_at(bytes: &[u8]) -> Option<(&[u8], usize)>
{
    let rest = bytes.strip_prefix(b"arxiv")?;
    let rest = if let Some(rest) = rest
        .strip_prefix(b".org/abs/")
        .or_else(|| rest.strip_prefix(b".org/pdf/"))
    {
        rest
    }
    else if let Some(rest) = rest.strip_prefix(b":") {
        rest.get(
            rest.iter()
                .take_while(|byte| byte.is_ascii_whitespace())
                .count() ..,
        )?
    }
    else {
        let spaces = rest
            .iter()
            .take_while(|byte| byte.is_ascii_whitespace())
            .count();
        if spaces == 0 {
            return None;
        }
        rest.get(spaces ..)?
    };
    let length = if digits(rest) >= 4 && rest.get(4) == Some(&b'.') {
        let after = digits(rest.get(5 ..)?);
        (after >= 4).then_some(after.min(5).saturating_add(5))?
    }
    else {
        let archive = rest
            .iter()
            .take_while(|byte| byte.is_ascii_lowercase() || **byte == b'-')
            .count();
        if archive == 0 {
            return None;
        }
        let mut at = archive;
        if rest.get(at) == Some(&b'.')
            && rest
                .get(at.saturating_add(1) .. at.saturating_add(3))
                .is_some_and(|class| class.iter().all(u8::is_ascii_lowercase))
        {
            at = at.saturating_add(3);
        }
        if rest.get(at) != Some(&b'/') || digits(rest.get(at.saturating_add(1) ..)?) < 7 {
            return None;
        }
        at.saturating_add(8)
    };
    let identifier = rest.get(.. length)?;
    Some((
        identifier,
        bytes
            .len()
            .saturating_sub(rest.len())
            .saturating_add(length),
    ))
}

/// Whether `key` is `vault:` and a lower-case uuid of version seven.
///
/// # Specification
/// trivial.
fn vault_key(key: &str) -> bool
{
    let Some(uuid) = key.strip_prefix("vault:")
    else {
        return false;
    };
    let bytes = uuid.as_bytes();
    let hex = |byte: &u8| byte.is_ascii_digit() || (b'a' ..= b'f').contains(byte);
    bytes.len() == 36
        && bytes.iter().enumerate().all(|(at, byte)| match at {
            8 | 13 | 18 | 23 => *byte == b'-',
            14 => *byte == b'7',
            19 => b"89ab".contains(byte),
            _ => hex(byte),
        })
}

/// What a [`Citation`] is.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Kind
{
    /// A key line of the References section of a module.
    Cite,
    /// A key line of the `## References` section of a README.
    Mirror,
    /// A locator in the documentation of a crate, outside a key line.
    Locator,
    /// A module source read.
    File,
    /// A locator in a comment of a corpus source.
    Corpus,
    /// A line refused; the reason is the key.
    Refused,
}

impl Kind
{
    /// The name of the kind, as the first column of a line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(self) -> &'static str
    {
        match self {
            Self::Cite => "cite",
            Self::Mirror => "mirror",
            Self::Locator => "locator",
            Self::File => "file",
            Self::Corpus => "corpus",
            Self::Refused => "refused",
        }
    }
}

/// One citation of a source, or one line refused.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Citation
{
    /// What the citation is.
    pub kind: Kind,
    /// The key or the locator; the reason of a refused line.
    pub key: String,
    /// The crate, or `corpus` for a corpus source.
    pub krate: String,
    /// The module, or the path of a corpus source under `corpus/`.
    pub module: String,
    /// The role of a key line, `background` for a locator, else empty.
    pub role: String,
    /// The path and the line, `<path>:<line>`; the path alone for a file.
    pub location: String,
}

impl Citation
{
    /// The site of the citation: `<crate>::<module>`, the crate alone at its
    /// root, or `corpus/<path>` for a corpus source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn site(&self) -> String
    {
        if self.kind == Kind::Corpus {
            format!("corpus/{}", self.module)
        }
        else if self.module.is_empty() {
            self.krate.clone()
        }
        else {
            format!("{}::{}", self.krate, self.module)
        }
    }
}

impl fmt::Display for Citation
{
    /// The citation as one tab-separated line: kind, key, crate, module, role
    /// and location.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{}\t{}\t{}\t{}\t{}\t{}",
            self.kind.name(),
            self.key,
            self.krate,
            self.module,
            self.role,
            self.location
        )
    }
}

/// The part of a key line that waits for the indented line under it.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Entry
{
    /// No entry of a References section.
    None,
    /// An entry with no key line: its locators are read.
    Legacy,
    /// A key line, whole: its lines give no locator.
    Key,
    /// A key alone; the dash and the role are on the next line.
    Bare(String),
    /// A key and the dash; the role is on the next line.
    Dashed(String),
    /// A key, the dash and the role; what it decides is on the next line.
    Roled(String, String),
}

/// The reader of one source.
struct Reader<'path>
{
    /// The path of the source.
    path: &'path str,
    /// The crate.
    krate: String,
    /// The module.
    module: String,
    /// Whether the source is a README.
    readme: bool,
    /// The citations read so far.
    out: Vec<Citation>,
}

impl Reader<'_>
{
    /// Adds a citation of `kind` at `line`.
    ///
    /// # Specification
    /// trivial.
    fn emit(
        &mut self,
        kind: Kind,
        key: String,
        role: &str,
        line: usize,
    )
    {
        self.out.push(Citation {
            kind,
            key,
            krate: self.krate.clone(),
            module: self.module.clone(),
            role: String::from(role),
            location: format!("{}:{line}", self.path),
        });
    }

    /// Adds each locator of `text`, once each: the DOIs, then the arXiv
    /// identifiers.
    ///
    /// # Specification
    /// - ensures: a DOI less the punctuation that ends a sentence and a closing
    ///   parenthesis it does not open, in lower case, as `doi:<doi>`; an arXiv
    ///   DOI and an arXiv identifier as `arXiv:<identifier>` with no version.
    /// - panics: none.
    fn locators(
        &mut self,
        text: &str,
        kind: Kind,
        line: usize,
    )
    {
        let mut seen = BTreeSet::new();
        let mut keys = Vec::new();
        let bytes = text.as_bytes();
        let mut at = 0;
        while let Some(rest) = bytes.get(at ..).filter(|rest| !rest.is_empty()) {
            match doi_at(rest) {
                Some(length) => {
                    let found = text.get(at .. at.saturating_add(length)).unwrap_or("");
                    let doi = trim_doi(found).to_ascii_lowercase();
                    keys.push(doi.strip_prefix("10.48550/arxiv.").map_or_else(
                        || format!("doi:{doi}"),
                        |identifier| format!("arXiv:{}", without_version(identifier)),
                    ));
                    at = at.saturating_add(length);
                },
                None => at = at.saturating_add(1),
            }
        }
        let lower = text.to_ascii_lowercase();
        let bytes = lower.as_bytes();
        let mut at = 0;
        while let Some(rest) = bytes.get(at ..).filter(|rest| !rest.is_empty()) {
            match arxiv_at(rest) {
                Some((identifier, length)) => {
                    keys.push(format!("arXiv:{}", String::from_utf8_lossy(identifier)));
                    at = at.saturating_add(length);
                },
                None => at = at.saturating_add(1),
            }
        }
        for key in keys {
            if seen.insert(key.clone()) {
                self.emit(kind, key, "background", line);
            }
        }
    }

    /// Adds the key line of `key`, `said` the text after its dash.
    ///
    /// # Specification
    /// - ensures: a refused line when the key is refused, when a dependency
    ///   names no section, or when the text after the dash has no role and no
    ///   text after the role; else a key line with its role.
    /// - panics: none.
    fn cited(
        &mut self,
        key: &str,
        said: &str,
        line: usize,
    )
    {
        if let Some(why) = refusal(key) {
            self.emit(Kind::Refused, String::from(why), "", line);
        }
        else if said.starts_with("dependency: ") && !said.contains('§') {
            self.emit(
                Kind::Refused,
                format!(
                    "a dependency names the section the site implements: - `{key}`{DASH}dependency: <what it decides>, § <section>"
                ),
                "",
                line,
            );
        }
        else if let Some(role) = role_of(said) {
            let kind = if self.readme {
                Kind::Mirror
            }
            else {
                Kind::Cite
            };
            self.emit(kind, String::from(key), role, line);
        }
        else {
            self.emit(
                Kind::Refused,
                format!(
                    "a References line gives its key a role and what it decides: - `{key}`{DASH}<newest|dependency|anchor|exemplar>: <what it decides>"
                ),
                "",
                line,
            );
        }
    }
}

/// The role that `said` opens with, when a word follows the role.
///
/// # Specification
/// - ensures: the role of [`ROLES`] that `said` opens with, then `: ` and a
///   character that is no whitespace.
/// - panics: none.
fn role_of(said: &str) -> Option<&'static str>
{
    ROLES.into_iter().find(|role| {
        said.strip_prefix(role)
            .and_then(|rest| rest.strip_prefix(": "))
            .and_then(|rest| rest.chars().next())
            .is_some_and(|first| !first.is_whitespace())
    })
}

/// A DOI as matched, less the punctuation that ends a sentence and a closing
/// parenthesis it does not open.
///
/// # Specification
/// - ensures: `doi` less each last `.`, `,`, `:` or `;`, and each last `)`
///   while the text has more `)` than `(`.
/// - panics: none.
fn trim_doi(mut doi: &str) -> &str
{
    loop {
        if let Some(shorter) = doi.strip_suffix(['.', ',', ':', ';']) {
            doi = shorter;
        }
        else if doi.ends_with(')') && doi.matches('(').count() < doi.matches(')').count() {
            doi = doi.get(.. doi.len().saturating_sub(1)).unwrap_or(doi);
        }
        else {
            return doi;
        }
    }
}

/// An arXiv identifier without its version, `v` and digits at its end.
///
/// # Specification
/// trivial.
fn without_version(identifier: &str) -> &str
{
    let digits = identifier.trim_end_matches(|character: char| character.is_ascii_digit());
    match digits.strip_suffix('v') {
        Some(stem) if digits.len() < identifier.len() => stem,
        Some(_) | None => identifier,
    }
}

/// Why a key line's key is refused.
///
/// # Specification
/// - ensures: a reason for a vault key that is no lower-case uuid of version
///   seven, for a locator, and for a key with whitespace; none else.
/// - panics: none.
fn refusal(key: &str) -> Option<&'static str>
{
    if key.starts_with("vault:") {
        return (!vault_key(key))
            .then_some("a vault key is `vault:` and the page's `mint:` uuid, in lower case");
    }
    let lower = key.to_ascii_lowercase();
    if ["doi:", "arxiv:", "isbn:", "hal:", "http:", "https:", "10."]
        .iter()
        .any(|prefix| lower.starts_with(prefix))
    {
        return Some(
            "a key is the library's citation key or `vault:<uuid>`, never a locator: the locator belongs in the README's entry",
        );
    }
    key.contains(char::is_whitespace)
        .then_some("a key holds no whitespace")
}

/// The crate, the module and whether it is a README, of the crate source
/// `path`.
///
/// # Specification
/// trivial.
fn site_of(path: &str) -> (String, String, bool)
{
    let rest = path.strip_prefix("crates/").unwrap_or(path);
    let (krate, rest) = rest.split_once('/').unwrap_or((rest, ""));
    if rest == "README.md" {
        return (String::from(krate), String::new(), true);
    }
    let module = rest.strip_prefix("src/").unwrap_or(rest);
    let module = module.strip_suffix(".rs").unwrap_or(module);
    let module = if module == "lib" || module == "main" {
        ""
    }
    else {
        module
    };
    let module = module.strip_suffix("/mod").unwrap_or(module);
    (String::from(krate), module.replace('/', "::"), false)
}

/// The leading whitespace of `text` and the rest, when there is whitespace.
///
/// # Specification
/// trivial.
fn indented(text: &str) -> Option<&str>
{
    let rest = text.trim_start();
    (rest.len() < text.len()).then_some(rest)
}

/// The citations of the source `path` with the text `text`.
///
/// # Specification
/// - requires: `path` is `crates/<crate>/README.md`,
///   `crates/<crate>/src/<module>.rs` or `corpus/<path>.gandr`.
/// - ensures: a module source's `file` line first; then each key line, each
///   locator and each refused line in the order of the text, each at its line,
///   from one.
/// - panics: none.
///
/// # Cost
/// - allocation: the citations and a set of the keys of a line, setup
///
/// # Adequacy
/// - hypothesis: L3 — the cases of `.config/references/cases.json` give their
///   recorded lines: the three wrappings of a key line, a refused key, a
///   dependency with no section, the locators of a corpus source and of a
///   README, and the modules by path.
/// - witness: `tests::cites::each_case_gives_its_lines`
#[inline]
#[must_use]
pub fn citations(
    path: &str,
    text: &str,
) -> Vec<Citation>
{
    if let Some(module) = path.strip_prefix("corpus/") {
        let mut reader = Reader {
            path,
            krate: String::from("corpus"),
            module: String::from(module),
            readme: false,
            out: Vec::new(),
        };
        for (line, content) in (1_usize ..).zip(text.lines()) {
            if let Some(comment) = corpus_comment(content) {
                reader.locators(comment, Kind::Corpus, line);
            }
        }
        return reader.out;
    }
    let (krate, module, readme) = site_of(path);
    let mut reader = Reader {
        path,
        krate,
        module,
        readme,
        out: Vec::new(),
    };
    if !readme {
        reader.out.push(Citation {
            kind: Kind::File,
            key: String::new(),
            krate: reader.krate.clone(),
            module: reader.module.clone(),
            role: String::new(),
            location: String::from(path),
        });
    }
    let mut block = "";
    let mut refs = false;
    let mut entry = Entry::None;
    let mut fence = false;
    for (line, content) in (1_usize ..).zip(text.lines()) {
        let (kind, text) = documentation(content, readme, &mut fence);
        if kind != block {
            block = kind;
            refs = false;
            entry = Entry::None;
        }
        if kind.is_empty() {
            continue;
        }
        let hashes = text
            .len()
            .saturating_sub(text.trim_start_matches('#').len());
        if hashes > 0
            && text
                .get(hashes ..)
                .is_some_and(|rest| rest.starts_with(' '))
        {
            let title = text
                .get(hashes.saturating_add(1) ..)
                .unwrap_or("")
                .trim_end();
            refs =
                title == "References" && hashes == (if readme { 2 } else { 1 }) && kind != "outer";
            entry = Entry::None;
        }
        else if refs && (text.starts_with("- ") || text.starts_with("* ")) {
            entry = item(&mut reader, text.get(2 ..).unwrap_or(""), line);
        }
        else if let (&Entry::Bare(ref key), Some(rest)) = (&entry, indented(text)) {
            let key = key.clone();
            match rest.strip_prefix("— ") {
                Some(said) => {
                    reader.cited(&key, said, line);
                    entry = Entry::Key;
                },
                None if !rest.is_empty() => entry = Entry::Legacy,
                None => entry = Entry::None,
            }
        }
        else if let (&Entry::Dashed(ref key), Some(rest)) = (&entry, indented(text)) {
            let key = key.clone();
            reader.cited(&key, rest, line);
            entry = Entry::Key;
        }
        else if let (&Entry::Roled(ref key, ref role), Some(rest)) =
            (&entry, indented(text).filter(|rest| !rest.is_empty()))
        {
            let (key, said) = (key.clone(), format!("{role} {rest}"));
            reader.cited(&key, &said, line);
            entry = Entry::Key;
        }
        else if entry != Entry::None && indented(text).is_some_and(|rest| !rest.is_empty()) {
            // A continuation line keeps its entry.
        }
        else {
            entry = Entry::None;
        }
        if entry != Entry::Key {
            reader.locators(text, Kind::Locator, line);
        }
    }
    reader.out
}

/// The text of a comment of a corpus source: after its `//`, more slashes
/// and an optional `!`.
///
/// # Specification
/// trivial.
fn corpus_comment(content: &str) -> Option<&str>
{
    let rest = content.trim_start().strip_prefix("//")?;
    let rest = rest.trim_start_matches('/');
    Some(rest.strip_prefix('!').unwrap_or(rest))
}

/// The kind of documentation of a line, and its text: `readme` for a line of
/// a README outside a fence, `inner` for `//!`, `outer` for `///`, else the
/// empty string.
///
/// # Specification
/// - ensures: a fence line of a README flips `fence` and is no documentation; a
///   `////` line is no documentation; one space after the mark of a source line
///   is dropped.
/// - panics: none.
fn documentation<'line>(
    content: &'line str,
    readme: bool,
    fence: &mut bool,
) -> (&'static str, &'line str)
{
    if readme {
        let start = content.trim_start();
        if start.starts_with("```") || start.starts_with("~~~") {
            *fence = !*fence;
            return ("", "");
        }
        return if *fence {
            ("", "")
        }
        else {
            ("readme", content)
        };
    }
    let Some(rest) = content.trim_start().strip_prefix("//")
    else {
        return ("", "");
    };
    let (kind, rest) = match rest.chars().next() {
        Some('!') => ("inner", rest.get(1 ..).unwrap_or("")),
        Some('/') if !rest.get(1 ..).unwrap_or("").starts_with('/') => {
            ("outer", rest.get(1 ..).unwrap_or(""))
        },
        Some(_) | None => return ("", ""),
    };
    (kind, rest.strip_prefix(' ').unwrap_or(rest))
}

/// Reads the `- ` line of an entry of a References section, `rest` the text
/// after the mark, and gives the entry that waits for the next line.
///
/// # Specification
/// - ensures: a whole key line is read and gives [`Entry::Key`]; a key alone, a
///   key and its dash, and a key, its dash and its role give the entry that
///   waits for the rest; any other line gives [`Entry::Legacy`].
/// - panics: none.
fn item(
    reader: &mut Reader<'_>,
    rest: &str,
    line: usize,
) -> Entry
{
    let Some(inner) = rest.strip_prefix('`')
    else {
        return Entry::Legacy;
    };
    let Some((key, after)) = inner.split_once('`')
    else {
        return Entry::Legacy;
    };
    if key.is_empty() {
        return Entry::Legacy;
    }
    if let Some(said) = after.strip_prefix(DASH) {
        let trimmed = said.trim_end();
        if let Some(role) = ROLES
            .into_iter()
            .find(|role| trimmed.strip_prefix(role).is_some_and(|tail| tail == ":"))
        {
            return Entry::Roled(String::from(key), format!("{role}:"));
        }
        reader.cited(key, said, line);
        return Entry::Key;
    }
    if after.trim().is_empty() {
        return Entry::Bare(String::from(key));
    }
    if after
        .strip_prefix(" —")
        .is_some_and(|tail| tail.trim().is_empty())
    {
        return Entry::Dashed(String::from(key));
    }
    Entry::Legacy
}
