//! The shape of one source's comments, as the package README's § Comments
//! states it (#2918): a head of four paragraphs, and item comments of at most
//! two short sentences.
//!
//! The head's paragraphs are what the source states, naming the item; why,
//! the law, the twin or the gap it closes, in at most three sentences; how,
//! what the checker, the kernel or the runtime does with it, in at most three
//! sentences; and the references, `- see:` lines only. A feature not built
//! yet is the references line `- see: #n — not implemented: <what>`, the
//! spelling `check:ledger` reads in a partial row's exemplar beside
//! `/// Not implemented:`.
//!
//! The check reads the paragraph count, the first sentence's length, the
//! reference tokens, the references lines, the sentence length and the
//! semicolon in the head, and the sentence count, length and references of an
//! item comment. The passive list, the tense, the colon that opens a list or
//! an example and never a second clause, the `-` list for three items or
//! more, and the three-sentence limits are read in review.
//!
//! Each finding is a ledger line `key kind`: `path:<file> unshaped:<rule>`
//! once per broken head rule, and `path:comment:<digest>
//! unshaped:ItemShape` for an item comment, the digest over its text, so a
//! rewritten comment drops its line.

use anodized::spec;

use crate::comments::judge::FILE_ITEM;
use crate::comments::judge::Finding;
use crate::comments::judge::digest;
use crate::comments::shape::Text;
use crate::comments::shape::Yes;

/// The paragraphs a head holds: what, why, how, references.
const HEAD_PARAGRAPHS: usize = 4;

/// The paragraphs before the references paragraph.
const PROSE_PARAGRAPHS: usize = 3;

/// A count of words.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Words(usize);

/// The words the head's first sentence may hold.
const WHAT_WORDS: Words = Words(20);

/// The words any sentence may hold.
const SENTENCE_WORDS: Words = Words(25);

/// The one word a code span reads as: a private-use character, so no prose
/// spells it.
const SPAN: char = '\u{e000}';

/// The sentences an item comment may hold.
const ITEM_SENTENCES: usize = 2;

/// The opening of a references line.
const SEE: &str = "- see:";

/// The opening of a comment line.
const LINE: &str = "//";

/// One rule of the shape a doc comment keeps.
///
/// # Specification
/// - provides: the rule name of an `unshaped:<rule>` ledger kind and the
///   sentence that tells it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rule
{
    /// The head is not exactly four paragraphs.
    HeadParagraphs,
    /// The head's first sentence runs past twenty words.
    WhatLength,
    /// A reference token stands outside the references paragraph.
    ReferenceOutsideReferences,
    /// A references line is not a `- see:` line.
    ReferenceLine,
    /// A head sentence runs past twenty-five words.
    SentenceLength,
    /// A semicolon stands in the head's prose.
    Semicolon,
    /// An item comment runs past two sentences, past twenty-five words in a
    /// sentence, or holds a reference token.
    ItemShape,
}

impl Rule
{
    /// The rule's name in the ledger's kind column.
    ///
    /// # Specification
    /// trivial.
    const fn name(self) -> Text<'static>
    {
        Text(match self {
            Self::HeadParagraphs => "HeadParagraphs",
            Self::WhatLength => "WhatLength",
            Self::ReferenceOutsideReferences => "ReferenceOutsideReferences",
            Self::ReferenceLine => "ReferenceLine",
            Self::SentenceLength => "SentenceLength",
            Self::Semicolon => "Semicolon",
            Self::ItemShape => "ItemShape",
        })
    }

    /// The clause the gate prints for the rule.
    ///
    /// # Specification
    /// trivial.
    const fn told(self) -> Text<'static>
    {
        Text(match self {
            Self::HeadParagraphs => "the head is not four paragraphs (what, why, how, references)",
            Self::WhatLength => "the head's first sentence runs past twenty words",
            Self::ReferenceOutsideReferences => {
                "a reference token stands outside the references paragraph"
            },
            Self::ReferenceLine => "a references line does not open with `- see:`",
            Self::SentenceLength => "a head sentence runs past twenty-five words",
            Self::Semicolon => "a semicolon stands in the head's prose",
            Self::ItemShape => {
                "the item comment runs past two sentences of twenty-five words, or names a \
                 reference"
            },
        })
    }
}

/// The comments of `source` outside the shape, keyed under `file`.
///
/// A comment run is a stretch of lines opening with `//`, `///` or `//!`, one
/// kind to a run. The head is the run the source opens on, of any kind;
/// every later `///` run is an item comment. The head is four paragraphs,
/// split at empty comment lines: what, why, how, and the references, each
/// references line a `- see:` line (an indented line continues it). A head
/// breaking a rule is `file:<file> unshaped:<rule>`, once per rule. An item
/// comment breaking its rule is `file:comment:digest unshaped:ItemShape`,
/// the digest over its text with whitespace collapsed.
///
/// A sentence ends at `.`, `?` or `!` before an end or a space and a capital,
/// a digit or a backtick. A code span is one word and holds no sentence end,
/// semicolon or reference token. A reference token is `pathological/`, `#`
/// before a digit, a `.md` file name, or a code span holding `/`.
///
/// # Specification
/// - requires: `file` contains no colon.
/// - ensures: one finding per broken head rule and per item comment outside its
///   shape, sorted, without repeats; no head finding for a source that does not
///   open on a comment.
/// - provides: the shape debt one source owes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a head of four short paragraphs with `- see:` lines owes
///   nothing, and each rule is broken alone by one changed head or item
///   comment. A swapped rule, a miscounted paragraph or a split inside a code
///   span changes the kinds the witnesses compare.
/// - witness: `tests::comments::prose::tests::a_shaped_source_owes_nothing`
/// - witness: `tests::comments::prose::tests::each_head_rule_is_named_alone`
/// - witness: `tests::comments::prose::tests::an_item_comment_owes_two_short_sentences`
/// - witness: `tests::comments::prose::tests::a_code_span_is_one_word`
/// - witness: `tests::comments::prose::tests::a_line_comment_head_is_judged_and_a_later_line_comment_is_not`
#[spec(ensures: |ret| ret.iter().all(|finding| finding.line().0.starts_with(file.0) && finding.line().0.contains(" unshaped:")))]
#[inline]
#[must_use]
pub fn unshaped(
    file: Text<'_>,
    source: Text<'_>,
) -> Vec<Finding>
{
    let runs = comment_runs(source);
    let opening = source
        .0
        .lines()
        .position(|line| !line.trim().is_empty() && !line.starts_with("#!"));
    let mut found = Vec::new();
    let mut items = runs.iter().peekable();
    if let Some(head) = items.next_if(|run| Some(run.first) == opening) {
        for rule in head_rules(&head.lines) {
            found.push(Finding::unshaped(
                format!("{file}:{FILE_ITEM}", file = file.0),
                rule.name(),
                rule.told(),
            ));
        }
    }
    let mut collapsed = String::new();
    for run in items.filter(|run| run.kind == Kind::Doc) {
        if item_shaped(&run.lines).0 {
            continue;
        }
        collapsed.clear();
        for word in run.lines.iter().flat_map(|line| line.split_whitespace()) {
            if !collapsed.is_empty() {
                collapsed.push(' ');
            }
            collapsed.push_str(word);
        }
        found.push(Finding::unshaped(
            format!(
                "{file}:comment:{digest}",
                file = file.0,
                digest = digest(Text(&collapsed))
            ),
            Rule::ItemShape.name(),
            Rule::ItemShape.told(),
        ));
    }
    found.sort_by(|left, right| left.line().cmp(&right.line()));
    found.dedup_by(|left, right| left.line() == right.line());
    found
}

/// The kind of a comment line.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// `///`, a doc comment.
    Doc,
    /// `//!`, an inner doc comment.
    Inner,
    /// `//`, a line comment.
    Line,
}

/// One comment run: its kind, the index of its first line, and each line past
/// its opening and one space.
struct Run
{
    /// The kind every line of the run shares.
    kind: Kind,
    /// The zero-based index of the run's first line in the source.
    first: usize,
    /// The lines, each past its opening and one space.
    lines: Vec<String>,
}

/// The comment runs of `source`.
///
/// # Specification
/// trivial.
fn comment_runs(source: Text<'_>) -> Vec<Run>
{
    let mut runs: Vec<Run> = Vec::new();
    let mut open = false;
    for (place, line) in source.0.lines().enumerate() {
        let trimmed = line.trim_start();
        let Some(rest) = trimmed.strip_prefix(LINE)
        else {
            open = false;
            continue;
        };
        let (kind, rest) = match rest.strip_prefix('/') {
            Some(doc) if !doc.starts_with('/') => (Kind::Doc, doc),
            Some(_) => (Kind::Line, rest),
            None => rest
                .strip_prefix('!')
                .map_or((Kind::Line, rest), |inner| (Kind::Inner, inner)),
        };
        let content = rest.strip_prefix(' ').unwrap_or(rest).trim_end().to_owned();
        match runs.last_mut() {
            Some(run) if open && run.kind == kind => run.lines.push(content),
            _ => runs.push(Run {
                kind,
                first: place,
                lines: vec![content],
            }),
        }
        open = true;
    }
    runs
}

/// The head rules `head` breaks, in declaration order.
///
/// # Specification
/// trivial.
fn head_rules(head: &[String]) -> Vec<Rule>
{
    let paragraphs = paragraphs(head);
    let split = paragraphs.len().min(PROSE_PARAGRAPHS);
    let (prose, references) = paragraphs.split_at(split);
    let mut broken = Vec::new();
    if paragraphs.len() != HEAD_PARAGRAPHS {
        broken.push(Rule::HeadParagraphs);
    }
    let first = prose
        .first()
        .map(|lines| sentences(Text(&lines.join(" "))))
        .unwrap_or_default();
    if first
        .first()
        .is_some_and(|sentence| over(Text(sentence), WHAT_WORDS).0)
    {
        broken.push(Rule::WhatLength);
    }
    if prose
        .iter()
        .any(|lines| references_a_source(Text(&lines.join(" "))).0)
    {
        broken.push(Rule::ReferenceOutsideReferences);
    }
    if references
        .iter()
        .flatten()
        .any(|line| !(line.starts_with(SEE) || line.starts_with(' ') || line.starts_with('\t')))
    {
        broken.push(Rule::ReferenceLine);
    }
    if prose.iter().any(|lines| {
        sentences(Text(&lines.join(" ")))
            .iter()
            .any(|sentence| over(Text(sentence), SENTENCE_WORDS).0)
    }) {
        broken.push(Rule::SentenceLength);
    }
    if prose
        .iter()
        .any(|lines| masked(Text(&lines.join(" "))).contains(';'))
    {
        broken.push(Rule::Semicolon);
    }
    broken
}

/// Whether the item comment `run` keeps its shape.
///
/// # Specification
/// trivial.
fn item_shaped(run: &[String]) -> Yes
{
    let text = run.join(" ");
    let said = sentences(Text(&text));
    Yes(said.len() <= ITEM_SENTENCES
        && said
            .iter()
            .all(|sentence| !over(Text(sentence), SENTENCE_WORDS).0)
        && !references_a_source(Text(&text)).0)
}

/// The paragraphs of `run`: its runs of non-empty lines.
///
/// # Specification
/// trivial.
fn paragraphs(run: &[String]) -> Vec<Vec<String>>
{
    let mut paragraphs: Vec<Vec<String>> = Vec::new();
    let mut open = false;
    for line in run {
        if line.trim().is_empty() {
            open = false;
            continue;
        }
        match paragraphs.last_mut() {
            Some(paragraph) if open => paragraph.push(line.clone()),
            _ => paragraphs.push(vec![line.clone()]),
        }
        open = true;
    }
    paragraphs
}

/// `text` with each code span read as the one word [`SPAN`].
///
/// # Specification
/// trivial.
fn masked(text: Text<'_>) -> String
{
    let mut out = String::with_capacity(text.0.len());
    let mut inside = false;
    for character in text.0.chars() {
        if character == '`' {
            if !inside {
                out.push(SPAN);
            }
            inside = !inside;
        }
        else if !inside {
            out.push(character);
        }
    }
    out
}

/// The sentences of `text`, code spans read as one word each.
///
/// # Specification
/// trivial.
fn sentences(text: Text<'_>) -> Vec<String>
{
    let plain = masked(text);
    let mut said = Vec::new();
    let mut start = 0_usize;
    for (place, held) in plain.char_indices() {
        if !matches!(held, '.' | '?' | '!') {
            continue;
        }
        let after = place.saturating_add(held.len_utf8());
        let rest = plain.get(after ..).unwrap_or_default();
        let next = rest.trim_start();
        let ends = rest.is_empty()
            || rest.starts_with(char::is_whitespace)
                && next.starts_with(|first: char| {
                    first.is_uppercase() || first.is_ascii_digit() || first == SPAN
                });
        if ends || next.is_empty() {
            let sentence = plain.get(start .. after).unwrap_or_default().trim();
            if !sentence.is_empty() {
                said.push(sentence.to_owned());
            }
            start = after;
        }
    }
    let tail = plain.get(start ..).unwrap_or_default().trim();
    if !tail.is_empty() {
        said.push(tail.to_owned());
    }
    said
}

/// Whether `sentence` runs past `limit` words.
///
/// # Specification
/// trivial.
fn over(
    sentence: Text<'_>,
    limit: Words,
) -> Yes
{
    Yes(sentence.0.split_whitespace().count() > limit.0)
}

/// Whether `text` holds a reference token.
///
/// # Specification
/// trivial.
fn references_a_source(text: Text<'_>) -> Yes
{
    let plain = masked(text);
    let issue = plain.match_indices('#').any(|(place, _)| {
        plain
            .get(place.saturating_add(1) ..)
            .is_some_and(|rest| rest.starts_with(|digit: char| digit.is_ascii_digit()))
    });
    let page = plain.split_whitespace().any(|word| {
        names_a_page(Text(
            word.trim_end_matches(|held: char| !held.is_alphanumeric()),
        ))
        .0
    });
    let span = text
        .0
        .split('`')
        .skip(1)
        .step_by(2)
        .any(|held| held.contains('/') || names_a_page(Text(held)).0);
    Yes(plain.contains("pathological/") || issue || page || span)
}

/// Whether `name` is a Markdown page's file name.
///
/// # Specification
/// trivial.
fn names_a_page(name: Text<'_>) -> Yes
{
    Yes(std::path::Path::new(name.0)
        .extension()
        .is_some_and(|extension| extension.eq_ignore_ascii_case("md")))
}

#[cfg(test)]
mod tests
{
    use super::unshaped;
    use crate::comments::shape::Text;

    /// The kinds `source` owes, as ledger lines.
    ///
    /// # Specification
    /// trivial.
    fn kinds(source: Text<'_>) -> Vec<String>
    {
        unshaped(Text("s.gandr"), source)
            .into_iter()
            .map(|finding| finding.line().0.to_owned())
            .collect()
    }

    /// A head in the shape, its references paragraph `references`.
    ///
    /// # Specification
    /// trivial.
    fn head(references: Text<'_>) -> String
    {
        format!(
            "/// Pairs sum their halves.\n///\n/// The sum is the reading the corpus \
             fixes.\n///\n/// The checker reduces both sides.\n///\n{references}\n\ndef x = \
             1;\n",
            references = references.0
        )
    }

    #[test]
    fn a_shaped_source_owes_nothing()
    {
        let source = head(Text(
            "/// - see: #12 — not implemented: the pair\n/// - see: `pathological/a.gandr` — \
             the negative\n///   twin, wrapped",
        ));
        assert_eq!(kinds(Text(&source)), Vec::<String>::new());
        let item = format!("{source}/// The pair. Its sum.\ndef y = 2;\n");
        assert_eq!(kinds(Text(&item)), Vec::<String>::new());
    }

    #[test]
    fn each_head_rule_is_named_alone()
    {
        let cases = [
            (
                "/// Pairs sum their halves.\n///\n/// Why.\n///\n/// The checker reduces \
                 both.\n",
                "HeadParagraphs",
            ),
            (
                "/// Pairs sum their halves and then the corpus reads the sum back through every \
                 single one of its many careful readers.\n///\n/// Why.\n///\n/// How.\n///\n/// \
                 - see: #1 — x\n",
                "WhatLength",
            ),
            (
                "/// Pairs sum.\n///\n/// See #4 for why.\n///\n/// How.\n///\n/// - see: #1 — \
                 x\n",
                "ReferenceOutsideReferences",
            ),
            (
                "/// Pairs sum.\n///\n/// Why.\n///\n/// How.\n///\n/// Not implemented: #1\n",
                "ReferenceLine",
            ),
            (
                "/// Pairs sum.\n///\n/// Why it holds is that one two three four five six \
                 seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen seventeen \
                 eighteen nineteen twenty twenty-one twenty-two.\n///\n/// How.\n///\n/// - see: \
                 #1 — x\n",
                "SentenceLength",
            ),
            (
                "/// Pairs sum.\n///\n/// Why; because.\n///\n/// How.\n///\n/// - see: #1 — \
                 x\n",
                "Semicolon",
            ),
        ];
        for (source, rule) in cases {
            assert_eq!(
                kinds(Text(source)),
                [format!("s.gandr:<file> unshaped:{rule}")],
                "{rule} alone is named"
            );
        }
    }

    #[test]
    fn an_item_comment_owes_two_short_sentences()
    {
        let shaped = head(Text("/// - see: #1 — x"));
        for item in [
            "/// One. Two. Three.\n",
            "/// The pair, as `pathological/p.gandr` refuses it.\n",
            "/// See #9.\n",
        ] {
            let found = kinds(Text(&format!("{shaped}{item}def y = 2;\n")));
            assert!(
                found.len() == 1
                    && found.iter().all(|line| line.starts_with("s.gandr:comment:")
                        && line.ends_with(" unshaped:ItemShape")),
                "{item:?} is named by its comment: {found:?}"
            );
        }
    }

    #[test]
    fn a_code_span_is_one_word()
    {
        let shaped = head(Text("/// - see: #1 — x"));
        let item = "/// The term `a. B. c; d e f g h i j k l m n o p q r s t u v w x y z` \
                    reduces.\ndef y = 2;\n";
        assert_eq!(
            kinds(Text(&format!("{shaped}{item}"))),
            Vec::<String>::new()
        );
    }

    #[test]
    fn a_line_comment_head_is_judged_and_a_later_line_comment_is_not()
    {
        let source = "#!/usr/bin/env gandr\n// Pairs sum.\n//\n// Why.\n\n// One. Two. \
                      Three.\ndef x = 1;\n";
        assert_eq!(
            kinds(Text(source)),
            ["s.gandr:<file> unshaped:HeadParagraphs"],
            "the `//` head is judged and the later `//` run is no item comment"
        );
    }
}
