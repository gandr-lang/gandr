//! The sentence rules and the procedural form, judged over the parse.
//!
//! Text inside backticks is code and no rule reads it; text inside double
//! quotes is a quotation, which the tense rule leaves alone. Each finding
//! names its rule, and the rule's fix is the line
//! `crates/workflow-prose/README.md` § Rules states.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt;
use core::str::FromStr;

use quenchant_shape::shape::Maybe;

use crate::glossary::Agrees;
use crate::glossary::Glossary;
use crate::glossary::Tag;
use crate::parse::Sentence;
use crate::parse::Token;
use crate::passage::Advice;
use crate::passage::CommentShape;
use crate::passage::Golden;
use crate::passage::LIMITS;
use crate::passage::Limits;
use crate::passage::Line;
use crate::passage::Opened;
use crate::passage::Passage;
use crate::passage::Placed;
use crate::passage::References;
use crate::passage::Source;
use crate::passage::Text;
use crate::passage::WhatLine;

/// The lemmas whose passive the corpus states: `is refused`, `is admitted`,
/// `is replayed`, `is checked`, `is normalised`.
const PASSIVES: [&str; 6] = [
    "refuse",
    "admit",
    "replay",
    "check",
    "normalise",
    "normalize",
];

/// The longest run of nouns a sentence may stack.
const STACK: usize = 3;

/// The most words a description sentence may hold, a code span counted as one.
const WORDS: usize = 25;

/// The most words a procedure sentence may hold.
const PROCEDURE_WORDS: usize = 20;

/// The most sentences a comment paragraph may hold.
const WALL: usize = 5;

/// The words the head's first sentence may hold.
const WHAT_WORDS: usize = 20;

/// The sentences an item comment may hold.
const ITEM_SENTENCES: usize = 2;

/// The paragraphs a head holds: what, why, how, references.
const HEAD_PARAGRAPHS: usize = 4;

/// The paragraphs a head holds with its `Limits` paragraph.
const LIMITED_PARAGRAPHS: usize = 5;

/// The coarse tags of a token that is not a word.
const UNWORDED: [&str; 3] = ["PUNCT", "SPACE", "SYM"];

/// The dashes that may join two clauses.
const DASHES: [&str; 2] = ["—", "–"];

/// The dependencies of an `-ing` form that is a clause of its own.
const CLAUSES: [&str; 8] = [
    "acl",
    "advcl",
    "pcomp",
    "xcomp",
    "ccomp",
    "csubj",
    "csubjpass",
    "relcl",
];

/// The directories a path in the tree starts with.
const ROOTS: [&str; 8] = [
    "crates/", "corpus/", "library/", "ledger/", ".config/", ".github/", "docs/", "contrib/",
];

/// The extensions that mark a word with a `/` as a file's path.
const EXTENSIONS: [&str; 12] = [
    ".rs", ".gandr", ".md", ".toml", ".json", ".txt", ".py", ".jq", ".bash", ".yml", ".sql",
    ".ledger",
];

/// A rule a sentence or a diagnostic is held to.
///
/// # Specification
/// - provides: the rule a finding names and the ledger keys.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Rule
{
    /// A passive outside the stated list.
    Passive,
    /// A verb in the past, the future or the progressive.
    Tense,
    /// A complex verb construction: a perfect, or a passive after a modal or
    /// `to`.
    Complex,
    /// Four or more nouns in a row.
    NounStack,
    /// An `-ing` form as the main verb, as a noun modifier or as a clause.
    IngMain,
    /// A phrasal verb: a verb with a particle.
    Phrasal,
    /// A glossary word in a part of speech the glossary refuses.
    Glossary,
    /// A sentence of a description longer than twenty-five words.
    Length,
    /// A procedure sentence longer than twenty words.
    ProcedureLength,
    /// Two instructions in one procedure sentence.
    Instructions,
    /// A semicolon joining two sentences of a body or a comment.
    Semicolon,
    /// A dash joining two clauses of a body or a comment.
    Dash,
    /// A path, an issue number, a URL or a paper's citation in a comment's
    /// prose.
    InlineReference,
    /// A comment paragraph of more than five sentences, or an item comment of
    /// more than two.
    Wall,
    /// A corpus source's head is not four paragraphs, a references line opens
    /// with none of `- see:`, `- owes:` and `- cites:`, or a `- cites:` label
    /// has no footer line with a quoted title.
    Head,
    /// The head's first sentence runs past twenty words.
    What,
    /// A diagnostic without its what, its where or its what-to-do.
    Procedure,
}

/// Every rule, in the order they are stated.
const RULES: [Rule; 17] = [
    Rule::Passive,
    Rule::Tense,
    Rule::Complex,
    Rule::NounStack,
    Rule::IngMain,
    Rule::Phrasal,
    Rule::Glossary,
    Rule::Length,
    Rule::ProcedureLength,
    Rule::Instructions,
    Rule::Semicolon,
    Rule::Dash,
    Rule::InlineReference,
    Rule::Wall,
    Rule::Head,
    Rule::What,
    Rule::Procedure,
];

impl fmt::Display for Rule
{
    /// Writes the rule's name as the ledger spells it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every rule's name round-trips through
    ///   [`Rule::from_str`], so a swapped or missing name breaks the trip.
    /// - witness: `rules::tests::every_rule_reads_back_and_states_its_fix`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Passive => "STE-3.6",
            Self::Tense => "STE-3.2",
            Self::Complex => "STE-3.4",
            Self::NounStack => "STE-2.1",
            Self::IngMain => "STE-3.5",
            Self::Phrasal => "STE-9.3",
            Self::Glossary => "STE-1.2",
            Self::Length => "STE-6.3",
            Self::ProcedureLength => "STE-5.1",
            Self::Instructions => "STE-5.2",
            Self::Semicolon => "STE-8.1",
            Self::Dash => "STE-4.1",
            Self::InlineReference => "STE-4.3",
            Self::Wall => "STE-6.6",
            Self::Head => "STE-6.4",
            Self::What => "STE-6.5",
            Self::Procedure => "STE-5.3",
        })
    }
}

/// Why a word is not a rule's name.
///
/// # Specification
/// - provides: the one way a ledger's rule is refused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NotARule
{
    /// The word names no rule.
    Unknown,
}

impl FromStr for Rule
{
    type Err = NotARule;

    /// Reads a rule's name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Rule`]'s rendering.
    /// - witness: `rules::tests::every_rule_reads_back_and_states_its_fix`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        RULES
            .into_iter()
            .find(|rule| rule.to_string() == text)
            .ok_or(NotARule::Unknown)
    }
}

/// The fix a rule's finding asks for.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Fix(pub Rule);

impl fmt::Display for Fix
{
    /// Writes the fix the README states for the rule.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each rule's fix is asserted, so a swapped fix changes
    ///   it.
    /// - witness: `rules::tests::every_rule_reads_back_and_states_its_fix`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            Rule::Passive => {
                "name the agent and make it the subject; a passive is allowed only as `is \
                 refused`, `is admitted`, `is replayed`, `is checked` or `is normalised`"
            },
            Rule::Tense => "state it in the present tense",
            Rule::Complex => "use one simple verb: drop the perfect, or make the agent the subject",
            Rule::NounStack => "break the stack of nouns with a preposition or a verb",
            Rule::IngMain => "make the `-ing` form a finite verb in a clause of its own",
            Rule::Phrasal => "use one verb in place of the verb and its particle",
            Rule::Glossary => {
                "use the glossary word only as its part of speech, or choose another word"
            },
            Rule::Length => "split it into sentences of at most 25 words, one clause each",
            Rule::ProcedureLength => "split the procedure into sentences of at most 20 words",
            Rule::Instructions => "write each instruction as a sentence of its own",
            Rule::Semicolon => "end the first sentence with a full stop and start the next",
            Rule::Dash => {
                "end the first clause with a full stop, or make the text after the dash a phrase \
                 with no verb"
            },
            Rule::InlineReference => {
                "move the path, the issue or the URL to a `- see:` line after the paragraph, and a \
                 paper to a `- cites: [label]` line with its footer line `[label]: <URL> \
                 \"<authors>, <title>\"`"
            },
            Rule::Wall => {
                "split the paragraph into paragraphs of at most five sentences, one idea each, or \
                 cut the item comment to at most two sentences"
            },
            Rule::Head => {
                "open the source on four paragraphs: what, why, how and references, with a \
                 `Limits:` paragraph after the how paragraph when the source has limits"
            },
            Rule::What => "cut the first sentence to at most twenty words",
            Rule::Procedure => {
                "state what is wrong in the headline, label the span, and end with an \
                 imperative `help:` or the issue that tracks it"
            },
        })
    }
}

/// One sentence or diagnostic that breaks a rule.
///
/// # Specification
/// - provides: what the check prints and the ledger keys.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding
{
    /// The file.
    pub path: String,
    /// The line its passage starts on.
    pub line: Line,
    /// The rule it breaks.
    pub rule: Rule,
    /// The sentence, or the diagnostic's headline.
    pub sentence: String,
}

/// How a character of a passage is read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// Prose.
    Prose,
    /// Inside backticks: code, which no rule reads.
    Code,
    /// Inside double quotes: a quotation, which the tense rule leaves alone.
    Quoted,
}

/// How each character of `text` is read, by index.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a passive inside backticks and a past tense inside quotes
///   fire nothing; a mask off by one fires them.
/// - witness: `rules::tests::code_and_quotations_are_not_read`
fn readings(text: Text<'_>) -> Vec<Reading>
{
    let mut reading = Reading::Prose;
    text.0
        .chars()
        .map(|character| match (character, reading) {
            ('`', Reading::Code) => {
                reading = Reading::Prose;
                Reading::Code
            },
            ('`', Reading::Prose | Reading::Quoted) => {
                reading = Reading::Code;
                Reading::Code
            },
            ('"', Reading::Quoted) => {
                reading = Reading::Prose;
                Reading::Quoted
            },
            ('"', Reading::Prose) => {
                reading = Reading::Quoted;
                Reading::Quoted
            },
            (_, current) => current,
        })
        .collect()
}

/// How `token` is read, given the passage's `readings`.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`readings`].
/// - witness: `rules::tests::code_and_quotations_are_not_read`
fn read(
    readings: &[Reading],
    token: &Token,
) -> Reading
{
    readings
        .get(token.offset)
        .copied()
        .unwrap_or(Reading::Prose)
}

/// The text of `sentence` in `passage`, from its first token to its last.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a finding prints its sentence alone; another span changes
///   the printed sentence and the ledger's digest.
/// - witness: `rules::tests::each_rule_fires_on_its_sentence_and_not_on_its_twin`
fn spoken(
    passage: &Passage,
    sentence: &Sentence,
) -> String
{
    let (Some(first), Some(last)) = (sentence.tokens.first(), sentence.tokens.last())
    else {
        return String::new();
    };
    let end = last.offset.saturating_add(last.text.chars().count());
    passage
        .text
        .chars()
        .skip(first.offset)
        .take(end.saturating_sub(first.offset))
        .collect()
}

/// How an item's sentence opens: on `Limits:`, as a third sentence that states
/// a limit does, or otherwise.
///
/// # Specification
/// - provides: whether a third item sentence may stand.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Opening
{
    /// The sentence opens on `Limits:`.
    Limit,
    /// The sentence opens on anything else.
    Other,
}

/// How `sentence` opens. The parse splits `Limits:` into the word and its
/// colon.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — an item of three sentences whose third opens on `Limits:`
///   holds, and one whose third opens otherwise is refused; a reading of
///   another token changes a verdict.
/// - witness: `rules::tests::a_head_and_an_item_hold_their_sentence_counts`
fn opening(sentence: &Sentence) -> Opening
{
    let word = LIMITS.trim_end_matches(':');
    match sentence.tokens.as_slice() {
        &[ref first, ref second, ..] if first.text == word && second.text == ":" => Opening::Limit,
        _ => Opening::Other,
    }
}

/// A count of words. A code span counts as one word.
#[repr(transparent)]
struct Words(usize);

/// The words of `sentence`, a code span counted as one.
///
/// # Specification
/// trivial.
fn words(
    readings: &[Reading],
    sentence: &Sentence,
) -> Words
{
    let worded = |token: &Token| !UNWORDED.contains(&token.pos.as_str());
    let mut count = 0_usize;
    let mut coded = false;
    for token in &sentence.tokens {
        let code = read(readings, token) == Reading::Code;
        if (code && !coded) || (!code && worded(token)) {
            count = count.saturating_add(1);
        }
        coded = code;
    }
    Words(count)
}

/// The body rules `sentence` breaks, each at most once: a body's and a
/// comment's.
///
/// # Specification
/// - requires: `sentence` is a sentence of the passage `readings` was taken
///   from.
/// - ensures: in the order of [`RULES`], [`Rule::ProcedureLength`] when the
///   root is `VB` and has no `nsubj` or `nsubjpass` child and the sentence
///   holds more than [`PROCEDURE_WORDS`] words. [`Rule::Length`] when that root
///   test fails and the sentence holds more than [`WORDS`] words. A word is a
///   token in prose or quotation that is not punctuation, a space or a symbol,
///   and each code span counts as one. [`Rule::Instructions`] when
///   [`instructions`] finds two instructions. [`Rule::Semicolon`] when a `;` in
///   prose has a word after it. [`Rule::Dash`] when an em or en dash in prose
///   has a verb or an auxiliary in prose after it.
/// - provides: the verdict a body or a comment adds to a sentence.
/// - fails: never.
/// - panics: none.
/// - executable: none — the walk is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — each rule's sentence and a twin it must pass: 26 words
///   and 25 words with a code span, two instructions joined by `and` and two
///   joined by `or`, a joining and a closing semicolon, a dash before a clause
///   and one before a phrase; an off-by-one limit, a code span counted per
///   token, a conjunction read wrongly, or a dropped look-ahead changes the
///   verdicts.
/// - witness: `rules::tests::a_body_holds_its_length_semicolons_and_dashes`
/// - witness: `rules::tests::a_comment_holds_the_body_rules_its_references_and_walls`
fn clauses(
    readings: &[Reading],
    sentence: &Sentence,
) -> Vec<Rule>
{
    let prose = |token: &Token| read(readings, token) == Reading::Prose;
    let worded = |token: &Token| !UNWORDED.contains(&token.pos.as_str());
    let mut rules = Vec::new();
    let count = words(readings, sentence).0;
    let procedure = match sentence.root() {
        Maybe::Present(root)
            if root.tag == "VB"
                && !sentence
                    .children(root)
                    .any(|child| child.dep == "nsubj" || child.dep == "nsubjpass") =>
        {
            true
        },
        Maybe::Present(_) | Maybe::Absent(_) => false,
    };
    if procedure && count > PROCEDURE_WORDS {
        rules.push(Rule::ProcedureLength);
    }
    else if count > WORDS {
        rules.push(Rule::Length);
    }
    if instructions(readings, sentence) == Agrees::Agrees {
        rules.push(Rule::Instructions);
    }
    let after = |mark: &dyn Fn(&Token) -> bool, follows: &dyn Fn(&Token) -> bool| {
        sentence
            .tokens
            .iter()
            .skip_while(|token| !(prose(token) && mark(token)))
            .skip(1)
            .any(|token| prose(token) && follows(token))
    };
    if after(&|token| token.text == ";", &worded) {
        rules.push(Rule::Semicolon);
    }
    if after(&|token| DASHES.contains(&token.text.as_str()), &|token| {
        token.pos == "VERB" || token.pos == "AUX"
    }) {
        rules.push(Rule::Dash);
    }
    rules
}

/// The rules `sentence` breaks, each at most once.
///
/// # Specification
/// - requires: `sentence` is a sentence of the passage `readings` was taken
///   from.
/// - ensures: in the order of [`RULES`], [`Rule::Passive`] when a token in
///   prose is `auxpass` and its head's lemma is not on the passive list.
///   [`Rule::Tense`] when a token in prose is `aux` and its lemma is `will` or
///   `shall`, or a token in prose is tagged `VBG` and has an `aux` child of
///   lemma `be`, or the root, in prose, is tagged `VBD`, or `VBN` with no
///   `auxpass` child in the present or the base form and no `aux` child of
///   lemma `have`. [`Rule::Complex`] when a token in prose is `aux` of lemma
///   `have` and its head is tagged `VBN`, or a token in prose is `auxpass` and
///   its head has an `aux` child tagged `MD` or `TO`. A `source` of
///   [`Source::Body`] adds the rules [`clauses`] states. Every other source
///   adds [`Rule::NounStack`] when more than three consecutive tokens in prose
///   are `NOUN` or `PROPN`. [`Rule::IngMain`] when a token in prose is tagged
///   `VBG` and is the root with no `aux` child of lemma `be`, or its dependency
///   is `amod`, `acl`, `advcl`, `pcomp`, `xcomp`, `ccomp`, `csubj`, `csubjpass`
///   or `relcl`, or it is the `conj` of a verb. [`Rule::Phrasal`] when a token
///   in prose is `prt` and its head is a verb. [`Rule::Glossary`] when a token
///   in prose has a lemma the glossary holds and a coarse tag its part of
///   speech does not admit. A `source` of [`Source::Comment`] adds the rules
///   [`clauses`] states after these.
/// - provides: the verdict of one sentence.
/// - fails: never.
/// - panics: none.
/// - executable: none — the walk is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — each rule's sentence and a twin it must pass; a dropped
///   condition, a widened list or a rule fired twice changes the verdicts.
/// - witness: `rules::tests::each_rule_fires_on_its_sentence_and_not_on_its_twin`
/// - witness: `rules::tests::code_and_quotations_are_not_read`
/// - witness: `rules::tests::a_body_holds_its_length_semicolons_and_dashes`
/// - witness: `rules::tests::a_comment_holds_the_body_rules_its_references_and_walls`
fn broken(
    readings: &[Reading],
    sentence: &Sentence,
    glossary: &Glossary,
    source: Source,
) -> Vec<Rule>
{
    let prose = |token: &Token| read(readings, token) == Reading::Prose;
    let mut rules = Vec::new();
    let passive = sentence.tokens.iter().any(|token| {
        token.dep == "auxpass"
            && prose(token)
            && sentence
                .tokens
                .get(token.head)
                .is_some_and(|head| !PASSIVES.contains(&head.lemma.to_lowercase().as_str()))
    });
    if passive {
        rules.push(Rule::Passive);
    }
    let root = match sentence.root() {
        Maybe::Present(root) if read(readings, root) == Reading::Prose => Some(root),
        Maybe::Present(_) | Maybe::Absent(_) => None,
    };
    let has_aux = |head: &Token, lemma: &str| {
        sentence
            .children(head)
            .any(|child| child.dep == "aux" && child.lemma.eq_ignore_ascii_case(lemma))
    };
    let present_passive = |root: &Token| {
        sentence.children(root).any(|child| {
            child.dep == "auxpass" && matches!(child.tag.as_str(), "VBZ" | "VBP" | "VB")
        })
    };
    let future = sentence.tokens.iter().any(|token| {
        prose(token)
            && token.dep == "aux"
            && matches!(token.lemma.to_lowercase().as_str(), "will" | "shall")
    });
    let progressive = sentence
        .tokens
        .iter()
        .any(|token| prose(token) && token.tag == "VBG" && has_aux(token, "be"));
    let past = root.is_some_and(|root| {
        root.tag == "VBD" || (root.tag == "VBN" && !present_passive(root) && !has_aux(root, "have"))
    });
    if future || progressive || past {
        rules.push(Rule::Tense);
    }
    let head_of = |token: &Token| sentence.tokens.get(token.head);
    let perfect = sentence.tokens.iter().any(|token| {
        prose(token)
            && token.dep == "aux"
            && token.lemma.eq_ignore_ascii_case("have")
            && head_of(token).is_some_and(|head| head.tag == "VBN")
    });
    let modal_passive = sentence.tokens.iter().any(|token| {
        prose(token)
            && token.dep == "auxpass"
            && head_of(token).is_some_and(|head| {
                sentence
                    .children(head)
                    .any(|child| child.dep == "aux" && (child.tag == "MD" || child.tag == "TO"))
            })
    });
    if perfect || modal_passive {
        rules.push(Rule::Complex);
    }
    if source == Source::Body {
        rules.extend(clauses(readings, sentence));
        return rules;
    }
    let mut run = 0_usize;
    let mut stacked = false;
    for token in &sentence.tokens {
        run = if prose(token) && (token.pos == "NOUN" || token.pos == "PROPN") {
            run.saturating_add(1)
        }
        else {
            0
        };
        stacked |= run > STACK;
    }
    if stacked {
        rules.push(Rule::NounStack);
    }
    let verbal = |token: &Token| token.pos == "VERB" || token.pos == "AUX";
    let ing = sentence.tokens.iter().any(|token| {
        prose(token)
            && token.tag == "VBG"
            && ((token.dep == "ROOT" && !has_aux(token, "be"))
                || CLAUSES.contains(&token.dep.as_str())
                || (token.dep == "conj" && head_of(token).is_some_and(verbal)))
    });
    if ing {
        rules.push(Rule::IngMain);
    }
    let phrasal = sentence
        .tokens
        .iter()
        .any(|token| prose(token) && token.dep == "prt" && head_of(token).is_some_and(verbal));
    if phrasal {
        rules.push(Rule::Phrasal);
    }
    let misused = sentence.tokens.iter().any(|token| {
        prose(token)
            && glossary
                .pos(Text(&token.lemma))
                .any(|pos| pos.admits(Tag(&token.pos)) == Agrees::Differs)
    });
    if misused {
        rules.push(Rule::Glossary);
    }
    if source == Source::Comment {
        rules.extend(clauses(readings, sentence));
    }
    rules
}

/// Whether `sentence` holds two instructions: its root, in prose, is a bare
/// verb with no subject, and a `conj` child of it, in prose, is a bare verb
/// with no subject, joined by `and` or by a comma alone.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — `read the file and write the log` holds two, and `read
///   the file or write the log` and `the kernel reads and writes` hold one; a
///   join read as `or`, or a subject left unread, changes one.
/// - witness: `rules::tests::a_body_holds_its_length_semicolons_and_dashes`
/// - witness: `rules::tests::a_diagnostic_needs_its_what_where_and_imperative`
fn instructions(
    readings: &[Reading],
    sentence: &Sentence,
) -> Agrees
{
    let prose = |token: &Token| read(readings, token) == Reading::Prose;
    let bare = |verb: &Token| {
        prose(verb)
            && verb.tag == "VB"
            && !sentence
                .children(verb)
                .any(|child| child.dep == "nsubj" || child.dep == "nsubjpass")
    };
    let Maybe::Present(root) = sentence.root()
    else {
        return Agrees::Differs;
    };
    if !bare(root) {
        return Agrees::Differs;
    }
    let twice = sentence.children(root).any(|second| {
        second.dep == "conj"
            && bare(second)
            && sentence
                .children(root)
                .chain(sentence.children(second))
                .filter(|join| join.dep == "cc")
                .all(|join| join.lemma.eq_ignore_ascii_case("and"))
    });
    if twice {
        Agrees::Agrees
    }
    else {
        Agrees::Differs
    }
}

/// [`Rule::InlineReference`] when `text` names a path in the tree, an issue, a
/// URL or a paper: a word, its opening quotes and brackets and its closing
/// quotes, brackets and punctuation left out in any order, holding `://`,
/// being `#` and digits, holding a `/` and starting with a tree directory or
/// ending with a file extension, or being a paper's locator ([`locator`]); or
/// a parenthesis holding a title in underscores ([`titled`]).
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a path in backticks, an issue in brackets or closing a
///   parenthesis before a full stop, a URL, a DOI, an arXiv identifier and a
///   parenthesised title fire, and a quotient `A/B`, an attribute `#[cfg]`, `#`
///   alone, a decimal and an emphasis outside a parenthesis do not; a dropped
///   pattern, a wider one or a closing bracket kept changes a verdict.
/// - witness: `rules::tests::a_comment_holds_the_body_rules_its_references_and_walls`
fn referenced(text: Text<'_>) -> Option<Rule>
{
    (text.0.split_whitespace().any(|word| {
        let word = word
            .trim_start_matches(|c: char| "`'\"([{".contains(c))
            .trim_end_matches(|c: char| "`'\")]},;:!?.".contains(c));
        word.contains("://")
            || word.strip_prefix('#').is_some_and(|digits| {
                !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())
            })
            || (word.contains('/')
                && (ROOTS.iter().any(|root| word.starts_with(root))
                    || EXTENSIONS.iter().any(|extension| word.ends_with(extension))))
            || locator(Text(word)).is_some()
    }) || titled(text).is_some())
    .then_some(Rule::InlineReference)
}

/// [`Rule::InlineReference`] when `word` is a paper's locator: `doi:` or
/// `arXiv:` before its identifier, in any case, or a bare DOI, `10.`, a
/// registrant of four digits or more, `/` and a suffix.
///
/// # Specification
/// trivial.
fn locator(word: Text<'_>) -> Option<Rule>
{
    let lower = word.0.to_ascii_lowercase();
    let named = ["doi:", "arxiv:"].iter().any(|scheme| {
        lower
            .strip_prefix(scheme)
            .is_some_and(|id| id.starts_with(|c: char| c.is_ascii_alphanumeric()))
    });
    (named
        || lower
            .strip_prefix("10.")
            .and_then(|rest| rest.split_once('/'))
            .is_some_and(|(registrant, suffix)| {
                registrant.len() >= 4
                    && registrant.chars().all(|c| c.is_ascii_digit())
                    && !suffix.is_empty()
            }))
    .then_some(Rule::InlineReference)
}

/// [`Rule::InlineReference`] when a parenthesis of `text` holds a title: a
/// word that opens with `_` and a capital letter, or a capital letter after
/// `, "`, the ways a citation sets a paper's title, `(Dybjer, _Inductive
/// families_, 1994)` or `(Levy, "Call-By-Push-Value", 2003)`. A code span is
/// skipped, so a parenthesis of code holds no title.
///
/// # Specification
/// trivial.
fn titled(text: Text<'_>) -> Option<Rule>
{
    let mut code = false;
    let mut depth = 0_usize;
    // The last three characters outside a code span, the latest last.
    let mut window = [' '; 3];
    for c in text.0.chars() {
        if c == '`' {
            code = !code;
            continue;
        }
        if code {
            continue;
        }
        match c {
            '(' => depth = depth.saturating_add(1),
            ')' => depth = depth.saturating_sub(1),
            _ if depth > 0 && c.is_uppercase() => {
                let [before, quote, latest] = window;
                let underscored = latest == '_' && (quote.is_whitespace() || quote == '(');
                let quoted = latest == '"' && quote == ' ' && before == ',';
                if underscored || quoted {
                    return Some(Rule::InlineReference);
                }
            },
            _ => {},
        }
        window = [window[1], window[2], c];
    }
    None
}

/// [`Rule::Wall`] when more than five of the parse `sentences` end in prose:
/// the passage's last, and each whose last token closes on a full stop, a
/// question mark or an exclamation mark that `readings` reads as prose. A split
/// the parser makes inside a code span ends no sentence.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — five sentences, one split by the parser inside a code
///   span, count five; counting every parse, or reading the token's first
///   character, counts six.
/// - witness: `rules::tests::a_comment_holds_the_body_rules_its_references_and_walls`
fn walled(
    readings: &[Reading],
    sentences: &[Sentence],
) -> Option<Rule>
{
    let last = sentences.len().saturating_sub(1);
    let ended = sentences
        .iter()
        .enumerate()
        .filter(|&(at, sentence)| {
            at == last
                || sentence.tokens.last().is_some_and(|token| {
                    let close = token
                        .offset
                        .saturating_add(token.text.chars().count())
                        .saturating_sub(1);
                    token.text.ends_with(['.', '?', '!'])
                        && readings.get(close).copied().unwrap_or(Reading::Prose) == Reading::Prose
                })
        })
        .count();
    (ended > WALL).then_some(Rule::Wall)
}

/// The findings of `passage`'s `sentences`.
///
/// # Specification
/// - requires: `sentences` are the passage's parse.
/// - ensures: one finding per rule each sentence breaks, under the rules of the
///   passage's source, in sentence order, each naming the passage's path and
///   line and the sentence's text. A comment's sentence that names a path, an
///   issue, a URL, a paper's locator or a paper's title ([`referenced`]) adds
///   [`Rule::InlineReference`] after its other rules; a comment paragraph of
///   more than five sentences that end in prose ([`walled`]) adds one
///   [`Rule::Wall`] last, naming the whole paragraph.
/// - provides: the sentence rules over one passage.
/// - fails: never.
/// - panics: none.
/// - executable: none — the walk is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — as the private rules; a comment of six sentences, one
///   naming an issue, and a body naming one; a wall at five, or a reference
///   read in a body, changes the findings.
/// - witness: `rules::tests::each_rule_fires_on_its_sentence_and_not_on_its_twin`
/// - witness: `rules::tests::a_comment_holds_the_body_rules_its_references_and_walls`
#[inline]
#[must_use]
pub fn sentences(
    passage: &Passage,
    sentences: &[Sentence],
    glossary: &Glossary,
) -> Vec<Finding>
{
    let readings = readings(Text(&passage.text));
    let comment = passage.source == Source::Comment;
    let mut findings = Vec::new();
    let mut found = |rule: Rule, sentence: &str| {
        findings.push(Finding {
            path: passage.path.clone(),
            line: passage.line,
            rule,
            sentence: sentence.to_owned(),
        });
    };
    for sentence in sentences {
        let mut rules = broken(&readings, sentence, glossary, passage.source);
        let text = spoken(passage, sentence);
        if comment {
            rules.extend(referenced(Text(&text)));
        }
        for rule in rules {
            found(rule, &text);
        }
    }
    if comment && let Some(wall) = walled(&readings, sentences) {
        found(wall, &passage.text);
    }
    findings
}

/// The head and item findings of `shapes`, read over the parsed `passages`.
///
/// # Specification
/// - requires: `parsed` is the parse of `passages`, in the same order.
/// - ensures: one [`Rule::Head`] when a corpus head is not four paragraphs, nor
///   five whose fourth opens on `Limits:`, or a references line opens with none
///   of `- see:`, `- owes:` and `- cites:`. One [`Rule::Head`] at a `Limits:`
///   paragraph in another place. One [`Rule::Head`] at the `- cites:` line
///   whose label no footer line defines, or else at the footer line that gives
///   no quoted title. One [`Rule::What`] when that head's first sentence holds
///   more than twenty words. One [`Rule::Wall`] when an item comment holds more
///   than two sentences, unless it holds three and the third opens on
///   `Limits:`. The word count is the one [`words`] states.
/// - provides: the shape rules over the spaCy sentences.
/// - fails: never.
/// - panics: none.
/// - executable: none — the walk is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a head of three paragraphs, a first sentence of
///   twenty-one words, an item of three sentences, a citation with no footer
///   line and a footer line with no quoted title, each beside a twin that
///   holds. A head of five with its `Limits` paragraph in place and out of
///   place, and an item of three and of four sentences whose third opens on
///   `Limits:`. An off-by-one limit or a dropped citation verdict changes a
///   verdict.
/// - witness: `rules::tests::a_head_and_an_item_hold_their_sentence_counts`
#[inline]
#[must_use]
pub fn shaped(
    shapes: &[CommentShape],
    passages: &[Passage],
    parsed: &[&[Sentence]],
) -> Vec<Finding>
{
    let mut by_line = BTreeMap::new();
    for (passage, sentences) in passages.iter().zip(parsed) {
        by_line.insert((passage.path.as_str(), passage.line), (passage, *sentences));
    }
    let mut findings = Vec::new();
    for shape in shapes {
        if let Opened::Run(head) = shape.opened {
            let counted = match head.limits {
                Limits::None => head.paragraphs == HEAD_PARAGRAPHS,
                Limits::After => head.paragraphs == LIMITED_PARAGRAPHS,
                Limits::Misplaced(_) => true,
            };
            if !counted || head.references == References::Broken {
                findings.push(Finding {
                    path: shape.path.clone(),
                    line: head.line,
                    rule: Rule::Head,
                    sentence: "the head is not four paragraphs".to_owned(),
                });
            }
            if let Limits::Misplaced(line) = head.limits {
                findings.push(Finding {
                    path: shape.path.clone(),
                    line,
                    rule: Rule::Head,
                    sentence: "a `Limits:` paragraph stands only after the how paragraph"
                        .to_owned(),
                });
            }
            let cited = match head.references {
                References::Unfooted(line) => Some((
                    line,
                    "a `- cites:` label has no footer line `[label]: <URL> \"<authors>, <title>\"` at the run's end",
                )),
                References::Untitled(line) => Some((
                    line,
                    "a footer line gives no quoted title: write `[label]: <URL> \"<authors>, <title>\"`",
                )),
                References::Shaped | References::Broken => None,
            };
            if let Some((line, sentence)) = cited {
                findings.push(Finding {
                    path: shape.path.clone(),
                    line,
                    rule: Rule::Head,
                    sentence: sentence.to_owned(),
                });
            }
            if let WhatLine::At(line) = head.what
                && let Some(&(passage, sentences)) = by_line.get(&(shape.path.as_str(), line))
                && let Some(first) = sentences.first()
                && words(&readings(Text(&passage.text)), first).0 > WHAT_WORDS
            {
                findings.push(Finding {
                    path: shape.path.clone(),
                    line,
                    rule: Rule::What,
                    sentence: spoken(passage, first),
                });
            }
        }
        for item in &shape.items {
            let mut count = 0_usize;
            let mut third = None;
            let mut said = String::new();
            for line in &item.prose {
                let Some(&(passage, sentences)) = by_line.get(&(shape.path.as_str(), *line))
                else {
                    continue;
                };
                for sentence in sentences {
                    count = count.saturating_add(1);
                    if count == ITEM_SENTENCES.saturating_add(1) {
                        third = Some(sentence);
                    }
                }
                if !said.is_empty() {
                    said.push(' ');
                }
                said.push_str(&passage.text);
            }
            let limited = count == ITEM_SENTENCES.saturating_add(1)
                && third.is_some_and(|sentence| opening(sentence) == Opening::Limit);
            if count > ITEM_SENTENCES && !limited {
                findings.push(Finding {
                    path: shape.path.clone(),
                    line: item.line,
                    rule: Rule::Wall,
                    sentence: said,
                });
            }
        }
    }
    findings
}

/// Whether `sentence` is an imperative: its root is a bare verb with no
/// subject.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — `apply this edit` is an imperative and `the edit applies`
///   is not; reading the subject or the tag alone changes one.
/// - witness: `rules::tests::a_diagnostic_needs_its_what_where_and_imperative`
fn imperative(sentence: &Sentence) -> Agrees
{
    match sentence.root() {
        Maybe::Present(root)
            if root.tag == "VB"
                && !sentence
                    .children(root)
                    .any(|child| child.dep == "nsubj" || child.dep == "nsubjpass") =>
        {
            Agrees::Agrees
        },
        Maybe::Present(_) | Maybe::Absent(_) => Agrees::Differs,
    }
}

/// The procedural findings of `golden`, given its `help:` line's parse.
///
/// # Specification
/// - requires: `help` is the parse of the golden's `help:` passage, empty when
///   it has none.
/// - ensures: one [`Rule::Procedure`] finding, naming the headline, when the
///   golden labels no span, or its advice is missing, or its `help:` line's
///   first sentence is not an imperative. Advice tracked by an issue passes.
///   Then one [`Rule::Instructions`] finding for each sentence of the `help:`
///   line that holds two instructions ([`instructions`]), naming that sentence.
/// - provides: the procedural form over one diagnostic.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is the comparison itself.
///
/// # Adequacy
/// - hypothesis: L3 — a labelled golden with an imperative help, one tracked by
///   an issue, one whose help is a statement, one with no label and one whose
///   help holds two instructions; any part left unchecked changes a verdict.
/// - witness: `rules::tests::a_diagnostic_needs_its_what_where_and_imperative`
#[inline]
#[must_use]
pub fn procedure(
    golden: &Golden,
    help: &[Sentence],
) -> Vec<Finding>
{
    let advised = match golden.advice {
        Advice::Help(_) => help
            .first()
            .is_some_and(|sentence| imperative(sentence) == Agrees::Agrees),
        Advice::Tracked => true,
        Advice::Missing => false,
    };
    let mut findings = Vec::new();
    if golden.placed != Placed::Labelled || !advised {
        findings.push(Finding {
            path: golden.what.path.clone(),
            line: golden.what.line,
            rule: Rule::Procedure,
            sentence: golden.what.text.clone(),
        });
    }
    if let Advice::Help(ref advice) = golden.advice {
        let read = readings(Text(&advice.text));
        for sentence in help {
            if instructions(&read, sentence) == Agrees::Agrees {
                findings.push(Finding {
                    path: advice.path.clone(),
                    line: advice.line,
                    rule: Rule::Instructions,
                    sentence: spoken(advice, sentence),
                });
            }
        }
    }
    findings
}

#[cfg(test)]
mod tests
{
    use super::Fix;
    use super::RULES;
    use super::Rule;
    use super::procedure;
    use super::sentences;
    use super::shaped;
    use crate::glossary::Glossary;
    use crate::parse::Sentence;
    use crate::parse::Token;
    use crate::passage;
    use crate::passage::Advice;
    use crate::passage::CommentShape;
    use crate::passage::Golden;
    use crate::passage::Head;
    use crate::passage::Item;
    use crate::passage::Limits;
    use crate::passage::Opened;
    use crate::passage::Placed;
    use crate::passage::References;
    use crate::passage::Source;
    use crate::passage::Text;
    use crate::passage::WhatLine;

    /// A passage of `$text` and its one sentence, each token
    /// `(word, lemma, pos, tag, dep, head)`, offsets found in the text.
    macro_rules! parsed {
        ($text:expr, [$(($word:literal, $lemma:literal, $pos:literal, $tag:literal, $dep:literal, $head:literal)),* $(,)?]) => {{
            let text: &str = $text;
            let words: Vec<(&str, &str, &str, &str, &str, usize)> =
                vec![$(($word, $lemma, $pos, $tag, $dep, $head)),*];
            let mut from = 0_usize;
            let mut tokens = Vec::new();
            for (word, lemma, pos, tag, dep, head) in words {
                let at = text
                    .get(from..)
                    .and_then(|rest| rest.find(word))
                    .unwrap()
                    .saturating_add(from);
                from = at.saturating_add(word.len());
                tokens.push(Token {
                    text: word.to_owned(),
                    lemma: lemma.to_owned(),
                    pos: pos.to_owned(),
                    tag: tag.to_owned(),
                    dep: dep.to_owned(),
                    head,
                    offset: text.get(..at).unwrap().chars().count(),
                });
            }
            let passage = passage::comments(Text("corpus/a.gandr"), Text(&format!("/// {text}")))
                .into_iter()
                .next()
                .unwrap();
            (passage, Sentence { tokens })
        }};
    }

    /// The rules `$parsed` breaks under `$glossary`.
    macro_rules! rules {
        ($parsed:expr, $glossary:expr) => {{
            let (passage, sentence) = $parsed;
            sentences(&passage, &[sentence], $glossary)
                .into_iter()
                .map(|finding| finding.rule)
                .collect::<Vec<_>>()
        }};
    }

    #[test]
    fn each_rule_fires_on_its_sentence_and_not_on_its_twin()
    {
        let glossary = Glossary::read(Text("[words]\nreplay = \"verb\"\n")).unwrap();
        let none = Glossary::default();
        let passive = parsed!("The term is reduced by the kernel.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("term", "term", "NOUN", "NN", "nsubjpass", 3),
            ("is", "be", "AUX", "VBZ", "auxpass", 3),
            ("reduced", "reduce", "VERB", "VBN", "ROOT", 3),
            ("by", "by", "ADP", "IN", "agent", 3),
            ("the", "the", "DET", "DT", "det", 6),
            ("kernel", "kernel", "NOUN", "NN", "pobj", 4),
            (".", ".", "PUNCT", ".", "punct", 3),
        ]);
        let finding = {
            let (passage, sentence) = passive;
            sentences(&passage, &[sentence], &none)
        };
        assert_eq!(
            finding
                .iter()
                .map(|finding| (
                    finding.rule,
                    finding.sentence.as_str(),
                    finding.line.to_string()
                ))
                .collect::<Vec<_>>(),
            [(
                Rule::Passive,
                "The term is reduced by the kernel.",
                "1".to_owned()
            )]
        );
        let listed = parsed!("The rule is refused.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("rule", "rule", "NOUN", "NN", "nsubjpass", 3),
            ("is", "be", "AUX", "VBZ", "auxpass", 3),
            ("refused", "refuse", "VERB", "VBN", "ROOT", 3),
            (".", ".", "PUNCT", ".", "punct", 3),
        ]);
        assert_eq!(rules!(listed, &none), []);
        let past = parsed!("The kernel reduced the term.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 2),
            ("reduced", "reduce", "VERB", "VBD", "ROOT", 2),
            ("the", "the", "DET", "DT", "det", 4),
            ("term", "term", "NOUN", "NN", "dobj", 2),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(rules!(past, &none), [Rule::Tense]);
        let perfect = parsed!("The kernel has reduced it.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 3),
            ("has", "have", "AUX", "VBZ", "aux", 3),
            ("reduced", "reduce", "VERB", "VBN", "ROOT", 3),
            ("it", "it", "PRON", "PRP", "dobj", 3),
            (".", ".", "PUNCT", ".", "punct", 3),
        ]);
        assert_eq!(rules!(perfect, &none), [Rule::Complex]);
        let future = parsed!("The kernel will reduce it.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 3),
            ("will", "will", "AUX", "MD", "aux", 3),
            ("reduce", "reduce", "VERB", "VB", "ROOT", 3),
            ("it", "it", "PRON", "PRP", "dobj", 3),
            (".", ".", "PUNCT", ".", "punct", 3),
        ]);
        assert_eq!(rules!(future, &none), [Rule::Tense]);
        let progressive = parsed!("The kernel is reducing it.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 3),
            ("is", "be", "AUX", "VBZ", "aux", 3),
            ("reducing", "reduce", "VERB", "VBG", "ROOT", 3),
            ("it", "it", "PRON", "PRP", "dobj", 3),
            (".", ".", "PUNCT", ".", "punct", 3),
        ]);
        assert_eq!(
            rules!(progressive, &none),
            [Rule::Tense],
            "a progressive is a tense, not an `-ing` main verb"
        );
        let modal = parsed!("The term can be reduced.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("term", "term", "NOUN", "NN", "nsubjpass", 4),
            ("can", "can", "AUX", "MD", "aux", 4),
            ("be", "be", "AUX", "VB", "auxpass", 4),
            ("reduced", "reduce", "VERB", "VBN", "ROOT", 4),
            (".", ".", "PUNCT", ".", "punct", 4),
        ]);
        assert_eq!(rules!(modal, &none), [Rule::Passive, Rule::Complex]);
        let refused = parsed!("The term can be refused.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("term", "term", "NOUN", "NN", "nsubjpass", 4),
            ("can", "can", "AUX", "MD", "aux", 4),
            ("be", "be", "AUX", "VB", "auxpass", 4),
            ("refused", "refuse", "VERB", "VBN", "ROOT", 4),
            (".", ".", "PUNCT", ".", "punct", 4),
        ]);
        assert_eq!(
            rules!(refused, &none),
            [Rule::Complex],
            "a listed passive after a modal is still complex"
        );
        let was = parsed!("The term was reduced.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("term", "term", "NOUN", "NN", "nsubjpass", 3),
            ("was", "be", "AUX", "VBD", "auxpass", 3),
            ("reduced", "reduce", "VERB", "VBN", "ROOT", 3),
            (".", ".", "PUNCT", ".", "punct", 3),
        ]);
        assert_eq!(rules!(was, &none), [Rule::Passive, Rule::Tense]);
        let present = parsed!("The kernel reduces the term.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 2),
            ("reduces", "reduce", "VERB", "VBZ", "ROOT", 2),
            ("the", "the", "DET", "DT", "det", 4),
            ("term", "term", "NOUN", "NN", "dobj", 2),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(rules!(present, &none), []);
        let stack = parsed!("It reads the kernel term cache entry.", [
            ("It", "it", "PRON", "PRP", "nsubj", 1),
            ("reads", "read", "VERB", "VBZ", "ROOT", 1),
            ("the", "the", "DET", "DT", "det", 6),
            ("kernel", "kernel", "NOUN", "NN", "compound", 6),
            ("term", "term", "NOUN", "NN", "compound", 6),
            ("cache", "cache", "NOUN", "NN", "compound", 6),
            ("entry", "entry", "NOUN", "NN", "dobj", 1),
            (".", ".", "PUNCT", ".", "punct", 1),
        ]);
        assert_eq!(rules!(stack, &none), [Rule::NounStack]);
        let three = parsed!("It reads the term cache entry.", [
            ("It", "it", "PRON", "PRP", "nsubj", 1),
            ("reads", "read", "VERB", "VBZ", "ROOT", 1),
            ("the", "the", "DET", "DT", "det", 5),
            ("term", "term", "NOUN", "NN", "compound", 5),
            ("cache", "cache", "NOUN", "NN", "compound", 5),
            ("entry", "entry", "NOUN", "NN", "dobj", 1),
            (".", ".", "PUNCT", ".", "punct", 1),
        ]);
        assert_eq!(rules!(three, &none), []);
        let ing = parsed!("Checking the term.", [
            ("Checking", "check", "VERB", "VBG", "ROOT", 0),
            ("the", "the", "DET", "DT", "det", 2),
            ("term", "term", "NOUN", "NN", "dobj", 0),
            (".", ".", "PUNCT", ".", "punct", 0),
        ]);
        assert_eq!(rules!(ing, &none), [Rule::IngMain]);
        let clause = parsed!("It ends the run, checking the term.", [
            ("It", "it", "PRON", "PRP", "nsubj", 1),
            ("ends", "end", "VERB", "VBZ", "ROOT", 1),
            ("the", "the", "DET", "DT", "det", 3),
            ("run", "run", "NOUN", "NN", "dobj", 1),
            (",", ",", "PUNCT", ",", "punct", 1),
            ("checking", "check", "VERB", "VBG", "advcl", 1),
            ("the", "the", "DET", "DT", "det", 7),
            ("term", "term", "NOUN", "NN", "dobj", 5),
            (".", ".", "PUNCT", ".", "punct", 1),
        ]);
        assert_eq!(rules!(clause, &none), [Rule::IngMain]);
        let gerund = parsed!("It ends the checking.", [
            ("It", "it", "PRON", "PRP", "nsubj", 1),
            ("ends", "end", "VERB", "VBZ", "ROOT", 1),
            ("the", "the", "DET", "DT", "det", 3),
            ("checking", "checking", "NOUN", "NN", "dobj", 1),
            (".", ".", "PUNCT", ".", "punct", 1),
        ]);
        assert_eq!(rules!(gerund, &none), [], "an `-ing` noun is no clause");
        let phrasal = parsed!("The kernel hands it back.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 2),
            ("hands", "hand", "VERB", "VBZ", "ROOT", 2),
            ("it", "it", "PRON", "PRP", "dobj", 2),
            ("back", "back", "ADP", "RP", "prt", 2),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(rules!(phrasal, &none), [Rule::Phrasal]);
        let returned = parsed!("The kernel returns it.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 2),
            ("returns", "return", "VERB", "VBZ", "ROOT", 2),
            ("it", "it", "PRON", "PRP", "dobj", 2),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(rules!(returned, &none), []);
        let noun = parsed!("The replay ends.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("replay", "replay", "NOUN", "NN", "nsubj", 2),
            ("ends", "end", "VERB", "VBZ", "ROOT", 2),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(rules!(noun.clone(), &glossary), [Rule::Glossary]);
        assert_eq!(rules!(noun, &none), []);
        let verb = parsed!("The kernel replays it.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 2),
            ("replays", "replay", "VERB", "VBZ", "ROOT", 2),
            ("it", "it", "PRON", "PRP", "dobj", 2),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(rules!(verb, &glossary), []);
    }

    /// The rules `$parsed` breaks when its passage is a body's.
    macro_rules! bodied {
        ($parsed:expr) => {{
            let (passage, sentence) = $parsed;
            let passage = passage::Passage {
                source: Source::Body,
                ..passage
            };
            rules!((passage, sentence), &Glossary::default())
        }};
    }

    #[test]
    fn a_body_holds_its_length_semicolons_and_dashes()
    {
        let worded = |text: &str| {
            let mut offset = 0_usize;
            let tokens = text
                .split(' ')
                .enumerate()
                .map(|(at, word)| {
                    let root = at == 0;
                    let token = Token {
                        text: word.to_owned(),
                        lemma: word.to_owned(),
                        pos: if root { "VERB" } else { "NOUN" }.to_owned(),
                        tag: if root { "VBZ" } else { "NN" }.to_owned(),
                        dep: if root { "ROOT" } else { "dobj" }.to_owned(),
                        head: 0,
                        offset,
                    };
                    offset = offset
                        .saturating_add(word.chars().count())
                        .saturating_add(1);
                    token
                })
                .collect();
            let passage = passage::body(Text("pr.md"), Text(text))
                .into_iter()
                .next()
                .unwrap();
            (passage, Sentence { tokens })
        };
        let terms = |count: usize| vec!["term"; count].join(" ");
        assert_eq!(bodied!(worded(&format!("reads {}", terms(25)))), [
            Rule::Length
        ]);
        assert_eq!(bodied!(worded(&format!("reads {}", terms(24)))), []);
        assert_eq!(
            bodied!(worded(&format!("reads `x y z` {}", terms(23)))),
            [],
            "a code span is one word"
        );
        let joined = parsed!("It reads it; the cache holds it.", [
            ("It", "it", "PRON", "PRP", "nsubj", 1),
            ("reads", "read", "VERB", "VBZ", "ROOT", 1),
            ("it", "it", "PRON", "PRP", "dobj", 1),
            (";", ";", "PUNCT", ":", "punct", 1),
            ("the", "the", "DET", "DT", "det", 6),
            ("cache", "cache", "NOUN", "NN", "nsubj", 7),
            ("holds", "hold", "VERB", "VBZ", "conj", 1),
            ("it", "it", "PRON", "PRP", "dobj", 7),
            (".", ".", "PUNCT", ".", "punct", 1),
        ]);
        assert_eq!(bodied!(joined.clone()), [Rule::Semicolon]);
        assert_eq!(
            rules!(joined, &Glossary::default()),
            [Rule::Semicolon],
            "a corpus comment holds the body's rules"
        );
        let two = parsed!("Read the file and write the log.", [
            ("Read", "read", "VERB", "VB", "ROOT", 0),
            ("the", "the", "DET", "DT", "det", 2),
            ("file", "file", "NOUN", "NN", "dobj", 0),
            ("and", "and", "CCONJ", "CC", "cc", 0),
            ("write", "write", "VERB", "VB", "conj", 0),
            ("the", "the", "DET", "DT", "det", 6),
            ("log", "log", "NOUN", "NN", "dobj", 4),
            (".", ".", "PUNCT", ".", "punct", 0),
        ]);
        assert_eq!(bodied!(two.clone()), [Rule::Instructions]);
        assert_eq!(
            rules!(two, &Glossary::default()),
            [Rule::Instructions],
            "a corpus comment holds the two instructions too"
        );
        let either = parsed!("Read the file or write the log.", [
            ("Read", "read", "VERB", "VB", "ROOT", 0),
            ("the", "the", "DET", "DT", "det", 2),
            ("file", "file", "NOUN", "NN", "dobj", 0),
            ("or", "or", "CCONJ", "CC", "cc", 0),
            ("write", "write", "VERB", "VB", "conj", 0),
            ("the", "the", "DET", "DT", "det", 6),
            ("log", "log", "NOUN", "NN", "dobj", 4),
            (".", ".", "PUNCT", ".", "punct", 0),
        ]);
        assert_eq!(bodied!(either), [], "a choice is one instruction");
        let stated = parsed!("The kernel reads and writes the log.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 2),
            ("reads", "read", "VERB", "VBZ", "ROOT", 2),
            ("and", "and", "CCONJ", "CC", "cc", 2),
            ("writes", "write", "VERB", "VBZ", "conj", 2),
            ("the", "the", "DET", "DT", "det", 6),
            ("log", "log", "NOUN", "NN", "dobj", 4),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(bodied!(stated), [], "a statement holds no instruction");
        let handed = parsed!("The kernel hands it back.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 2),
            ("hands", "hand", "VERB", "VBZ", "ROOT", 2),
            ("it", "it", "PRON", "PRP", "dobj", 2),
            ("back", "back", "ADP", "RP", "prt", 2),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(
            bodied!(handed),
            [],
            "a body is not held to the phrasal verb"
        );
        let closing = parsed!("It reads a term;", [
            ("It", "it", "PRON", "PRP", "nsubj", 1),
            ("reads", "read", "VERB", "VBZ", "ROOT", 1),
            ("a", "a", "DET", "DT", "det", 3),
            ("term", "term", "NOUN", "NN", "dobj", 1),
            (";", ";", "PUNCT", ":", "punct", 1),
        ]);
        assert_eq!(bodied!(closing), []);
        let clause = parsed!("The kernel stops — the cache holds it.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 2),
            ("stops", "stop", "VERB", "VBZ", "ROOT", 2),
            ("—", "—", "PUNCT", ":", "punct", 2),
            ("the", "the", "DET", "DT", "det", 5),
            ("cache", "cache", "NOUN", "NN", "nsubj", 6),
            ("holds", "hold", "VERB", "VBZ", "parataxis", 2),
            ("it", "it", "PRON", "PRP", "dobj", 6),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(bodied!(clause), [Rule::Dash]);
        let phrase = parsed!("The kernel reads one value — the term.", [
            ("The", "the", "DET", "DT", "det", 1),
            ("kernel", "kernel", "NOUN", "NN", "nsubj", 2),
            ("reads", "read", "VERB", "VBZ", "ROOT", 2),
            ("one", "one", "NUM", "CD", "nummod", 4),
            ("value", "value", "NOUN", "NN", "dobj", 2),
            ("—", "—", "PUNCT", ":", "punct", 4),
            ("the", "the", "DET", "DT", "det", 7),
            ("term", "term", "NOUN", "NN", "appos", 4),
            (".", ".", "PUNCT", ".", "punct", 2),
        ]);
        assert_eq!(bodied!(phrase), []);
        let stack = parsed!("It reads the kernel term cache entry.", [
            ("It", "it", "PRON", "PRP", "nsubj", 1),
            ("reads", "read", "VERB", "VBZ", "ROOT", 1),
            ("the", "the", "DET", "DT", "det", 6),
            ("kernel", "kernel", "NOUN", "NN", "compound", 6),
            ("term", "term", "NOUN", "NN", "compound", 6),
            ("cache", "cache", "NOUN", "NN", "compound", 6),
            ("entry", "entry", "NOUN", "NN", "dobj", 1),
            (".", ".", "PUNCT", ".", "punct", 1),
        ]);
        assert_eq!(bodied!(stack), [], "a body keeps no noun-stack rule");
    }

    /// A comment passage of the one line `text` and its sentences, a sentence
    /// ending at each word that ends in `.`, its first word a verb and the rest
    /// adverbs under it, so no noun stacks.
    ///
    /// # Specification
    /// trivial.
    fn said(text: Text<'_>) -> (passage::Passage, Vec<Sentence>)
    {
        let text = text.0;
        let passage = passage::comments(Text("corpus/a.gandr"), Text(&format!("/// {text}")))
            .into_iter()
            .next()
            .unwrap();
        let mut sentences: Vec<Sentence> = Vec::new();
        let mut open = true;
        let mut offset = 0_usize;
        for word in text.split(' ') {
            if open {
                sentences.push(Sentence { tokens: Vec::new() });
            }
            let tokens = &mut sentences.last_mut().unwrap().tokens;
            let root = tokens.is_empty();
            tokens.push(Token {
                text: word.to_owned(),
                lemma: word.to_owned(),
                pos: if root { "VERB" } else { "ADV" }.to_owned(),
                tag: if root { "VBZ" } else { "RB" }.to_owned(),
                dep: if root { "ROOT" } else { "advmod" }.to_owned(),
                head: 0,
                offset,
            });
            offset = offset
                .saturating_add(word.chars().count())
                .saturating_add(1);
            open = word.ends_with('.');
        }
        (passage, sentences)
    }

    /// The rules `text`, said in a comment or, with `source`, elsewhere,
    /// breaks.
    ///
    /// # Specification
    /// trivial.
    fn commented(
        text: Text<'_>,
        source: Source,
    ) -> Vec<Rule>
    {
        let (passage, said) = said(text);
        let passage = passage::Passage { source, ..passage };
        sentences(&passage, &said, &Glossary::default())
            .into_iter()
            .map(|finding| finding.rule)
            .collect()
    }

    #[test]
    fn a_comment_holds_the_body_rules_its_references_and_walls()
    {
        let terms = |count: usize| vec!["term"; count].join(" ");
        assert_eq!(
            commented(Text(&format!("Reads {}.", terms(25))), Source::Comment),
            [Rule::Length],
            "a comment's sentence holds the body's length"
        );
        for reference in [
            "Reads the term (#12).",
            "Reads `crates/workflow-prose/src/rules.rs` today.",
            "Reads [#4900] today.",
            "Reads https://example.org now.",
            "Reads the twin pathological/a.gandr now.",
            "Reads the families (doi:10.1007/BF01211308) now.",
            "Reads the path types, arXiv:2501.11620, now.",
            "Reads 10.1145/96709.96718 now.",
            "Reads the families (Dybjer, _Inductive families_, 1994) now.",
            "Reads the case (Levy, \"Call-By-Push-Value\", 2003) now.",
            "Reads the attribute (after `#[doc]`, _The Rust Reference_) now.",
        ] {
            assert_eq!(
                commented(Text(reference), Source::Comment),
                [Rule::InlineReference],
                "{reference:?} names a reference in a comment"
            );
            assert_eq!(
                commented(Text(reference), Source::Body),
                [],
                "{reference:?} stands in a body"
            );
        }
        for plain in [
            "Reads A/B here.",
            "Reads #[cfg] here.",
            "Reads # here.",
            "Reads #x here.",
            "Reads 10.5 here.",
            "Reads _Stressed_ here.",
            "Reads `f(x, \"Hello\")` here.",
            "Reads the greeting (\"Hello\") here.",
            "Reads doi: here.",
        ] {
            assert_eq!(
                commented(Text(plain), Source::Comment),
                [],
                "{plain:?} names no reference"
            );
        }
        let five = "Reads one. Reads two. Reads three. Reads four. Reads five.";
        assert_eq!(
            commented(Text(five), Source::Comment),
            [],
            "five sentences are no wall"
        );
        let split = "Reads `a. b` one. Reads two. Reads three. Reads four. Reads five.";
        assert_eq!(
            commented(Text(split), Source::Comment),
            [],
            "a parse split inside a code span ends no sentence"
        );
        let six = format!("{five} Reads six.");
        assert_eq!(commented(Text(&six), Source::Comment), [Rule::Wall]);
        assert_eq!(
            commented(Text(&six), Source::Body),
            [],
            "a body keeps no wall rule"
        );
        let (passage, said) = said(Text(&six));
        let wall = sentences(&passage, &said, &Glossary::default());
        assert_eq!(
            wall.iter()
                .map(|finding| finding.sentence.as_str())
                .collect::<Vec<_>>(),
            [six.as_str()],
            "the wall names the whole paragraph"
        );
    }

    #[test]
    fn code_and_quotations_are_not_read()
    {
        let none = Glossary::default();
        let coded = parsed!("Then `x is reduced` holds.", [
            ("Then", "then", "ADV", "RB", "advmod", 5),
            ("x", "x", "NOUN", "NN", "nsubjpass", 3),
            ("is", "be", "AUX", "VBZ", "auxpass", 3),
            ("reduced", "reduce", "VERB", "VBN", "ccomp", 5),
            ("`", "`", "PUNCT", "``", "punct", 5),
            ("holds", "hold", "VERB", "VBZ", "ROOT", 5),
            (".", ".", "PUNCT", ".", "punct", 5),
        ]);
        assert_eq!(rules!(coded, &none), []);
        let quoted = parsed!("\"Reduced\" names it.", [
            ("Reduced", "reduce", "VERB", "VBD", "ROOT", 0),
            ("names", "name", "VERB", "VBZ", "dep", 0),
            ("it", "it", "PRON", "PRP", "dobj", 1),
            (".", ".", "PUNCT", ".", "punct", 0),
        ]);
        assert_eq!(rules!(quoted, &none), []);
    }

    #[test]
    fn a_diagnostic_needs_its_what_where_and_imperative()
    {
        let what = passage::comments(Text("g.txt"), Text("/// mismatched types"))
            .into_iter()
            .next()
            .unwrap();
        let help_passage = passage::Passage {
            source: Source::Diagnostic,
            ..what.clone()
        };
        let golden = |placed: Placed, advice: Advice| Golden {
            what: what.clone(),
            placed,
            advice,
        };
        let (_, apply) = parsed!("apply this edit", [
            ("apply", "apply", "VERB", "VB", "ROOT", 0),
            ("this", "this", "DET", "DT", "det", 2),
            ("edit", "edit", "NOUN", "NN", "dobj", 0),
        ]);
        let (_, stated) = parsed!("the edit applies", [
            ("the", "the", "DET", "DT", "det", 1),
            ("edit", "edit", "NOUN", "NN", "nsubj", 2),
            ("applies", "apply", "VERB", "VBZ", "ROOT", 2),
        ]);
        let helped = Advice::Help(help_passage.clone());
        assert_eq!(
            procedure(
                &golden(Placed::Labelled, helped.clone()),
                core::slice::from_ref(&apply)
            ),
            []
        );
        assert_eq!(
            procedure(&golden(Placed::Labelled, Advice::Tracked), &[]),
            []
        );
        for (placed, advice, help) in [
            (Placed::Labelled, helped.clone(), stated),
            (Placed::Labelled, Advice::Missing, Sentence::default()),
            (Placed::Unlabelled, helped, apply),
        ] {
            let findings = procedure(&golden(placed, advice.clone()), &[help]);
            assert_eq!(
                findings
                    .iter()
                    .map(|finding| (finding.rule, finding.sentence.as_str()))
                    .collect::<Vec<_>>(),
                [(Rule::Procedure, "mismatched types")],
                "{placed:?} {advice:?}"
            );
        }
        let (_, twice) = parsed!("apply this edit and rerun it", [
            ("apply", "apply", "VERB", "VB", "ROOT", 0),
            ("this", "this", "DET", "DT", "det", 2),
            ("edit", "edit", "NOUN", "NN", "dobj", 0),
            ("and", "and", "CCONJ", "CC", "cc", 0),
            ("rerun", "rerun", "VERB", "VB", "conj", 0),
            ("it", "it", "PRON", "PRP", "dobj", 4),
        ]);
        let two_passage = passage::Passage {
            text: "apply this edit and rerun it".to_owned(),
            ..help_passage
        };
        assert_eq!(
            procedure(&golden(Placed::Labelled, Advice::Help(two_passage)), &[
                twice
            ])
            .iter()
            .map(|finding| (finding.rule, finding.sentence.as_str()))
            .collect::<Vec<_>>(),
            [(Rule::Instructions, "apply this edit and rerun it")],
            "a help line holds one instruction"
        );
    }

    #[test]
    fn a_head_and_an_item_hold_their_sentence_counts()
    {
        let tokens = |count: usize| {
            (0 .. count)
                .map(|at| Token {
                    text: "term".to_owned(),
                    lemma: "term".to_owned(),
                    pos: "NOUN".to_owned(),
                    tag: "NN".to_owned(),
                    dep: if at == 0 { "ROOT" } else { "dobj" }.to_owned(),
                    head: 0,
                    offset: 0,
                })
                .collect()
        };
        let passage = |text: &str| {
            passage::comments(Text("corpus/a.gandr"), Text(text))
                .into_iter()
                .next()
                .unwrap()
        };
        let shape =
            |paragraphs: usize, references: References, what: WhatLine, items: Vec<Item>| {
                CommentShape {
                    path: "corpus/a.gandr".to_owned(),
                    opened: Opened::Run(Head {
                        line: passage("/// term\n").line,
                        paragraphs,
                        references,
                        what,
                        limits: Limits::None,
                    }),
                    items,
                }
            };
        let rules_of =
            |shape: CommentShape, passages: Vec<passage::Passage>, parsed: Vec<Vec<Sentence>>| {
                let borrowed: Vec<&[Sentence]> = parsed.iter().map(Vec::as_slice).collect();
                shaped(core::slice::from_ref(&shape), &passages, &borrowed)
                    .into_iter()
                    .map(|finding| finding.rule)
                    .collect::<Vec<_>>()
            };
        let long = passage("/// term\n");
        let long_line = long.line;
        let long_parse = vec![Sentence { tokens: tokens(21) }];
        assert_eq!(
            rules_of(
                shape(4, References::Shaped, WhatLine::At(long_line), Vec::new()),
                vec![long],
                vec![long_parse]
            ),
            [Rule::What]
        );
        let short = passage("/// term\n");
        let short_line = short.line;
        let short_parse = vec![Sentence { tokens: tokens(20) }];
        assert_eq!(
            rules_of(
                shape(4, References::Shaped, WhatLine::At(short_line), Vec::new()),
                vec![short],
                vec![short_parse]
            ),
            []
        );
        assert_eq!(
            rules_of(
                shape(3, References::Shaped, WhatLine::None, Vec::new()),
                Vec::new(),
                Vec::new()
            ),
            [Rule::Head]
        );
        assert_eq!(
            rules_of(
                shape(4, References::Broken, WhatLine::None, Vec::new()),
                Vec::new(),
                Vec::new()
            ),
            [Rule::Head]
        );
        let at = passage("/// term\n").line;
        for cited in [References::Unfooted(at), References::Untitled(at)] {
            let held = shape(4, cited, WhatLine::None, Vec::new());
            assert_eq!(
                shaped(core::slice::from_ref(&held), &[], &[])
                    .iter()
                    .map(|finding| (finding.rule, finding.line))
                    .collect::<Vec<_>>(),
                [(Rule::Head, at)],
                "{cited:?} is refused once, at its line"
            );
        }
        let item = passage("/// One. Two. Three.\n");
        let item_line = item.line;
        let item_parse = vec![
            Sentence { tokens: tokens(1) },
            Sentence { tokens: tokens(1) },
            Sentence { tokens: tokens(1) },
        ];
        assert_eq!(
            rules_of(
                shape(4, References::Shaped, WhatLine::None, vec![Item {
                    line: item_line,
                    prose: vec![item_line],
                }]),
                vec![item],
                vec![item_parse]
            ),
            [Rule::Wall]
        );
        let held = passage("/// One. Two.\n");
        let held_line = held.line;
        let held_parse = vec![Sentence { tokens: tokens(1) }, Sentence {
            tokens: tokens(1),
        }];
        assert_eq!(
            rules_of(
                shape(4, References::Shaped, WhatLine::None, vec![Item {
                    line: held_line,
                    prose: vec![held_line],
                }]),
                vec![held],
                vec![held_parse]
            ),
            []
        );
        let limited = |paragraphs: usize, limits: Limits| CommentShape {
            path: "corpus/a.gandr".to_owned(),
            opened: Opened::Run(Head {
                line: passage("/// term\n").line,
                paragraphs,
                references: References::Shaped,
                what: WhatLine::None,
                limits,
            }),
            items: Vec::new(),
        };
        assert_eq!(
            rules_of(limited(5, Limits::After), Vec::new(), Vec::new()),
            [],
            "a head of five holds with its `Limits` paragraph after the how paragraph"
        );
        assert_eq!(
            rules_of(limited(5, Limits::None), Vec::new(), Vec::new()),
            [Rule::Head],
            "a head of five with no `Limits` paragraph is refused"
        );
        let misplaced = passage("/// term\n").line;
        assert_eq!(
            shaped(
                core::slice::from_ref(&limited(5, Limits::Misplaced(misplaced))),
                &[],
                &[]
            )
            .iter()
            .map(|finding| (finding.rule, finding.line))
            .collect::<Vec<_>>(),
            [(Rule::Head, misplaced)],
            "a misplaced `Limits` paragraph is refused once, at its line"
        );
        let opening = |words: &[&str]| Sentence {
            tokens: words
                .iter()
                .enumerate()
                .map(|(at, word)| Token {
                    text: (*word).to_owned(),
                    lemma: (*word).to_owned(),
                    pos: "NOUN".to_owned(),
                    tag: "NN".to_owned(),
                    dep: if at == 0 { "ROOT" } else { "dobj" }.to_owned(),
                    head: 0,
                    offset: 0,
                })
                .collect(),
        };
        let item_of = |parse: Vec<Sentence>| {
            let item = passage("/// One. Two. Limits: three. Four.\n");
            let line = item.line;
            rules_of(
                shape(4, References::Shaped, WhatLine::None, vec![Item {
                    line,
                    prose: vec![line],
                }]),
                vec![item],
                vec![parse],
            )
        };
        let one = || Sentence { tokens: tokens(1) };
        assert_eq!(
            item_of(vec![one(), one(), opening(&["Limits", ":", "three"])]),
            [],
            "an item of three sentences holds when the third opens on `Limits:`"
        );
        assert_eq!(
            item_of(vec![
                one(),
                one(),
                opening(&["Limits", ":", "three"]),
                one()
            ]),
            [Rule::Wall],
            "an item of four sentences is refused, a `Limits:` third or not"
        );
        assert_eq!(
            item_of(vec![one(), one(), opening(&["Limited", ":", "three"])]),
            [Rule::Wall],
            "an item of three sentences whose third opens otherwise is refused"
        );
    }

    #[test]
    fn every_rule_reads_back_and_states_its_fix()
    {
        for rule in RULES {
            assert_eq!(rule.to_string().parse::<Rule>(), Ok(rule));
            assert!(!Fix(rule).to_string().is_empty(), "{rule:?}");
        }
        assert_eq!(
            Fix(Rule::Tense).to_string(),
            "state it in the present tense"
        );
        assert!("Unknown".parse::<Rule>().is_err());
    }
}
