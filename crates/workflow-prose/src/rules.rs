//! The sentence rules and the procedural form, judged over the parse.
//!
//! Text inside backticks is code and no rule reads it; text inside double
//! quotes is a quotation, which the tense rule leaves alone. Each finding
//! names its rule, and the rule's fix is the line
//! `crates/workflow-prose/README.md` § Rules states.

use core::fmt;
use core::str::FromStr;

use quenchant_shape::shape::Maybe;

use crate::glossary::Agrees;
use crate::glossary::Glossary;
use crate::glossary::Tag;
use crate::parse::Sentence;
use crate::parse::Token;
use crate::passage::Advice;
use crate::passage::Golden;
use crate::passage::Line;
use crate::passage::Passage;
use crate::passage::Placed;
use crate::passage::Text;

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

/// A rule a sentence or a diagnostic is held to.
///
/// # Specification
/// - provides: the rule a finding names and the ledger keys.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Rule
{
    /// A passive outside the stated list.
    Passive,
    /// A main verb in a past form.
    Tense,
    /// Four or more nouns in a row.
    NounStack,
    /// An `-ing` form as the main verb.
    IngMain,
    /// A glossary word in a part of speech the glossary refuses.
    Glossary,
    /// A diagnostic without its what, its where or its what-to-do.
    Procedure,
}

/// Every rule, in the order they are stated.
const RULES: [Rule; 6] = [
    Rule::Passive,
    Rule::Tense,
    Rule::NounStack,
    Rule::IngMain,
    Rule::Glossary,
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
            Self::Passive => "Passive",
            Self::Tense => "Tense",
            Self::NounStack => "NounStack",
            Self::IngMain => "IngMain",
            Self::Glossary => "Glossary",
            Self::Procedure => "Procedure",
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
            Rule::NounStack => "break the stack of nouns with a preposition or a verb",
            Rule::IngMain => "make the main verb a finite verb, not an `-ing` form",
            Rule::Glossary => {
                "use the glossary word only as its part of speech, or choose another word"
            },
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

/// The rules `sentence` breaks, each at most once.
///
/// # Specification
/// - requires: `sentence` is a sentence of the passage `readings` was taken
///   from.
/// - ensures: in the order of [`RULES`], [`Rule::Passive`] when a token in
///   prose is `auxpass` and its head's lemma is not on the passive list;
///   [`Rule::Tense`] when the root, in prose, is tagged `VBD`, or `VBN` with no
///   present-tense `auxpass` child; [`Rule::NounStack`] when more than three
///   consecutive tokens in prose are `NOUN` or `PROPN`; [`Rule::IngMain`] when
///   the root, in prose, is tagged `VBG`; [`Rule::Glossary`] when a token in
///   prose has a lemma the glossary holds and a coarse tag its part of speech
///   does not admit.
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
fn broken(
    readings: &[Reading],
    sentence: &Sentence,
    glossary: &Glossary,
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
    let present_passive = |root: &Token| {
        sentence
            .children(root)
            .any(|child| child.dep == "auxpass" && (child.tag == "VBZ" || child.tag == "VBP"))
    };
    if root.is_some_and(|root| root.tag == "VBD" || (root.tag == "VBN" && !present_passive(root))) {
        rules.push(Rule::Tense);
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
    if root.is_some_and(|root| root.tag == "VBG") {
        rules.push(Rule::IngMain);
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
    rules
}

/// The findings of `passage`'s `sentences`.
///
/// # Specification
/// - requires: `sentences` are the passage's parse.
/// - ensures: one finding per rule each sentence breaks, in sentence order,
///   each naming the passage's path and line and the sentence's text.
/// - provides: the sentence rules over one passage.
/// - fails: never.
/// - panics: none.
/// - executable: none — the walk is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — as the private rules.
/// - witness: `rules::tests::each_rule_fires_on_its_sentence_and_not_on_its_twin`
#[inline]
#[must_use]
pub fn sentences(
    passage: &Passage,
    sentences: &[Sentence],
    glossary: &Glossary,
) -> Vec<Finding>
{
    let readings = readings(Text(&passage.text));
    let mut findings = Vec::new();
    for sentence in sentences {
        let rules = broken(&readings, sentence, glossary);
        if rules.is_empty() {
            continue;
        }
        let text = spoken(passage, sentence);
        for rule in rules {
            findings.push(Finding {
                path: passage.path.clone(),
                line: passage.line,
                rule,
                sentence: text.clone(),
            });
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

/// The procedural finding of `golden`, given its `help:` line's parse.
///
/// # Specification
/// - requires: `help` is the parse of the golden's `help:` passage, empty when
///   it has none.
/// - ensures: one [`Rule::Procedure`] finding, naming the headline, when the
///   golden labels no span, or its advice is missing, or its `help:` line's
///   first sentence is not an imperative; none otherwise. Advice tracked by an
///   issue passes.
/// - provides: the procedural form over one diagnostic.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is the comparison itself.
///
/// # Adequacy
/// - hypothesis: L3 — a labelled golden with an imperative help, one tracked by
///   an issue, one whose help is a statement and one with no label; any part
///   left unchecked changes a verdict.
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
    if golden.placed == Placed::Labelled && advised {
        return Vec::new();
    }
    vec![Finding {
        path: golden.what.path.clone(),
        line: golden.what.line,
        rule: Rule::Procedure,
        sentence: golden.what.text.clone(),
    }]
}

#[cfg(test)]
mod tests
{
    use super::Fix;
    use super::RULES;
    use super::Rule;
    use super::procedure;
    use super::sentences;
    use crate::glossary::Glossary;
    use crate::parse::Sentence;
    use crate::parse::Token;
    use crate::passage;
    use crate::passage::Advice;
    use crate::passage::Golden;
    use crate::passage::Placed;
    use crate::passage::Source;
    use crate::passage::Text;

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
        assert_eq!(rules!(perfect, &none), [Rule::Tense]);
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
        let helped = Advice::Help(help_passage);
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
    }

    #[test]
    fn every_rule_reads_back_and_states_its_fix()
    {
        for rule in RULES {
            assert_eq!(rule.to_string().parse::<Rule>(), Ok(rule));
            assert!(!Fix(rule).to_string().is_empty());
        }
        assert_eq!(
            Fix(Rule::Tense).to_string(),
            "state it in the present tense"
        );
        assert!("Unknown".parse::<Rule>().is_err());
    }
}
