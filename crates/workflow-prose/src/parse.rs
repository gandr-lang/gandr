//! The parse: each passage's sentences and tokens as spaCy reads them, through
//! the parse script the pinned spaCy venv's interpreter runs.
//!
//! The script, `parse.py` beside this crate's manifest, reads the passages as
//! a JSON array on standard input and prints, for each, its sentences, each a
//! list of tokens. The crate applies every rule to that first-order data, so a
//! rule is tested on a hand-written sentence without Python.

use std::io::Write as _;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;

use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::error::ProseError;
use crate::passage::Passage;

/// One token of a parsed sentence.
///
/// # Specification
/// - provides: what a rule reads of a word: its spelling, lemma, tags,
///   dependency, head and place in the passage.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token
{
    /// The word as written.
    pub text: String,
    /// Its lemma.
    pub lemma: String,
    /// Its coarse part of speech: `NOUN`, `VERB`, `PROPN` and so on.
    pub pos: String,
    /// Its fine tag: `VBD`, `VBN`, `VBG`, `VB` and so on.
    pub tag: String,
    /// Its dependency label: `ROOT`, `nsubj`, `auxpass` and so on.
    pub dep: String,
    /// Its head, as an index into the sentence's tokens.
    pub head: usize,
    /// Its first character's index in the passage.
    pub offset: usize,
}

/// One token as the script prints it: text, lemma, coarse tag, fine tag,
/// dependency, head relative to the sentence's start, and character offset.
#[derive(Debug, Deserialize)]
struct Printed(String, String, String, String, String, i64, usize);

/// One parsed sentence.
///
/// # Specification
/// - provides: the unit every sentence rule judges.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Sentence
{
    /// Its tokens, in order.
    pub tokens: Vec<Token>,
}

/// Why a sentence has no root.
///
/// # Specification
/// - provides: the one way a sentence lacks its root.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rootless
{
    /// No token carries the `ROOT` dependency.
    NoRootToken,
}

impl Sentence
{
    /// The sentence's root token.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the tense, `-ing` and imperative rules read the root,
    ///   so another token changes their verdicts.
    /// - witness: `rules::tests::each_rule_fires_on_its_sentence_and_not_on_its_twin`
    #[inline]
    pub fn root(&self) -> Maybe<&Token, Rootless>
    {
        self.tokens
            .iter()
            .find(|token| token.dep == "ROOT")
            .map_or(Maybe::Absent(Rootless::NoRootToken), Maybe::Present)
    }

    /// The tokens whose head is `head`, `head` itself left out.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the tense and imperative rules read the root's
    ///   auxiliaries and subject; a child of another token changes them.
    /// - witness: `rules::tests::each_rule_fires_on_its_sentence_and_not_on_its_twin`
    #[inline]
    pub fn children<'sentence>(
        &'sentence self,
        head: &'sentence Token,
    ) -> impl Iterator<Item = &'sentence Token>
    {
        let index = self
            .tokens
            .iter()
            .position(|token| token.offset == head.offset);
        self.tokens
            .iter()
            .enumerate()
            .filter(move |&(at, token)| Some(token.head) == index && Some(at) != index)
            .map(|(_, token)| token)
    }
}

/// Each passage's sentences, parsed by running `python` on `script` with the
/// passages on standard input.
///
/// # Specification
/// - requires: `python` can import spaCy and `en_core_web_sm`.
/// - ensures: one vector of sentences per passage, in order; each token's head
///   is an index into its own sentence, a head the script places outside its
///   sentence read as the token itself.
/// - provides: the parse every rule reads.
/// - fails: [`ProseError::Parse`] when the interpreter cannot start, its input
///   cannot be written, it exits unsuccessfully, or it prints what is not one
///   list of sentences per passage.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake interpreter printing two passages' sentences and
///   one failing with a message; a passage's sentences misattributed, a lost
///   message or a short reply accepted changes the result.
/// - witness: `tests::cli::a_new_finding_is_refused_with_its_fix`
/// - witness: `tests::cli::a_failing_parse_is_reported_with_its_message`
#[inline]
pub fn parse(
    python: &Path,
    script: &Path,
    passages: &[&Passage],
) -> Result<Vec<Vec<Sentence>>, ProseError>
{
    let mut command = Command::new(python);
    command.arg(script);
    let label = format!("{command:?}");
    let refuse = |message: String| ProseError::Parse {
        command: label.clone(),
        message,
    };
    let input = serde_json::to_string(
        &passages
            .iter()
            .map(|passage| passage.text.as_str())
            .collect::<Vec<_>>(),
    )
    .map_err(|error| refuse(error.to_string()))?;
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| refuse(error.to_string()))?;
    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(input.as_bytes())
            .map_err(|error| refuse(error.to_string()))?;
    }
    let output = child
        .wait_with_output()
        .map_err(|error| refuse(error.to_string()))?;
    if !output.status.success() {
        return Err(refuse(format!(
            "{}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    let printed: Vec<Vec<Vec<Printed>>> =
        serde_json::from_slice(&output.stdout).map_err(|error| refuse(error.to_string()))?;
    if printed.len() != passages.len() {
        return Err(refuse(format!(
            "{} passages parsed for {} given",
            printed.len(),
            passages.len()
        )));
    }
    Ok(printed
        .into_iter()
        .map(|sentences| {
            sentences
                .into_iter()
                .map(|tokens| {
                    let count = tokens.len();
                    Sentence {
                        tokens: tokens
                            .into_iter()
                            .enumerate()
                            .map(
                                |(at, Printed(text, lemma, pos, tag, dep, head, offset))| Token {
                                    text,
                                    lemma,
                                    pos,
                                    tag,
                                    dep,
                                    head: usize::try_from(head)
                                        .ok()
                                        .filter(|&head| head < count)
                                        .unwrap_or(at),
                                    offset,
                                },
                            )
                            .collect(),
                    }
                })
                .collect()
        })
        .collect())
}
