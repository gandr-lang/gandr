//! The parse: each passage's sentences and tokens as spaCy reads them, through
//! the parse script the pinned spaCy venv's interpreter runs.
//!
//! The script, `parse.py` beside this crate's manifest, reads the passages as
//! a JSON array on standard input and prints, for each, one line: its
//! sentences, each a list of tokens. The crate reads each line as it comes,
//! so a passage is judged before the last one parses. The crate applies every
//! rule to that first-order data, so a rule is tested on a hand-written
//! sentence without Python. The cache keeps each passage's line by its text's
//! digest, so the script reads only the texts the cache misses.

use std::collections::HashMap;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Write as _;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;

use quenchant_shape::shape::Maybe;
use serde::Deserialize;
use serde::Serialize;

use crate::cache::Cache;
use crate::cache::Keeping;
use crate::cache::Kept;
use crate::digest::Digest;
use crate::error::ProseError;
use crate::passage::Passage;
use crate::passage::Text;

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
/// The cache keeps a passage's parse in the same form.
#[derive(Clone, Debug, Deserialize, Serialize)]
struct Printed(String, String, String, String, String, i64, usize);

/// One passage's parse as the script prints it: its sentences, each a list of
/// tokens.
type Printing = Vec<Vec<Printed>>;

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

/// What a run parsed afresh.
///
/// # Specification
/// - provides: the words a gate's wall stands beside, and the parses the cache
///   could not keep.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Fresh
{
    /// The passages the cache did not hold, each text once.
    pub passages: usize,
    /// Their words, split at white space.
    pub words: usize,
    /// The fresh parses the cache could not keep.
    pub unkept: usize,
}

/// Each passage's sentences, with what the parser read afresh.
///
/// # Specification
/// - provides: what [`parse`] answers.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Parsed
{
    /// One vector of sentences per passage, in the order given.
    pub sentences: Vec<Vec<Sentence>>,
    /// What the parser read, the cache's entries left out.
    pub fresh: Fresh,
}

/// Each passage's sentences, read from `cache` where it keeps them and parsed
/// by running `python` on `script` where it does not; `judge` reads each
/// passage's sentences as soon as they are known.
///
/// # Specification
/// - requires: `python` can import spaCy and `en_core_web_sm` when a passage
///   misses the cache.
/// - ensures: one vector of sentences per passage, in order; each token's head
///   is an index into its own sentence, a head the script places outside its
///   sentence read as the token itself. The script runs once, on each text the
///   cache misses, each distinct text once, and not at all when every text
///   hits. Each fresh parse is kept by its text's digest. An entry whose text
///   the crate cannot read is a miss. `judge` reads each passage once: a hit
///   before the script starts, and a miss as the script's line for its text
///   arrives.
/// - provides: the parse every rule reads, and the first finding before the
///   last passage parses.
/// - fails: [`ProseError::Parse`] when the interpreter cannot start, its input
///   cannot be written, it exits unsuccessfully, or it prints what is not one
///   line of sentences per text; every refusal of `judge`.
/// - panics: none.
/// - executable: none — the outcome is the external process's and the file
///   system's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the digests, the parses and the texts to parse, growth within
///   the passages given
///
/// # Adequacy
/// - hypothesis: L3 — a fake interpreter that saves its input and prints one
///   line per text, or fails with a message; a second run over the same
///   passages starts no interpreter and judges alike, a repeated text parses
///   once, and a damaged entry parses again; a passage's sentences
///   misattributed, a lost message, a short reply accepted, a second run that
///   parses or a damaged entry read as a parse changes the result.
/// - witness: `tests::cli::a_new_finding_is_refused_with_its_fix`
/// - witness: `tests::cli::a_failing_parse_is_reported_with_its_message`
/// - witness: `tests::cli::a_second_run_reads_every_parse_from_the_cache`
#[inline]
pub fn parse<Judge>(
    python: &Path,
    script: &Path,
    passages: &[&Passage],
    cache: &Cache,
    mut judge: Judge,
) -> Result<Parsed, ProseError>
where
    Judge: FnMut(&Passage, &[Sentence]) -> Result<(), ProseError>,
{
    let digests: Vec<Digest> = passages
        .iter()
        .map(|passage| Digest::of(Text(&passage.text)))
        .collect();
    let mut found: HashMap<Digest, Vec<Sentence>> = HashMap::with_capacity(digests.len());
    let mut waiting: HashMap<Digest, Vec<&Passage>> = HashMap::new();
    let mut missed: Vec<(Digest, &str)> = Vec::new();
    for (&passage, &digest) in passages.iter().zip(&digests) {
        if let Some(sentences) = found.get(&digest) {
            judge(passage, sentences)?;
            continue;
        }
        if let Some(held) = waiting.get_mut(&digest) {
            held.push(passage);
            continue;
        }
        let kept = match cache.read(digest) {
            Maybe::Present(Kept(text)) => serde_json::from_str::<Printing>(&text).ok(),
            Maybe::Absent(_) => None,
        };
        if let Some(printing) = kept {
            let read = sentences(printing);
            judge(passage, &read)?;
            found.insert(digest, read);
        }
        else {
            waiting.insert(digest, vec![passage]);
            missed.push((digest, passage.text.as_str()));
        }
    }
    let mut fresh = Fresh::default();
    if !missed.is_empty() {
        let texts: Vec<Text<'_>> = missed.iter().map(|&(_, text)| Text(text)).collect();
        let mut next = missed.iter();
        printed(python, script, &texts, |printing| {
            let Some(&(digest, text)) = next.next()
            else {
                return Ok(());
            };
            fresh.passages = fresh.passages.saturating_add(1);
            fresh.words = fresh.words.saturating_add(text.split_whitespace().count());
            let keeping = serde_json::to_string(&printing)
                .map_or(Keeping::Unwritten, |line| cache.keep(digest, &Kept(line)));
            if keeping == Keeping::Unwritten {
                fresh.unkept = fresh.unkept.saturating_add(1);
            }
            let read = sentences(printing);
            for &passage in waiting.get(&digest).map_or(&[][..], Vec::as_slice) {
                judge(passage, &read)?;
            }
            found.insert(digest, read);
            Ok(())
        })?;
    }
    Ok(Parsed {
        sentences: digests
            .iter()
            .map(|digest| found.get(digest).cloned().unwrap_or_default())
            .collect(),
        fresh,
    })
}

/// Runs the script on `texts` and hands `each` one printing per text, in
/// order, as each line arrives.
///
/// # Specification
/// - requires: as [`parse`].
/// - ensures: `each` reads one printing per text, or the run refuses. A writer
///   thread feeds the script, so a long input never waits on a full output
///   pipe.
/// - provides: the one run of the script [`parse`] makes.
/// - fails: as [`parse`].
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the JSON input and each line read, growth within the texts
///   given
///
/// # Adequacy
/// - hypothesis: L3 — as [`parse`].
/// - witness: `tests::cli::a_failing_parse_is_reported_with_its_message`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "a writer feeds the script's stdin while this thread reads its stdout, so neither pipe fills; a pool job must not block on a child process"
    )
)]
fn printed<Each>(
    python: &Path,
    script: &Path,
    texts: &[Text<'_>],
    mut each: Each,
) -> Result<(), ProseError>
where
    Each: FnMut(Printing) -> Result<(), ProseError>,
{
    let mut command = Command::new(python);
    command.arg(script);
    let label = format!("{command:?}");
    let refuse = |message: String| ProseError::Parse {
        command: label.clone(),
        message,
    };
    let input = serde_json::to_string(texts).map_err(|error| refuse(error.to_string()))?;
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| refuse(error.to_string()))?;
    let stdin = child.stdin.take();
    let stdout = child.stdout.take();
    let mut count = 0_usize;
    let streamed = std::thread::scope(|scope| {
        let writer = scope
            .spawn(move || stdin.map_or(Ok(()), |mut stdin| stdin.write_all(input.as_bytes())));
        let mut read = Ok(());
        if let Some(stdout) = stdout {
            for line in BufReader::new(stdout).lines() {
                read = line
                    .map_err(|error| refuse(error.to_string()))
                    .and_then(|line| {
                        serde_json::from_str::<Printing>(&line)
                            .map_err(|error| refuse(error.to_string()))
                    })
                    .and_then(|printing| {
                        count = count.saturating_add(1);
                        each(printing)
                    });
                if read.is_err() {
                    break;
                }
            }
        }
        let written = writer
            .join()
            .unwrap_or(Ok(()))
            .map_err(|error| refuse(error.to_string()));
        read.and(written)
    });
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
    streamed?;
    if count != texts.len() {
        return Err(refuse(format!(
            "{count} passages parsed for {} given",
            texts.len()
        )));
    }
    Ok(())
}

/// The sentences of one printing: each token's head an index into its own
/// sentence, a head outside it read as the token itself.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the sentences and their tokens, growth within the printing
///
/// # Adequacy
/// - hypothesis: L3 — as [`parse`].
/// - witness: `tests::cli::a_new_finding_is_refused_with_its_fix`
fn sentences(printing: Printing) -> Vec<Sentence>
{
    printing
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
}
