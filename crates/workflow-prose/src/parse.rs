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

extern crate alloc;

use alloc::collections::VecDeque;
use core::num::NonZeroUsize;
use std::collections::HashMap;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Write as _;
use std::path::Path;
use std::process::Child;
use std::process::Command;
use std::process::Stdio;
use std::sync::mpsc;

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

/// The most interpreters a cold parse runs at once.
///
/// # Specification
/// - provides: the bound of a run's interpreters: the host's parallelism, or
///   the invocation's `--width`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Width(pub NonZeroUsize);

/// The fewest texts that one interpreter of a fanned-out parse takes. The
/// measure sets it: over a cold tree of 11,200 passages at width 32, shards of
/// 512 give the lowest median wall of 256, 512, 1,024 and 2,048. A smaller
/// shard adds model loads, and each interpreter holds about 227 MiB.
const SHARD: usize = 512;

/// What a reader heard from one shard's interpreter.
///
/// # Specification
/// - provides: the messages the readers send to the thread that delivers.
#[derive(Debug)]
enum Heard
{
    /// One printing, as the script wrote it.
    Line(String),
    /// The interpreter's output closed.
    Ended,
    /// The interpreter's output could not be read.
    Unread(String),
}

/// What a run holds of one shard.
///
/// # Specification
/// - provides: the order in which the shards' printings reach `each`.
#[derive(Debug)]
struct Shard<'slice, 'text>
{
    /// The texts that the shard's interpreter parses.
    texts: &'slice [Text<'text>],
    /// The lines that arrived before every shard ahead of this one ended.
    waiting: VecDeque<String>,
    /// The lines read.
    read: usize,
    /// Whether the interpreter's output closed.
    ended: bool,
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
///   sentence read as the token itself. The script parses each text the cache
///   misses, each distinct text once, across at most `width` interpreters as
///   `printed` states. It does not start when every text hits. Each fresh parse
///   is kept by its text's digest. An entry whose text the crate cannot read is
///   a miss. `judge` reads each passage once: a hit before the script starts,
///   and a miss as the script's line for its text arrives.
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
    width: Width,
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
        printed(python, script, &texts, width, |printing| {
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

/// Runs the script on `texts` across interpreters and hands `each` one
/// printing per text, in order, as each line arrives.
///
/// # Specification
/// - requires: as [`parse`].
/// - ensures: the texts split into at most `width` shards of at least [`SHARD`]
///   texts each, one interpreter for each. The first interpreter starts alone,
///   and the rest start when it prints its first line, so the first printing
///   costs one interpreter's load. `each` reads the first shard's printings as
///   they arrive, and each later shard's when every shard ahead of it has
///   ended: one printing per text, in order, or the run refuses. A writer feeds
///   each interpreter, so no pipe fills.
/// - provides: the one fanned-out run of the script that [`parse`] makes.
/// - fails: as [`parse`]; an interpreter that exits unsuccessfully refuses with
///   its status and its message before a short or an unread output.
/// - panics: none.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: each shard's input and each line read, growth within the texts
///
/// # Adequacy
/// - hypothesis: L3 — as [`parse`]; three shards over a fake interpreter
///   deliver every printing in the texts' order, and a lost, repeated or
///   reordered line changes the judged findings.
/// - witness: `tests::cli::a_failing_parse_is_reported_with_its_message`
/// - witness: `tests::cli::a_cold_parse_across_interpreters_judges_in_order`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "each interpreter has a writer that feeds its stdin and a reader that sends its lines to this thread, so no pipe fills; a pool job must not block on a child process"
    )
)]
fn printed<Each>(
    python: &Path,
    script: &Path,
    texts: &[Text<'_>],
    width: Width,
    mut each: Each,
) -> Result<(), ProseError>
where
    Each: FnMut(Printing) -> Result<(), ProseError>,
{
    let label = format!("{:?}", Command::new(python).arg(script));
    let refuse = |message: String| ProseError::Parse {
        command: label.clone(),
        message,
    };
    let interpreters = texts.len().div_ceil(SHARD).clamp(1, width.0.get());
    let size = texts.len().div_ceil(interpreters).max(1);
    let mut shards: Vec<Shard<'_, '_>> = texts
        .chunks(size)
        .map(|texts| Shard {
            texts,
            waiting: VecDeque::new(),
            read: 0,
            ended: false,
        })
        .collect();
    let mut children: Vec<Child> = Vec::with_capacity(shards.len());
    let streamed = std::thread::scope(|scope| {
        let (heard, hearing) = mpsc::channel::<(usize, Heard)>();
        let mut start = |index: usize, texts: &[Text<'_>]| -> Result<(), ProseError> {
            let input = serde_json::to_string(texts).map_err(|error| refuse(error.to_string()))?;
            let mut child = Command::new(python)
                .arg(script)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .map_err(|error| refuse(error.to_string()))?;
            let stdin = child.stdin.take();
            let stdout = child.stdout.take();
            children.push(child);
            scope.spawn(move || {
                if let Some(mut stdin) = stdin {
                    drop(stdin.write_all(input.as_bytes()));
                }
            });
            let heard = heard.clone();
            scope.spawn(move || {
                if let Some(stdout) = stdout {
                    for line in BufReader::new(stdout).lines() {
                        let said =
                            line.map_or_else(|error| Heard::Unread(error.to_string()), Heard::Line);
                        let unread = matches!(said, Heard::Unread(_));
                        if heard.send((index, said)).is_err() || unread {
                            return;
                        }
                    }
                }
                drop(heard.send((index, Heard::Ended)));
            });
            Ok(())
        };
        let mut deliver = |line: &str| {
            serde_json::from_str::<Printing>(line)
                .map_err(|error| refuse(error.to_string()))
                .and_then(&mut each)
        };
        start(0, shards.first().map_or(&[][..], |shard| shard.texts))?;
        let mut alone = true;
        let mut current = 0_usize;
        while current < shards.len() {
            let Ok((index, said)) = hearing.recv()
            else {
                break;
            };
            if alone && index == 0 {
                alone = false;
                for (later, shard) in shards.iter().enumerate().skip(1) {
                    start(later, shard.texts)?;
                }
            }
            match said {
                Heard::Line(line) => {
                    let Some(shard) = shards.get_mut(index)
                    else {
                        continue;
                    };
                    shard.read = shard.read.saturating_add(1);
                    if index == current {
                        deliver(&line)?;
                    }
                    else {
                        shard.waiting.push_back(line);
                    }
                },
                Heard::Ended => {
                    if let Some(shard) = shards.get_mut(index) {
                        shard.ended = true;
                    }
                    while let Some(shard) = shards.get_mut(current).filter(|shard| shard.ended) {
                        if shard.read != shard.texts.len() {
                            return Err(refuse(format!(
                                "{} passages parsed for {} given",
                                shard.read,
                                shard.texts.len()
                            )));
                        }
                        current = current.saturating_add(1);
                        if let Some(next) = shards.get_mut(current) {
                            while let Some(line) = next.waiting.pop_front() {
                                deliver(&line)?;
                            }
                        }
                    }
                },
                Heard::Unread(message) => return Err(refuse(message)),
            }
        }
        Ok(())
    });
    let mut failed = None;
    for child in children {
        let output = child
            .wait_with_output()
            .map_err(|error| refuse(error.to_string()))?;
        if failed.is_none()
            && !output.status.success()
            && (output.status.code().is_some() || streamed.is_ok())
        {
            failed = Some(refuse(format!(
                "{}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            )));
        }
    }
    failed.map_or(streamed, Err)
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
