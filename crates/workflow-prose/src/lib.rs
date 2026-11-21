//! **Prose**: the sentence rules that need a parse. They hold over the corpus
//! comments and the rendered diagnostics with the committed debt in a ledger,
//! over the paragraphs a change writes in the markdown documents and the `#`
//! comments with no debt, and over a pull request's or an issue's body with
//! none.
//!
//! - [`passage`] reads the text: a corpus source's `///` paragraphs, a
//!   document's prose paragraphs, the `#` comments of a task, a script, a
//!   workflow, a manifest or a list ([`passage::hash`]), a rendered
//!   diagnostic's headline, label and advice, and a body's paragraphs and list
//!   items.
//! - [`documents`] lists the files a change touched since the merge base, each
//!   with its reader, and reads the paragraphs the base holds of them. A
//!   paragraph whose digest the base holds is one the change did not write.
//! - [`mechanical`] reads a body's named override for a mechanical change and
//!   admits only the paragraphs its substitution makes of the base's.
//! - [`parse`] runs the parse script under the pinned spaCy venv's interpreter
//!   and reads back each passage's sentences and tokens. [`cache`] keeps each
//!   parse by the [`digest`] of its passage, so a passage parses once.
//! - [`rules`] judges each sentence and each diagnostic by the rules the crate
//!   README lists.
//! - [`glossary`] reads `corpus/glossary.toml`.
//! - [`ledger`] keys each finding by file, rule and sentence digest.
//!
//! # Boundaries
//!
//! spaCy parses; this crate decides. The script prints first-order data, every
//! token's text, lemma, tags, dependency, head and offset, so each rule is a
//! function of a sentence and is tested on a hand-written one. No Python
//! enters the build: the interpreter is a tool the check task pins, never a
//! dependency of the workspace.
//!
//! A rule reads prose alone: text inside backticks is code, and text inside
//! double quotes is a quotation the tense rule leaves alone. A rule fires at
//! most once per sentence. The small English model mislabels some technical
//! words; a misreading is debt the ledger names, and the glossary pins a word
//! the model reads both ways.
//!
//! The ledger keys a finding by its sentence's digest, never its line, so
//! moving a sentence keeps its key and rewording it retires the key. A new
//! finding refuses, and a ledger line no finding matches is stale and refuses
//! too, so the debt only shrinks.
//!
//! A markdown document and a `#` comment keep no ledger. A passage's digest is
//! the BLAKE3 digest of its lines joined by single spaces, and [`documents`]
//! reads the touched files at the merge base with one `git cat-file --batch`. A
//! paragraph whose digest the base holds is a paragraph that the change keeps,
//! so the rules leave a moved or a re-wrapped paragraph alone. Each other
//! paragraph meets every rule, and a finding refuses.
//!
//! The [`cache`] under the host's cache directory keeps each parse by its
//! passage's digest. Its directory names spaCy's version, the model's version
//! and the parse script's digest, so a new model starts a new cache. A rule
//! that changes reads the kept parses, and a run whose passages the cache
//! holds starts no interpreter. The script prints a line for each passage, so
//! a written paragraph's finding prints before the last passage parses.
//!
//! # References
//!
//! - `vault:01a1dbb1-8f03-73b2-bbab-a82afed5f02f` — newest: the gate reads what
//!   a change wrote. A paragraph whose digest the base holds is not the
//!   change's, a body's override admits a mechanical change, and the cache
//!   keeps each parse by the digest of its text.
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-prose/README.md).

pub mod cache;
pub mod digest;
pub mod documents;
pub mod error;
pub mod glossary;
pub mod ledger;
pub mod mechanical;
pub mod parse;
pub mod passage;
pub mod rules;

pub use crate::error::ProseError;
pub use crate::glossary::Glossary;
pub use crate::ledger::Key;
pub use crate::rules::Finding;
pub use crate::rules::Rule;
