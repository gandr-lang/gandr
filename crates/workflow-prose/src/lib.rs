//! **Prose**: the sentence rules that need a parse, held over the corpus
//! comments, the rendered diagnostics and the crate READMEs, with the
//! committed debt in a ledger, and over a pull request's or an issue's body,
//! with none.
//!
//! - [`passage`] reads the text: a corpus source's `///` paragraphs, a README's
//!   prose paragraphs, a rendered diagnostic's headline, label and advice, and
//!   a body's paragraphs and list items.
//! - [`parse`] runs the parse script under the pinned spaCy venv's interpreter
//!   and reads back each passage's sentences and tokens.
//! - [`rules`] judges each sentence: a passive outside the stated list, a past
//!   tense, a stack of four nouns, an `-ing` main verb, a glossary word in the
//!   wrong part of speech; a body's sentence past 25 words, or joined to the
//!   next by a semicolon or a dash; and each diagnostic's procedural form.
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
//! # References
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-prose/README.md).

pub mod error;
pub mod glossary;
pub mod ledger;
pub mod parse;
pub mod passage;
pub mod rules;

pub use crate::error::ProseError;
pub use crate::glossary::Glossary;
pub use crate::ledger::Key;
pub use crate::rules::Finding;
pub use crate::rules::Rule;
