//! The glossary: the corpus's technical words, each with the one part of
//! speech it carries, read from `corpus/glossary.toml`.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt;

use serde::Deserialize;

use crate::error::ProseError;
use crate::passage::Text;

/// The part of speech a glossary word carries.
///
/// # Specification
/// - provides: the four parts of speech the glossary states.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum Pos
{
    /// A noun; spaCy's `NOUN` or `PROPN`.
    Noun,
    /// A verb; spaCy's `VERB` or `AUX`.
    Verb,
    /// An adjective; spaCy's `ADJ`.
    Adjective,
    /// An adverb; spaCy's `ADV`.
    Adverb,
}

/// A coarse tag as spaCy prints it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Tag<'tag>(pub &'tag str);

/// Whether a token's coarse tag is the glossary's part of speech.
///
/// # Specification
/// - provides: the verdict the glossary rule reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Agrees
{
    /// The tag is one the part of speech admits.
    Agrees,
    /// It is not.
    Differs,
}

impl Pos
{
    /// Whether spaCy's coarse `tag` is this part of speech.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a verb read as a noun and as a verb; another mapping
    ///   changes the glossary rule's verdict.
    /// - witness: `rules::tests::each_rule_fires_on_its_sentence_and_not_on_its_twin`
    #[inline]
    #[must_use]
    pub fn admits(
        self,
        tag: Tag<'_>,
    ) -> Agrees
    {
        let admitted: &[&str] = match self {
            Self::Noun => &["NOUN", "PROPN"],
            Self::Verb => &["VERB", "AUX"],
            Self::Adjective => &["ADJ"],
            Self::Adverb => &["ADV"],
        };
        if admitted.contains(&tag.0) {
            Agrees::Agrees
        }
        else {
            Agrees::Differs
        }
    }
}

impl fmt::Display for Pos
{
    /// Writes the part of speech as the glossary spells it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the glossary finding names the expected part of
    ///   speech, so writing nothing changes its line.
    /// - witness: `rules::tests::each_rule_fires_on_its_sentence_and_not_on_its_twin`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Noun => "noun",
            Self::Verb => "verb",
            Self::Adjective => "adjective",
            Self::Adverb => "adverb",
        })
    }
}

/// The file as TOML reads it: one `[words]` table of word and part of speech.
#[repr(transparent)]
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct File
{
    /// Each word, in lower case, and its part of speech.
    words: BTreeMap<String, Pos>,
}

/// The glossary's words, each with its part of speech.
///
/// # Specification
/// - provides: what the glossary rule holds a lemma to.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Glossary(BTreeMap<String, Pos>);

impl Glossary
{
    /// Reads the glossary's TOML.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, every word of the `[words]` table, lower-cased,
    ///   with its part of speech.
    /// - provides: the glossary from `corpus/glossary.toml`.
    /// - fails: [`ProseError::Glossary`] when the text is not TOML, holds a key
    ///   beside `words`, or names a part of speech other than `noun`, `verb`,
    ///   `adjective` and `adverb`.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a glossary read with a capitalised word, one with an
    ///   unknown part of speech and one with a stray key; accepting either
    ///   refusal or keeping the capital changes the result.
    /// - witness: `glossary::tests::a_glossary_reads_its_words_and_refuses_the_rest`
    #[inline]
    pub fn read(text: Text<'_>) -> Result<Self, ProseError>
    {
        let file: File = toml::from_str(text.0).map_err(|error| ProseError::Glossary {
            message: error.message().to_owned(),
        })?;
        Ok(Self(
            file.words
                .into_iter()
                .map(|(word, pos)| (word.to_lowercase(), pos))
                .collect(),
        ))
    }

    /// The part of speech of `lemma`, lower-cased, if the glossary holds it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Glossary::read`].
    /// - witness: `glossary::tests::a_glossary_reads_its_words_and_refuses_the_rest`
    #[inline]
    pub fn pos(
        &self,
        lemma: Text<'_>,
    ) -> impl Iterator<Item = Pos>
    {
        self.0.get(&lemma.0.to_lowercase()).copied().into_iter()
    }
}

#[cfg(test)]
mod tests
{
    use super::Glossary;
    use super::Pos;
    use crate::error::ProseError;
    use crate::passage::Text;

    #[test]
    fn a_glossary_reads_its_words_and_refuses_the_rest()
    {
        let glossary =
            Glossary::read(Text("[words]\nReplay = \"verb\"\nterm = \"noun\"\n")).unwrap();
        assert_eq!(glossary.pos(Text("replay")).collect::<Vec<_>>(), [
            Pos::Verb
        ]);
        assert_eq!(glossary.pos(Text("Term")).collect::<Vec<_>>(), [Pos::Noun]);
        assert_eq!(glossary.pos(Text("rule")).count(), 0);
        for text in ["[words]\nreplay = \"verbal\"\n", "other = 1\n[words]\n"] {
            assert!(
                matches!(Glossary::read(Text(text)), Err(ProseError::Glossary { .. })),
                "{text}"
            );
        }
    }
}
