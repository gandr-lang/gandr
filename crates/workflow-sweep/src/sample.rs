//! A sweep's sample: a hashed slice of its candidates at a fixed size, at
//! least one of each class, and every candidate a change touches.

use alloc::collections::BTreeSet;

use anodized::spec;

use crate::changed::Changed;
use crate::corpus::Class;
use crate::corpus::Source;

/// What salts a sample's ranking: the sweep test's own name, so two sweeps
/// draw different slices of one corpus.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SampleName(pub &'static str);

/// How many sources a sample draws by rank, before its class floor and the
/// changed sources join.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SampleSize(pub usize);

/// A sweep's stated sample.
///
/// # Specification
/// - provides: the deterministic selection [`Sample::select`] applies; the name
///   and size are the statement a sweep test's documentation repeats.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Sample
{
    /// The salt of its ranking.
    pub name: SampleName,
    /// How many sources it draws by rank.
    pub size: SampleSize,
}

/// A source's place in a sample's ranking: the BLAKE3 digest of the sample's
/// name, a zero byte and the source's name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Rank([u8; 32]);

impl Sample
{
    /// The sources of `candidates` this sample visits, in name order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: ranks every candidate by the BLAKE3 digest of the sample's
    ///   name, a zero byte and the candidate's name, ascending; takes the
    ///   first-ranked candidate of every class present, then candidates in rank
    ///   order until the sample's size is reached, then every candidate
    ///   `changed` touches; returns what it took in the candidates' order. The
    ///   result holds `size` candidates, or all of them when fewer, or one per
    ///   class when there are more classes than that, plus the changed ones
    ///   beyond either.
    /// - provides: a slice that is the same on every machine and every run,
    ///   that moves by at most one source when one is added or removed, that
    ///   keeps every class and every changed source.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a corpus of three classes sampled at one, at four and
    ///   past its length, with a changed source ranked last; an unsalted rank,
    ///   a dropped class floor, a size overshoot, a lost changed source or a
    ///   reordered result fails the witness, and an added candidate moves at
    ///   most one choice.
    /// - witness: `sample::tests::a_sample_keeps_every_class_and_every_change`
    /// - witness: `sample::tests::an_added_source_moves_at_most_one_choice`
    #[spec(ensures: |ret| ret.iter().all(|kept| candidates.iter().any(|candidate| candidate.name == kept.name)) && candidates.iter().filter(|candidate| changed.touches(&candidate.name)).all(|touched| ret.iter().any(|kept| kept.name == touched.name)))]
    #[inline]
    #[must_use]
    pub fn select(
        &self,
        candidates: &[Source],
        changed: &Changed,
    ) -> Vec<Source>
    {
        let mut ranked: Vec<(Rank, usize)> = candidates
            .iter()
            .enumerate()
            .map(|(at, source)| (self.rank(source), at))
            .collect();
        ranked.sort_unstable();
        let mut taken: BTreeSet<usize> = BTreeSet::new();
        let mut classes: BTreeSet<&Class> = BTreeSet::new();
        for &(_, at) in &ranked {
            if let Some(source) = candidates.get(at)
                && classes.insert(&source.class)
            {
                let _first = taken.insert(at);
            }
        }
        for &(_, at) in &ranked {
            if taken.len() >= self.size.0 {
                break;
            }
            let _ranked = taken.insert(at);
        }
        for (at, source) in candidates.iter().enumerate() {
            if changed.touches(&source.name) {
                let _changed = taken.insert(at);
            }
        }
        taken
            .into_iter()
            .filter_map(|at| candidates.get(at).cloned())
            .collect()
    }

    /// `source`'s rank in this sample.
    ///
    /// # Specification
    /// trivial.
    fn rank(
        &self,
        source: &Source,
    ) -> Rank
    {
        let mut hasher = blake3::Hasher::new();
        let _name = hasher.update(self.name.0.as_bytes());
        let _separator = hasher.update(&[0]);
        let _source = hasher.update(source.name.as_str().as_bytes());
        Rank(*hasher.finalize().as_bytes())
    }
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use super::Sample;
    use super::SampleName;
    use super::SampleSize;
    use crate::changed::Changed;
    use crate::corpus::Class;
    use crate::corpus::CorpusName;
    use crate::corpus::Source;

    /// A source named `name`, nowhere on disk.
    ///
    /// # Specification
    /// trivial.
    fn source(name: &str) -> Source
    {
        let name = CorpusName::from(name);
        Source {
            path: PathBuf::from(name.as_str()),
            class: Class::of(&name),
            name,
        }
    }

    /// Twelve model sources, four pending and one strict, in name order.
    ///
    /// # Specification
    /// trivial.
    fn corpus() -> Vec<Source>
    {
        let mut sources: Vec<Source> = (0_u8 .. 12_u8)
            .map(|index| source(&format!("fixture/model/m{index:02}.gandr")))
            .chain((0_u8 .. 4_u8).map(|index| source(&format!("fixture/pending/p{index}.gandr"))))
            .chain([source("strict/values.gandr")])
            .collect();
        sources.sort_by(|left, right| left.name.cmp(&right.name));
        sources
    }

    /// The names of `sources`.
    ///
    /// # Specification
    /// trivial.
    fn names(sources: &[Source]) -> Vec<String>
    {
        sources
            .iter()
            .map(|source| source.name.to_string())
            .collect()
    }

    #[test]
    fn a_sample_keeps_every_class_and_every_change()
    {
        let corpus = corpus();
        let none = Changed::default();
        let at = |size| Sample {
            name: SampleName("a sweep"),
            size: SampleSize(size),
        };
        let one = at(1).select(&corpus, &none);
        assert_eq!(
            one.iter()
                .map(|source| source.class.to_string())
                .collect::<Vec<_>>(),
            ["fixture/model", "fixture/pending", "strict"],
            "a size below the class count still keeps one of each class"
        );
        let four = at(4).select(&corpus, &none);
        assert_eq!(four.len(), 4, "the size is the count drawn");
        assert!(
            four.windows(2)
                .all(|pair| matches!(pair, [left, right] if left.name < right.name)),
            "the sample is in the candidates' order"
        );
        assert_eq!(four, at(4).select(&corpus, &none), "the same sample twice");
        let other = Sample {
            name: SampleName("another sweep"),
            size: SampleSize(4),
        };
        assert_ne!(
            names(&four),
            names(&other.select(&corpus, &none)),
            "the sample's name salts its slice"
        );
        assert_eq!(
            at(100).select(&corpus, &none),
            corpus,
            "a size past the corpus takes all of it"
        );
        let outside = corpus
            .iter()
            .find(|source| !four.contains(source))
            .expect("a source outside the sample");
        let changed: Changed = core::iter::once(outside.name.clone()).collect();
        let with_change = at(4).select(&corpus, &changed);
        assert_eq!(with_change.len(), 5, "a changed source joins the slice");
        assert!(
            with_change.contains(outside),
            "the changed source is visited"
        );
        assert!(
            four.iter().all(|kept| with_change.contains(kept)),
            "the slice itself is unchanged"
        );
    }

    #[test]
    fn an_added_source_moves_at_most_one_choice()
    {
        let corpus = corpus();
        let sample = Sample {
            name: SampleName("a sweep"),
            size: SampleSize(6),
        };
        let before = names(&sample.select(&corpus, &Changed::default()));
        let mut grown = corpus;
        grown.push(source("fixture/model/m99.gandr"));
        let after = names(&sample.select(&grown, &Changed::default()));
        let dropped = before.iter().filter(|name| !after.contains(name)).count();
        assert!(
            dropped <= 1,
            "{before:?} became {after:?}: at most the one displaced source leaves"
        );
    }
}
