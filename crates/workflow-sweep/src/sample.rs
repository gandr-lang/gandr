//! A sweep's sample: at least one of each class, then the sources a change
//! touches in an order keyed by its commit, then a hashed slice of the rest,
//! to a fixed size.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;

use anodized::spec;

use crate::changed::Changed;
use crate::changed::Head;
use crate::corpus::Class;
use crate::corpus::CorpusName;
use crate::corpus::Source;

/// What salts a sample's ranking: the sweep test's own name, so two sweeps
/// draw different slices of one corpus.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SampleName(pub &'static str);

/// How many sources a sample visits: its class floor, then the changed
/// sources, then its ranked slice, until this many are taken.
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

/// A source's place in a sample's ranking: the BLAKE3 digest of a key, the
/// sample's name, a zero byte and the source's name.
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
    ///   name, a zero byte and the candidate's name, ascending, and every
    ///   candidate `changed` touches by the same digest with the commit it was
    ///   read at first; takes the first-ranked candidate of every class
    ///   present, then the touched candidates in their order, then candidates
    ///   in rank order, until the sample's size is reached; returns what it
    ///   took in the candidates' order. The result holds `size` candidates, or
    ///   all of them when fewer, or one per class when there are more classes
    ///   than that; every touched candidate is among them when they and the
    ///   classes fit the size.
    /// - provides: a slice whose cost is the size's whatever the change, the
    ///   same on every machine for one commit, that moves by at most one source
    ///   when one is added or removed, that keeps every class, and that visits
    ///   a change wider than the size a different part at each commit — the
    ///   rest is the nightly profile's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a corpus of three classes sampled at one, at four and
    ///   past its length, with a changed source ranked last, and a change
    ///   touching every source at two commits; an unsalted rank, a dropped
    ///   class floor, a size overshoot, a lost changed source, a touched source
    ///   ranked below the slice, an unkeyed rotation or a reordered result
    ///   fails the witness, and an added candidate moves at most one choice.
    /// - witness: `sample::tests::a_sample_keeps_every_class_and_every_change`
    /// - witness: `sample::tests::a_wide_change_is_visited_at_the_size_a_part_per_commit`
    /// - witness: `sample::tests::an_added_source_moves_at_most_one_choice`
    #[spec(ensures: |ret| ret.iter().all(|kept| candidates.iter().any(|candidate| candidate.name == kept.name)) && ret.len() <= self.size.0.max(candidates.iter().map(|candidate| &candidate.class).collect::<BTreeSet<_>>().len()) && (changed.names().filter(|name| candidates.iter().any(|candidate| candidate.name == **name)).count().saturating_add(candidates.iter().map(|candidate| &candidate.class).collect::<BTreeSet<_>>().len()) > self.size.0 || changed.names().all(|name| candidates.iter().all(|candidate| candidate.name != *name) || ret.iter().any(|kept| kept.name == *name))))]
    #[inline]
    #[must_use]
    pub fn select(
        &self,
        candidates: &[Source],
        changed: &Changed,
    ) -> Vec<Source>
    {
        let unkeyed = Head::default();
        let mut ranked: Vec<(Rank, usize)> = candidates
            .iter()
            .enumerate()
            .map(|(at, source)| (self.rank(&unkeyed, source), at))
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
        let mut by_name: BTreeMap<&CorpusName, usize> = BTreeMap::new();
        for (at, source) in candidates.iter().enumerate() {
            let _first = by_name.entry(&source.name).or_insert(at);
        }
        let mut touched: Vec<(Rank, usize)> = changed
            .names()
            .filter_map(|name| by_name.get(name).copied())
            .filter_map(|at| {
                candidates
                    .get(at)
                    .map(|source| (self.rank(changed.head(), source), at))
            })
            .collect();
        touched.sort_unstable();
        for &(_, at) in touched.iter().chain(&ranked) {
            if taken.len() >= self.size.0 {
                break;
            }
            let _taken = taken.insert(at);
        }
        taken
            .into_iter()
            .filter_map(|at| candidates.get(at).cloned())
            .collect()
    }

    /// `source`'s rank in this sample under `key`: the empty key ranks the
    /// slice, a change's commit its touched sources.
    ///
    /// # Specification
    /// trivial.
    fn rank(
        &self,
        key: &Head,
        source: &Source,
    ) -> Rank
    {
        let mut hasher = blake3::Hasher::new();
        key.key(&mut hasher);
        let _name = hasher.update(self.name.0.as_bytes());
        let _separator = hasher.update(&[0]);
        let _source = hasher.update(source.name.as_ref().as_bytes());
        Rank(*hasher.finalize().as_bytes())
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use std::path::PathBuf;

    use super::Sample;
    use super::SampleName;
    use super::SampleSize;
    use crate::changed::Changed;
    use crate::changed::Head;
    use crate::corpus::Class;
    use crate::corpus::CorpusName;
    use crate::corpus::Source;

    /// A source named `name`, nowhere on disk.
    ///
    /// # Specification
    /// trivial.
    fn source(name: CorpusName) -> Source
    {
        Source {
            path: PathBuf::from(name.as_ref()),
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
            .map(|index| {
                source(CorpusName::from(
                    format!("fixture/model/m{index:02}.gandr").as_str(),
                ))
            })
            .chain((0_u8 .. 4_u8).map(|index| {
                source(CorpusName::from(
                    format!("fixture/pending/p{index}.gandr").as_str(),
                ))
            }))
            .chain([source(CorpusName::from("strict/values.gandr"))])
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
        let sampled: BTreeSet<&CorpusName> = four.iter().map(|source| &source.name).collect();
        let outside = corpus
            .iter()
            .find(|source| !sampled.contains(&source.name))
            .expect("a source outside the sample");
        let changed: Changed = core::iter::once(outside.name.clone()).collect();
        let with_change = at(4).select(&corpus, &changed);
        assert_eq!(with_change.len(), 4, "a changed source keeps the size");
        assert!(
            with_change.contains(outside),
            "the changed source is visited"
        );
        let visited: BTreeSet<&CorpusName> =
            with_change.iter().map(|source| &source.name).collect();
        assert_eq!(
            four.iter()
                .filter(|kept| !visited.contains(&kept.name))
                .count(),
            1,
            "the changed source displaces the slice's last-ranked source alone"
        );
    }

    #[test]
    fn a_wide_change_is_visited_at_the_size_a_part_per_commit()
    {
        let corpus = corpus();
        let sample = Sample {
            name: SampleName("a sweep"),
            size: SampleSize(6),
        };
        let every: Changed = corpus.iter().map(|source| source.name.clone()).collect();
        let at = |head: &str| every.clone().at(Head::from(head));
        let one = sample.select(&corpus, &at("1914"));
        let other = sample.select(&corpus, &at("1946"));
        assert_eq!(
            (one.len(), other.len()),
            (6, 6),
            "a change touching every source is visited at the size"
        );
        assert_eq!(
            one,
            sample.select(&corpus, &at("1914")),
            "one commit visits one part"
        );
        assert_ne!(
            names(&one),
            names(&other),
            "another commit visits another part"
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
        grown.push(source(CorpusName::from("fixture/model/m99.gandr")));
        let after = names(&sample.select(&grown, &Changed::default()));
        let after: BTreeSet<&String> = after.iter().collect();
        let dropped = before.iter().filter(|name| !after.contains(name)).count();
        assert!(
            dropped <= 1,
            "{before:?} became {after:?}: at most the one displaced source leaves"
        );
    }
}
