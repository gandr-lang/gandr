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

/// How many sources a sample visits: its class floor, then its ranked slice,
/// until this many are taken; and at most this many of the change's sources
/// beside them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SampleSize(pub usize);

/// A sweep's stated sample.
///
/// # Specification
/// - provides: the deterministic selections [`Sample::select`] and
///   [`Sample::touched`] apply; the name and size are the statement a sweep
///   test's documentation repeats.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Sample
{
    /// The salt of its ranking.
    pub name: SampleName,
    /// How many sources it draws by rank, and the most of the change's it
    /// visits beside them.
    pub size: SampleSize,
}

/// A source's place in a sample's ranking: the BLAKE3 digest of a key, the
/// sample's name, a zero byte and the source's name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Rank([u8; 32]);

/// The positions in a sample's candidates of its fixed set.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Fixed(BTreeSet<usize>);

impl Sample
{
    /// The fixed set this sample visits among `candidates`, in name order:
    /// the same whatever a change touches (#4654).
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: ranks every candidate by the BLAKE3 digest of the sample's
    ///   name, a zero byte and the candidate's name, ascending; takes the
    ///   first-ranked candidate of every class present, then candidates in rank
    ///   order, until the sample's size is reached; returns what it took in the
    ///   candidates' order. The result holds `size` candidates, or all of them
    ///   when fewer, or one per class when there are more classes than that.
    /// - provides: a slice whose cost is the size's, the same on every machine
    ///   and for every change, that moves by at most one source when one is
    ///   added or removed and that keeps every class, so a defect in it fails
    ///   the landing that makes it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a corpus of three classes sampled at one, at four and
    ///   past its length; an unsalted rank, a dropped class floor, a size
    ///   overshoot or a reordered result fails the witness, and an added
    ///   candidate moves at most one choice.
    /// - witness: `sample::tests::a_sample_keeps_every_class`
    /// - witness: `sample::tests::an_added_source_moves_at_most_one_choice`
    #[spec(ensures: |ret| ret.iter().all(|kept| candidates.iter().any(|candidate| candidate.name == kept.name)) && ret.len() <= self.size.0.max(candidates.iter().map(|candidate| &candidate.class).collect::<BTreeSet<_>>().len()))]
    #[inline]
    #[must_use]
    pub fn select(
        &self,
        candidates: &[Source],
    ) -> Vec<Source>
    {
        let Fixed(taken) = self.fixed(candidates);
        taken
            .into_iter()
            .filter_map(|at| candidates.get(at).cloned())
            .collect()
    }

    /// The sources of `candidates` that `changed` touches outside the fixed
    /// set, at most the sample's size of them, in name order: what a sweep's
    /// companion visits beside the fixed set (#4654).
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every candidate `changed` touches that [`Sample::select`]
    ///   leaves out, ranked by the BLAKE3 digest of the commit the change was
    ///   read at, the sample's name, a zero byte and the candidate's name,
    ///   ascending; the first `size` of them, in the candidates' order. Every
    ///   such candidate is among them when they number at most the size.
    /// - provides: the change's sources on top of the fixed set, never in its
    ///   place, at a cost the size bounds; a change wider than the size visits
    ///   a different part at each commit — the rest is the nightly profile's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a change of one source outside the fixed set, of one
    ///   inside it, and of every source at two commits; a touched source lost,
    ///   a fixed source repeated, a size overshoot or an unkeyed rotation fails
    ///   the witness.
    /// - witness: `sample::tests::a_change_is_visited_beside_the_fixed_set`
    /// - witness: `sample::tests::a_wide_change_is_visited_at_the_size_a_part_per_commit`
    /// - witness: `sample::tests::a_change_never_displaces_the_fixed_set_4654`
    #[spec(ensures: |ret| ret.len() <= self.size.0 && ret.iter().all(|kept| changed.names().any(|name| *name == kept.name)))]
    #[inline]
    #[must_use]
    pub fn touched(
        &self,
        candidates: &[Source],
        changed: &Changed,
    ) -> Vec<Source>
    {
        let Fixed(fixed) = self.fixed(candidates);
        let mut by_name: BTreeMap<&CorpusName, usize> = BTreeMap::new();
        for (at, source) in candidates.iter().enumerate() {
            let _first = by_name.entry(&source.name).or_insert(at);
        }
        let mut touched: Vec<(Rank, usize)> = changed
            .names()
            .filter_map(|name| by_name.get(name).copied())
            .filter(|at| !fixed.contains(at))
            .filter_map(|at| {
                candidates
                    .get(at)
                    .map(|source| (self.rank(changed.head(), source), at))
            })
            .collect();
        touched.sort_unstable();
        let taken: BTreeSet<usize> = touched
            .into_iter()
            .take(self.size.0)
            .map(|(_, at)| at)
            .collect();
        taken
            .into_iter()
            .filter_map(|at| candidates.get(at).cloned())
            .collect()
    }

    /// The positions in `candidates` of the fixed set: the first-ranked
    /// candidate of every class, then candidates in rank order, until the
    /// size is reached.
    ///
    /// # Specification
    /// trivial.
    fn fixed(
        &self,
        candidates: &[Source],
    ) -> Fixed
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
        for &(_, at) in &ranked {
            if taken.len() >= self.size.0 {
                break;
            }
            let _taken = taken.insert(at);
        }
        Fixed(taken)
    }

    /// `source`'s rank in this sample under `key`: the empty key ranks the
    /// slice, a change's commit its touched sources.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two samples' names draw two slices, so ranks that do
    ///   not differ draw one.
    /// - witness: `sample::tests::a_sample_keeps_every_class`
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
    fn a_sample_keeps_every_class()
    {
        let corpus = corpus();
        let at = |size| Sample {
            name: SampleName("a sweep"),
            size: SampleSize(size),
        };
        let one = at(1).select(&corpus);
        assert_eq!(
            one.iter()
                .map(|source| source.class.to_string())
                .collect::<Vec<_>>(),
            ["fixture/model", "fixture/pending", "strict"],
            "a size below the class count still keeps one of each class"
        );
        let four = at(4).select(&corpus);
        assert_eq!(four.len(), 4, "the size is the count drawn");
        assert!(
            four.windows(2)
                .all(|pair| matches!(pair, [left, right] if left.name < right.name)),
            "the sample is in the candidates' order"
        );
        assert_eq!(four, at(4).select(&corpus), "the same sample twice");
        let other = Sample {
            name: SampleName("another sweep"),
            size: SampleSize(4),
        };
        assert_ne!(
            names(&four),
            names(&other.select(&corpus)),
            "the sample's name salts its slice"
        );
        assert_eq!(
            at(100).select(&corpus),
            corpus,
            "a size past the corpus takes all of it"
        );
    }

    #[test]
    fn a_change_is_visited_beside_the_fixed_set()
    {
        let corpus = corpus();
        let sample = Sample {
            name: SampleName("a sweep"),
            size: SampleSize(4),
        };
        let four = sample.select(&corpus);
        let sampled: BTreeSet<&CorpusName> = four.iter().map(|source| &source.name).collect();
        let outside = corpus
            .iter()
            .find(|source| !sampled.contains(&source.name))
            .expect("a source outside the sample");
        let changed: Changed = core::iter::once(outside.name.clone()).collect();
        assert_eq!(
            sample.touched(&corpus, &changed),
            core::slice::from_ref(outside),
            "a changed source outside the fixed set is visited beside it"
        );
        let inside: Changed = four.iter().map(|source| source.name.clone()).collect();
        assert_eq!(
            sample.touched(&corpus, &inside),
            [],
            "a changed source the fixed set holds is visited there, once"
        );
        assert_eq!(
            sample.touched(&corpus, &Changed::default()),
            [],
            "no change, nothing beside the fixed set"
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
        let one = sample.touched(&corpus, &at("1914"));
        let other = sample.touched(&corpus, &at("1946"));
        assert_eq!(
            (one.len(), other.len()),
            (6, 6),
            "a change touching every source is visited at the size"
        );
        assert_eq!(
            one,
            sample.touched(&corpus, &at("1914")),
            "one commit visits one part"
        );
        assert_ne!(
            names(&one),
            names(&other),
            "another commit visits another part"
        );
    }

    /// #4654: a change's sources come on top of the fixed set, never in its
    /// place, so a defect in the fixed set fails the landing that makes it
    /// however many sources that landing changes.
    #[test]
    fn a_change_never_displaces_the_fixed_set_4654()
    {
        let corpus = corpus();
        let sample = Sample {
            name: SampleName("a sweep"),
            size: SampleSize(6),
        };
        let fixed: BTreeSet<String> = names(&sample.select(&corpus)).into_iter().collect();
        let every: Changed = corpus.iter().map(|source| source.name.clone()).collect();
        let beside = names(&sample.touched(&corpus, &every.at(Head::from("1914"))));
        let mut visited = fixed.clone();
        visited.extend(beside.iter().cloned());
        let displaced: Vec<&String> = fixed
            .iter()
            .filter(|name| !visited.contains(*name))
            .collect();
        assert!(
            displaced.is_empty(),
            "a change touching every source displaces {displaced:?} of the fixed set {fixed:?}"
        );
        assert!(
            beside.iter().all(|name| !fixed.contains(name)),
            "the change's sources come beside the fixed set: {beside:?} against {fixed:?}"
        );
        assert_eq!(beside.len(), 6, "the change's part is held to the size");
    }

    #[test]
    fn an_added_source_moves_at_most_one_choice()
    {
        let corpus = corpus();
        let sample = Sample {
            name: SampleName("a sweep"),
            size: SampleSize(6),
        };
        let before = names(&sample.select(&corpus));
        let mut grown = corpus;
        grown.push(source(CorpusName::from("fixture/model/m99.gandr")));
        let after = names(&sample.select(&grown));
        let after: BTreeSet<&String> = after.iter().collect();
        let dropped = before.iter().filter(|name| !after.contains(name)).count();
        assert!(
            dropped <= 1,
            "{before:?} became {after:?}: at most the one displaced source leaves"
        );
    }
}
