//! The strata store: a level kept, recalled and refused by the store that
//! answers it.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;

use gandr_core_term::CoreArena;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Family;
use gandr_theory_sites::Level as _;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeBudget;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::StratumImage;
use gandr_theory_sites::Unreplayed;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathShape;
use gandr_theory_sites::WreathStratum;
use quenchant_shape::shape::Maybe;

use super::Built;
use super::BuiltKey;
use super::StratumAt;
use super::StratumDefect;
use super::StratumLevel;
use super::StratumStore;
use super::recalled;
use super::shared;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::fixture::ua::Answering;
use crate::fixture::ua::Counts;

/// #4123: level two over the chains at total size nine and degree four,
/// asked for twice of one context handed a store. A store holding nothing is
/// handed level two once, and never level one's chain stratum. A store
/// holding its image replays it and is handed nothing to keep. A store
/// holding a damaged image hears it refused as malformed, and is handed level
/// two certified afresh. A degree past every object is refused by the degree.
#[test]
fn level_two_is_kept_recalled_and_refused_by_the_store_4123()
{
    let at = StratumAt {
        bound: ShapeSize::from(9),
        degree: Degree::from(4),
    };
    let chains = Arc::new(Catalogue::chains(at.bound).expect("the chains build"));
    let below = SegalStratum::certify(Arc::clone(&chains), chains.reach())
        .expect("level one is certified at the chains' reach");
    let level: &Catalogue = &chains;
    let wreath = Arc::new(Wreath::build(level, level, at.bound));
    let image = WreathStratum::certify(wreath, at.degree, below)
        .expect("level two is certified at degree four")
        .image();
    let mut damaged = Vec::from(image.clone());
    let _last = damaged.pop();
    let stores = [
        (
            Answering::new(
                Maybe::Absent(recalled::Absent::Unkept),
                Unreplayed::Malformed,
            ),
            Counts {
                kept: 1,
                refused: 0,
                other: 0,
            },
            "a store holding nothing keeps level two once",
        ),
        (
            Answering::new(Maybe::Present(image.clone()), Unreplayed::Malformed),
            Counts {
                kept: 0,
                refused: 0,
                other: 0,
            },
            "a stored image replays, and nothing is certified",
        ),
        (
            Answering::new(
                Maybe::Present(StratumImage::from(damaged)),
                Unreplayed::Malformed,
            ),
            Counts {
                kept: 1,
                refused: 1,
                other: 0,
            },
            "a damaged image is refused by name and certified afresh",
        ),
    ];
    for (store, counts, case) in stores {
        let mut arena = CoreArena::new();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_strata_in(Arc::<Answering>::clone(&store));
        for _asked in 0_usize .. 2_usize {
            let stratum = context.level_two(at).expect("level two is answered");
            assert_eq!(stratum.image(), image, "{case}: level two's own image");
        }
        assert_eq!(store.counts(), counts, "{case}");
    }
    let past = Degree::from(100);
    let mut arena = CoreArena::new();
    assert!(
        matches!(
            CheckingContext::new(&mut arena, CheckBudget::DEFAULT)
                .level_two(StratumAt { degree: past, ..at }),
            Err(StratumDefect::Degree { degree }) if degree == past
        ),
        "a degree past every object"
    );
}

/// A store that answers, keeps and hears at one level alone, through the
/// store it wraps, and recalls nothing at any other.
#[derive(Debug)]
struct AtLevel
{
    /// The level the store answers at.
    level: StratumLevel,
    /// The store it answers through.
    inner: Arc<Answering>,
}

impl StratumStore for AtLevel
{
    /// The wrapped store's image at the level, and none elsewhere.
    ///
    /// # Specification
    /// trivial.
    fn recall(
        &self,
        family: &Family,
        at: StratumAt,
        level: StratumLevel,
    ) -> Maybe<StratumImage, recalled::Absent>
    {
        if level == self.level {
            self.inner.recall(family, at, level)
        }
        else {
            Maybe::Absent(recalled::Absent::Unkept)
        }
    }

    /// Hand the wrapped store a stratum at the level.
    ///
    /// # Specification
    /// trivial.
    fn keep(
        &self,
        family: &Family,
        at: StratumAt,
        level: StratumLevel,
        image: &StratumImage,
    )
    {
        if level == self.level {
            self.inner.keep(family, at, level, image);
        }
    }

    /// Hand the wrapped store a refusal at the level.
    ///
    /// # Specification
    /// trivial.
    fn refuse(
        &self,
        family: &Family,
        at: StratumAt,
        level: StratumLevel,
        why: Unreplayed,
    )
    {
        if level == self.level {
            self.inner.refuse(family, at, level, why);
        }
    }
}

/// #4437: level three over the chains at total size nine and degree five,
/// asked for twice of one context handed a store that answers at level
/// three. Level three reads level two at that wreath's top degree. A store
/// holding nothing is handed level three once. A store holding its image
/// replays it and is handed nothing to keep. A store holding a damaged image
/// hears it refused as malformed, and is handed level three certified
/// afresh. A bound past the allowance is refused by it.
#[test]
fn level_three_is_kept_recalled_and_refused_by_the_store_4437()
{
    let at = StratumAt {
        bound: ShapeSize::from(9),
        degree: Degree::from(5),
    };
    let chains = Arc::new(Catalogue::chains(at.bound).expect("the chains build"));
    let one = SegalStratum::certify(Arc::clone(&chains), chains.reach())
        .expect("level one is certified at the chains' reach");
    let level: &Catalogue = &chains;
    let wreath = Arc::new(Wreath::build(level, level, at.bound));
    let top = wreath
        .objects()
        .iter()
        .map(<Wreath<Catalogue> as gandr_theory_sites::Level>::degree)
        .max()
        .expect("the wreath holds objects");
    let two = WreathStratum::certify(wreath, top, one).expect("level two is certified at its top");
    let above = Arc::new(Wreath::build(level, two.wreath(), at.bound));
    let image = WreathStratum::certify(above, at.degree, two)
        .expect("level three is certified at degree five")
        .image();
    let mut damaged = Vec::from(image.clone());
    let _last = damaged.pop();
    let stores = [
        (
            Answering::new(
                Maybe::Absent(recalled::Absent::Unkept),
                Unreplayed::Malformed,
            ),
            Counts {
                kept: 1,
                refused: 0,
                other: 0,
            },
            "a store holding nothing keeps level three once",
        ),
        (
            Answering::new(Maybe::Present(image.clone()), Unreplayed::Malformed),
            Counts {
                kept: 0,
                refused: 0,
                other: 0,
            },
            "a stored image replays, and nothing is certified",
        ),
        (
            Answering::new(
                Maybe::Present(StratumImage::from(damaged)),
                Unreplayed::Malformed,
            ),
            Counts {
                kept: 1,
                refused: 1,
                other: 0,
            },
            "a damaged image is refused by name and certified afresh",
        ),
    ];
    for (store, counts, case) in stores {
        let mut arena = CoreArena::new();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_strata_in(Arc::new(AtLevel {
            level: StratumLevel::Three,
            inner: Arc::clone(&store),
        }));
        for _asked in 0_usize .. 2_usize {
            let stratum = context
                .strata_mut()
                .level_three(at)
                .expect("level three is answered");
            assert_eq!(stratum.image(), image, "{case}: level three's own image");
        }
        assert_eq!(store.counts(), counts, "{case}");
    }
    let past = StratumAt {
        bound: ShapeSize::from(15),
        ..at
    };
    let mut arena = CoreArena::new();
    assert!(
        matches!(
            CheckingContext::new(&mut arena, CheckBudget::DEFAULT)
                .strata_mut()
                .level_three(past),
            Err(StratumDefect::Allowance { bound }) if bound == past.bound
        ),
        "a bound past the allowance"
    );
}

/// A store that shares each built value under its key, as the store of a
/// process does. It recalls and keeps no stratum, and it counts each value
/// that it is handed to share.
#[derive(Debug, Default)]
struct Sharing
{
    /// Each value shared, by its key.
    built: std::sync::Mutex<BTreeMap<BuiltKey, Built>>,
    /// The values handed to share.
    shares: AtomicUsize,
}

impl StratumStore for Sharing
{
    /// None.
    ///
    /// # Specification
    /// trivial.
    fn recall(
        &self,
        _family: &Family,
        _at: StratumAt,
        _level: StratumLevel,
    ) -> Maybe<StratumImage, recalled::Absent>
    {
        Maybe::Absent(recalled::Absent::Unkept)
    }

    /// Nothing is kept.
    ///
    /// # Specification
    /// trivial.
    fn keep(
        &self,
        _family: &Family,
        _at: StratumAt,
        _level: StratumLevel,
        _image: &StratumImage,
    )
    {
    }

    /// Nothing is heard.
    ///
    /// # Specification
    /// trivial.
    fn refuse(
        &self,
        _family: &Family,
        _at: StratumAt,
        _level: StratumLevel,
        _why: Unreplayed,
    )
    {
    }

    /// The value shared under `key`.
    ///
    /// # Specification
    /// trivial.
    fn built(
        &self,
        key: &BuiltKey,
    ) -> Maybe<Built, shared::Absent>
    {
        self.built
            .lock()
            .expect("the shelf's lock holds")
            .get(key)
            .cloned()
            .map_or(Maybe::Absent(shared::Absent::Unshared), Maybe::Present)
    }

    /// Share `built` under `key` unless a value is shared there, and answer
    /// the value shared there.
    ///
    /// # Specification
    /// trivial.
    fn share(
        &self,
        key: BuiltKey,
        built: Built,
    ) -> Built
    {
        let _before = self.shares.fetch_add(1, Ordering::Relaxed);
        self.built
            .lock()
            .expect("the shelf's lock holds")
            .entry(key)
            .or_insert(built)
            .clone()
    }
}

/// #7413: level two over the chains at total size nine and degree four, asked
/// of two contexts handed one sharing store. The first context shares four
/// values: the chain catalogue, its wreath, level one at the catalogue's
/// reach, and level two. The second context reads the first's level two from
/// the store and shares nothing. A third context asks for a chain stratum
/// under a budget that the chains at total size nine exceed. The catalogue
/// shared under every budget does not answer it, so the budget refuses it.
#[test]
fn a_second_context_builds_nothing_a_first_shared_7413()
{
    let at = StratumAt {
        bound: ShapeSize::from(9),
        degree: Degree::from(4),
    };
    let store = Arc::new(Sharing::default());
    let mut first_arena = CoreArena::new();
    let mut first = CheckingContext::new(&mut first_arena, CheckBudget::DEFAULT);
    first.keep_strata_in(Arc::<Sharing>::clone(&store));
    let level = first.level_two(at).expect("level two is certified");
    assert_eq!(
        store.shares.load(Ordering::Relaxed),
        4,
        "the first context shares the catalogue, the wreath and two strata"
    );
    let mut second_arena = CoreArena::new();
    let mut second = CheckingContext::new(&mut second_arena, CheckBudget::DEFAULT);
    second.keep_strata_in(Arc::<Sharing>::clone(&store));
    let again = second.level_two(at).expect("level two is read");
    assert!(
        Arc::ptr_eq(&level, &again),
        "the second context reads the first's level two"
    );
    assert_eq!(
        store.shares.load(Ordering::Relaxed),
        4,
        "the second context shares nothing"
    );
    let mut third_arena = CoreArena::new();
    let mut third = CheckingContext::new(&mut third_arena, CheckBudget::DEFAULT);
    third.keep_strata_in(Arc::<Sharing>::clone(&store));
    let below = StratumAt {
        bound: at.bound,
        degree: Degree::from(2),
    };
    assert!(
        matches!(
            third
                .strata_mut()
                .certified(&Family::Chains, below, ShapeBudget::from(1)),
            Err(StratumDefect::Budget { bound, .. }) if bound == at.bound
        ),
        "a budget that the chains exceed refuses them, whatever is shared"
    );
}

/// #7453: level two over the faces of `[1](2)`, the 1-chain carrying the
/// 2-chain, at total size nine, asked of two contexts handed one sharing
/// store. The stratum is at the object's degree, over the objects with a map
/// into it alone. The first context shares three values: the chain catalogue,
/// level one at its reach, and the stratum. The second context reads the
/// first's stratum and shares nothing. A store that keeps strata is handed no
/// image. A degree zero and a degree past every object are refused by the
/// degree, and an object past the bound is absent.
#[test]
fn level_two_over_a_composite_s_faces_is_shared_and_refused_as_the_whole_7453()
{
    let at = StratumAt {
        bound: ShapeSize::from(9),
        degree: Degree::from(4),
    };
    let chain = |cells: usize| Shape::chain(cells.into()).expect("the chain builds");
    let object = WreathShape::new(chain(1), alloc::vec![chain(2)]).expect("one column");
    let degree = <Wreath<Catalogue> as gandr_theory_sites::Level>::degree(&object);
    let chains = Catalogue::chains(at.bound).expect("the chains build");
    let whole = Wreath::build(&chains, &chains, at.bound);
    let target = whole.find(&object);
    let faces = (0 .. whole.objects().len())
        .filter(|&source| {
            matches!(target, Maybe::Present(onto)
                if !whole.hom(ShapeIndex::from(source), onto).is_empty())
        })
        .count();
    let store = Arc::new(Sharing::default());
    let mut first_arena = CoreArena::new();
    let mut first = CheckingContext::new(&mut first_arena, CheckBudget::DEFAULT);
    first.keep_strata_in(Arc::<Sharing>::clone(&store));
    let Ok(Maybe::Present(stratum)) = first.strata_mut().faces_two(at, &object)
    else {
        panic!("level two over the faces is certified");
    };
    assert_eq!(
        stratum.degree(),
        degree,
        "the stratum is at the object's degree"
    );
    assert_eq!(stratum.wreath().objects().len(), faces, "the faces alone");
    assert!(
        faces < whole.objects().len(),
        "fewer objects than the whole"
    );
    assert_eq!(
        store.shares.load(Ordering::Relaxed),
        3,
        "the first context shares the catalogue, level one and the stratum"
    );
    let mut second_arena = CoreArena::new();
    let mut second = CheckingContext::new(&mut second_arena, CheckBudget::DEFAULT);
    second.keep_strata_in(Arc::<Sharing>::clone(&store));
    let Ok(Maybe::Present(again)) = second.strata_mut().faces_two(at, &object)
    else {
        panic!("level two over the faces is read");
    };
    assert!(
        Arc::ptr_eq(&stratum, &again),
        "the second context reads the first's stratum"
    );
    assert_eq!(
        store.shares.load(Ordering::Relaxed),
        3,
        "the second context shares nothing"
    );
    let keeping = Answering::new(
        Maybe::Absent(recalled::Absent::Unkept),
        Unreplayed::Malformed,
    );
    let mut kept_arena = CoreArena::new();
    let mut kept = CheckingContext::new(&mut kept_arena, CheckBudget::DEFAULT);
    kept.keep_strata_in(Arc::<Answering>::clone(&keeping));
    assert!(matches!(
        kept.strata_mut().faces_two(at, &object),
        Ok(Maybe::Present(_))
    ));
    assert_eq!(
        keeping.counts(),
        Counts {
            kept: 0,
            refused: 0,
            other: 0,
        },
        "a store that keeps strata is handed no image"
    );
    for past in [Degree::from(0), Degree::from(100)] {
        let mut arena = CoreArena::new();
        assert!(
            matches!(
                CheckingContext::new(&mut arena, CheckBudget::DEFAULT)
                    .strata_mut()
                    .faces_two(StratumAt { degree: past, ..at }, &object),
                Err(StratumDefect::Degree { degree }) if degree == past
            ),
            "the degree {past}"
        );
    }
    let beyond = WreathShape::new(chain(1), alloc::vec![chain(6)]).expect("one column");
    let mut arena = CoreArena::new();
    assert!(
        matches!(
            CheckingContext::new(&mut arena, CheckBudget::DEFAULT)
                .strata_mut()
                .faces_two(at, &beyond),
            Ok(Maybe::Absent(
                gandr_theory_sites::shape_class::Absent::PastTheBound
            ))
        ),
        "an object past the bound"
    );
}
