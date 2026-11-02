//! Where a context's certified strata come from.
//!
//! A `ua[n, k]` statement names the stratum of degree `n` over the sub-site
//! of the wiring catalogue at bound `k` on the corollas its two species
//! inhabit, and a `compose[n, k]` composite the one over the chain catalogue
//! ([`Family`]). A composite of a level-two shape names level two of degree
//! `n` over the wreath of the chains at total size `k` over themselves
//! ([`StratumLevel`]). A context builds each catalogue and wreath it needs
//! once and holds each stratum it certifies or recalls for its own life. No
//! static outlives the context, so a stratum crosses contexts and processes
//! only through a store, which keeps no level-one chain stratum.
//!
//! A run that keeps strata hands each context a [`StratumStore`]. Before it
//! certifies, the context asks the store for the stratum's image at its level
//! and replays it over its own catalogue ([`SegalStratum::replay`]) or wreath
//! ([`WreathStratum::replay`]). An image that does not replay is refused to
//! the store by name, and the context certifies afresh. What the context
//! certifies, it hands the store to keep. The store answers integrity and
//! attestation, and the replay checks the structure. A context handed no
//! store keeps [`NoStratumStore`], which recalls and keeps nothing. The
//! checker depends on no storage crate, so the driver implements the store.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — a recalled verdict is believed only under a
//!   receipt, and a full re-check is always available.
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — the
//!   strata persist in the store, and certification runs over the sub-site a
//!   use demands.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use anodized::spec;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Certificate;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Family;
use gandr_theory_sites::Level as _;
use gandr_theory_sites::LevelUncertified;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::ShapeBudget;
use gandr_theory_sites::ShapeObstruction;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::StratumImage;
use gandr_theory_sites::Uncertified;
use gandr_theory_sites::Unreplayed;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathStratum;
use quenchant_shape::shape::Maybe;

use super::StratumDefect;

/// A stratum a statement names: the catalogue's bound and the degree.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StratumAt
{
    /// The catalogue's bound.
    pub bound: ShapeSize,
    /// The degree.
    pub degree: Degree,
}

/// Which level of the site a stratum certifies, which a store's key adds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StratumLevel
{
    /// The catalogue's shapes: a [`SegalStratum`].
    One,
    /// The wreath of the catalogue over itself: a [`WreathStratum`].
    Two,
    /// The wreath of the catalogue over level two: a [`LevelThree`].
    Three,
    /// The wreath of the catalogue over level three: a [`LevelFour`].
    Four,
}

impl core::fmt::Display for StratumLevel
{
    /// `1`, `2`, `3` or `4`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::One => "1",
            Self::Two => "2",
            Self::Three => "3",
            Self::Four => "4",
        })
    }
}

/// Level three over the chains, certified from level two.
pub type LevelThree = WreathStratum<WreathStratum>;

/// Level four over the chains, certified from level three.
pub type LevelFour = WreathStratum<LevelThree>;

/// The wreath of the chains over level two, level three's objects.
type ThreeWreath = Wreath<Wreath<Catalogue>>;

/// The largest bound levels three and four are certified at.
///
/// economy: in a release build, level three certifies at total size 13 in
/// 0.55 s and level four in 2.9 s. At total size 15 they take 27 s and 126 s,
/// and two 3-cells side by side, at total size 17, take 52 s at their least
/// degree. Each level reads the one below at its top degree. Reversal: a
/// certificate restricted to what a pasting reaches (#4474).
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn above_two_allowance() -> ShapeSize
{
    ShapeSize::from(13_usize)
}

quenchant_shape::reason_enum! {
    /// Why a store answers no image for a stratum.
    pub mod recalled {
        /// The reason no image is answered.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The store holds no image at the stratum's key, or none it can
            /// read.
            Unkept,
            /// The image's receipt is not one the run's policy believes.
            Unattested,
        }
    }
}

/// Where a run's certified strata are recalled from and kept to.
///
/// # Specification
/// - requires: nothing; what a store answers is replayed before it is used.
/// - ensures: an implementor answers, for a stratum, an image it believes was
///   certified there, and keeps an image of each stratum it is handed.
/// - provides: the one way a stratum crosses contexts and processes.
/// - panics: none.
/// - executable: none — a trait whose implementors are untrusted.
///
/// # Adequacy
/// - hypothesis: L3 — a context recalls the image a first context kept and
///   certifies nothing, and refuses a damaged image by name and certifies
///   afresh.
/// - witness: `ua::tests::a_stored_stratum_replays_and_a_damaged_one_is_certified_afresh_4034`
pub trait StratumStore: core::fmt::Debug + Send + Sync
{
    /// The image of the stratum at `at` and `level` over `family`'s
    /// catalogue, when the store holds one it believes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as the trait.
    /// - panics: none.
    /// - executable: none — a required method.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the trait.
    /// - declaration-only: the obligation is each implementation's answer; the
    ///   trait's witness runs an implementor.
    fn recall(
        &self,
        family: &Family,
        at: StratumAt,
        level: StratumLevel,
    ) -> Maybe<StratumImage, recalled::Absent>;

    /// Keep `image`, the stratum at `at` and `level` over `family`'s
    /// catalogue, which this process certified.
    ///
    /// # Specification
    /// - requires: `image` is the image of a stratum certified at `at` and
    ///   `level` over `family`'s catalogue in this process.
    /// - ensures: as the trait.
    /// - panics: none.
    /// - executable: none — a required method.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the trait.
    /// - declaration-only: the obligation is each implementation's answer; the
    ///   trait's witness runs an implementor.
    fn keep(
        &self,
        family: &Family,
        at: StratumAt,
        level: StratumLevel,
        image: &StratumImage,
    );

    /// Hear that the image recalled at `at` and `level` over `family`'s
    /// catalogue does not replay, and why.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as the trait.
    /// - panics: none.
    /// - executable: none — a required method.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the trait.
    /// - declaration-only: the obligation is each implementation's answer; the
    ///   trait's witness runs an implementor.
    fn refuse(
        &self,
        family: &Family,
        at: StratumAt,
        level: StratumLevel,
        why: Unreplayed,
    );
}

/// A store holding nothing, for a context handed none.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct NoStratumStore;

impl StratumStore for NoStratumStore
{
    /// None.
    ///
    /// # Specification
    /// trivial.
    #[inline]
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
    #[inline]
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
    #[inline]
    fn refuse(
        &self,
        _family: &Family,
        _at: StratumAt,
        _level: StratumLevel,
        _why: Unreplayed,
    )
    {
    }
}

/// A context's strata: the store, and each catalogue and stratum the context
/// holds for its life.
#[derive(Clone, Debug)]
pub struct Strata
{
    /// Where strata are recalled from and kept to.
    store: Arc<dyn StratumStore>,
    /// The catalogue of each family at each bound built so far.
    catalogues: BTreeMap<Family, BTreeMap<ShapeSize, Arc<Catalogue>>>,
    /// Each stratum of each family certified or recalled so far.
    held: BTreeMap<Family, BTreeMap<StratumAt, Arc<SegalStratum>>>,
    /// The wreath of the chains over themselves at each bound built so far.
    wreaths: BTreeMap<ShapeSize, Arc<Wreath<Catalogue>>>,
    /// Each level-two stratum over the chains certified or recalled so far.
    held_two: BTreeMap<StratumAt, Arc<WreathStratum>>,
    /// The wreath of the chains over level two at each bound built so far.
    wreaths_three: BTreeMap<ShapeSize, Arc<ThreeWreath>>,
    /// Each level-three stratum over the chains certified or recalled so far.
    held_three: BTreeMap<StratumAt, Arc<LevelThree>>,
    /// The wreath of the chains over level three at each bound built so far.
    wreaths_four: BTreeMap<ShapeSize, Arc<Wreath<ThreeWreath>>>,
    /// Each level-four stratum over the chains certified or recalled so far.
    held_four: BTreeMap<StratumAt, Arc<LevelFour>>,
}

impl Default for Strata
{
    /// No store, and nothing held.
    ///
    /// # Specification
    /// trivial.
    fn default() -> Self
    {
        Self {
            store: Arc::new(NoStratumStore),
            catalogues: BTreeMap::new(),
            held: BTreeMap::new(),
            wreaths: BTreeMap::new(),
            held_two: BTreeMap::new(),
            wreaths_three: BTreeMap::new(),
            held_three: BTreeMap::new(),
            wreaths_four: BTreeMap::new(),
            held_four: BTreeMap::new(),
        }
    }
}

impl Strata
{
    /// Recall from and keep to `store` from now on.
    ///
    /// # Specification
    /// trivial.
    pub fn keep_in(
        &mut self,
        store: Arc<dyn StratumStore>,
    )
    {
        self.store = store;
    }

    /// The stratum at `at` over the catalogue of `family` at its bound, under
    /// `budget`: [`Catalogue::profiles`] for [`Family::Profiles`] and
    /// [`Catalogue::within`] for [`Family::Wirings`], each recalled from the
    /// store and replayed when it holds one, and [`Catalogue::chains_within`]
    /// for [`Family::Chains`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stratum [`SegalStratum::certify`] gives at `at`, or one
    ///   the store's image replays to at `at`'s degree, over the catalogue of
    ///   `family` at `at`'s bound; every call at one family and one stratum
    ///   answers the stratum the first answered.
    /// - fails: [`StratumDefect::Allowance`] for a bound past
    ///   [`ShapeSize::LARGEST`] or a catalogue the site refuses;
    ///   [`StratumDefect::Budget`] for a bound whose catalogue holds more
    ///   wirings, or more chains, than `budget`; [`StratumDefect::Degree`] and
    ///   [`StratumDefect::Condition`] as [`SegalStratum::certify`] refuses.
    /// - panics: none.
    /// - intension: the first call at a family and a bound builds its
    ///   catalogue. The first at a stratum past the chains asks the store,
    ///   replays what it answers, and certifies when the store answers nothing
    ///   or an image that does not replay; the store hears the refusal and
    ///   keeps what is certified. A chain stratum is certified and held, and
    ///   the store never hears of it. A refusal of the catalogue or the stratum
    ///   is not held, so it is checked again. A catalogue built under one
    ///   budget answers a later call under any other.
    ///
    /// # Errors
    /// [`StratumDefect`] as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every written statement is decided over the stratum
    ///   this answers, and the defects are each refused by name. A stored image
    ///   replays in place of a certification, and a damaged one is refused and
    ///   certified afresh. A composite at a degree its chains do not reach is
    ///   refused by the degree. The magma's stratum of degree seven at bound
    ///   seven is certified over its sub-site.
    /// - witness: `ua::tests::a_written_statement_refuses_each_defect_by_name`
    /// - witness: `ua::tests::a_stored_stratum_replays_and_a_damaged_one_is_certified_afresh_4034`
    /// - witness: `ua::tests::a_statement_derives_over_its_sub_site_the_path_the_wirings_give_4035`
    /// - witness: `compose::tests::a_composite_refuses_each_defect_by_name`
    #[spec(ensures: |ref ret| match *ret {
        | Ok(ref stratum) => at.bound <= ShapeSize::LARGEST && stratum.degree() == at.degree
            && stratum.catalogue().family() == family,
        | Err(StratumDefect::Allowance { bound: refused }) => refused == at.bound,
        | Err(StratumDefect::Budget { bound: refused, counted }) => refused == at.bound
            && usize::from(counted) > usize::from(budget),
        | Err(StratumDefect::Degree { degree: refused }) => refused == at.degree,
        | Err(StratumDefect::Condition { degree: failing }) => failing <= at.degree,
    })]
    pub fn certified(
        &mut self,
        family: &Family,
        at: StratumAt,
        budget: ShapeBudget,
    ) -> Result<Arc<SegalStratum>, StratumDefect>
    {
        let bound = at.bound;
        if bound > ShapeSize::LARGEST {
            return Err(StratumDefect::Allowance { bound });
        }
        if let Some(held) = self
            .held
            .get(family)
            .and_then(|by_stratum| by_stratum.get(&at))
        {
            return Ok(Arc::clone(held));
        }
        let catalogue = self.catalogue(family, bound, budget)?;
        let kept = *family != Family::Chains;
        if kept && let Maybe::Present(image) = self.store.recall(family, at, StratumLevel::One) {
            match SegalStratum::replay(Arc::clone(&catalogue), &image) {
                Ok(stratum) if stratum.degree() == at.degree => {
                    return Ok(self.hold(family, at, stratum));
                },
                Ok(_) => self
                    .store
                    .refuse(family, at, StratumLevel::One, Unreplayed::Degree),
                Err(why) => self.store.refuse(family, at, StratumLevel::One, why),
            }
        }
        let stratum =
            SegalStratum::certify(catalogue, at.degree).map_err(|refused| match refused {
                Uncertified::Degree { degree: refused } => {
                    StratumDefect::Degree { degree: refused }
                },
                Uncertified::Condition {
                    degree: failing, ..
                } => StratumDefect::Condition { degree: failing },
            })?;
        if kept {
            self.store
                .keep(family, at, StratumLevel::One, &stratum.image());
        }
        Ok(self.hold(family, at, stratum))
    }

    /// Level two at `at` over the wreath of the chains at `at`'s bound over
    /// themselves, built from level one's chain stratum at the catalogue's
    /// reach: recalled from the store and replayed when it holds one,
    /// certified and kept otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stratum [`WreathStratum::certify`] gives at `at`'s
    ///   degree, or one the store's image replays to at that degree; every call
    ///   at one stratum answers the stratum the first answered.
    /// - fails: [`StratumDefect::Allowance`] for a bound past
    ///   [`ShapeSize::LARGEST`]; [`StratumDefect::Degree`] for a degree zero or
    ///   past every object of the wreath; [`StratumDefect::Condition`] at the
    ///   degree of the source of the first map out of order, or of the first
    ///   object that is not the colimit of its cells; level one's refusals as
    ///   [`Strata::certified`] gives them.
    /// - panics: none.
    /// - intension: the first call at a bound builds the chains and their
    ///   wreath, and certifies level one at the catalogue's reach. The first at
    ///   a stratum asks the store at level two, replays what it answers, and
    ///   certifies when the store answers nothing or an image that does not
    ///   replay; the store hears the refusal and keeps what is certified. A
    ///   refusal is not held, so it is checked again.
    ///
    /// # Errors
    /// [`StratumDefect`] as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a second context recalls the level-two stratum a
    ///   first kept and certifies nothing, a damaged image is refused and
    ///   certified afresh, and a degree past every object is refused by the
    ///   degree.
    /// - witness: `ua::tests::level_two_is_kept_recalled_and_refused_by_the_store_4123`
    #[spec(ensures: |ref ret| match *ret {
        | Ok(ref stratum) => at.bound <= ShapeSize::LARGEST && stratum.degree() == at.degree,
        | Err(StratumDefect::Allowance { bound: refused }) => refused == at.bound,
        | Err(StratumDefect::Budget { .. }) => false,
        | Err(StratumDefect::Degree { .. } | StratumDefect::Condition { .. }) => true,
    })]
    pub fn level_two(
        &mut self,
        at: StratumAt,
    ) -> Result<Arc<WreathStratum>, StratumDefect>
    {
        if at.bound > ShapeSize::LARGEST {
            return Err(StratumDefect::Allowance { bound: at.bound });
        }
        if let Some(held) = self.held_two.get(&at) {
            return Ok(Arc::clone(held));
        }
        let (catalogue, wreath) = self.wreath_two(at.bound)?;
        let below = self.certified(
            &Family::Chains,
            StratumAt {
                bound: at.bound,
                degree: catalogue.reach(),
            },
            ShapeBudget::EVERY,
        )?;
        let stratum = ascend(
            &*self.store,
            wreath,
            SegalStratum::clone(&below),
            (at, StratumLevel::Two),
        )?;
        let held = Arc::new(stratum);
        let _first = self.held_two.insert(at, Arc::clone(&held));
        Ok(held)
    }

    /// Level three at `at` over the wreath of the chains at `at`'s bound over
    /// level two, built from level two at that wreath's top degree: recalled
    /// from the store and replayed when it holds one, certified and kept
    /// otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stratum [`WreathStratum::certify`] gives at `at`'s
    ///   degree, or one the store's image replays to at that degree; every call
    ///   at one stratum answers the stratum the first answered.
    /// - fails: [`StratumDefect::Allowance`] for a bound past
    ///   [`above_two_allowance`]; [`StratumDefect::Degree`] for a degree zero
    ///   or past every object of the wreath; [`StratumDefect::Condition`] at
    ///   the degree of the first object out of order or not the colimit of its
    ///   cells; level two's refusals as [`Strata::level_two`] gives them.
    /// - panics: none.
    /// - intension: as [`Strata::level_two`], one level up. Level two is read
    ///   at its wreath's top degree, so every column is certified below.
    ///
    /// # Errors
    /// [`StratumDefect`] as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a 3-cell whiskered by a 1-cell is admitted at level
    ///   three, and a bound past the allowance is refused by it.
    /// - witness: `compose::tests::a_pasting_at_level_three_or_four_is_read_at_its_level_4431`
    #[spec(ensures: |ref ret| match *ret {
        | Ok(ref stratum) => at.bound <= above_two_allowance() && stratum.degree() == at.degree,
        | Err(StratumDefect::Allowance { .. } | StratumDefect::Degree { .. } | StratumDefect::Condition { .. }) => true,
        | Err(StratumDefect::Budget { .. }) => false,
    })]
    pub fn level_three(
        &mut self,
        at: StratumAt,
    ) -> Result<Arc<LevelThree>, StratumDefect>
    {
        if at.bound > above_two_allowance() {
            return Err(StratumDefect::Allowance { bound: at.bound });
        }
        if let Some(held) = self.held_three.get(&at) {
            return Ok(Arc::clone(held));
        }
        let (below, wreath) = self.wreath_three(at.bound)?;
        let stratum = ascend(
            &*self.store,
            wreath,
            WreathStratum::clone(&below),
            (at, StratumLevel::Three),
        )?;
        let held = Arc::new(stratum);
        let _first = self.held_three.insert(at, Arc::clone(&held));
        Ok(held)
    }

    /// Level four at `at` over the wreath of the chains at `at`'s bound over
    /// level three, built from level three at that wreath's top degree:
    /// recalled from the store and replayed when it holds one, certified and
    /// kept otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Strata::level_three`], one level up.
    /// - fails: as [`Strata::level_three`], one level up; level three's
    ///   refusals as [`Strata::level_three`] gives them.
    /// - panics: none.
    ///
    /// # Errors
    /// [`StratumDefect`] as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one 4-cell is admitted at level four, and a bound
    ///   past the allowance is refused by it.
    /// - witness: `compose::tests::a_pasting_at_level_three_or_four_is_read_at_its_level_4431`
    #[spec(ensures: |ref ret| match *ret {
        | Ok(ref stratum) => at.bound <= above_two_allowance() && stratum.degree() == at.degree,
        | Err(StratumDefect::Allowance { .. } | StratumDefect::Degree { .. } | StratumDefect::Condition { .. }) => true,
        | Err(StratumDefect::Budget { .. }) => false,
    })]
    pub fn level_four(
        &mut self,
        at: StratumAt,
    ) -> Result<Arc<LevelFour>, StratumDefect>
    {
        if at.bound > above_two_allowance() {
            return Err(StratumDefect::Allowance { bound: at.bound });
        }
        if let Some(held) = self.held_four.get(&at) {
            return Ok(Arc::clone(held));
        }
        let (catalogue, _two) = self.wreath_two(at.bound)?;
        let (_level_two, three) = self.wreath_three(at.bound)?;
        let below = self.level_three(StratumAt {
            bound: at.bound,
            degree: top(&three)?,
        })?;
        let wreath = if let Some(wreath) = self.wreaths_four.get(&at.bound) {
            Arc::clone(wreath)
        }
        else {
            let built = Arc::new(Wreath::build(&catalogue, below.wreath(), at.bound));
            let _first = self.wreaths_four.insert(at.bound, Arc::clone(&built));
            built
        };
        let stratum = ascend(
            &*self.store,
            wreath,
            LevelThree::clone(&below),
            (at, StratumLevel::Four),
        )?;
        let held = Arc::new(stratum);
        let _first = self.held_four.insert(at, Arc::clone(&held));
        Ok(held)
    }

    /// The catalogue of `family` at `bound`, built under `budget` on the first
    /// call and held for the context's life.
    ///
    /// # Specification
    /// - ensures: under `budget` at `bound`, [`Catalogue::profiles`] for
    ///   [`Family::Profiles`], [`Catalogue::within`] for [`Family::Wirings`]
    ///   and [`Catalogue::chains_within`] for [`Family::Chains`]; a catalogue
    ///   built under one budget answers a later call under any other.
    /// - fails: [`StratumDefect::Budget`] for a catalogue past `budget`, and
    ///   [`StratumDefect::Allowance`] for one the site refuses otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// [`StratumDefect`] as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Strata::certified`].
    /// - witness: `ua::tests::a_written_statement_refuses_each_defect_by_name`
    #[spec(ensures: |ref ret| match *ret {
        | Ok(ref catalogue) => catalogue.family() == family,
        | Err(StratumDefect::Allowance { bound: refused } | StratumDefect::Budget { bound: refused, .. }) => refused == bound,
        | Err(StratumDefect::Degree { .. } | StratumDefect::Condition { .. }) => false,
    })]
    fn catalogue(
        &mut self,
        family: &Family,
        bound: ShapeSize,
        budget: ShapeBudget,
    ) -> Result<Arc<Catalogue>, StratumDefect>
    {
        if let Some(catalogue) = self
            .catalogues
            .get(family)
            .and_then(|by_bound| by_bound.get(&bound))
        {
            return Ok(Arc::clone(catalogue));
        }
        let built = match *family {
            Family::Profiles(ref profiles) => Catalogue::profiles(bound, profiles.clone(), budget),
            Family::Wirings => Catalogue::within(bound, budget),
            Family::Chains => Catalogue::chains_within(bound, budget),
        }
        .map_err(|obstruction| match obstruction {
            ShapeObstruction::PastTheBudget { counted } => StratumDefect::Budget { bound, counted },
            ShapeObstruction::TooManyVertices { .. }
            | ShapeObstruction::UnknownVertex { .. }
            | ShapeObstruction::Stick { .. }
            | ShapeObstruction::UnknownWire { .. }
            | ShapeObstruction::Carrier(_) => StratumDefect::Allowance { bound },
        })?;
        let built = Arc::new(built);
        if let Some(by_bound) = self.catalogues.get_mut(family) {
            let _first = by_bound.insert(bound, Arc::clone(&built));
        }
        else {
            let _first = self.catalogues.insert(
                family.clone(),
                BTreeMap::from([(bound, Arc::clone(&built))]),
            );
        }
        Ok(built)
    }

    /// The chain catalogue at `bound` and the wreath of it over itself, each
    /// built on the first call and held for the context's life.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`StratumDefect`] as [`Strata::catalogue`] refuses the chains.
    fn wreath_two(
        &mut self,
        bound: ShapeSize,
    ) -> Result<(Arc<Catalogue>, Arc<Wreath<Catalogue>>), StratumDefect>
    {
        let catalogue = self.catalogue(&Family::Chains, bound, ShapeBudget::EVERY)?;
        if let Some(wreath) = self.wreaths.get(&bound) {
            return Ok((catalogue, Arc::clone(wreath)));
        }
        let level: &Catalogue = &catalogue;
        let built = Arc::new(Wreath::build(level, level, bound));
        let _first = self.wreaths.insert(bound, Arc::clone(&built));
        Ok((catalogue, built))
    }

    /// Level two at the top degree of the chains' wreath at `bound`, and the
    /// wreath of the chains over level two, the wreath built on the first call
    /// and held for the context's life.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`StratumDefect`] as [`Strata::level_two`] refuses level two.
    fn wreath_three(
        &mut self,
        bound: ShapeSize,
    ) -> Result<(Arc<WreathStratum>, Arc<ThreeWreath>), StratumDefect>
    {
        let (catalogue, two) = self.wreath_two(bound)?;
        let below = self.level_two(StratumAt {
            bound,
            degree: top(&two)?,
        })?;
        if let Some(wreath) = self.wreaths_three.get(&bound) {
            return Ok((below, Arc::clone(wreath)));
        }
        let built = Arc::new(Wreath::build(&catalogue, below.wreath(), bound));
        let _first = self.wreaths_three.insert(bound, Arc::clone(&built));
        Ok((below, built))
    }

    /// Hold `stratum` at `at` over `family`'s catalogue for the context's life,
    /// and answer it.
    ///
    /// # Specification
    /// trivial.
    fn hold(
        &mut self,
        family: &Family,
        at: StratumAt,
        stratum: SegalStratum,
    ) -> Arc<SegalStratum>
    {
        let held = Arc::new(stratum);
        if let Some(by_stratum) = self.held.get_mut(family) {
            let _first = by_stratum.insert(at, Arc::clone(&held));
        }
        else {
            let _first = self
                .held
                .insert(family.clone(), BTreeMap::from([(at, Arc::clone(&held))]));
        }
        held
    }
}

/// The top degree of `wreath`'s objects, the degree its level is read at as
/// the level below the next.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`StratumDefect::Degree`] at degree zero for a wreath of no object.
fn top<Inner>(wreath: &Wreath<Inner>) -> Result<Degree, StratumDefect>
where
    Inner: gandr_theory_sites::Level,
{
    wreath
        .objects()
        .iter()
        .map(<Wreath<Inner> as gandr_theory_sites::Level>::degree)
        .max()
        .ok_or_else(|| StratumDefect::Degree {
            degree: Degree::from(0_usize),
        })
}

/// The level above `below` at `at` and `level` over `wreath`: the store's
/// image replayed when it holds one that replays at `at`'s degree, and
/// certified and handed the store to keep otherwise.
///
/// # Specification
/// - requires: `wreath` is the wreath of the chains at `at`'s bound over
///   `below`'s level, and `level` names the level above `below`'s.
/// - ensures: a stratum at `at`'s degree. The store hears an image that does
///   not replay, and keeps what is certified.
/// - fails: [`StratumDefect::Degree`] for a degree zero or past every object;
///   [`StratumDefect::Condition`] at the degree of the first object out of
///   order or not the colimit of its cells.
/// - panics: none.
/// - executable: none — the store is untrusted and answers through a trait.
///
/// # Errors
/// [`StratumDefect`] as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Strata::level_two`] and [`Strata::level_three`].
/// - witness: `ua::tests::level_two_is_kept_recalled_and_refused_by_the_store_4123`
/// - witness: `compose::tests::a_pasting_at_level_three_or_four_is_read_at_its_level_4431`
fn ascend<Below>(
    store: &dyn StratumStore,
    wreath: Arc<Wreath<Below::Level>>,
    below: Below,
    (at, level): (StratumAt, StratumLevel),
) -> Result<WreathStratum<Below>, StratumDefect>
where
    Below: Certificate,
{
    let chains = Family::Chains;
    if let Maybe::Present(image) = store.recall(&chains, at, level) {
        match WreathStratum::replay(Arc::clone(&wreath), below.clone(), &image) {
            Ok(stratum) if stratum.degree() == at.degree => return Ok(stratum),
            Ok(_) => store.refuse(&chains, at, level, Unreplayed::Degree),
            Err(why) => store.refuse(&chains, at, level, why),
        }
    }
    let stratum =
        WreathStratum::certify(wreath, at.degree, below).map_err(|refused| match refused {
            LevelUncertified::Degree { degree: refused } => {
                StratumDefect::Degree { degree: refused }
            },
            LevelUncertified::Direct { case } => StratumDefect::Condition {
                degree: <Wreath<Below::Level> as gandr_theory_sites::Level>::degree(case.source()),
            },
            LevelUncertified::Condition { failure } => StratumDefect::Condition {
                degree: <Wreath<Below::Level> as gandr_theory_sites::Level>::degree(
                    &failure.object,
                ),
            },
        })?;
    store.keep(&chains, at, level, &stratum.image());
    Ok(stratum)
}
