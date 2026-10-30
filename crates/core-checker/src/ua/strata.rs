//! Where a context's certified strata come from.
//!
//! A `ua[n, k]` statement names the stratum of degree `n` over the sub-site
//! of the wiring catalogue at bound `k` on the corollas its two species
//! inhabit, and a `compose[n, k]` composite the one over the chain catalogue
//! ([`Family`]). A context builds each catalogue it needs once and holds each
//! stratum it certifies or recalls for its own life. No static outlives the
//! context, so a stratum crosses contexts and processes only through a store,
//! which keeps no chain stratum.
//!
//! A run that keeps strata hands each context a [`StratumStore`]. Before it
//! certifies, the context asks the store for the stratum's image and replays
//! it over its own catalogue ([`SegalStratum::replay`]). An image that does
//! not replay is refused to the store by name, and the context certifies
//! afresh. What the context certifies, it hands the store to keep. The store
//! answers integrity and attestation, and the replay checks the structure. A
//! context handed no store keeps [`NoStratumStore`], which recalls and keeps
//! nothing. The checker depends on no storage crate, so the driver implements
//! the store.
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
use gandr_theory_sites::Degree;
use gandr_theory_sites::Family;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::ShapeBudget;
use gandr_theory_sites::ShapeObstruction;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::StratumImage;
use gandr_theory_sites::Uncertified;
use gandr_theory_sites::Unreplayed;
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
    /// The image of the stratum at `at` over `family`'s catalogue, when the
    /// store holds one it believes.
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
    ) -> Maybe<StratumImage, recalled::Absent>;

    /// Keep the stratum at `at` over `family`'s catalogue, which this process
    /// certified.
    ///
    /// # Specification
    /// - requires: `stratum` was certified at `at` over `family`'s catalogue in
    ///   this process.
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
        stratum: &SegalStratum,
    );

    /// Hear that the image recalled at `at` over `family`'s catalogue does not
    /// replay, and why.
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
        _stratum: &SegalStratum,
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

    /// The stratum at `at` over the catalogue of `family`: at its bound,
    /// [`Catalogue::profiles`] under `budget` for [`Family::Profiles`] and
    /// [`Catalogue::within`] for [`Family::Wirings`], each recalled from the
    /// store and replayed when it holds one, and [`Catalogue::chains`] for
    /// [`Family::Chains`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stratum [`SegalStratum::certify`] gives at `at`, or one
    ///   the store's image replays to at `at`'s degree, over the catalogue of
    ///   `family` at `at`'s bound; every call at one family and one stratum
    ///   answers the stratum the first answered.
    /// - fails: [`StratumDefect::Allowance`] for a bound past
    ///   [`ShapeSize::LARGEST`] or a catalogue the site refuses;
    ///   [`StratumDefect::Budget`] for a family past the chains whose bound
    ///   holds more wirings than `budget`; [`StratumDefect::Degree`] and
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
        let catalogue = if let Some(catalogue) = self
            .catalogues
            .get(family)
            .and_then(|by_bound| by_bound.get(&bound))
        {
            Arc::clone(catalogue)
        }
        else {
            let built = match *family {
                Family::Profiles(ref profiles) => {
                    Catalogue::profiles(bound, profiles.clone(), budget)
                },
                Family::Wirings => Catalogue::within(bound, budget),
                Family::Chains => Catalogue::chains(bound),
            }
            .map_err(|obstruction| match obstruction {
                ShapeObstruction::PastTheBudget { counted } => {
                    StratumDefect::Budget { bound, counted }
                },
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
            built
        };
        let kept = *family != Family::Chains;
        if kept && let Maybe::Present(image) = self.store.recall(family, at) {
            match SegalStratum::replay(Arc::clone(&catalogue), &image) {
                Ok(stratum) if stratum.degree() == at.degree => {
                    return Ok(self.hold(family, at, stratum));
                },
                Ok(_) => self.store.refuse(family, at, Unreplayed::Degree),
                Err(why) => self.store.refuse(family, at, why),
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
            self.store.keep(family, at, &stratum);
        }
        Ok(self.hold(family, at, stratum))
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
