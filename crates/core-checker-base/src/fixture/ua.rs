//! The profiles, catalogues, corollas and answering stores that the
//! univalence witnesses build. Its unit tests and the tests that readmit
//! through the bridge read them both.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;

use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Family;
use gandr_theory_sites::GeneratorCount;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Species;
use gandr_theory_sites::StratumImage;
use gandr_theory_sites::Unreplayed;
use quenchant_shape::shape::Maybe;

use crate::ua::StratumAt;
use crate::ua::StratumLevel;
use crate::ua::StratumStore;
use crate::ua::recalled;

/// A profile's legs: its inputs, then its outputs.
#[derive(Clone, Copy, Debug)]
pub struct Legs(pub usize, pub usize);

/// The profile of `inputs` input legs and `outputs` output legs.
///
/// # Specification
/// trivial.
pub fn profile(Legs(inputs, outputs): Legs) -> Profile
{
    Profile {
        inputs: PortCount::from(inputs),
        outputs: PortCount::from(outputs),
    }
}

/// Two binary generators and nothing else: at the binary corolla four
/// elements, generator by generator, each attached in order and then crossed.
///
/// # Specification
/// trivial.
pub fn two() -> Species
{
    Species::new(BTreeMap::from([(
        profile(Legs(2, 1)),
        GeneratorCount::from(2),
    )]))
}

/// The catalogue at size four: the binary corolla is its largest.
///
/// # Specification
/// trivial.
pub fn catalogue() -> Arc<Catalogue>
{
    Arc::new(Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds"))
}

/// The catalogue position of the corolla of `legs`.
///
/// # Specification
/// trivial.
pub fn corolla(
    stratum: &SegalStratum,
    legs: Legs,
) -> ShapeIndex
{
    match stratum.corolla(profile(legs)) {
        Maybe::Present(corolla) => corolla.index(),
        Maybe::Absent(reason) => panic!("the corolla is within the bound: {reason:?}"),
    }
}

/// What a test store was handed: the strata kept, the refusals heard as
/// expected, and the others.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Counts
{
    /// The strata handed to keep.
    pub kept: usize,
    /// The refusals heard as expected.
    pub refused: usize,
    /// The refusals heard otherwise.
    pub other: usize,
}

/// A store answering one image, or none, at every stratum, counting the
/// strata it is handed to keep and the refusals it hears, as expected or not.
#[derive(Debug)]
pub struct Answering
{
    /// The image answered.
    image: Maybe<StratumImage, recalled::Absent>,
    /// The refusal the store expects to hear.
    expected: Unreplayed,
    /// The strata handed to keep.
    kept: AtomicUsize,
    /// The refusals heard as expected.
    refused: AtomicUsize,
    /// The refusals heard otherwise.
    other: AtomicUsize,
}

impl Answering
{
    /// The store answering `image`, expecting `expected` when it refuses.
    ///
    /// # Specification
    /// trivial.
    pub fn new(
        image: Maybe<StratumImage, recalled::Absent>,
        expected: Unreplayed,
    ) -> Arc<Self>
    {
        Arc::new(Self {
            image,
            expected,
            kept: AtomicUsize::new(0),
            refused: AtomicUsize::new(0),
            other: AtomicUsize::new(0),
        })
    }

    /// The strata kept, the expected refusals and the others.
    ///
    /// # Specification
    /// trivial.
    pub fn counts(&self) -> Counts
    {
        Counts {
            kept: self.kept.load(Ordering::Relaxed),
            refused: self.refused.load(Ordering::Relaxed),
            other: self.other.load(Ordering::Relaxed),
        }
    }
}

impl StratumStore for Answering
{
    /// The image the store answers.
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
        self.image.clone()
    }

    /// Count one stratum kept.
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
        let _before = self.kept.fetch_add(1, Ordering::Relaxed);
    }

    /// Count one refusal, as expected or not.
    ///
    /// # Specification
    /// trivial.
    fn refuse(
        &self,
        _family: &Family,
        _at: StratumAt,
        _level: StratumLevel,
        why: Unreplayed,
    )
    {
        let count = if why == self.expected {
            &self.refused
        }
        else {
            &self.other
        };
        let _before = count.fetch_add(1, Ordering::Relaxed);
    }
}

/// The table of `translator` at `corolla`, from the elements `from` into the
/// elements `to`, as the univalence derivation reads it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As the derivation's reading: the refusal where the translator's run sticks
/// or leaves the code.
pub fn tabulated(
    context: &mut crate::context::CheckingContext<'_>,
    corolla: ShapeIndex,
    translator: gandr_core_term::ValueId,
    elements: (
        &[gandr_theory_sites::Element],
        &[gandr_theory_sites::Element],
    ),
) -> Result<gandr_theory_sites::Table, crate::ua::UaRefusal>
{
    crate::ua::tabulated(context, corolla, translator, elements)
}
