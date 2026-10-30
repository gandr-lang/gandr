//! A certified stratum as bytes, and its replay over a catalogue.
//!
//! [`SegalStratum::image`] writes a stratum's canonical image: the count of
//! the catalogue's shapes, the degree, each corolla by its catalogue index,
//! and each cocone by its shape's index, its inclusions as a corolla index
//! and a position in the corolla's hom set into the shape, and its grafts.
//! Every number is a little-endian 64-bit word after one version byte.
//!
//! [`SegalStratum::replay`] reads an image back over a catalogue and checks
//! its structure against it. The corollas are the catalogue's shapes of degree
//! one, and their automorphisms are rebuilt from the catalogue. The cocones
//! stand at the shapes of degree two to the degree, in catalogue order. Each
//! inclusion is a raising map of its hom set whose one image is its vertex.
//! Each graft glues the legs its inclusions send onto one inner wire. The
//! replay walks no Segal family and decides no corolla condition. Those two
//! verdicts are what a store attests beside the image, under the key of
//! [`SitesBuild`], the bound and the degree.
//!
//! # Decisions
//!
//! - **The replay checks structure, and attestation carries the verdicts.** At
//!   bound 7 and degree 7 the replay checks in 0.18 ms what the walk certifies
//!   in 2.56 s. The alternative stores a certificate the replay decides, each
//!   colimit's mediating maps among them. Reversal: a consumer that believes no
//!   installation's key.
//! - **A corolla is stored by its index alone.** Its automorphisms are the
//!   included maps of its hom set to itself, so the catalogue determines them.
//!   The alternative stores their positions and checks them. Reversal: a
//!   corolla whose automorphisms the catalogue does not determine.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: a store's
//!   integrity never stands for validity, so the replay checks every part an
//!   image names against the catalogue.
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — the
//!   strata persist in the store.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::Wire;
use quenchant_shape::shape::Maybe;

use super::Corolla;
use super::Legs;
use super::SegalStratum;
use super::Vacuity;
use super::corollas_of;
use crate::catalogue::Catalogue;
use crate::catalogue::ShapeIndex;
use crate::degree::Degree;
use crate::map::Membership;
use crate::map::VertexSet;
use crate::segal::Cocone;
use crate::segal::Graft;
use crate::segal::Inclusion;
use crate::segal::Leg;
use crate::shape::End;

wrapper! {
    /// The byte an image leads with, which names its level and its version.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct Lead(u8);
}

impl Lead
{
    /// The lead of a level-one image.
    ///
    /// # Specification
    /// trivial.
    pub const ONE: Self = Self(1);
    /// The lead of a level-two image.
    ///
    /// # Specification
    /// trivial.
    pub const TWO: Self = Self(2);
}

wrapper! {
    /// One word of an image: a count, a catalogue index, a hom-set position,
    /// a vertex or a wire.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct Word(usize);
}

/// The theory crates' build identity, which `build.rs` writes.
const SITES_BUILD: &[u8; 32] = include_bytes!(concat!(env!("OUT_DIR"), "/sites-build"));

/// The build of the theory crates that certifies a stratum: a digest of every
/// theory crate's files and the workspace lock, which a stored stratum's key
/// binds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SitesBuild([u8; 32]);

impl SitesBuild
{
    /// This build's identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn current() -> Self
    {
        Self(*SITES_BUILD)
    }
}

impl From<SitesBuild> for [u8; 32]
{
    /// The digest.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(build: SitesBuild) -> Self
    {
        build.0
    }
}

/// A certified stratum's canonical bytes.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct StratumImage(Vec<u8>);

impl From<Vec<u8>> for StratumImage
{
    /// The image whose bytes are `bytes`, as a store read them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl From<StratumImage> for Vec<u8>
{
    /// The bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(image: StratumImage) -> Self
    {
        image.0
    }
}

impl AsRef<[u8]> for StratumImage
{
    /// The bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

impl StratumImage
{
    /// An image holding `lead` alone.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn led(lead: Lead) -> Self
    {
        Self(Vec::from([lead.0]))
    }

    /// Append `word`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn word(
        &mut self,
        word: Word,
    )
    {
        self.0.extend_from_slice(
            &u64::try_from(usize::from(word))
                .unwrap_or(u64::MAX)
                .to_le_bytes(),
        );
    }
}

/// Why an image does not replay over a catalogue.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unreplayed
{
    /// The bytes do not read as an image: another version, a stream that
    /// ends early or runs on, or a number past the host's addresses.
    Malformed,
    /// The image counts another number of shapes than the catalogue holds,
    /// or of objects than the wreath holds.
    Catalogue,
    /// The degree is zero, or past the catalogue's or the wreath's reach.
    Degree,
    /// The corollas are not the catalogue's shapes of degree one, in
    /// catalogue order.
    Corollas,
    /// The cocones do not stand at the catalogue's shapes, or the wreath's
    /// objects, of degree two to the image's degree, in their order.
    Cocones,
    /// An inclusion or a graft of the shape's cocone does not stand in the
    /// catalogue, or a cell or a graft of the object's cocone is not the one
    /// level one gives.
    Cocone
    {
        /// The shape, or the wreath's object.
        shape: ShapeIndex,
    },
}

impl fmt::Display for Unreplayed
{
    /// Names what the image fails at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Malformed => f.write_str("the bytes are no stratum image"),
            Self::Catalogue => f.write_str("the image counts another catalogue's shapes"),
            Self::Degree => f.write_str("the degree is no stratum of the catalogue"),
            Self::Corollas => f.write_str("the corollas are not the catalogue's"),
            Self::Cocones => f.write_str("the cocones stand at other shapes"),
            Self::Cocone { shape } => write!(
                f,
                "the cocone of shape {} does not stand in the catalogue",
                usize::from(shape)
            ),
        }
    }
}

/// A cursor over an image's bytes.
#[repr(transparent)]
pub struct Reader<'bytes>(&'bytes [u8]);

impl<'bytes> Reader<'bytes>
{
    /// A cursor past `image`'s lead, when it is `lead`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Unreplayed::Malformed`] for an empty image or another lead.
    pub fn opened(
        image: &'bytes StratumImage,
        lead: Lead,
    ) -> Result<Self, Unreplayed>
    {
        match image.0.split_first() {
            Some((&first, rest)) if first == lead.0 => Ok(Self(rest)),
            Some(_) | None => Err(Unreplayed::Malformed),
        }
    }
}

impl Reader<'_>
{
    /// Whether every byte is read.
    ///
    /// # Specification
    /// trivial.
    pub const fn finished(&self) -> Membership
    {
        if self.0.is_empty() {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// The next word.
    ///
    /// # Specification
    /// trivial.
    pub fn word(&mut self) -> Result<Word, Unreplayed>
    {
        let (word, rest) = self
            .0
            .split_first_chunk::<8>()
            .ok_or(Unreplayed::Malformed)?;
        self.0 = rest;
        usize::try_from(u64::from_le_bytes(*word))
            .map(Word::from)
            .map_err(|_wide| Unreplayed::Malformed)
    }
}

/// One cocone as an image holds it: the shape's index, each inclusion's
/// corolla and hom-set position, and the grafts.
struct Read
{
    /// The shape's index.
    shape: ShapeIndex,
    /// Each vertex's corolla and the inclusion's position in its hom set.
    inclusions: Vec<(ShapeIndex, usize)>,
    /// The grafts, in wire order.
    grafts: Vec<Graft>,
}

impl SegalStratum
{
    /// The stratum's canonical image.
    ///
    /// # Specification
    /// - ensures: [`SegalStratum::replay`] over the stratum's catalogue reads
    ///   the image back to a stratum of the same degree, corollas and cocones.
    /// - panics: none.
    /// - executable: none — the round trip is the witness's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stratum at bound 5 replays from its image to its
    ///   own corollas and cocones.
    /// - witness: `tests::stratum::a_stratum_replays_its_image_and_refuses_a_damaged_one_4034`
    #[inline]
    #[must_use]
    pub fn image(&self) -> StratumImage
    {
        let mut image = StratumImage::led(Lead::ONE);
        image.word(Word::from(self.catalogue.shapes().len()));
        image.word(Word::from(usize::from(self.degree)));
        image.word(Word::from(self.corollas.len()));
        for corolla in &self.corollas {
            image.word(Word::from(usize::from(corolla.index)));
        }
        image.word(Word::from(self.cocones.len()));
        for cocone in &self.cocones {
            image.word(Word::from(usize::from(cocone.shape())));
            image.word(Word::from(cocone.inclusions().len()));
            for inclusion in cocone.inclusions() {
                let position = match self.catalogue.maps(inclusion.corolla, cocone.shape()) {
                    Maybe::Present(maps) => maps.iter().position(|map| *map == inclusion.map),
                    Maybe::Absent(_) => None,
                };
                image.word(Word::from(usize::from(inclusion.corolla)));
                // A certified cocone's inclusion is in its hom set; a word
                // past every position is refused by the replay.
                image.word(Word::from(position.unwrap_or(usize::MAX)));
            }
            image.word(Word::from(cocone.grafts().len()));
            for graft in cocone.grafts() {
                image.word(Word::from(usize::from(graft.wire)));
                for leg in [graft.producer, graft.consumer] {
                    image.word(Word::from(usize::from(leg.vertex)));
                    image.word(Word::from(usize::from(leg.wire)));
                }
            }
        }
        image
    }

    /// The stratum `image` holds over `catalogue`, its structure checked.
    ///
    /// # Specification
    /// - ensures: on success, a stratum of the image's degree whose corollas
    ///   are the catalogue's shapes of degree one with their automorphisms,
    ///   whose cocones stand at its shapes of degree two to the degree, each
    ///   inclusion a raising map of its hom set onto its vertex alone and each
    ///   graft the legs its inclusions send onto an inner wire, and which names
    ///   the degrees above the catalogue's top shape vacuous, as certification
    ///   does.
    /// - fails: [`Unreplayed`], the first check that fails, in the order of the
    ///   image's parts.
    /// - panics: none.
    /// - intension: the replay reads the hom sets the inclusions name and the
    ///   corollas' hom sets to themselves; it walks no Segal family and decides
    ///   no corolla condition.
    /// - executable: none — the checks are the body's; the witness damages each
    ///   part.
    ///
    /// # Errors
    /// [`Unreplayed`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stratum's own image replays, and an image damaged
    ///   at its version, its catalogue, its degree, its corollas, its cocones'
    ///   shapes, an inclusion and a graft is refused under each name.
    /// - witness: `tests::stratum::a_stratum_replays_its_image_and_refuses_a_damaged_one_4034`
    #[inline]
    pub fn replay(
        catalogue: Arc<Catalogue>,
        image: &StratumImage,
    ) -> Result<Self, Unreplayed>
    {
        let mut reader = Reader::opened(image, Lead::ONE)?;
        if usize::from(reader.word()?) != catalogue.shapes().len() {
            return Err(Unreplayed::Catalogue);
        }
        let degree = Degree::from(usize::from(reader.word()?));
        let one = Degree::from(1_usize);
        if degree < one || catalogue.reach() < degree {
            return Err(Unreplayed::Degree);
        }
        // Each count is the stream's claim, so it bounds a loop and never
        // reserves memory: a short stream is refused when it runs out.
        let mut indices = Vec::new();
        for _corolla in 0 .. usize::from(reader.word()?) {
            indices.push(ShapeIndex::from(usize::from(reader.word()?)));
        }
        let mut read = Vec::new();
        for _cocone in 0 .. usize::from(reader.word()?) {
            let shape = ShapeIndex::from(usize::from(reader.word()?));
            let mut inclusions = Vec::new();
            for _inclusion in 0 .. usize::from(reader.word()?) {
                inclusions.push((
                    ShapeIndex::from(usize::from(reader.word()?)),
                    usize::from(reader.word()?),
                ));
            }
            let mut grafts = Vec::new();
            for _graft in 0 .. usize::from(reader.word()?) {
                let wire = Wire::from(usize::from(reader.word()?));
                let mut leg = || -> Result<Leg, Unreplayed> {
                    Ok(Leg {
                        vertex: Edge::from(usize::from(reader.word()?)),
                        wire: Wire::from(usize::from(reader.word()?)),
                    })
                };
                let producer = leg()?;
                let consumer = leg()?;
                grafts.push(Graft {
                    wire,
                    producer,
                    consumer,
                });
            }
            read.push(Read {
                shape,
                inclusions,
                grafts,
            });
        }
        if !reader.0.is_empty() {
            return Err(Unreplayed::Malformed);
        }
        let corollas = corollas_of(&catalogue);
        if !corollas.iter().map(Corolla::index).eq(indices) {
            return Err(Unreplayed::Corollas);
        }
        let stands = |shape: ShapeIndex| {
            matches!(catalogue.shape(shape), Maybe::Present(form)
                if Degree::of(form) > one && Degree::of(form) <= degree)
        };
        let expected = catalogue
            .entries()
            .map(|(index, _)| index)
            .filter(|&index| stands(index));
        if !expected.eq(read.iter().map(|cocone| cocone.shape)) {
            return Err(Unreplayed::Cocones);
        }
        let mut cocones = Vec::with_capacity(read.len());
        for cocone in read {
            cocones.push(replayed(&catalogue, &corollas, cocone)?);
        }
        let vacuity = Vacuity::new(Degree::top(catalogue.shapes()), degree);
        Ok(Self {
            catalogue,
            degree,
            vacuity,
            corollas,
            cocones,
        })
    }
}

/// The cocone `read` holds, checked against `catalogue` and its `corollas`.
///
/// # Specification
/// - ensures: on success, one inclusion per vertex of the shape, each the map
///   at its position in the hom set from the corolla of the vertex's legs,
///   raising, with the vertex its one image; one graft per inner wire both of
///   whose ends are vertices, in wire order, each leg a wire of its vertex's
///   corolla that the vertex's inclusion sends onto the inner wire.
/// - fails: [`Unreplayed::Cocone`] at the shape when any of these does not
///   hold.
/// - panics: none.
/// - executable: none — the checks are the body's; the witness damages an
///   inclusion and a graft.
///
/// # Errors
/// [`Unreplayed::Cocone`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SegalStratum::replay`].
/// - witness: `tests::stratum::a_stratum_replays_its_image_and_refuses_a_damaged_one_4034`
fn replayed(
    catalogue: &Catalogue,
    corollas: &[Corolla],
    read: Read,
) -> Result<Cocone, Unreplayed>
{
    let refused = Unreplayed::Cocone { shape: read.shape };
    let Maybe::Present(shape) = catalogue.shape(read.shape)
    else {
        return Err(refused);
    };
    if read.inclusions.len() != usize::from(shape.vertex_count()) {
        return Err(refused);
    }
    let mut inclusions = Vec::with_capacity(read.inclusions.len());
    for (vertex, (corolla, position)) in shape.vertices().zip(read.inclusions) {
        let profile = Legs::of(shape, vertex).profile();
        if !corollas
            .iter()
            .any(|held| held.index == corolla && held.profile() == profile)
        {
            return Err(refused);
        }
        let Maybe::Present(maps) = catalogue.maps(corolla, read.shape)
        else {
            return Err(refused);
        };
        let Some(map) = maps.get(position)
        else {
            return Err(refused);
        };
        if map.raising() != Membership::Inside || map.images() != [VertexSet::single(vertex)] {
            return Err(refused);
        }
        inclusions.push(Inclusion {
            corolla,
            map: map.clone(),
        });
    }
    let mut inner = shape
        .ends()
        .iter()
        .enumerate()
        .filter_map(
            |(position, ends)| match (ends.producer(), ends.consumer()) {
                (End::Vertex(producer), End::Vertex(consumer)) => {
                    Some((Wire::from(position), producer, consumer))
                },
                _ => None,
            },
        );
    for graft in &read.grafts {
        let Some((wire, producer, consumer)) = inner.next()
        else {
            return Err(refused);
        };
        if graft.wire != wire
            || graft.producer.vertex != producer
            || graft.consumer.vertex != consumer
        {
            return Err(refused);
        }
        for leg in [graft.producer, graft.consumer] {
            let lands = inclusions
                .get(usize::from(leg.vertex))
                .and_then(|inclusion| inclusion.map.wires().get(usize::from(leg.wire)))
                .is_some_and(|image| *image == wire);
            if !lands {
                return Err(refused);
            }
        }
    }
    if inner.next().is_some() {
        return Err(refused);
    }
    Ok(Cocone::replayed(
        read.shape,
        inclusions.into_boxed_slice(),
        Box::from(read.grafts),
    ))
}
