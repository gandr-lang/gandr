//! A level-two stratum as bytes, and its replay over a wreath.
//!
//! [`WreathStratum::image`] writes level two's canonical image: the count of
//! the wreath's objects, the degree, and each cocone by its object's index,
//! its cells, its outer grafts and its inner grafts. A cell is its column, its
//! spot, its object's index and its map's position in the hom set from its
//! object into the cocone's. Every number is a little-endian 64-bit word after
//! one leading byte, which is not level one's, so neither level's image
//! replays as the other's.
//!
//! [`WreathStratum::replay`] reads an image back over a wreath and level one's
//! certificate of its catalogue. The cocones stand at the wreath's objects of
//! degree two to the degree, in wreath order. Each is the cocone level one
//! gives its object, cell for cell and graft for graft. The replay walks no
//! agreeing family and decides no directness. Those two verdicts are what a
//! store attests beside the image, under a key that adds the level.
//!
//! # Decisions
//!
//! - **The replay rebuilds each cocone from level one and compares.** A cocone
//!   is read off level one's cocones of its outer shape and its columns, so the
//!   rebuild reads one hom set per cell. At total size 13 and degree 11 the
//!   replay checks in 0.43 ms what the certification decides in 30 ms, beside
//!   the 6.9 ms both spend building the wreath. The alternative checks each
//!   part against the wreath alone, as level one's replay does against its
//!   catalogue. Reversal: a cocone level one does not determine.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: a store's
//!   integrity never stands for validity, so the replay checks every cocone an
//!   image names against the one level one gives.
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — the
//!   strata persist in the store.

use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::Wire;

use super::Cell;
use super::InnerGraft;
use super::Spot;
use super::Two;
use super::WreathCocone;
use super::WreathStratum;
use super::cocone;
use super::within;
use crate::catalogue::ShapeIndex;
use crate::degree::Degree;
use crate::level::Level as _;
use crate::map::Membership;
use crate::segal::Graft;
use crate::segal::Leg;
use crate::stratum::SegalStratum;
use crate::stratum::StratumImage;
use crate::stratum::Unreplayed;
use crate::stratum::image::Lead;
use crate::stratum::image::Reader;
use crate::stratum::image::Word;

impl StratumImage
{
    /// Append `graft`'s wire and its two legs.
    ///
    /// # Specification
    /// trivial.
    fn graft(
        &mut self,
        graft: Graft,
    )
    {
        self.word(Word::from(usize::from(graft.wire)));
        for leg in [graft.producer, graft.consumer] {
            self.word(Word::from(usize::from(leg.vertex)));
            self.word(Word::from(usize::from(leg.wire)));
        }
    }
}

impl Reader<'_>
{
    /// The next graft: its wire and its two legs.
    ///
    /// # Specification
    /// trivial.
    fn graft(&mut self) -> Result<Graft, Unreplayed>
    {
        let wire = Wire::from(usize::from(self.word()?));
        let mut leg = || -> Result<Leg, Unreplayed> {
            Ok(Leg {
                vertex: Edge::from(usize::from(self.word()?)),
                wire: Wire::from(usize::from(self.word()?)),
            })
        };
        let producer = leg()?;
        let consumer = leg()?;
        Ok(Graft {
            wire,
            producer,
            consumer,
        })
    }
}

impl WreathStratum
{
    /// Level two's canonical image.
    ///
    /// # Specification
    /// - ensures: [`WreathStratum::replay`] over the stratum's wreath and level
    ///   one's certificate reads the image back to a stratum of the same degree
    ///   and cocones.
    /// - panics: none.
    /// - executable: none — the round trip is the witness's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — level two over the chains at total size 9 replays
    ///   from its image to its own cocones.
    /// - witness: `tests::stratum::level_two_replays_its_image_and_refuses_a_damaged_one_4123`
    #[inline]
    #[must_use]
    pub fn image(&self) -> StratumImage
    {
        let mut image = StratumImage::led(Lead::TWO);
        image.word(Word::from(self.wreath.objects().len()));
        image.word(Word::from(usize::from(self.degree)));
        image.word(Word::from(self.cocones.len()));
        for cocone in &self.cocones {
            image.word(Word::from(usize::from(cocone.object)));
            image.word(Word::from(cocone.cells.len()));
            for cell in &cocone.cells {
                image.word(Word::from(usize::from(cell.column)));
                image.word(Word::from(match cell.spot {
                    Spot::Empty => 0_usize,
                    Spot::Vertex(vertex) => usize::from(vertex).saturating_add(1),
                }));
                image.word(Word::from(usize::from(cell.object)));
                let position = self
                    .wreath
                    .hom(cell.object, cocone.object)
                    .iter()
                    .position(|map| *map == cell.map);
                // A certified cell's map is in its hom set; a word past every
                // position is refused by the replay.
                image.word(Word::from(position.unwrap_or(usize::MAX)));
            }
            image.word(Word::from(cocone.outer.len()));
            for &graft in &cocone.outer {
                image.graft(graft);
            }
            image.word(Word::from(cocone.inner.len()));
            for &inner in &cocone.inner {
                image.word(Word::from(usize::from(inner.column)));
                image.graft(inner.graft);
            }
        }
        image
    }

    /// Level two `image` holds over `wreath` and `below`, its structure
    /// checked.
    ///
    /// # Specification
    /// - requires: `wreath` is built over `below`'s catalogue as both its outer
    ///   and its inner level, as [`WreathStratum::certify`] requires.
    /// - ensures: on success, a stratum of the image's degree whose cocones
    ///   stand at the wreath's objects of degree two to the degree, each the
    ///   cocone level one gives its object.
    /// - fails: [`Unreplayed`], the first check that fails, in the order of the
    ///   image's parts.
    /// - panics: none.
    /// - intension: the replay reads level one's cocones and one hom set per
    ///   cell; it walks no agreeing family and decides no directness.
    /// - executable: none — the checks are the body's; the witness damages each
    ///   part.
    ///
    /// # Errors
    /// [`Unreplayed`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — level two's own image replays, and an image damaged
    ///   at its leading byte, its object count, its degree, its cocones'
    ///   objects, a cell and a graft is refused under each name. A level-one
    ///   image is refused as malformed.
    /// - witness: `tests::stratum::level_two_replays_its_image_and_refuses_a_damaged_one_4123`
    #[inline]
    pub fn replay(
        wreath: Arc<Two>,
        below: SegalStratum,
        image: &StratumImage,
    ) -> Result<Self, Unreplayed>
    {
        let mut reader = Reader::opened(image, Lead::TWO)?;
        if usize::from(reader.word()?) != wreath.objects().len() {
            return Err(Unreplayed::Catalogue);
        }
        let degree = Degree::from(usize::from(reader.word()?));
        if degree < Degree::from(1_usize)
            || wreath
                .objects()
                .iter()
                .all(|object| Two::degree(object) < degree)
        {
            return Err(Unreplayed::Degree);
        }
        // Each count is the stream's claim, so it bounds a loop and never
        // reserves memory: a short stream is refused when it runs out.
        let mut read = Vec::new();
        for _cocone in 0 .. usize::from(reader.word()?) {
            let object = ShapeIndex::from(usize::from(reader.word()?));
            let mut cells = Vec::new();
            for _cell in 0 .. usize::from(reader.word()?) {
                let column = Edge::from(usize::from(reader.word()?));
                let spot = usize::from(reader.word()?)
                    .checked_sub(1)
                    .map_or(Spot::Empty, |vertex| Spot::Vertex(Edge::from(vertex)));
                let at = ShapeIndex::from(usize::from(reader.word()?));
                cells.push((column, spot, at, usize::from(reader.word()?)));
            }
            let mut outer = Vec::new();
            for _graft in 0 .. usize::from(reader.word()?) {
                outer.push(reader.graft()?);
            }
            let mut inner = Vec::new();
            for _graft in 0 .. usize::from(reader.word()?) {
                let column = Edge::from(usize::from(reader.word()?));
                inner.push(InnerGraft {
                    column,
                    graft: reader.graft()?,
                });
            }
            read.push(Read {
                object,
                cells,
                outer,
                inner,
            });
        }
        if reader.finished() == Membership::Outside {
            return Err(Unreplayed::Malformed);
        }
        let expected = wreath
            .objects()
            .iter()
            .enumerate()
            .filter(|&(_, object)| within(object, degree) == Membership::Inside)
            .map(|(position, _)| ShapeIndex::from(position));
        if !expected.eq(read.iter().map(|cocone| cocone.object)) {
            return Err(Unreplayed::Cocones);
        }
        let mut cocones = Vec::with_capacity(read.len());
        for cocone in read {
            cocones.push(replayed(&wreath, &below, cocone)?);
        }
        Ok(Self {
            wreath,
            below,
            degree,
            cocones,
        })
    }
}

/// One cocone as an image holds it: the object's index, each cell's column,
/// spot, object and hom-set position, and the grafts.
struct Read
{
    /// The object's index.
    object: ShapeIndex,
    /// Each cell's column, spot, object and its map's position in the hom
    /// set into the cocone's object.
    cells: Vec<(Edge, Spot, ShapeIndex, usize)>,
    /// The outer grafts.
    outer: Vec<Graft>,
    /// The inner grafts.
    inner: Vec<InnerGraft>,
}

/// The cocone `read` holds, checked against the one level one gives its
/// object in `wreath`.
///
/// # Specification
/// - ensures: on success, the cocone [`cocone`] builds at the object over
///   `below`, cell for cell and graft for graft.
/// - fails: [`Unreplayed::Cocone`] at the object when a cell's position is past
///   its hom set, or the cocone is not level one's.
/// - panics: none.
/// - executable: none — the checks are the body's; the witness damages a cell's
///   position and a graft.
///
/// # Errors
/// [`Unreplayed::Cocone`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`WreathStratum::replay`].
/// - witness: `tests::stratum::level_two_replays_its_image_and_refuses_a_damaged_one_4123`
fn replayed(
    wreath: &Two,
    below: &SegalStratum,
    read: Read,
) -> Result<WreathCocone, Unreplayed>
{
    let misplaced = Unreplayed::Cocone { shape: read.object };
    let mut cells = Vec::with_capacity(read.cells.len());
    for (column, spot, at, position) in read.cells {
        let map = wreath
            .hom(at, read.object)
            .get(position)
            .cloned()
            .ok_or(misplaced)?;
        cells.push(Cell {
            column,
            spot,
            object: at,
            map,
        });
    }
    let replayed = WreathCocone {
        object: read.object,
        cells: cells.into_boxed_slice(),
        outer: read.outer.into_boxed_slice(),
        inner: read.inner.into_boxed_slice(),
    };
    let object = wreath
        .objects()
        .get(usize::from(read.object))
        .ok_or(misplaced)?;
    if cocone(wreath, below, (read.object, object)).as_ref() == Ok(&replayed) {
        Ok(replayed)
    }
    else {
        Err(misplaced)
    }
}
