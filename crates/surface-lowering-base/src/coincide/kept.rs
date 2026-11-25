//! Rule blocks' decisions kept across lowerings, so that a block a revision
//! leaves as it was is not decided again.
//!
//! [`decide`] reads a block's oriented description and the cell gate's
//! elaboration of it, which the description and the way its members were
//! elaborated fix. Where the block is written reaches the answer only through
//! the spans it reports, each a rule's provenance or the declaration's
//! interval. A block is kept under its description with every provenance
//! counted from the declaration's start, beside the declaration's length and
//! the way its members were elaborated; its answer is kept with every span
//! counted the same way, beside the cells deciding appended to each store. A
//! block found again — the same rules wherever an edit moved them — is
//! answered by appending those cells and moving the spans to where the
//! declaration now starts, without deciding.
//!
//! A lowering that keeps nothing passes [`Decisions::none`], which reads no
//! key; an editor's session holds [`Decisions::held`] across its revisions.

use alloc::vec::Vec;
use core::convert::Infallible;

use anodized::spec;
use gandr_surface_syntax::ByteLength;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellCount;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_computads::AdmittedFaceIndex;
use gandr_theory_computads::PresentedRules;
use gandr_theory_computads::TermAlphabet;
use gandr_theory_computads::presented_reading;
use gandr_theory_levitation::SurfaceSpan;
use gandr_theory_levitation::TheoryDesc;
use quenchant_shape::shape::Maybe;

use super::CoherenceFault;
use super::Coincidence;
use super::decide;
use crate::desc_cells::CircuitCell;
use crate::description::DescriptionGrade;

/// The most blocks [`Decisions::held`] keeps before it lets the one asked for
/// longest ago go: the rule blocks of the few documents an editor has open.
const DECISIONS_HELD: usize = 16;

/// A block's answer: its coincidence, or the fault and the span it stands at.
type Answer = Result<Coincidence, (ByteSpan, CoherenceFault)>;

/// How a declaration's members were elaborated into cells.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Members
{
    /// As a `theory` block's presentation.
    Theory,
    /// As a `data` family's description.
    Data,
}

/// A rule block as its decision reads it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub struct Block<'block>
{
    /// The block's description, its rules oriented.
    pub reading: &'block TheoryDesc<DescriptionGrade>,
    /// The declaration's interval.
    pub at: ByteSpan,
    /// How the cell gate elaborated its members.
    pub members: Members,
}

/// What selects a kept decision: the block wherever it is written.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Key
{
    /// The oriented description, every provenance counted from the
    /// declaration's start.
    reading: TheoryDesc<DescriptionGrade>,
    /// The declaration's length, which a span falling back to the declaration
    /// reads.
    length: ByteLength,
    /// How the members were elaborated.
    members: Members,
}

impl Key
{
    /// The key of `block`; `None` when a provenance starts or ends before the
    /// declaration does, so that no span of its answer counts from there.
    ///
    /// # Specification
    /// - ensures: [`Some`] of `block`'s reading with every rule's and every
    ///   circuit sphere's provenance less the declaration's start, its length
    ///   and its members, exactly when no provenance endpoint lies before that
    ///   start.
    /// - panics: none.
    /// - executable: none — the clause restates the walk over every face.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block moved by a comment keys as it did before the
    ///   move, and a block whose rule changed keys apart from it.
    /// - witness: `coincide::kept::tests::a_block_an_edit_moves_is_answered_as_decided_where_it_stands_1547`
    /// - witness: `coincide::kept::tests::a_block_whose_rule_changed_is_decided_again_1547`
    fn of(block: &Block<'_>) -> Option<Self>
    {
        let origin = usize::from(block.at.start());
        let mut reading = block.reading.clone();
        let faces = reading.rules.iter_mut().chain(
            reading
                .circuits
                .iter_mut()
                .map(|circuit| &mut circuit.sphere),
        );
        for face in faces {
            face.provenance = SurfaceSpan::new(
                usize::from(face.provenance.start)
                    .checked_sub(origin)?
                    .into(),
                usize::from(face.provenance.end).checked_sub(origin)?.into(),
            );
        }
        Some(Self {
            reading,
            length: block.at.length(),
            members: block.members,
        })
    }
}

/// One block's decision, its spans counted from the declaration's start.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Kept
{
    /// The block it was decided for.
    key: Key,
    /// The answer.
    answer: Answer,
    /// The cells deciding appended to the rewriting store, in order.
    commands: Vec<Cell<SequentAlphabet>>,
    /// The cells deciding appended to the presented reading's store, in order.
    terms: Vec<Cell<TermAlphabet>>,
}

/// The rule blocks' decisions a lowering reuses.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct Decisions
{
    /// The most blocks kept.
    held: usize,
    /// The blocks kept, the one asked for last at the end.
    kept: Vec<Kept>,
}

impl Decisions
{
    /// Decisions that keep nothing: every block is decided, and no key is read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn none() -> Self
    {
        Self {
            held: 0,
            kept: Vec::new(),
        }
    }

    /// Decisions that keep the blocks asked for last, for a session lowering
    /// one document revision after another.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn held() -> Self
    {
        Self {
            held: DECISIONS_HELD,
            kept: Vec::new(),
        }
    }

    /// Decide `block`, as [`decide`] does, from the decision kept for it when
    /// there is one.
    ///
    /// # Specification
    /// - requires: as [`decide`]'s, `store`, `faces`, `presented` and
    ///   `circuits` the cell gate's elaboration of `block.reading` as
    ///   `block.members` says, and `block.at` the declaration's interval.
    /// - ensures: the answer and the cells appended to `store` and to the
    ///   presented reading's store are [`decide`]'s. A block kept under its key
    ///   is answered without deciding: its kept cells are appended in the order
    ///   deciding appended them and its kept spans moved to where `block.at`
    ///   starts. A block decided is kept, when these decisions keep any and
    ///   every span of its answer counts from the declaration's start, the one
    ///   asked for longest ago let go past [`DECISIONS_HELD`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`decide`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused block and a completed one, moved by a
    ///   comment, are answered as deciding them where they stand does, each
    ///   from the one decision kept; a block whose rule changed is decided
    ///   again.
    /// - witness: `coincide::kept::tests::a_block_an_edit_moves_is_answered_as_decided_where_it_stands_1547`
    /// - witness: `coincide::kept::tests::a_block_whose_rule_changed_is_decided_again_1547`
    #[spec(ensures: self.kept.len() <= self.held)]
    pub(crate) fn decide(
        &mut self,
        block: Block<'_>,
        store: &mut CellStore,
        faces: &[(AdmittedFaceIndex, CellId)],
        presented: &mut Maybe<PresentedRules, presented_reading::Absent>,
        circuits: &[CircuitCell],
    ) -> Answer
    {
        let origin = block.at.start();
        let Some(key) = (self.held > 0).then(|| Key::of(&block)).flatten()
        else {
            return decide(block.reading, block.at, store, faces, presented, circuits);
        };
        if let Some(found) = self.kept.iter().position(|kept| kept.key == key) {
            let kept = self.kept.remove(found);
            for cell in &kept.commands {
                let _appended = store.insert(cell.clone());
            }
            if let Maybe::Present(ref mut reading) = *presented {
                for cell in &kept.terms {
                    let _appended = reading.store.insert(cell.clone());
                }
            }
            let Ok(answer) = moved(&kept.answer, |span| {
                Ok::<_, Infallible>(relocated(span, origin))
            });
            self.kept.push(kept);
            return answer;
        }
        let commands_before = store.len();
        let terms_before = match *presented {
            Maybe::Present(ref reading) => reading.store.len(),
            Maybe::Absent(_) => CellCount::from(0_usize),
        };
        let answer = decide(block.reading, block.at, store, faces, presented, circuits);
        if let Ok(relative) = moved(&answer, |span| counted_from(span, origin)) {
            if self.kept.len() >= self.held {
                let _oldest = self.kept.remove(0);
            }
            self.kept.push(Kept {
                key,
                answer: relative,
                commands: appended(store, commands_before),
                terms: match *presented {
                    Maybe::Present(ref reading) => appended(&reading.store, terms_before),
                    Maybe::Absent(_) => Vec::new(),
                },
            });
        }
        answer
    }
}

/// The cells of `store` from the one numbered `before` on, in order.
///
/// # Specification
/// trivial.
fn appended<A>(
    store: &CellStore<A>,
    before: CellCount,
) -> Vec<Cell<A>>
where
    A: CellAlphabet,
{
    store
        .iter()
        .skip(usize::from(before))
        .map(|(_, cell)| cell.clone())
        .collect()
}

/// `answer` with every span it reports — the fault's and the earlier rule's —
/// taken through `through`, or the first refusal `through` makes.
///
/// # Specification
/// trivial.
fn moved<E>(
    answer: &Answer,
    through: impl Fn(ByteSpan) -> Result<ByteSpan, E>,
) -> Result<Answer, E>
{
    match *answer {
        Ok(ref coincidence) => Ok(Ok(coincidence.clone())),
        Err((span, ref fault)) => {
            let mut fault = fault.clone();
            match fault {
                CoherenceFault::Unoriented => {},
                CoherenceFault::OverlapsSecondOrder { ref mut first }
                | CoherenceFault::OverlapsCondition { ref mut first }
                | CoherenceFault::Diverges { ref mut first, .. }
                | CoherenceFault::Uncompleted { ref mut first, .. }
                | CoherenceFault::Undecided { ref mut first, .. }
                | CoherenceFault::Unfinished { ref mut first, .. }
                | CoherenceFault::NeverCompletes { ref mut first, .. } => {
                    *first = through(*first)?;
                },
            }
            Ok(Err((through(span)?, fault)))
        },
    }
}

/// A span that starts or ends before the origin it would be counted from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct BeforeOrigin;

/// `span` counted from `origin`, or [`BeforeOrigin`] when it starts or ends
/// before it.
///
/// # Specification
/// trivial.
fn counted_from(
    span: ByteSpan,
    origin: ByteOffset,
) -> Result<ByteSpan, BeforeOrigin>
{
    let origin = usize::from(origin);
    let start = usize::from(span.start())
        .checked_sub(origin)
        .ok_or(BeforeOrigin)?;
    let end = usize::from(span.end())
        .checked_sub(origin)
        .ok_or(BeforeOrigin)?;
    ByteSpan::new(start.into(), end.into()).map_err(|_unordered| BeforeOrigin)
}

/// `span`, counted from `origin`, as the bytes it covers.
///
/// # Specification
/// trivial.
fn relocated(
    span: ByteSpan,
    origin: ByteOffset,
) -> ByteSpan
{
    span.shifted(ByteLength::from(usize::from(origin)))
}

#[cfg(test)]
mod tests;
