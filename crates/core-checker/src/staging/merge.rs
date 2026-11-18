//! The program's side of a check: join each source's segment to the program's
//! arena, in source order.
//!
//! A segment's classifiers and terms join through the arena's own interning,
//! each with its children and classifiers already placed in the program's
//! coordinates: a term the arena holds is found and compared there, and only a
//! miss is appended.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Extent;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;

use super::segment::Segment;

/// Where one worker's syntax landed in the program's arena: the merged
/// coordinate of every classifier and term the worker's snapshot holds above
/// the program's extent, in the snapshot's allocation order.
///
/// # Specification
/// - provides: once the worker's segments up to one have joined, the merged
///   coordinate of each coordinate that segment's snapshot held above the
///   floor.
/// - panics: none.
/// - executable: none — [`Merge::join`] carries the laws.
#[derive(Debug)]
struct Placement
{
    /// The program's own extent, below which every coordinate is shared.
    floor: Extent,
    /// Each classifier's merged coordinate, by offset above the floor.
    types: Vec<TypeId>,
    /// Each term's merged coordinate, by offset above the floor.
    terms: Vec<TermId>,
}

impl Placement
{
    /// A worker's term coordinate in the program's arena: itself below the
    /// floor, its merged coordinate above.
    ///
    /// # Specification
    /// - ensures: `id` below the floor; above it, the coordinate the worker's
    ///   term at that offset merged to.
    /// - fails: `UnknownTerm` above every merged term of the worker.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::UnknownTerm`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every coordinate of the power and double programs'
    ///   certificates is placed, and the certificates equal one-arena
    ///   normalization's.
    /// - witness: `staging::tests::the_merged_arena_is_one_arena_normalization`
    #[spec(ensures: |output| output.is_err() || id.0 >= self.floor.terms.0 || output == Ok(id))]
    fn term_at(
        &self,
        id: TermId,
    ) -> Result<TermId, StageError>
    {
        id.0.checked_sub(self.floor.terms.0)
            .map_or(Ok(id), |offset| {
                self.terms
                    .get(offset)
                    .copied()
                    .ok_or(StageError::UnknownTerm(id))
            })
    }

    /// A worker's classifier coordinate in the program's arena: itself below
    /// the floor, its merged coordinate above.
    ///
    /// # Specification
    /// - ensures: `id` below the floor; above it, the coordinate the worker's
    ///   classifier at that offset merged to.
    /// - fails: `UnknownType` above every merged classifier of the worker.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Placement::term_at`], over classifiers.
    /// - witness: `staging::tests::the_merged_arena_is_one_arena_normalization`
    #[spec(ensures: |output| output.is_err() || id.0 >= self.floor.types.0 || output == Ok(id))]
    fn type_at(
        &self,
        id: TypeId,
    ) -> Result<TypeId, StageError>
    {
        id.0.checked_sub(self.floor.types.0)
            .map_or(Ok(id), |offset| {
                self.types
                    .get(offset)
                    .copied()
                    .ok_or(StageError::UnknownType(id))
            })
    }

    /// A worker's term with every child and classifier placed in the
    /// program's arena.
    ///
    /// # Specification
    /// - ensures: the same constructor and payload, each child and classifier
    ///   at its placed coordinate.
    /// - fails: a child or classifier not yet merged.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::UnknownTerm` or `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Merge::join`].
    /// - witness: `staging::tests::the_merged_arena_is_one_arena_normalization`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|placed|
        core::mem::discriminant(placed) == core::mem::discriminant(&term)))]
    fn placed(
        &self,
        term: Term,
    ) -> Result<Term, StageError>
    {
        Ok(match term {
            Term::Variable(_) | Term::Natural(..) => term,
            Term::Code(ty) => {
                let ty = self.type_at(ty)?;
                Term::Code(ty)
            },
            Term::Lambda(domain, body) => {
                let domain = self.type_at(domain)?;
                let body = self.term_at(body)?;
                Term::Lambda(domain, body)
            },
            Term::Apply(function, argument) => {
                let function = self.term_at(function)?;
                let argument = self.term_at(argument)?;
                Term::Apply(function, argument)
            },
            Term::Multiply(left, right) => {
                let left = self.term_at(left)?;
                let right = self.term_at(right)?;
                Term::Multiply(left, right)
            },
            Term::Quote(quoted) => {
                let quoted = self.term_at(quoted)?;
                Term::Quote(quoted)
            },
            Term::Splice(spliced) => {
                let spliced = self.term_at(spliced)?;
                Term::Splice(spliced)
            },
            Term::Iterate(count, initial, step) => {
                let count = self.term_at(count)?;
                let initial = self.term_at(initial)?;
                let step = self.term_at(step)?;
                Term::Iterate(count, initial, step)
            },
            Term::Eliminate(scrutinee, result) => {
                let scrutinee = self.term_at(scrutinee)?;
                let result = self.type_at(result)?;
                Term::Eliminate(scrutinee, result)
            },
        })
    }

    /// A worker's classifier with every child placed in the program's arena.
    ///
    /// # Specification
    /// - ensures: the same constructor and payload, each child at its placed
    ///   coordinate.
    /// - fails: a child not yet merged.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Merge::join`].
    /// - witness: `staging::tests::the_merged_arena_is_one_arena_normalization`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|placed|
        core::mem::discriminant(placed) == core::mem::discriminant(&ty)))]
    fn placed_type(
        &self,
        ty: Type,
    ) -> Result<Type, StageError>
    {
        Ok(match ty {
            Type::In(_) | Type::Universe(_) | Type::Nat(_) => ty,
            Type::Arrow(domain, codomain) => {
                let domain = self.type_at(domain)?;
                let codomain = self.type_at(codomain)?;
                Type::Arrow(domain, codomain)
            },
            Type::Lift(lifted) => {
                let lifted = self.type_at(lifted)?;
                Type::Lift(lifted)
            },
        })
    }
}

/// The program's arena as segments join it.
///
/// # Specification
/// - provides: after each [`Merge::join`] in source order, the arena
///   normalizing those sources in order in the program's arena gives.
/// - panics: none.
/// - executable: none — [`Merge::join`] carries the laws.
#[derive(Debug)]
pub(super) struct Merge
{
    /// The program's arena, growing.
    arena: Arena,
    /// The program's own extent, below which every coordinate is shared.
    floor: Extent,
    /// Each worker's placement, by worker.
    workers: Vec<Placement>,
}

impl Merge
{
    /// A merge into the program's arena, before any segment joins.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn new(arena: Arena) -> Self
    {
        Self {
            floor: arena.extent(),
            arena,
            workers: Vec::new(),
        }
    }

    /// Join one segment and return its certificate in the program's
    /// coordinates, remapped in place and taken from the segment.
    ///
    /// # Specification
    /// - requires: `segment` was normalized on its worker's snapshot of the
    ///   program's arena, and every earlier segment that snapshot still held
    ///   has joined.
    /// - ensures: every classifier and term of the segment is held by the arena
    ///   at the coordinate interning it there in allocation order gives, found
    ///   by the arena's own lookup when it is already held. The worker's
    ///   placement covers its snapshot to the segment's end; the certificate
    ///   names merged coordinates, and the segment keeps none of its steps.
    /// - fails: a segment starting above what its worker has joined, a child
    ///   the snapshot does not hold below it, or the arena's coordinate bound.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`, `StageError::UnknownTerm`,
    /// `StageError::UnknownType` or `StageError::Overflow`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — the power and double programs merge to the arena
    ///   and certificates one-arena normalization gives, term for term, from
    ///   workers that keep their snapshots across sources, from workers that
    ///   start every source afresh, and from one that meets its sources last
    ///   first.
    /// - witness: `staging::tests::the_merged_arena_is_one_arena_normalization`
    #[spec(captures: steps = segment.certificate.steps.len(),
        ensures: |output| output.as_ref().ok().is_none_or(|certificate|
            certificate.steps.len() == steps
                && self.arena.term(certificate.source).is_ok()
                && self.arena.term(certificate.target).is_ok()))]
    pub(super) fn join(
        &mut self,
        segment: &mut Segment,
    ) -> Result<Certificate, StageError>
    {
        let Self {
            ref mut arena,
            floor,
            ref mut workers,
        } = *self;
        while workers.len() <= segment.worker.0 {
            workers.push(Placement {
                floor,
                types: Vec::new(),
                terms: Vec::new(),
            });
        }
        let placement = workers
            .get_mut(segment.worker.0)
            .ok_or(StageError::Unbalanced)?;
        let kept_types = segment
            .start
            .types
            .0
            .checked_sub(floor.types.0)
            .filter(|kept| *kept <= placement.types.len())
            .ok_or(StageError::Unbalanced)?;
        let kept_terms = segment
            .start
            .terms
            .0
            .checked_sub(floor.terms.0)
            .filter(|kept| *kept <= placement.terms.len())
            .ok_or(StageError::Unbalanced)?;
        placement.types.truncate(kept_types);
        placement.terms.truncate(kept_terms);
        for ty in &segment.types {
            let placed = placement.placed_type(*ty)?;
            let id = arena.alloc_type(placed)?;
            placement.types.push(id);
        }
        for term in &segment.terms {
            let placed = placement.placed(*term)?;
            let id = arena.alloc(placed)?;
            placement.terms.push(id);
        }
        let certificate = &mut segment.certificate;
        let source = placement.term_at(certificate.source)?;
        let target = placement.term_at(certificate.target)?;
        for step in &mut certificate.steps {
            step.source = placement.term_at(step.source)?;
            step.target = placement.term_at(step.target)?;
        }
        Ok(Certificate {
            source,
            target,
            steps: core::mem::take(&mut certificate.steps),
        })
    }

    /// The program's arena with every joined segment.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn finish(self) -> Arena
    {
        self.arena
    }
}
