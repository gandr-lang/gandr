//! The adversary frame: alphabets that are the toy alphabet in every answer
//! but one.
//!
//! An engine generic over [`CellAlphabet`] spends clauses of the trait it
//! cannot check. A correct inhabitant never exercises the code that runs when
//! one of those clauses is broken, so a check defending against a broken
//! inhabitant needs an inhabitant that breaks it. [`Lying`] is that
//! inhabitant: it delegates every method to [`ToyAlphabet`] except the ones its
//! [`AlphabetLie`] overrides, so a behaviour observed over `Lying<L>` and not
//! over the toy alphabet is attributable to `L`'s one lie.
//!
//! Two lies are carried: [`IncomparablePositions`] reports every position pair
//! as disjoint, and [`NonLocalSplice`] disturbs a sibling of the position it
//! splices. Both break a clause [`CellAlphabet`] states, on purpose, and are
//! instantiated only by test suites.

use alloc::vec::Vec;
use core::marker::PhantomData;

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellInvertibility;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CommandSpliceRefusal;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::FiringPermission;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::SeamRole;
use gandr_theory_cell_complexes::SubstitutionDecision;
use gandr_theory_cell_complexes::command_subterm;
use quenchant_shape::shape::Maybe;

use crate::toy::Toy;
use crate::toy::ToyAlphabet;
use crate::toy::ToyMeta;
use crate::toy::ToyOrient;
use crate::toy::ToyPos;
use crate::toy::ToyProv;
use crate::toy::ToySubst;
use crate::toy::ToyVar;

/// The answers a [`Lying`] alphabet may give dishonestly.
///
/// Every method has the toy alphabet's honest answer as its default, so an
/// adversary overrides exactly the one it lies about.
pub trait AlphabetLie: Copy + Default + Eq + Ord + core::fmt::Debug + core::hash::Hash
{
    /// The order this alphabet reports for a position pair.
    ///
    /// # Specification
    /// - ensures: by default, the toy alphabet's path order.
    /// - panics: none.
    #[inline]
    #[must_use]
    fn position_order(
        left: &ToyPos,
        right: &ToyPos,
    ) -> PositionOrder
    {
        ToyAlphabet::position_order(left, right)
    }

    /// `cmd` with `replacement` spliced in at `pos`, as this alphabet answers
    /// it.
    ///
    /// # Specification
    /// - ensures: by default, the toy alphabet's splice.
    /// - fails: by default, as the toy alphabet's splice fails.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CommandSpliceRefusal::OffTerm`] when a step of `pos` leaves the term.
    #[inline]
    fn splice_cmd_at(
        cmd: &Toy,
        pos: &ToyPos,
        replacement: Toy,
    ) -> Result<Toy, CommandSpliceRefusal>
    {
        ToyAlphabet::splice_cmd_at(cmd, pos, replacement)
    }
}

/// The adversary that reports **every** position pair as
/// [`PositionOrder::Incomparable`], a nesting pair and a position with itself
/// included.
///
/// It breaks the [`CellAlphabet::position_order`] clauses that incomparable
/// positions address disjoint subtrees and that a position is the same as
/// itself, so an application enclosing another is licensed to commute with it.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct IncomparablePositions;

impl AlphabetLie for IncomparablePositions
{
    /// Every pair is incomparable.
    ///
    /// # Specification
    /// - ensures: [`PositionOrder::Incomparable`] for every pair.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nesting pair the honest alphabet orders is reported
    ///   incomparable, while a match decided through the same wrapper is the
    ///   honest one.
    /// - witness: `tests::adversary::the_incomparable_wrapper_breaks_the_position_order_and_keeps_the_match`
    #[inline]
    fn position_order(
        _left: &ToyPos,
        _right: &ToyPos,
    ) -> PositionOrder
    {
        PositionOrder::Incomparable
    }
}

/// The adversary whose splice is **non-local**: replacing the subterm at a
/// one-step position under a binary root also resets that position's sibling
/// to `Add(Zero, Zero)`.
///
/// It breaks the [`CellAlphabet::splice_cmd_at`] clause that the result equals
/// the term everywhere but the spliced position. An engine that reads only
/// positions and cell contents cannot see the lie, so two applications at
/// incomparable positions can fail to commute through it. Only a one-step
/// position under a binary root is entangled; reading and every splice
/// elsewhere stay honest.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NonLocalSplice;

impl AlphabetLie for NonLocalSplice
{
    /// The honest splice, followed by a reset of the spliced position's sibling
    /// under a binary root.
    ///
    /// # Specification
    /// - ensures: the toy alphabet's splice, except that a splice at `[i]`
    ///   under a root with a child `[1 - i]` also replaces that child with
    ///   `Add(Zero, Zero)`.
    /// - fails: as the toy alphabet's splice fails.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CommandSpliceRefusal::OffTerm`] when a step of `pos` leaves the term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a splice at one child of a binary root also resets
    ///   the sibling, a splice at the only child of a unary root does not, and
    ///   the read at the spliced position is the honest one.
    /// - witness: `tests::adversary::the_non_local_splice_wrapper_breaks_the_splice_and_keeps_the_read`
    #[inline]
    fn splice_cmd_at(
        cmd: &Toy,
        pos: &ToyPos,
        replacement: Toy,
    ) -> Result<Toy, CommandSpliceRefusal>
    {
        let spliced = ToyAlphabet::splice_cmd_at(cmd, pos, replacement)?;
        let &[step] = pos.steps()
        else {
            return Ok(spliced);
        };
        // The step is a child index, and the sibling of a child of a binary
        // node is the other index; no conversion trait names "the other child".
        let sibling = match usize::from(step) {
            | 0 => 1_usize,
            | 1 => 0_usize,
            | _ => return Ok(spliced),
        };
        let sibling = ToyAlphabet::position_at_path(&[PositionStep::from(sibling)]);
        match ToyAlphabet::subterm_cmd_at(&spliced, &sibling) {
            | Maybe::Present(_) => {
                ToyAlphabet::splice_cmd_at(&spliced, &sibling, Toy::add(Toy::zero(), Toy::zero()))
            },
            | Maybe::Absent(_) => Ok(spliced),
        }
    }
}

/// [`ToyAlphabet`], except for the answers `L` gives dishonestly.
///
/// Every associated type is the toy alphabet's own, so a toy term, position or
/// substitution is one of this alphabet's too, and a cell over it hashes as the
/// toy cell with the same fields.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lying<L>(PhantomData<L>);

impl<L> CellAlphabet for Lying<L>
where
    L: AlphabetLie,
{
    type Cmd = Toy;
    type Hole = ToyVar;
    type Meta = ToyMeta;
    type Orientation = ToyOrient;
    type Pos = ToyPos;
    type Provenance = ToyProv;
    type Subst = ToySubst;
    type Var = ToyVar;

    /// The toy alphabet's matching.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn match_cmd(
        pattern: &Self::Cmd,
        target: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision
    {
        ToyAlphabet::match_cmd(pattern, target, subst)
    }

    /// The toy alphabet's unification.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn unify_cmd(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision
    {
        ToyAlphabet::unify_cmd(lhs, rhs, subst)
    }

    /// The toy alphabet's substitution.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn apply_subst(
        subst: &Self::Subst,
        cmd: &Self::Cmd,
    ) -> Self::Cmd
    {
        ToyAlphabet::apply_subst(subst, cmd)
    }

    /// The toy alphabet's metavariables.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn metavariables(cmd: &Self::Cmd) -> Vec<Self::Var>
    {
        ToyAlphabet::metavariables(cmd)
    }

    /// The toy alphabet's command positions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn command_positions(cmd: &Self::Cmd) -> Vec<Self::Pos>
    {
        ToyAlphabet::command_positions(cmd)
    }

    /// The toy alphabet's root position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn root_position() -> Self::Pos
    {
        ToyAlphabet::root_position()
    }

    /// The toy alphabet's position of `path`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn position_at_path(path: &[PositionStep]) -> Self::Pos
    {
        ToyAlphabet::position_at_path(path)
    }

    /// `L`'s position order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn position_order(
        left: &Self::Pos,
        right: &Self::Pos,
    ) -> PositionOrder
    {
        L::position_order(left, right)
    }

    /// The toy alphabet's discharge, restated: the store is keyed by this
    /// alphabet, so the toy answer cannot be asked for it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn convexity_discharge(_store: &CellStore<Self>) -> ConvexityDischarge
    {
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget
    }

    /// The toy alphabet's read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn subterm_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
    ) -> Maybe<Self::Cmd, command_subterm::Absent>
    {
        ToyAlphabet::subterm_cmd_at(cmd, pos)
    }

    /// `L`'s splice.
    ///
    /// # Specification
    /// - ensures: as `L` answers it.
    /// - fails: as `L` fails it.
    /// - panics: none.
    ///
    /// # Errors
    /// As `L`'s splice errs.
    #[inline]
    fn splice_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
        replacement: Self::Cmd,
    ) -> Result<Self::Cmd, CommandSpliceRefusal>
    {
        L::splice_cmd_at(cmd, pos, replacement)
    }

    /// The toy alphabet's reduction order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn reduction_cmp(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
    ) -> core::cmp::Ordering
    {
        ToyAlphabet::reduction_cmp(lhs, rhs)
    }

    /// The toy alphabet's renaming apart.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn rename_apart(
        anchor: (&Self::Cmd, &Self::Cmd),
        renamed: (&Self::Cmd, &Self::Cmd),
    ) -> (Self::Cmd, Self::Cmd)
    {
        ToyAlphabet::rename_apart(anchor, renamed)
    }

    /// The toy alphabet's skolemization.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn skolemize(cmd: &Self::Cmd) -> Self::Cmd
    {
        ToyAlphabet::skolemize(cmd)
    }

    /// The toy alphabet's hole identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hole_of(var: &Self::Var) -> Self::Hole
    {
        ToyAlphabet::hole_of(var)
    }

    /// The toy alphabet's certificate reading.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn completion_certificate(provenance: &Self::Provenance) -> CellInvertibility
    {
        ToyAlphabet::completion_certificate(provenance)
    }

    /// The toy alphabet's metadata.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derive_meta(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        invertible: CellInvertibility,
    ) -> Self::Meta
    {
        ToyAlphabet::derive_meta(lhs, rhs, invertible)
    }

    /// The toy alphabet's hole flow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hole_flow(
        meta: &Self::Meta,
        hole: &Self::Hole,
    ) -> Vec<(Self::Var, SeamRole)>
    {
        ToyAlphabet::hole_flow(meta, hole)
    }

    /// The toy alphabet's firing discipline.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn may_fire(
        provenance: &Self::Provenance,
        target: &Self::Cmd,
    ) -> FiringPermission
    {
        ToyAlphabet::may_fire(provenance, target)
    }

    /// The toy alphabet's derived orientation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derived_orientation() -> Self::Orientation
    {
        ToyAlphabet::derived_orientation()
    }

    /// The toy alphabet's derived provenance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derived_provenance() -> Self::Provenance
    {
        ToyAlphabet::derived_provenance()
    }
}

/// A rule cell `lhs ~> rhs` over a [`Lying`] alphabet, with the toy rule
/// cell's tags.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn lying_cell<L>(
    lhs: Toy,
    rhs: Toy,
) -> Cell<Lying<L>>
where
    L: AlphabetLie,
{
    Cell::new(lhs, rhs, ToyOrient::Given, ToyProv::Rule)
}
