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
//! Four adversaries are carried. [`IncomparablePositions`] reports every
//! position pair as disjoint, and [`NonLocalSplice`] disturbs a sibling of the
//! position it splices: each breaks a clause [`CellAlphabet`] states.
//! [`WithheldConvexity`] withholds the convexity warrant, and
//! [`CollidingAddresses`] hashes every orientation tag to nothing: each gives
//! an answer the trait and [`core::hash::Hash`] permit and no honest
//! inhabitant gives. All four are instantiated only by test suites.

use alloc::vec::Vec;
use core::marker::PhantomData;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellInvertibility;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CommandSpliceRefusal;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::FiringPermission;
use gandr_theory_cell_complexes::Generalization;
use gandr_theory_cell_complexes::PatternSize;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::SeamRole;
use gandr_theory_cell_complexes::SubstitutionDecision;
use gandr_theory_cell_complexes::anti_unification;
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
use crate::toy::anti_unify_toys;

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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal positions, both nesting directions and disjoint
    ///   children have exact default answers. Swapped enclosure or broken
    ///   reflexivity changes the relation.
    /// - witness: `tests::adversary::default_answers_and_adversarial_boundaries_stay_distinct`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output == ToyAlphabet::position_order(left, right))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a below-root replacement changes the selected subtree
    ///   and preserves its sibling; an off-term path refuses. A non-local
    ///   change or wrong refusal alters the result.
    /// - witness: `tests::adversary::default_answers_and_adversarial_boundaries_stay_distinct`
    #[inline]
    #[spec(captures: expected = replacement.clone(), ensures: |output| match output {
        Ok(ref result) => matches!(ToyAlphabet::subterm_cmd_at(result, pos), Maybe::Present(ref held) if held == &expected),
        Err(CommandSpliceRefusal::OffTerm) => matches!(ToyAlphabet::subterm_cmd_at(cmd, pos), Maybe::Absent(command_subterm::Absent::OffTerm)),
        Err(CommandSpliceRefusal::NotACommand) => false,
    })]
    fn splice_cmd_at(
        cmd: &Toy,
        pos: &ToyPos,
        replacement: Toy,
    ) -> Result<Toy, CommandSpliceRefusal>
    {
        ToyAlphabet::splice_cmd_at(cmd, pos, replacement)
    }

    /// The convexity warrant this alphabet supplies for any store.
    ///
    /// The toy alphabet's own answer cannot be asked here: its
    /// [`CellAlphabet::convexity_discharge`] reads a store of toy cells, and a
    /// store over [`Lying`] is a different type. The default restates the
    /// answer the toy alphabet gives every store, since its left-hand sides
    /// are single trees.
    ///
    /// # Specification
    /// - ensures: by default,
    ///   [`ConvexityDischarge::StronglyConnectedOverAcyclicTarget`], the toy
    ///   alphabet's answer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a non-withholding strategy retains the structural
    ///   warrant while the withholding strategy refuses it. Reversing or
    ///   merging the answers changes the discharge.
    /// - witness: `tests::adversary::default_answers_and_adversarial_boundaries_stay_distinct`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output == ConvexityDischarge::StronglyConnectedOverAcyclicTarget)]
    fn convexity_discharge() -> ConvexityDischarge
    {
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget
    }

    /// Feed an orientation tag to `state`, as a [`LyingOrient`] hashes.
    ///
    /// # Specification
    /// - ensures: by default, exactly the writes the tag's own
    ///   [`core::hash::Hash`] makes, so a cell over a [`Lying`] alphabet hashes
    ///   as the toy cell with the same fields.
    /// - panics: none.
    /// - executable: none — a generic hasher exposes its digest, not the
    ///   sequence of writes or an independent copy of its state; the byte trace
    ///   is a witness observation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — cells differing only in orientation write distinct
    ///   byte streams under the default hash strategy and retain the toy hash
    ///   protocol. Suppressed or altered tag writes change that observation.
    /// - witness: `tests::adversary::the_colliding_addresses_wrapper_hides_the_orientation_and_keeps_the_cell`
    #[inline]
    fn hash_orientation<H>(
        orient: ToyOrient,
        state: &mut H,
    ) where
        H: core::hash::Hasher,
    {
        core::hash::Hash::hash(&orient, state);
    }
}

/// The toy orientation tag, hashed as `L` decides.
///
/// A cell's orientation enters its derived [`core::hash::Hash`] and nothing
/// else an engine reads to address the cell, so it is the narrowest place for
/// an adversary to make two distinct cells hash alike. Equality stays the
/// tag's own: two tags are equal exactly when their toy tags are.
///
/// # Specification
/// - ensures: [`Eq`] is the toy tag's equality; [`core::hash::Hash`] is
///   [`AlphabetLie::hash_orientation`] of the toy tag, which may identify
///   unequal tags, as the trait permits.
/// - panics: none.
/// - executable: none — this type relates structural equality to a strategy's
///   hash writes; only its hashing operation owns the output state.
///
/// # Adequacy
/// - hypothesis: L3 — equal tags compare equal and distinct orientation tags
///   remain distinct even when their hash streams collide. Conflating equality
///   with hashing changes store identity.
/// - witness: `tests::adversary::the_colliding_addresses_wrapper_hides_the_orientation_and_keeps_the_cell`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LyingOrient<L>
{
    /// The toy tag.
    orient: ToyOrient,
    /// The adversary deciding how the tag hashes.
    lie: PhantomData<L>,
}

impl<L> From<ToyOrient> for LyingOrient<L>
{
    /// Wraps the toy tag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(orient: ToyOrient) -> Self
    {
        Self {
            orient,
            lie: PhantomData,
        }
    }
}

impl<L> From<LyingOrient<L>> for ToyOrient
{
    /// Unwraps the toy tag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: LyingOrient<L>) -> Self
    {
        value.orient
    }
}

impl<L> core::hash::Hash for LyingOrient<L>
where
    L: AlphabetLie,
{
    /// Hashes the toy tag as `L` decides; deliberately coarser than [`Eq`]
    /// when `L` lies about it, which the [`core::hash::Hash`] law permits.
    ///
    /// # Specification
    /// - ensures: the writes [`AlphabetLie::hash_orientation`] makes for the
    ///   toy tag.
    /// - panics: none.
    /// - executable: none — the strategy controls writes to an opaque generic
    ///   hasher; its digest cannot reconstruct the required write history.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — under [`CollidingAddresses`] two cells differing only
    ///   in orientation write one byte stream, and under an adversary that does
    ///   not lie about the tag they write two.
    /// - witness: `tests::adversary::the_colliding_addresses_wrapper_hides_the_orientation_and_keeps_the_cell`
    #[inline]
    fn hash<H>(
        &self,
        state: &mut H,
    ) where
        H: core::hash::Hasher,
    {
        L::hash_orientation(self.orient, state);
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
    /// - witness: `tests::adversary::default_answers_and_adversarial_boundaries_stay_distinct`
    #[inline]
    #[spec(ensures: |output| output == PositionOrder::Incomparable)]
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
    /// - witness: `tests::adversary::default_answers_and_adversarial_boundaries_stay_distinct`
    #[inline]
    #[spec(captures: expected = replacement.clone(), ensures: |output| match output {
        Ok(ref result) => matches!(ToyAlphabet::subterm_cmd_at(result, pos), Maybe::Present(ref held) if held == &expected),
        Err(CommandSpliceRefusal::OffTerm) => matches!(ToyAlphabet::subterm_cmd_at(cmd, pos), Maybe::Absent(command_subterm::Absent::OffTerm)),
        Err(CommandSpliceRefusal::NotACommand) => false,
    })]
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

/// The adversary that **withholds** the convexity warrant, answering
/// [`ConvexityDischarge::ReCheckRequired`] for every store.
///
/// It breaks no clause: [`CellAlphabet::convexity_discharge`] provides the
/// answer, and an alphabet whose left-hand sides could match non-convexly owes
/// it. No honest inhabitant in the workspace gives it, so a commutation check
/// whose third conjunct reads the warrant has no other input that reaches the
/// refusal.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WithheldConvexity;

impl AlphabetLie for WithheldConvexity
{
    /// The warrant is withheld.
    ///
    /// # Specification
    /// - ensures: [`ConvexityDischarge::ReCheckRequired`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the toy alphabet's store carries the warrant and the
    ///   wrapper's withholds it, while a match decided through the wrapper is
    ///   the honest one.
    /// - witness: `tests::adversary::the_withheld_convexity_wrapper_withholds_the_warrant_and_keeps_the_match`
    /// - witness: `tests::adversary::default_answers_and_adversarial_boundaries_stay_distinct`
    #[inline]
    #[spec(ensures: |output| output == ConvexityDischarge::ReCheckRequired)]
    fn convexity_discharge() -> ConvexityDischarge
    {
        ConvexityDischarge::ReCheckRequired
    }
}

/// The adversary whose orientation tag hashes to **nothing**, so two cells
/// that differ only in orientation write one byte stream to any hasher.
///
/// It breaks no clause either: the [`core::hash::Hash`] law asks that equal
/// values hash equally and lets unequal ones collide. A store deduplicating on
/// structural equality keeps the two cells under two identifiers, so a
/// content address digested over a cell's hash gives two identifiers one
/// address — the input a refusal of address collisions needs, and that no
/// honest digest produces on demand.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CollidingAddresses;

impl AlphabetLie for CollidingAddresses
{
    /// Writes nothing.
    ///
    /// # Specification
    /// - ensures: `state` is left as it was.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the given and the derived orientation of one toy cell
    ///   write one byte stream through the wrapper and two through an honest
    ///   hasher, while the store keeps both cells apart.
    /// - witness: `tests::adversary::the_colliding_addresses_wrapper_hides_the_orientation_and_keeps_the_cell`
    /// - witness: `tests::adversary::default_answers_and_adversarial_boundaries_stay_distinct`
    #[inline]
    #[spec(captures: before = state.finish(), ensures: state.finish() == before)]
    fn hash_orientation<H>(
        _orient: ToyOrient,
        state: &mut H,
    ) where
        H: core::hash::Hasher,
    {
    }
}

/// [`ToyAlphabet`], except for the answers `L` gives dishonestly.
///
/// Every associated type but the orientation is the toy alphabet's own, so a
/// toy term, position or substitution is one of this alphabet's too. The
/// orientation is the toy tag in a [`LyingOrient`], so a cell over this
/// alphabet hashes as the toy cell with the same fields unless `L` lies about
/// the tag's hash.
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
    type Orientation = LyingOrient<L>;
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

    /// The toy alphabet's anti-unification.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn anti_unify_cmd(
        family: &[&[Self::Cmd]]
    ) -> Maybe<Generalization<Self>, anti_unification::Absent>
    {
        anti_unify_toys(family)
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

    /// The toy alphabet's restriction.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn restrict_subst(
        subst: &Self::Subst,
        vars: &[Self::Var],
    ) -> Self::Subst
    {
        ToyAlphabet::restrict_subst(subst, vars)
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

    /// The toy alphabet's node count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cmd_size(cmd: &Self::Cmd) -> PatternSize
    {
        ToyAlphabet::cmd_size(cmd)
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

    /// `L`'s convexity warrant, the same for every store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn convexity_discharge(_store: &CellStore<Self>) -> ConvexityDischarge
    {
        L::convexity_discharge()
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
    /// - executable: none — the arbitrary strategy owns the entire result;
    ///   checking delegation requires another invocation, which need not be
    ///   observationally inert.
    ///
    /// # Errors
    /// As `L`'s splice errs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — honest and non-local strategies expose exact
    ///   replacement contexts and refusals through the wrapper. Root and nested
    ///   paths bound the sibling lie; substituting the wrong strategy changes
    ///   those terms.
    /// - witness: `tests::adversary::default_answers_and_adversarial_boundaries_stay_distinct`
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

    /// The toy alphabet's derived orientation, wrapped.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derived_orientation() -> Self::Orientation
    {
        LyingOrient::from(ToyAlphabet::derived_orientation())
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
    Cell::new(lhs, rhs, LyingOrient::from(ToyOrient::Given), ToyProv::Rule)
}

/// The cell [`lying_cell`] builds, tagged with the derived orientation instead
/// of the given one.
///
/// The two are structurally distinct, so one store holds both under two
/// identifiers; under [`CollidingAddresses`] they nonetheless hash alike.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn reoriented_lying_cell<L>(
    lhs: Toy,
    rhs: Toy,
) -> Cell<Lying<L>>
where
    L: AlphabetLie,
{
    Cell::new(
        lhs,
        rhs,
        <Lying<L> as CellAlphabet>::derived_orientation(),
        ToyProv::Rule,
    )
}
