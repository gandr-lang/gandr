//! The cell-alphabet abstraction: the one trait the overlap enumerator, the
//! completion loop and the normalizer quantify over.
//!
//! # The interface
//!
//! One deep trait, not a spray of knobs. An alphabet fixes:
//!
//! - the pattern grammar — the term type [`CellAlphabet::Cmd`] cells rewrite,
//!   its metavariables [`CellAlphabet::Var`] with the hole identity
//!   [`CellAlphabet::Hole`] the composition gate keys on, its positions
//!   [`CellAlphabet::Pos`], navigation and splicing
//!   ([`CellAlphabet::subterm_cmd_at`], [`CellAlphabet::splice_cmd_at`]), the
//!   well-founded [`CellAlphabet::reduction_cmp`] completion orients by, the
//!   deterministic apartness renaming [`CellAlphabet::rename_apart`], and the
//!   replay [`CellAlphabet::skolemize`];
//! - the ordered-map substitution — one-sided matching
//!   ([`CellAlphabet::match_cmd`], cell application) and two-sided unification
//!   ([`CellAlphabet::unify_cmd`], overlap superposition), both over the
//!   deterministic [`CellAlphabet::Subst`] carrier;
//! - the cell vocabulary — orientation and provenance tags, the derived
//!   per-cell metadata [`CellAlphabet::Meta`], the firing discipline
//!   ([`CellAlphabet::may_fire`]), and the provenance-to-certificate reading
//!   ([`CellAlphabet::completion_certificate`]).
//!
//! The sequent command-pattern alphabet ([`crate::sequent::SequentAlphabet`])
//! is the first inhabitant and the reference implementation.
//!
//! # Term identity is structural
//!
//! The equality the engines decide with — a completion join check comparing
//! two normal forms, the store's deduplication — rides
//! [`CellAlphabet::Cmd`]'s [`Eq`], so that equality must be structural content
//! identity: no arena address, generation stamp or session state may enter a
//! hashed or compared term. That is also why an alphabet is a stateless marker
//! type, never a handle to an interner. A faster equality for normal forms
//! would land behind a guard and a soundness witness, never as an unchecked
//! [`Eq`] shortcut.
//!
//! Terms are identified structurally; certificates of joinability are
//! identified by replay equivalence, in the layer above. An alphabet
//! contributes the term plane only.

use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::boundary::CellInvertibility;
use crate::boundary::FiringPermission;
use crate::boundary::PositionStep;
use crate::boundary::SubstitutionDecision;
use crate::cell::CellStore;

/// The flow role a metavariable hole contributes across a composed seam: the
/// alphabet-neutral dinaturality vocabulary the directed composition gate
/// reads.
///
/// The sequent alphabet maps its [`crate::sequent::CellVariance`] onto these
/// roles (producer → [`SeamRole::Forward`], consumer → [`SeamRole::Backward`],
/// mixed → [`SeamRole::Both`]); an alphabet without a polarity split reports
/// the roles its own metadata supports.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SeamRole
{
    /// Forward flow across the seam, from the first cell to the second.
    Forward,
    /// Backward flow across the seam, from the second cell to the first.
    Backward,
    /// Both directions: the dinaturality-shaped hole that closes a loop when
    /// shared across the seam.
    Both,
}

/// How two positions in one term relate.
///
/// Only [`PositionOrder::Incomparable`] makes two applications address
/// disjoint subtrees, the relation a later shift guard reads as its first
/// conjunct.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PositionOrder
{
    /// The same position: one application, not two.
    Same,
    /// The left position is a proper prefix of the right: the left addresses
    /// a subtree strictly containing the right's.
    Encloses,
    /// The right position is a proper prefix of the left.
    EnclosedBy,
    /// Neither is a prefix of the other: the two address disjoint subtrees.
    Incomparable,
}

/// The warrant an alphabet's store carries for skipping a per-pair convexity
/// re-check: whether every match image is still convex in the other
/// application's reduct.
///
/// The re-check would cost a directed reachability sweep per query. On a
/// store whose left-hand sides are strongly connected, over targets that are
/// acyclic, it is constant-true, so it is skipped and the skip names this
/// warrant.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ConvexityDischarge
{
    /// Discharged outright: every left-hand side the alphabet can express is
    /// strongly connected and every target is acyclic, so no match can be
    /// made non-convex and the re-check is constant-true.
    StronglyConnectedOverAcyclicTarget,
    /// Not discharged: the per-pair re-check would have to run, and it is not
    /// built, so a caller refuses rather than assumes.
    ReCheckRequired,
}

/// The path order of two child-index paths: the shared implementation of
/// [`CellAlphabet::position_order`] for every alphabet whose positions are
/// paths of child indices.
///
/// # Specification
/// - requires: both iterators yield the position's child indices from the root
///   outward.
/// - ensures: [`PositionOrder::Same`] on equal paths;
///   [`PositionOrder::Encloses`] when `left` is a proper prefix of `right`;
///   [`PositionOrder::EnclosedBy`] when `right` is a proper prefix of `left`;
///   [`PositionOrder::Incomparable`] at the first differing step, which is
///   exactly when the two paths address disjoint subtrees.
/// - panics: none.
/// - intension: one pass over the shorter path.
///
/// # Adequacy
/// - hypothesis: L3 — the four outcomes are separated pointwise by an equal
///   pair, a proper-prefix pair each way, and a pair diverging at a shared
///   depth.
/// - witness: `alphabet::tests::the_path_order_separates_its_four_outcomes`
#[inline]
#[must_use]
pub fn path_order<Left, Right>(
    left: Left,
    right: Right,
) -> PositionOrder
where
    Left: IntoIterator<Item = PositionStep>,
    Right: IntoIterator<Item = PositionStep>,
{
    let mut right = right.into_iter();
    for step in left {
        match right.next() {
            | None => return PositionOrder::EnclosedBy,
            | Some(other) if other == step => {},
            | Some(_) => return PositionOrder::Incomparable,
        }
    }
    match right.next() {
        | Some(_) => PositionOrder::Encloses,
        | None => PositionOrder::Same,
    }
}

quenchant_shape::reason_enum! {
    /// Why a position addresses no command subterm.
    pub mod command_subterm {
        /// The reason the read finds no command.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A step of the position leaves the term.
            OffTerm,
            /// The position addresses a subterm that is not a command.
            NotACommand,
        }
    }
}

/// A refused command splice.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CommandSpliceRefusal
{
    /// A step of the position leaves the term.
    OffTerm,
    /// The position addresses a subterm a command cannot replace.
    NotACommand,
}

impl core::fmt::Display for CommandSpliceRefusal
{
    /// Names the refusal.
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
            | Self::OffTerm => "the position leaves the term",
            | Self::NotACommand => "the position addresses a subterm a command cannot replace",
        })
    }
}

impl core::error::Error for CommandSpliceRefusal
{
}

/// The cell alphabet the engines quantify over: the pattern grammar, the
/// ordered-map substitution, and the seam and overlap vocabulary of one term
/// language.
///
/// An alphabet is a stateless marker type: the supertraits require [`Copy`]
/// and [`Default`], and every operation is an associated function, so no
/// arena, generation or session state can leak into term identity or into an
/// engine's decisions.
///
/// # Specification
/// - requires: an implementor keeps [`CellAlphabet::Cmd`] equality and hashing
///   structural, content identity only; [`CellAlphabet::match_cmd`] is
///   one-sided and [`CellAlphabet::unify_cmd`] finds a most general unifier;
///   [`CellAlphabet::rename_apart`] is deterministic and structure-preserving.
/// - requires: two occurrences of one primitive at one position remain
///   dependent: [`CellAlphabet::position_order`] returns
///   [`PositionOrder::Same`] for a position paired with itself.
/// - ensures: an engine generic over the trait reads every decline as data — an
///   absence, a refusal or a negative decision — never a panic.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the sequent alphabet's own suite runs through the trait's
///   methods, and a second inhabitant over a different, nesting term language
///   satisfies the three inhabitant laws the engines spend: a match followed by
///   its substitution reproduces the matched term, a successful match binds
///   every metavariable its pattern names, and a splice at a position agrees
///   with the read there.
/// - witness: `tests::inhabitant::matching_then_substituting_returns_the_matched_term`
/// - witness: `tests::inhabitant::a_successful_match_binds_every_metavariable_the_pattern_names`
/// - witness: `tests::inhabitant::splicing_at_a_position_agrees_with_reading_it`
/// - witness: `sequent::tests::each_eta_kind_requires_its_own_polarity`
pub trait CellAlphabet: Copy + Default + Eq + Ord + core::hash::Hash + core::fmt::Debug
{
    /// The command-pattern term type: the tree a cell's two faces are and the
    /// engines rewrite. Equality and hashing are structural content identity.
    type Cmd: Clone + Eq + core::hash::Hash + core::fmt::Debug;
    /// The metavariable type: a hole in a pattern.
    type Var: Clone + Eq + core::hash::Hash + core::fmt::Debug;
    /// The hole identity: how a metavariable is keyed across a cell's two
    /// faces.
    type Hole: Clone + Eq + Ord + core::hash::Hash + core::fmt::Debug;
    /// The position type: a path addressing a command subterm.
    type Pos: Clone + Eq + core::hash::Hash + core::fmt::Debug;
    /// The ordered substitution map, deterministic in its iteration.
    type Subst: Clone + Default + Eq + core::hash::Hash + core::fmt::Debug;
    /// How a cell's orientation was fixed.
    type Orientation: Copy + Eq + core::hash::Hash + core::fmt::Debug;
    /// Where a cell came from.
    type Provenance: Copy + Eq + core::hash::Hash + core::fmt::Debug;
    /// The derived per-cell metadata, computed by
    /// [`CellAlphabet::derive_meta`].
    type Meta: Clone + Eq + core::hash::Hash + core::fmt::Debug;

    /// One-sided matching: binds `pattern`'s metavariables so the
    /// instantiated pattern equals `target`, extending `subst`.
    ///
    /// # Specification
    /// - ensures: a positive decision instantiates `pattern` to `target` under
    ///   `subst`.
    /// - fails: a negative decision when no extension of `subst` does; an
    ///   implementation may leave `subst` partially extended then.
    /// - panics: none.
    fn match_cmd(
        pattern: &Self::Cmd,
        target: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision;

    /// Two-sided unification: a most general unifier of `lhs` and `rhs`,
    /// extending `subst`.
    ///
    /// # Specification
    /// - requires: the two sides' metavariables are kept apart, by
    ///   [`CellAlphabet::rename_apart`] first.
    /// - ensures: a positive decision makes `subst` a unifier — both sides
    ///   instantiate to the same term.
    /// - fails: a negative decision on a clash or an occurs-check failure; an
    ///   implementation may leave `subst` partially extended then.
    /// - panics: none.
    fn unify_cmd(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision;

    /// A term with a substitution applied.
    ///
    /// # Specification
    /// - ensures: every bound metavariable is replaced by its image; unbound
    ///   metavariables stay.
    /// - panics: none.
    fn apply_subst(
        subst: &Self::Subst,
        cmd: &Self::Cmd,
    ) -> Self::Cmd;

    /// The term's metavariables, left to right with repeats, so linearity is
    /// judged by counting occurrences.
    ///
    /// # Specification
    /// - ensures: one entry per metavariable occurrence, in left-to-right
    ///   order.
    /// - panics: none.
    fn metavariables(cmd: &Self::Cmd) -> Vec<Self::Var>;

    /// Every command position of the term — the seams a cell can fire at and
    /// the composition enumerator unifies at — outer to inner.
    ///
    /// # Specification
    /// - ensures: each position addresses a command subterm, so
    ///   [`CellAlphabet::subterm_cmd_at`] is present at it; the order is
    ///   deterministic and no position precedes one enclosing it.
    /// - panics: none.
    fn command_positions(cmd: &Self::Cmd) -> Vec<Self::Pos>;

    /// The root position, the seam of a confluence overlap.
    ///
    /// # Specification
    /// - ensures: [`CellAlphabet::subterm_cmd_at`] at the root is the whole
    ///   term.
    /// - panics: none.
    fn root_position() -> Self::Pos;

    /// The position addressing the child-index `path`, read from the root
    /// outward.
    ///
    /// A position can arrive from outside the store: a record that addresses
    /// subterms by argument-index path enters the engines through this.
    ///
    /// # Specification
    /// - requires: `path` reads the child indices from the root outward.
    /// - ensures: the empty path is [`CellAlphabet::root_position`]; two
    ///   positions built here relate under [`CellAlphabet::position_order`]
    ///   exactly as their paths relate under [`path_order`]; a path off a term
    ///   is a position that addresses nothing there.
    /// - panics: none.
    fn position_at_path(path: &[PositionStep]) -> Self::Pos;

    /// How two positions relate: whether one addresses a subtree containing
    /// the other, or the two address disjoint subtrees.
    ///
    /// # Specification
    /// - ensures: [`PositionOrder::Incomparable`] exactly when neither position
    ///   is a prefix of the other; [`PositionOrder::Same`] for a position
    ///   paired with itself; symmetric up to swapping
    ///   [`PositionOrder::Encloses`] and [`PositionOrder::EnclosedBy`].
    /// - panics: none.
    fn position_order(
        left: &Self::Pos,
        right: &Self::Pos,
    ) -> PositionOrder;

    /// The convexity discharge `store` certifies: the warrant a convexity
    /// re-check is skipped under, or the refusal to skip it.
    ///
    /// # Specification
    /// - requires: an implementor answers
    ///   [`ConvexityDischarge::StronglyConnectedOverAcyclicTarget`] only when
    ///   every left-hand side in `store` is strongly connected and every target
    ///   the engines rewrite is acyclic; otherwise
    ///   [`ConvexityDischarge::ReCheckRequired`].
    /// - ensures: the answer is stable for a given store.
    /// - panics: none.
    fn convexity_discharge(store: &CellStore<Self>) -> ConvexityDischarge;

    /// The command subterm at `pos`.
    ///
    /// # Specification
    /// - ensures: the command `pos` addresses inside `cmd`, owned.
    /// - provides: [`command_subterm::Absent::OffTerm`] when the path leaves
    ///   the term, [`command_subterm::Absent::NotACommand`] when it addresses a
    ///   subterm that is not a command.
    /// - panics: none.
    fn subterm_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
    ) -> Maybe<Self::Cmd, command_subterm::Absent>;

    /// `cmd` with `replacement` spliced in at `pos`.
    ///
    /// # Specification
    /// - ensures: the term equal to `cmd` except at `pos`, which holds
    ///   `replacement`; reading `pos` there returns `replacement`.
    /// - fails: [`CommandSpliceRefusal::OffTerm`] when the path leaves the
    ///   term; [`CommandSpliceRefusal::NotACommand`] when it addresses a
    ///   subterm a command cannot replace.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn splice_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
        replacement: Self::Cmd,
    ) -> Result<Self::Cmd, CommandSpliceRefusal>;

    /// The reduction order: a well-founded orientation completion uses to
    /// turn a divergent critical pair into a cell, larger side on the left.
    ///
    /// # Specification
    /// - ensures: [`core::cmp::Ordering::Equal`] for every pair the order
    ///   cannot orient — an honest obstruction, never a guessed orientation;
    ///   antisymmetric otherwise.
    /// - panics: none.
    fn reduction_cmp(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
    ) -> core::cmp::Ordering;

    /// `renamed`'s two faces with their metavariables renamed apart from
    /// `anchor`'s: the deterministic renaming overlap enumeration performs on
    /// the second cell of a pair before unifying.
    ///
    /// # Specification
    /// - ensures: `renamed`'s faces with every metavariable replaced by one
    ///   absent from both `anchor` faces and from the other renamed variables,
    ///   the pattern shapes kept, so the original faces are recoverable by
    ///   zipping occurrences; an already disjoint cell is returned unchanged.
    /// - panics: none.
    fn rename_apart(
        anchor: (&Self::Cmd, &Self::Cmd),
        renamed: (&Self::Cmd, &Self::Cmd),
    ) -> (Self::Cmd, Self::Cmd);

    /// The term with each metavariable replaced by a fresh, reserved
    /// constant, so replay can ground-rewrite a schematic peak.
    ///
    /// # Specification
    /// - ensures: the result is metavariable-free; the mapping is
    ///   name-deterministic, so shared metavariables skolemize identically
    ///   across a peak and its join, and the constants are irreducible under
    ///   the alphabet's own cells.
    /// - panics: none.
    fn skolemize(cmd: &Self::Cmd) -> Self::Cmd;

    /// The hole identity of a metavariable.
    ///
    /// # Specification
    /// - ensures: metavariables denoting one hole across a cell's two faces map
    ///   to equal holes.
    /// - panics: none.
    fn hole_of(var: &Self::Var) -> Self::Hole;

    /// Whether `provenance` marks an invertible joinability certificate, as
    /// opposed to an oriented optimization cell.
    ///
    /// # Specification
    /// - ensures: positive exactly for the provenance
    ///   [`CellAlphabet::derived_provenance`] produces.
    /// - panics: none.
    fn completion_certificate(provenance: &Self::Provenance) -> CellInvertibility;

    /// The per-cell metadata, derived from the two faces.
    ///
    /// # Specification
    /// - ensures: the metadata a freshly built cell carries; `invertible` is
    ///   carried through as given.
    /// - panics: none.
    fn derive_meta(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        invertible: CellInvertibility,
    ) -> Self::Meta;

    /// The `(variable, flow role)` endpoints `meta` carries for `hole`: the
    /// composition gate's per-cell read of one seam hole.
    ///
    /// # Specification
    /// - ensures: one endpoint per metadata entry whose hole identity equals
    ///   `hole`; empty when the hole does not occur.
    /// - panics: none.
    fn hole_flow(
        meta: &Self::Meta,
        hole: &Self::Hole,
    ) -> Vec<(Self::Var, SeamRole)>;

    /// The firing discipline: whether a cell of `provenance` may fire at
    /// `target`.
    ///
    /// # Specification
    /// - ensures: a negative permission means the cell must not fire at
    ///   `target`, however well its left-hand side matches.
    /// - panics: none.
    fn may_fire(
        provenance: &Self::Provenance,
        target: &Self::Cmd,
    ) -> FiringPermission;

    /// The orientation tag stamped on cells completion and fusion derive.
    ///
    /// # Specification
    /// trivial.
    fn derived_orientation() -> Self::Orientation;

    /// The provenance tag stamped on cells completion and fusion derive, the
    /// tag [`CellAlphabet::completion_certificate`] reads.
    ///
    /// # Specification
    /// trivial.
    fn derived_provenance() -> Self::Provenance;
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn the_path_order_separates_its_four_outcomes()
    {
        let outer = [1_usize].map(PositionStep::from);
        let inner = [1_usize, 0_usize].map(PositionStep::from);
        let sibling = [1_usize, 1_usize].map(PositionStep::from);
        assert_eq!(
            PositionOrder::Same,
            path_order(inner, inner),
            "equal paths are one position"
        );
        assert_eq!(
            PositionOrder::Encloses,
            path_order(outer, inner),
            "a proper prefix encloses"
        );
        assert_eq!(
            PositionOrder::EnclosedBy,
            path_order(inner, outer),
            "and is enclosed from the other side"
        );
        assert_eq!(
            PositionOrder::Incomparable,
            path_order(inner, sibling),
            "paths diverging at a shared depth address disjoint subtrees"
        );
    }
}
