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
//!   ([`CellAlphabet::subterm_cmd_at`], [`CellAlphabet::splice_cmd_at`]), its
//!   node count ([`CellAlphabet::cmd_size`]), the well-founded
//!   [`CellAlphabet::reduction_cmp`] completion orients by, the deterministic
//!   apartness renaming [`CellAlphabet::rename_apart`], and the replay
//!   [`CellAlphabet::skolemize`];
//! - the ordered-map substitution — one-sided matching
//!   ([`CellAlphabet::match_cmd`], cell application), two-sided unification
//!   ([`CellAlphabet::unify_cmd`], overlap superposition) and its dual,
//!   anti-unification ([`CellAlphabet::anti_unify_cmd`], folding a family of
//!   instances into one pattern), all over the deterministic
//!   [`CellAlphabet::Subst`] carrier, which [`CellAlphabet::restrict_subst`]
//!   cuts down to chosen metavariables;
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
use crate::boundary::PatternSize;
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
/// - executable: none — both generic iterators are consumed; an independent
///   exit check cannot recover their paths without changing the iterator bounds
///   or buffering the input.
/// - intension: one pass over the shorter path.
///
/// # Adequacy
/// - hypothesis: L3 — empty and nonempty paths, equal paths, proper prefixes
///   each way and early divergence have exact relation observations. Dropping a
///   step, confusing exhaustion and reversing enclosure changes an answer.
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

quenchant_shape::reason_enum! {
    /// Why a family of terms has no generalization.
    pub mod anti_unification {
        /// The reason the anti-unifier finds no pattern.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The family has no member.
            EmptyFamily,
            /// Two members are tuples of different lengths.
            RaggedFamily,
            /// Two members differ where the grammar has no metavariable to
            /// stand.
            Ungeneralizable,
        }
    }
}

/// One member's arm at a generalization point: the subterm the member holds
/// where the point stands.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct GeneralizationArm<A: CellAlphabet>
{
    /// The substitution binding the point's metavariable, and nothing else, to
    /// the member's subterm.
    pub binding: A::Subst,
    /// The node count of the member's subterm.
    pub size: PatternSize,
}

/// One generalization point: a fresh metavariable, and the subterm it stands
/// for in each member.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneralizationPoint<A: CellAlphabet>
{
    /// The fresh metavariable standing at the point.
    pub var: A::Var,
    /// One arm per member, in family order.
    pub arms: Vec<GeneralizationArm<A>>,
}

/// The least general generalization of a family of term tuples: the patterns
/// every member instantiates, and what each point stands for in each member.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Generalization<A: CellAlphabet>
{
    /// One pattern per tuple component.
    pub patterns: Vec<A::Cmd>,
    /// The generalization points, in the order the walk first meets them.
    pub points: Vec<GeneralizationPoint<A>>,
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
///   one-sided, [`CellAlphabet::unify_cmd`] finds a most general unifier and
///   [`CellAlphabet::anti_unify_cmd`] a least general generalization;
///   [`CellAlphabet::rename_apart`] is deterministic and structure-preserving.
/// - requires: two occurrences of one primitive at one position remain
///   dependent: [`CellAlphabet::position_order`] returns
///   [`PositionOrder::Same`] for a position paired with itself.
/// - ensures: an engine generic over the trait reads every decline as data — an
///   absence, a refusal or a negative decision — never a panic.
/// - panics: none.
/// - executable: none — this trait states laws of every inhabitant; its
///   declarations have no bodies. Instrumenting the entire trait changes the
///   method protocol required of external implementations.
///
/// # Adequacy
/// - hypothesis: L3 — the sequent alphabet's own suite runs through the trait's
///   methods: renaming apart, skolemization and the firing discipline are
///   asserted on cells that wear a seam, repeat a name and carry each η kind.
///   The four inhabitant laws the engines spend — a match followed by its
///   substitution reproduces the matched term, a successful match binds every
///   metavariable its pattern names, a splice at a position agrees with the
///   read there, and each member of a family is its generalization under its
///   own arms — are asserted over this inhabitant and a second, nesting term
///   language by `gandr-theory-cell-complexes-tools`' inhabitant suite, which
///   depends on this crate, so the laws are cited here rather than witnessed.
/// - witness: `sequent::tests::renaming_apart_keeps_a_seam_one_hole`
/// - witness: `sequent::tests::skolemization_is_name_stable`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sequent patterns with two hole categories and a
    ///   constructor clash are observed through replayed substitutions and
    ///   refusal; this separates dropped bindings from unconditional success.
    /// - witness: `alphabet::tests::substitution_and_generalization_obey_the_alphabet_laws`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — renamed-apart sequent terms with compatible holes or
    ///   clashing heads are observed after substitution on both sides; this
    ///   separates incomplete unifiers from false success.
    /// - witness: `alphabet::tests::substitution_and_generalization_obey_the_alphabet_laws`
    fn unify_cmd(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision;

    /// Anti-unification: the least general generalization of `family`, a
    /// family of equal-length term tuples, taken component by component over
    /// one table of fresh metavariables.
    ///
    /// Unification's dual: where a unifier finds the most general term two
    /// patterns both instantiate to, the generalization is the most specific
    /// pattern tuple every member instantiates.
    ///
    /// # Specification
    /// - requires: none; a member may carry metavariables of its own, which an
    ///   arm binds like any other subterm.
    /// - ensures: one pattern per component; for every member, applying its
    ///   arm's binding at every point to each pattern gives the member's
    ///   component back; a position where every member holds one head keeps
    ///   that head and is descended into, so a point stands only where two
    ///   members differ; two positions whose subterms agree member by member
    ///   carry one point; no point's metavariable occurs in any member; the
    ///   points are listed in the order the walk first meets them, component by
    ///   component, left to right.
    /// - provides: [`anti_unification::Absent::EmptyFamily`] for a family with
    ///   no member; [`anti_unification::Absent::RaggedFamily`] when two members
    ///   are tuples of different lengths;
    ///   [`anti_unification::Absent::Ungeneralizable`] when two members differ
    ///   where the grammar admits no metavariable.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, singleton and differing sequent families are
    ///   observed by typed refusal and reconstruction under each member arm;
    ///   lost components and incorrect point bindings are separated.
    /// - witness: `alphabet::tests::substitution_and_generalization_obey_the_alphabet_laws`
    fn anti_unify_cmd(
        family: &[&[Self::Cmd]]
    ) -> Maybe<Generalization<Self>, anti_unification::Absent>;

    /// A term with a substitution applied.
    ///
    /// # Specification
    /// - ensures: every bound metavariable is replaced by its image; unbound
    ///   metavariables stay.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sequent substitutions bind producer and consumer
    ///   holes or leave either unbound. Exact instantiated terms distinguish
    ///   missed replacements and accidental replacement of an unbound hole.
    /// - witness: `alphabet::tests::substitution_and_generalization_obey_the_alphabet_laws`
    fn apply_subst(
        subst: &Self::Subst,
        cmd: &Self::Cmd,
    ) -> Self::Cmd;

    /// `subst` restricted to `vars`: the bindings it holds for exactly those
    /// metavariables.
    ///
    /// # Specification
    /// - ensures: every binding of `subst` whose metavariable is in `vars`, and
    ///   no other; a metavariable of `vars` that `subst` leaves unbound stays
    ///   unbound.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sequent substitutions restricted to none, one or all
    ///   bound variables are observed by their images. Extra bindings, missing
    ///   requested bindings and rebinding an unbound variable are separated.
    /// - witness: `alphabet::tests::substitution_and_generalization_obey_the_alphabet_laws`
    fn restrict_subst(
        subst: &Self::Subst,
        vars: &[Self::Var],
    ) -> Self::Subst;

    /// The term's metavariables, left to right with repeats, so linearity is
    /// judged by counting occurrences.
    ///
    /// # Specification
    /// - ensures: one entry per metavariable occurrence, in left-to-right
    ///   order.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ground terms and repeated producer/consumer holes are
    ///   observed as ordered occurrence vectors; deduplication, category loss
    ///   and reversal change the result.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
    fn metavariables(cmd: &Self::Cmd) -> Vec<Self::Var>;

    /// The term's node count.
    ///
    /// # Specification
    /// - ensures: one per node of the term; at least one.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf cuts and nested sequent terms have hand-counted
    ///   sizes; missing cut, producer or continuation nodes changes the count.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
    fn cmd_size(cmd: &Self::Cmd) -> PatternSize;

    /// Every command position of the term — the seams a cell can fire at and
    /// the composition enumerator unifies at — outer to inner.
    ///
    /// # Specification
    /// - ensures: each position addresses a command subterm, so
    ///   [`CellAlphabet::subterm_cmd_at`] is present at it; the order is
    ///   deterministic and no position precedes one enclosing it.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf and nested sequent terms expose exactly their
    ///   root command. A missing root or a noncommand position changes the full
    ///   position list.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
    fn command_positions(cmd: &Self::Cmd) -> Vec<Self::Pos>;

    /// The root position, the seam of a confluence overlap.
    ///
    /// # Specification
    /// - ensures: [`CellAlphabet::subterm_cmd_at`] at the root is the whole
    ///   term.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ground and schematic sequent roots read back their
    ///   complete terms; returning a child or absence changes the observed
    ///   term.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, child and off-term paths are observed by reads
    ///   and prefix ordering. Dropped or shifted child indices change the read
    ///   or relation.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal paths, both proper-prefix directions and
    ///   first-step divergence are distinguished. Reflexivity loss and reversed
    ///   enclosure change the relation.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and nonempty sequent stores retain the
    ///   grammar-specific discharge. Refusing one state changes the warrant;
    ///   finite tests cannot prove the acyclicity of every external alphabet.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
    fn convexity_discharge(store: &CellStore<Self>) -> ConvexityDischarge;

    /// The command subterm at `pos`.
    ///
    /// # Specification
    /// - ensures: the command `pos` addresses inside `cmd`, owned.
    /// - provides: [`command_subterm::Absent::OffTerm`] when the path leaves
    ///   the term, [`command_subterm::Absent::NotACommand`] when it addresses a
    ///   subterm that is not a command.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root, producer/consumer children and off-term sequent
    ///   positions separate command, noncommand and absent reads. Each exact
    ///   result rejects a merged refusal class.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root, producer/consumer children and off-term sequent
    ///   positions separate replacement from the two typed refusals. Exact
    ///   terms reject a discarded replacement or changed sibling.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sequent pairs separated by size, equal-size
    ///   precedence and missing holes observe strict orientations and
    ///   obstructions; swapped signs and dropped hole guards change the
    ///   answers.
    /// - witness: `order::tests::a_size_difference_orients_when_the_larger_side_dominates`
    /// - witness: `sequent::tests::frame_cells_and_alphabet_reduction_preserve_structure`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — intersecting and already disjoint sequent faces
    ///   observe fresh names and the shared producer/consumer seam; collapsing
    ///   holes or splitting one seam changes the renamed terms.
    /// - witness: `sequent::tests::renaming_apart_keeps_a_seam_one_hole`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — producer and consumer holes in one sequent term are
    ///   compared to exact reserved constants; missed grounding or name
    ///   conflation changes the term.
    /// - witness: `sequent::tests::skolemization_is_name_stable`
    fn skolemize(cmd: &Self::Cmd) -> Self::Cmd;

    /// The hole identity of a metavariable.
    ///
    /// # Specification
    /// - ensures: metavariables denoting one hole across a cell's two faces map
    ///   to equal holes.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal-spelled producer and consumer variables share
    ///   one hole, while distinct spellings stay distinct; category-sensitive
    ///   identity or a constant hole changes equality.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
    fn hole_of(var: &Self::Var) -> Self::Hole;

    /// Whether `provenance` marks an invertible joinability certificate, as
    /// opposed to an oriented optimization cell.
    ///
    /// # Specification
    /// - ensures: positive exactly for the provenance
    ///   [`CellAlphabet::derived_provenance`] produces.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every sequent provenance is observed at both
    ///   orientations; only completion provenance is invertible. A reversed or
    ///   widened certificate guard changes metadata.
    /// - witness: `sequent::tests::completion_cells_are_invertible_certificates`
    fn completion_certificate(provenance: &Self::Provenance) -> CellInvertibility;

    /// The per-cell metadata, derived from the two faces.
    ///
    /// # Specification
    /// - ensures: the metadata a freshly built cell carries; `invertible` is
    ///   carried through as given.
    /// - panics: none.
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sequent cells with no holes, producer-only,
    ///   consumer-only and shared holes observe metadata and invertibility;
    ///   wrong counts, variance or a lost flag change the projections.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — absent, producer-only, consumer-only and shared
    ///   sequent holes expose exact endpoints and roles; extra endpoints, wrong
    ///   hole filtering and swapped flow roles change the result.
    /// - witness: `alphabet::tests::position_and_metadata_observations_obey_the_alphabet_laws`
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
    /// - executable: none — an abstract declaration has no body; trait-wide
    ///   instrumentation changes the required implementation protocol.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both eta kinds at both cut polarities distinguish
    ///   permission and refusal; ignoring provenance or reversing the polarity
    ///   guard changes the decision.
    /// - witness: `sequent::tests::each_eta_kind_requires_its_own_polarity`
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
        assert_eq!(PositionOrder::Same, path_order([], []));
        assert_eq!(PositionOrder::Encloses, path_order([], inner));
        assert_eq!(PositionOrder::EnclosedBy, path_order(inner, []));
        assert_eq!(
            PositionOrder::Incomparable,
            path_order([0_usize, 1].map(PositionStep::from), inner)
        );
    }

    #[test]
    fn substitution_and_generalization_obey_the_alphabet_laws()
    {
        use crate::pattern::CmdPat;
        use crate::pattern::ConsPat;
        use crate::pattern::MetaVar;
        use crate::pattern::ProdPat;
        use crate::polarity::Polarity;
        use crate::sequent::SequentAlphabet as A;
        use crate::subst::Subst;

        let cut = |prod, cons| CmdPat::cut(Polarity::Positive, prod, cons);
        let pattern = cut(
            ProdPat::ctor("Succ", [ProdPat::meta("x")]),
            ConsPat::meta("alpha"),
        );
        let target = cut(
            ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]),
            ConsPat::frame("F", ConsPat::top()),
        );
        let vars = [MetaVar::producer("x"), MetaVar::consumer("alpha")];
        let mut subst = Subst::new();
        assert!(bool::from(A::match_cmd(&pattern, &target, &mut subst)));
        assert_eq!(target, A::apply_subst(&subst, &pattern));
        assert_eq!(
            pattern,
            A::apply_subst(&A::restrict_subst(&subst, &[]), &pattern)
        );
        assert_eq!(
            target,
            A::apply_subst(&A::restrict_subst(&subst, &vars), &pattern)
        );
        assert_eq!(
            cut(
                ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]),
                ConsPat::meta("alpha")
            ),
            A::apply_subst(&A::restrict_subst(&subst, &vars[.. 1]), &pattern)
        );
        assert_eq!(
            pattern,
            A::apply_subst(
                &A::restrict_subst(&subst, &[MetaVar::producer("absent")]),
                &pattern
            )
        );

        let left = cut(
            ProdPat::ctor("Succ", [ProdPat::meta("left")]),
            ConsPat::top(),
        );
        let right = cut(ProdPat::meta("right"), ConsPat::top());
        let mut unifier = Subst::new();
        assert!(bool::from(A::unify_cmd(&left, &right, &mut unifier)));
        assert_eq!(left, A::apply_subst(&unifier, &left));
        assert_eq!(left, A::apply_subst(&unifier, &right));
        let zero = cut(ProdPat::ctor("Zero", []), ConsPat::top());
        let one = cut(ProdPat::ctor("One", []), ConsPat::top());
        assert!(!bool::from(A::match_cmd(&zero, &one, &mut Subst::new())));
        assert!(!bool::from(A::unify_cmd(&zero, &one, &mut Subst::new())));

        assert_eq!(
            Maybe::Absent(anti_unification::Absent::EmptyFamily),
            A::anti_unify_cmd(&[])
        );
        let singleton = [zero.clone()];
        let Maybe::Present(unchanged) = A::anti_unify_cmd(&[&singleton])
        else {
            panic!("a singleton has its exact generalization");
        };
        assert_eq!(singleton.as_slice(), unchanged.patterns.as_slice());
        assert!(unchanged.points.is_empty());
        let members = [[zero], [one]];
        let Maybe::Present(generalization) = A::anti_unify_cmd(&[&members[0], &members[1]])
        else {
            panic!("distinct producer constants have a generalization");
        };
        assert_eq!(1, generalization.patterns.len());
        assert_eq!(1, generalization.points.len());
        for (member, expected) in members.iter().enumerate() {
            let rebuilt = generalization
                .points
                .iter()
                .fold(generalization.patterns[0].clone(), |term, point| {
                    A::apply_subst(&point.arms[member].binding, &term)
                });
            assert_eq!(&expected[0], &rebuilt);
        }
    }

    #[test]
    fn position_and_metadata_observations_obey_the_alphabet_laws()
    {
        use crate::pattern::CmdPat;
        use crate::pattern::ConsPat;
        use crate::pattern::HoleName;
        use crate::pattern::MetaVar;
        use crate::pattern::ProdPat;
        use crate::pattern::Sym;
        use crate::polarity::Polarity;
        use crate::sequent::SequentAlphabet as A;
        use crate::sequent::frame_defining_cell;

        let cut = |prod, cons| CmdPat::cut(Polarity::Positive, prod, cons);
        let ground = cut(ProdPat::ctor("Zero", []), ConsPat::top());
        let nested = cut(
            ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("x")]),
            ConsPat::frame("F", ConsPat::meta("alpha")),
        );
        assert!(A::metavariables(&ground).is_empty());
        assert_eq!(
            alloc::vec![
                MetaVar::producer("x"),
                MetaVar::producer("x"),
                MetaVar::consumer("alpha")
            ],
            A::metavariables(&nested)
        );
        assert_eq!(PatternSize::from(3_usize), A::cmd_size(&ground));
        assert_eq!(PatternSize::from(6_usize), A::cmd_size(&nested));
        let root = A::root_position();
        let prod = A::position_at_path(&[PositionStep::from(0_usize)]);
        let cons = A::position_at_path(&[PositionStep::from(1_usize)]);
        let absent = A::position_at_path(&[PositionStep::from(2_usize)]);
        assert_eq!(root, A::position_at_path(&[]));
        assert_eq!(PositionOrder::Same, A::position_order(&root, &root));
        assert_eq!(PositionOrder::Encloses, A::position_order(&root, &prod));
        assert_eq!(PositionOrder::EnclosedBy, A::position_order(&cons, &root));
        assert_eq!(PositionOrder::Incomparable, A::position_order(&prod, &cons));
        for term in [&ground, &nested] {
            assert_eq!(alloc::vec![root.clone()], A::command_positions(term));
            assert_eq!(Maybe::Present(term.clone()), A::subterm_cmd_at(term, &root));
            assert_eq!(
                Ok(ground.clone()),
                A::splice_cmd_at(term, &root, ground.clone())
            );
            for pos in [&prod, &cons] {
                assert_eq!(
                    Maybe::Absent(command_subterm::Absent::NotACommand),
                    A::subterm_cmd_at(term, pos)
                );
                assert_eq!(
                    Err(CommandSpliceRefusal::NotACommand),
                    A::splice_cmd_at(term, pos, ground.clone())
                );
            }
            assert_eq!(
                Maybe::Absent(command_subterm::Absent::OffTerm),
                A::subterm_cmd_at(term, &absent)
            );
            assert_eq!(
                Err(CommandSpliceRefusal::OffTerm),
                A::splice_cmd_at(term, &absent, ground.clone())
            );
        }
        assert_eq!(
            A::hole_of(&MetaVar::producer("x")),
            A::hole_of(&MetaVar::consumer("x"))
        );
        assert_ne!(
            A::hole_of(&MetaVar::producer("x")),
            A::hole_of(&MetaVar::producer("y"))
        );
        let mut store = CellStore::new();
        assert_eq!(
            ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
            A::convexity_discharge(&store)
        );
        store.insert(frame_defining_cell(&Sym::new("Succ")));
        assert_eq!(
            ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
            A::convexity_discharge(&store)
        );
        for (term, expected) in [
            (ground, alloc::vec![]),
            (cut(ProdPat::meta("x"), ConsPat::top()), alloc::vec![(
                MetaVar::producer("x"),
                SeamRole::Forward
            )]),
            (
                cut(ProdPat::ctor("Zero", []), ConsPat::meta("x")),
                alloc::vec![(MetaVar::consumer("x"), SeamRole::Backward)],
            ),
            (cut(ProdPat::meta("x"), ConsPat::meta("x")), alloc::vec![(
                MetaVar::producer("x"),
                SeamRole::Both
            )]),
        ] {
            for invertible in [false, true] {
                let meta = A::derive_meta(&term, &term, CellInvertibility::from(invertible));
                assert_eq!(invertible, bool::from(meta.invertible()));
                assert_eq!(expected, A::hole_flow(&meta, &HoleName::new("x")));
                assert!(A::hole_flow(&meta, &HoleName::new("missing")).is_empty());
            }
        }
    }
}
