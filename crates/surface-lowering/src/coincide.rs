//! The two readings of a description's rules made one.
//!
//! # Two readings, one meaning
//!
//! A `data` family's rules are read twice. The operation route compiles an
//! operation's rules, in the order written, to a decision tree whose first
//! matching rule fires (`operation`); the cell layer reads every rule as an
//! equation between commands and rewrites with whichever cell matches. The two
//! agree on every call when the rules terminate and every critical pair — two
//! rules matching one term — joins: the rewriting is then confluent, every
//! strategy reaches the one normal form, and first match is one strategy
//! (Newman's lemma with the critical-pair lemma). [`decide`] decides both
//! halves for every `data` and `theory` block with rules, at `checks`:
//!
//! 1. Termination, by the lexicographic path order over the block's faces
//!    (`orient_rules`; the order and why it is not the cell layer's own are in
//!    that function's crate), the higher-order recursive path order where a
//!    rule instantiates a variable. The first rule it does not orient is
//!    refused as [`LoweringRefusal::RulesUnoriented`] at that rule. A rule that
//!    instantiates a variable, `let(u, t) ==> t(u)`, is a second-order rule: no
//!    cell holds one, and its left side may overlap no rule's, the later of two
//!    such rules refused as [`LoweringRefusal::RulesOverlapSecondOrder`] naming
//!    the earlier. Orthogonal second-order pattern rules are confluent (Mayr
//!    and Nipkow), so the joins below decide the rest.
//! 2. Joinability of every critical pair over the block's own cells
//!    (`PairJoining`), completed where a pair parts. A pair whose two normal
//!    forms are both headed by a constructor is refused as
//!    [`LoweringRefusal::RulesDiverge`] at the later rule, naming the earlier
//!    one, the peak and both normal forms kept in the cell diagnostic
//!    ([`CoherenceFault::Diverges`]): no rule joins two values. Any other
//!    divergent pair is joined by the rule it derives — both its sides are
//!    reducts of one peak, so it follows from the rules before it — its left
//!    side headed by an operation and oriented by the path order
//!    (`orient_rules_with`): first over the precedence the block's rules and
//!    the ranking rules derived so far induce, and failing that as a ranking
//!    rule itself, its calls raising its head. The rule is appended to the
//!    reading's store and the joining resumed at the pair that parted: every
//!    pair a rule makes with the rules before it is decided before any pair of
//!    a later one, so a pair already joined is never decided again. A pair no
//!    direction orients is refused as [`LoweringRefusal::RulesUncompleted`]. A
//!    derived rule that embeds a rule derived from one of its pair's cells
//!    (`embeds`), and is that rule with one subterm wrapped in a context, the
//!    rest renamed, where no rule of the store rewrites any further wrapping
//!    (`rule_keeps_growing`), is refused as
//!    [`LoweringRefusal::RulesNeverComplete`] naming both rules
//!    ([`CoherenceFault::NeverCompletes`]): each round wraps the rule before,
//!    so completion never ends. A family a rule completion would derive later
//!    from another pair stops is refused all the same. A pair a reduct of which
//!    reaches no normal form within [`JOIN_STEPS`] steps, or one that still
//!    parts once [`DERIVED_RULES`] rules are derived, is refused as
//!    [`LoweringRefusal::RulesUndecided`], which reports the budget and no
//!    verdict.
//!
//! A block that passes is orthogonal — no two of its rules overlap — or
//! joined, with one replaying certificate per critical pair and one per
//! derived rule ([`Coincidence`], [`DerivedRule`]). A derived rule's left
//! side is headed by an operation, so a constructor term stays a normal form
//! of the completed rules: the value a decision tree computes for a call is
//! the completed rules' normal form of it. Witnesses:
//! `coincide::tests::an_overlap_that_joins_is_certified_and_runs_either_way`,
//! `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`,
//! `coincide::tests::a_rule_that_rebuilds_its_own_call_refuses_the_block`,
//! `coincide::tests::a_groups_inverse_law_completes_to_the_rules_it_derives`,
//! `coincide::tests::a_permuted_call_no_order_orients_is_uncompleted`,
//! `coincide::tests::a_scope_extrusion_family_never_completes`.
//!
//! A circuit rule is a congruence over the rewrite it binds — `add(x, y) ==>
//! add(x′, y)` reads "a rewrite of `x` rewrites the sum" — not a rewrite of
//! its own: its right-hand side names a hole its left does not bind, so it is
//! left out of the rewriting the check reads ([`DeclarationCells::rewriting`]).
//! A block the cell gate declined an operation or a member of is not examined
//! ([`Coincidence::Unexamined`]): the decline is already its refusal, and a
//! verdict over the members left would be over rules the author did not write
//! alone.
//!
//! A block whose two readings part is refused whole, as a family: the
//! equational reading is what the rules mean — what a model of the family
//! satisfies, and what a `theory` block's models state as paths — and the
//! decision tree is how they run, so a tree computing what the equations do
//! not is refused rather than run. A derived rule adds no equation: it
//! certifies one the written rules already state.
//!
//! # The equation
//!
//! `<=>` states the equation and leaves the direction to the order.
//! [`orient_block`] tries the written left-to-right direction, then the
//! written right-to-left direction, and refuses
//! [`LoweringRefusal::RulesUnoriented`] when
//! neither puts one side above the other. `==>` pins left to right: a pinned
//! rule the order refuses stays [`LoweringRefusal::RulesUnoriented`], as a rule
//! written only that way always has. The kernel-facing table receives the
//! oriented rule only — left above right
//! — and the declaration's rules keep the written arrow so the printer reads
//! `<=>` back.
//!
//! # A presented type
//!
//! A `data` family whose rules rewrite its own constructor words — the
//! circle's `Loop(Unloop(x)) ==> x` and `Unloop(Loop(x)) ==> x` — has no
//! operation for the decision tree to compile and no sequent cell for its
//! rules: its reading is the rewriting of the words, over terms
//! (`DeclarationCells::presented`). Step 2 decides that reading's critical
//! pairs as well, and there a rule overlaps another inside its left-hand side,
//! not only at the root (`interior_overlaps_between`): the circle's
//! cancellations meet at `Loop(Unloop(Loop(x)))` and at
//! `Unloop(Loop(Unloop(x)))`, and both join, while a third rule `Loop(Loop(x))
//! ==> x` meets the second at `Unloop(Loop(Loop(x)))`, which it leaves at
//! `Unloop(x)` and the second at `Loop(x)`, and is refused. A divergence is
//! located at the later of the two rules whichever of them the overlap reads
//! first. Witnesses:
//! `coincide::tests::the_circles_cancellations_join_below_the_root`,
//! `coincide::tests::a_third_cancellation_parts_the_circles_readings`.
//!
//! A `theory` block's laws over unindexed sorts take the same road where one
//! applies an operation where an argument stands: the circle's shape,
//! `turn(unturn(x)) ==> x` and `unturn(turn(x)) ==> x` over the operations
//! `turn` and `unturn`, meets at the peaks the circle's constructor rules meet
//! at and joins there, so the presentation and the presented type are one
//! rewriting system read twice. A law over an indexed sort, a category's
//! `comp(id(a), f) ==> f`, stays declined at the cell gate
//! (`gandr_theory_computads::DescReading`). Witness:
//! `coincide::tests::the_circles_shape_joins_where_the_circle_does`.
//!
//! # The normal form a call reaches
//!
//! [`normal_form`] reads a call written in the inspection notation —
//! `divmod(Succ(Succ(Zero)), Succ(Zero))` — elaborates it to the command its
//! operation's faces match, normalizes it under the block's rewriting, replays
//! the path it took to certify the normal form, and reads the normal form back
//! as a first-order term (`read_command`): a constructor term for one output,
//! the results tuple for several. A presented type's word —
//! `Loop(Unloop(Base))` — is read as a term and normalized under the term
//! store instead. It is the engine's reading of a call, the one the corpus's
//! `normalizes` attribute states and the differential test holds the machine's
//! run of the same call to. Only a block the check admitted is read; a call
//! into any other is [`NormalFormFault::Incoherent`].
//!
//! # Boundaries
//!
//! The verdict here is the lowering's. An operation a `data` block routes
//! carries its oriented rules to the kernel on the definition it lowers to
//! ([`crate::operation::OperationPlan::rules`]), and the kernel decides them
//! itself (`gandr_kernel_term::OperationRules::converge`): the path order with
//! the admission order as its precedence, every critical pair by unification
//! of the linear patterns, and each join by normalizing both reducts. That a
//! lowered function computes what its rules state, and a `theory` block's
//! sequent reading, are decided here only.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::Joinability;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::PairJoining;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::TraceletReplay;
use gandr_theory_coherent_resolutions::normalize;
use gandr_theory_coherent_resolutions::replay_path;
use gandr_theory_computads::AdmittedFaceIndex;
use gandr_theory_computads::ElaborateError;
use gandr_theory_computads::PresentedRules;
use gandr_theory_computads::Term;
use gandr_theory_computads::TermAlphabet;
use gandr_theory_computads::command_reading;
use gandr_theory_computads::elaborate_call;
use gandr_theory_computads::presented_reading;
use gandr_theory_computads::read_command;
use gandr_theory_computads::rule_keeps_growing;
use gandr_theory_computads::term_reading;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::Precedence;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::RuleIndex;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::Termination;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::derive_cell_var_meta;
use gandr_theory_levitation::embeds;
use gandr_theory_levitation::orient_rules;
use gandr_theory_levitation::orient_rules_with;
use gandr_theory_levitation::path_greater;
use quenchant_shape::shape::Maybe;

use crate::LoweringRefusal;
use crate::desc_cells::CellDiagnosticIndex;
use crate::desc_cells::CircuitCell;
use crate::desc_cells::DeclarationCells;
use crate::desc_cells::located;
use crate::description::written::RuleDirection;
use crate::description::written::RuleOrientation;

/// The most steps one reduct of a critical pair may take before the pair is
/// left undecided.
pub const JOIN_STEPS: usize = 4_096;

/// The most steps a call's normalization may take before it reports no normal
/// form.
pub const NORMAL_FORM_STEPS: usize = 1 << 16;

/// The most rules completion derives for one reading of a block before a pair
/// that still parts leaves the block undecided.
pub const DERIVED_RULES: usize = 64;

/// A block's rules oriented so each left side is above its right, with the
/// direction the order chose for each written rule.
pub(crate) struct OrientedBlock<G>
{
    /// The description the kernel-facing table is read from.
    pub description: TheoryDesc<G>,
    /// The direction chosen for each written rule, in rule order.
    pub directions: Vec<RuleDirection>,
}

/// Orient `description`'s rules by the path order, honouring each written
/// arrow.
///
/// # Specification
/// - requires: `orientations` is parallel to `description.rules`; a missing
///   entry is read as pinned left to right.
/// - ensures: [`Ok`] when every rule orients: an unpinned rule left to right
///   when the order admits that, otherwise right to left, and a pinned rule
///   only in its pinned direction. The returned description's corresponding
///   rule has its left side above its right. [`Err`] names the first rule, in
///   rule order, that does not orient.
/// - panics: none.
///
/// # Errors
/// The index of the first rule the order does not orient.
///
/// # Adequacy
/// - hypothesis: L3 — a cancellation written right to left flips, the same
///   cancellation pinned left to right is refused, a growing pinned rule is
///   refused at itself, each rule pinned the way the order runs it orients and
///   pinned against it is refused, and a commuting rule orients neither way.
/// - witness: `coincide::tests::an_equation_written_backwards_orients_forwards`
/// - witness: `coincide::tests::a_rule_that_rebuilds_its_own_call_refuses_the_block`
/// - witness: `coincide::tests::a_pinned_rule_orients_only_the_way_it_is_pinned`
#[spec(ensures: |ret| match ret.as_ref() {
    Ok(oriented) => oriented.directions.len() == description.rules.len()
        && oriented.description.rules.len() == description.rules.len()
        && orient_rules(&oriented.description) == Termination::Oriented,
    Err(index) => usize::from(*index) < description.rules.len(),
})]
pub(crate) fn orient_block<G>(
    description: &TheoryDesc<G>,
    orientations: &[RuleOrientation],
) -> Result<OrientedBlock<G>, RuleIndex>
where
    G: Clone,
{
    let precedence = Precedence::of(description);
    let mut rules = Vec::with_capacity(description.rules.len());
    let mut directions = Vec::with_capacity(description.rules.len());
    for (index, face) in description.rules.iter().enumerate() {
        let orientation = orientations
            .get(index)
            .copied()
            .unwrap_or(RuleOrientation::Pinned(RuleDirection::LeftToRight));
        let forward = bool::from(path_greater(&precedence, &face.lhs, &face.rhs));
        let backward = bool::from(path_greater(&precedence, &face.rhs, &face.lhs));
        let direction = match orientation {
            RuleOrientation::Pinned(RuleDirection::LeftToRight) if forward => {
                RuleDirection::LeftToRight
            },
            RuleOrientation::Pinned(RuleDirection::RightToLeft) if backward => {
                RuleDirection::RightToLeft
            },
            RuleOrientation::Unpinned if forward => RuleDirection::LeftToRight,
            RuleOrientation::Unpinned if backward => RuleDirection::RightToLeft,
            RuleOrientation::Pinned(_) | RuleOrientation::Unpinned => {
                return Err(RuleIndex::from(index));
            },
        };
        rules.push(facing(face, direction));
        directions.push(direction);
    }
    let mut oriented = description.clone();
    oriented.rules = rules.into();
    Ok(OrientedBlock {
        description: oriented,
        directions,
    })
}

/// `face` with its sides ordered as `direction` says.
///
/// # Specification
/// trivial.
fn facing(
    face: &RuleFace,
    direction: RuleDirection,
) -> RuleFace
{
    match direction {
        RuleDirection::LeftToRight => face.clone(),
        RuleDirection::RightToLeft => {
            let variables = derive_cell_var_meta(&face.rhs);
            RuleFace::new(
                face.rhs.clone(),
                face.lhs.clone(),
                variables,
                face.provenance,
            )
        },
    }
}

/// How a description's rules stand as one rewriting system.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Coincidence
{
    /// The rules were not examined as one system: the cell gate declined an
    /// operation or a member, and that decline is the declaration's refusal.
    Unexamined,
    /// The rules terminate and no two of them overlap.
    Orthogonal,
    /// The rules terminate and every critical pair joins, with the rules
    /// completion derived among them: one certificate per pair and one per
    /// derived rule, in the reading each was decided in.
    Joined(Certificates),
    /// The rules' two readings part, or the check could not tell: the report's
    /// diagnostic at this index says why.
    Refused(CellDiagnosticIndex),
}

/// The join certificates of a block's critical pairs and the rules completion
/// derived, by reading.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Certificates
{
    /// One per critical pair of the sequent reading, each replaying over
    /// [`DeclarationCells::rewriting`].
    pub commands: Vec<Tracelet>,
    /// One per critical pair of the presented reading, interior overlaps
    /// included, each replaying over its term store.
    pub terms: Vec<Tracelet<TermAlphabet>>,
    /// The rules completion derived for the sequent reading, in derivation
    /// order, each a cell [`DeclarationCells::rewriting`] ends with.
    pub derived_commands: Vec<DerivedRule>,
    /// The rules completion derived for the presented reading, in derivation
    /// order, each a cell its term store ends with.
    pub derived_terms: Vec<DerivedRule<TermAlphabet>>,
}

/// A rule completion derived to join a critical pair whose two normal forms
/// differ, with the certificate that it follows from the cells before it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DerivedRule<A: CellAlphabet = SequentAlphabet>
{
    /// The derived rule's cell.
    pub cell: CellId,
    /// The derived rule as a rewrite of terms: its left side, headed by an
    /// operation, then its right.
    pub rule: (FreeTerm, FreeTerm),
    /// The pair's two paths from its peak, one reaching the rule's left side
    /// and then firing [`DerivedRule::cell`] at the root, the other reaching
    /// its right side: the join is the rule's right side.
    pub certificate: Tracelet<A>,
    /// Whether the rule rides the precedence or ranks it: a ranking rule
    /// raises its head above what it calls.
    pub joined: Joined,
}

impl<A: CellAlphabet> DerivedRule<A>
{
    /// Replay the derivation over `store`: the rule follows from the cells
    /// before it.
    ///
    /// # Specification
    /// - ensures: positive exactly when the certificate replays over `store`,
    ///   exactly one of its paths ends with [`DerivedRule::cell`] fired at the
    ///   root, and every other step of both paths fires a cell `store` issued
    ///   before it — so the rule's two sides are reducts of one peak under the
    ///   cells before it, and the rule rewrites one to the other.
    /// - panics: none.
    /// - executable: none — the clause is the replay itself; a predicate would
    ///   replay the certificate a second time.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every rule a group's inverse law derives replays over
    ///   the completed store, and the same certificate retargeted at a later
    ///   cell, or with its final step dropped, does not.
    /// - witness: `coincide::tests::a_groups_inverse_law_completes_to_the_rules_it_derives`
    #[inline]
    #[must_use]
    pub fn replay(
        &self,
        store: &CellStore<A>,
    ) -> TraceletReplay
    {
        let fires = |path: &[CellApp<A>]| {
            path.last()
                .is_some_and(|step| step.cell == self.cell && step.at == A::root_position())
        };
        let (path_a, path_b) = (&self.certificate.path_a, &self.certificate.path_b);
        let (deriving, other) = match (fires(path_a), fires(path_b)) {
            (true, false) => (path_a, path_b),
            (false, true) => (path_b, path_a),
            (true, true) | (false, false) => return TraceletReplay::from(false),
        };
        let before = |path: &[CellApp<A>]| path.iter().all(|step| step.cell < self.cell);
        TraceletReplay::from(
            before(deriving.split_last().map_or(&[][..], |(_, rest)| rest))
                && before(other)
                && bool::from(self.certificate.replay(store)),
        )
    }
}

/// A term a coherence fault names, in the reading whose pair it is.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PairTerm
{
    /// A command of the sequent reading.
    Command(CmdPat),
    /// A term of the presented reading.
    Term(Term),
}

/// Why a block's rules are refused as one rewriting system.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CoherenceFault
{
    /// The path order does not put the rule's right-hand side below its left,
    /// so the rules are not known to terminate.
    Unoriented,
    /// The rule and an earlier one, or the rule itself below its root,
    /// overlap, and one of them instantiates a variable: a second-order rule
    /// takes part in no critical pair.
    OverlapsSecondOrder
    {
        /// The earlier rule's written interval.
        first: ByteSpan,
    },
    /// The rule and an earlier one overlap at `peak` and rewrite it to two
    /// normal forms each headed by a constructor or a results tuple: no rule
    /// joins two values.
    Diverges
    {
        /// The earlier rule's written interval.
        first: ByteSpan,
        /// The term both rules match.
        peak: Box<PairTerm>,
        /// The earlier rule's normal form of it.
        left: Box<PairTerm>,
        /// This rule's normal form of it.
        right: Box<PairTerm>,
    },
    /// The rule and an earlier one overlap at `peak` and rewrite it to two
    /// normal forms the path order does not orient into a rule from an
    /// operation call, beside the block's rules and those derived before.
    Uncompleted
    {
        /// The earlier rule's written interval.
        first: ByteSpan,
        /// The term both rules match.
        peak: Box<PairTerm>,
        /// The earlier rule's normal form of it.
        left: Box<PairTerm>,
        /// This rule's normal form of it.
        right: Box<PairTerm>,
    },
    /// The rule and an earlier one overlap at `peak`, and a reduct reaches no
    /// normal form within [`JOIN_STEPS`] steps.
    Undecided
    {
        /// The earlier rule's written interval.
        first: ByteSpan,
        /// The term both rules match.
        peak: Box<PairTerm>,
    },
    /// The rule and an earlier one overlap at `peak` and part once completion
    /// has derived [`DERIVED_RULES`] rules.
    Unfinished
    {
        /// The earlier rule's written interval.
        first: ByteSpan,
        /// The term both rules match.
        peak: Box<PairTerm>,
    },
    /// The rule and an earlier one part, and the rule completion derives from
    /// them wraps, at one point, a derived rule whose cell is one of the
    /// pair's, where no rule rewrites any further wrapping: completion derives
    /// a longer rule every round and never ends.
    NeverCompletes
    {
        /// The earlier rule's written interval.
        first: ByteSpan,
        /// The derived rule the new one wraps, its left side then its right.
        earlier: Box<(FreeTerm, FreeTerm)>,
        /// The round that derived it.
        earlier_round: DerivedRound,
        /// The new rule, its left side then its right.
        later: Box<(FreeTerm, FreeTerm)>,
        /// The round that derived it.
        later_round: DerivedRound,
    },
}

/// A round of one reading's completion: the place of the rule it derives
/// among the reading's derived rules, counted from one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DerivedRound(usize);

impl From<usize> for DerivedRound
{
    /// The round numbered `round`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(round: usize) -> Self
    {
        Self(round)
    }
}

impl From<DerivedRound> for usize
{
    /// The round's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(round: DerivedRound) -> Self
    {
        round.0
    }
}

impl fmt::Display for DerivedRound
{
    /// Writes the round's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

impl CoherenceFault
{
    /// The refusal a held declaration carries for this fault at `span`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lowering_refusal(
        &self,
        span: ByteSpan,
    ) -> LoweringRefusal<'static>
    {
        match *self {
            Self::Unoriented => LoweringRefusal::RulesUnoriented { span },
            Self::OverlapsSecondOrder { first } => {
                LoweringRefusal::RulesOverlapSecondOrder { span, first }
            },
            Self::Diverges { first, .. } => LoweringRefusal::RulesDiverge { span, first },
            Self::Uncompleted { first, .. } => LoweringRefusal::RulesUncompleted { span, first },
            Self::Undecided { first, .. } | Self::Unfinished { first, .. } => {
                LoweringRefusal::RulesUndecided { span, first }
            },
            Self::NeverCompletes { first, .. } => {
                LoweringRefusal::RulesNeverComplete { span, first }
            },
        }
    }
}

impl fmt::Display for CoherenceFault
{
    /// Writes the fault with the terms it names in the inspection notation: the
    /// peak and both normal forms of a divergence or of a pair completion
    /// leaves apart, the peak of an undecided or unfinished pair, and both
    /// derived rules of a completion that never ends.
    ///
    /// # Specification
    /// - ensures: one sentence per fault; a command the term reading cannot
    ///   write is spelled as the terminal it ends in.
    /// - fails: the formatting sink's error when it refuses the text.
    /// - panics: none.
    /// - executable: none — a formatter exposes no readback of the written
    ///   text.
    ///
    /// # Errors
    /// Propagates a refusal from the formatting sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a divergent pair of either reading is written with
    ///   its peak and both normal forms in order, and so is a pair completion
    ///   leaves apart; swapping them or dropping the peak changes the witnessed
    ///   text.
    /// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
    /// - witness: `coincide::tests::a_third_cancellation_parts_the_circles_readings`
    /// - witness: `coincide::tests::a_permuted_call_no_order_orients_is_uncompleted`
    /// - witness: `coincide::tests::a_scope_extrusion_family_never_completes`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unoriented => f.write_str(
                "the right-hand side is not below the left in the path order, so the rules may not \
                 end",
            ),
            Self::OverlapsSecondOrder { .. } => f.write_str(
                "the two rules' left sides overlap, and one of them instantiates a variable, \
                 which no critical pair may hold",
            ),
            Self::Diverges {
                ref peak,
                ref left,
                ref right,
                ..
            } => write!(
                f,
                "both rules rewrite `{}`, one to `{}` and the other to `{}`",
                Spelled(peak),
                Spelled(left),
                Spelled(right)
            ),
            Self::Uncompleted {
                ref peak,
                ref left,
                ref right,
                ..
            } => write!(
                f,
                "both rules rewrite `{}`, one to `{}` and the other to `{}`, and the path order \
                 orients no rule from an operation call between the two",
                Spelled(peak),
                Spelled(left),
                Spelled(right)
            ),
            Self::Undecided { ref peak, .. } => write!(
                f,
                "both rules rewrite `{}`, and its rewrites reach no normal form within \
                 {JOIN_STEPS} steps",
                Spelled(peak)
            ),
            Self::Unfinished { ref peak, .. } => write!(
                f,
                "both rules rewrite `{}` to two normal forms still once completion has derived \
                 {DERIVED_RULES} rules",
                Spelled(peak)
            ),
            Self::NeverCompletes {
                ref earlier,
                earlier_round,
                ref later,
                later_round,
                ..
            } => write!(
                f,
                "the rule completion derives at round {later_round}, `{} ==> {}`, is the rule it \
                 derived at round {earlier_round}, `{} ==> {}`, with one subterm wrapped, and no \
                 rule rewrites a further wrapping, so every round derives a longer rule",
                later.0, later.1, earlier.0, earlier.1
            ),
        }
    }
}

/// A pair's term spelled as the term it denotes.
#[repr(transparent)]
struct Spelled<'term>(&'term PairTerm);

impl fmt::Display for Spelled<'_>
{
    /// Writes the term a command or a term reads as, or the reason it reads as
    /// none: a terminal as `★`, split results as `…`, and a replay's constant,
    /// which no pair holds, as `★` too.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let read = match *self.0 {
            PairTerm::Command(ref command) => match read_command(command) {
                Maybe::Present(written) => Ok(written),
                Maybe::Absent(command_reading::Absent::Terminal) => Err("★"),
                Maybe::Absent(command_reading::Absent::SplitResults) => Err("…"),
            },
            PairTerm::Term(ref term) => match term.read() {
                Maybe::Present(written) => Ok(written),
                Maybe::Absent(term_reading::Absent::Skolem) => Err("★"),
            },
        };
        match read {
            Ok(written) => f.write_str(&spell(&written)),
            Err(sign) => f.write_str(sign),
        }
    }
}

/// Decide whether a description's rules are one rewriting system: termination
/// by the path order, then joinability of every critical pair over its
/// rewriting store and, for a presented type, over its term store, each
/// reading completed by the rules its divergent pairs derive.
///
/// # Specification
/// - requires: `store`, `faces`, `presented` and `circuits` are the cell gate's
///   elaboration of `description`, which declined none of its operations, faces
///   or circuit rules; `at` is the declaration's interval.
/// - ensures: the first unoriented rule as [`CoherenceFault::Unoriented`] at
///   its span; else the first overlap of a second-order rule, as
///   [`second_order_overlap`] finds it, as
///   [`CoherenceFault::OverlapsSecondOrder`] at the later rule's span naming
///   the earlier one's; else each reading completed in turn, the sequent one
///   first, as [`Reading::complete`] completes it, its first fault at the later
///   rule's span naming the earlier one's; else [`Coincidence::Orthogonal`]
///   when no two cells overlap in either reading and [`Coincidence::Joined`]
///   with every pair's certificate and every derived rule otherwise. Each
///   derived rule's cell is appended to `store` or to the presented reading's
///   store, in derivation order, so the store a reading rewrites with ends with
///   them.
/// - panics: none.
///
/// # Errors
/// The fault and the span it stands at, as the ensures clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the addition family is orthogonal, the family adding a
///   right unit is joined with one certificate per overlap, a right unit
///   returning a successor diverges at the later rule, and a rule rebuilding
///   its own call is unoriented before any pair is read; the circle's two
///   cancellations join over terms at the two words they overlap in, and a
///   third cancellation diverges at itself naming the one before; a group's
///   inverse law completes to the rules that join it, each derived rule's
///   certificate replaying over the cells before it, and two operations a pair
///   leaves apart at one rank are uncompleted; a scope-extrusion family whose
///   second derived rule wraps its first never completes, and beside a rule
///   flattening its third wrapping completes; reporting the earlier rule's
///   span, deciding joinability first, reading the circle in the sequent store
///   alone, or deriving a rule between two constructor terms changes one of
///   them.
/// - witness: `coincide::tests::an_overlap_that_joins_is_certified_and_runs_either_way`
/// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
/// - witness: `coincide::tests::a_rule_that_rebuilds_its_own_call_refuses_the_block`
/// - witness: `coincide::tests::the_circles_cancellations_join_below_the_root`
/// - witness: `coincide::tests::a_third_cancellation_parts_the_circles_readings`
/// - witness: `coincide::tests::a_groups_inverse_law_completes_to_the_rules_it_derives`
/// - witness: `coincide::tests::a_permuted_call_no_order_orients_is_uncompleted`
/// - witness: `coincide::tests::a_data_blocks_derived_rule_is_a_pattern_rule`
/// - witness: `coincide::tests::a_second_order_rule_overlapping_another_refuses_the_block`
/// - witness: `coincide::tests::a_scope_extrusion_family_never_completes`
#[spec(captures: written = store.len(), ensures: |ret| match ret {
    Ok(Coincidence::Joined(ref certificates)) => (!certificates.commands.is_empty() || !certificates.terms.is_empty())
        && usize::from(store.len()) == usize::from(written).saturating_add(certificates.derived_commands.len()),
    Ok(Coincidence::Orthogonal) => store.len() == written,
    Ok(Coincidence::Unexamined | Coincidence::Refused(_)) => false,
    Err((span, CoherenceFault::Unoriented)) => matches!(orient_rules(description), Termination::Unoriented(_))
        && span.start() >= at.start() && span.end() <= at.end(),
    Err((_, CoherenceFault::OverlapsSecondOrder { .. })) => orient_rules(description) == Termination::Oriented
        && second_order_overlap(&description.rules).is_some(),
    Err((_, CoherenceFault::Diverges { .. } | CoherenceFault::Uncompleted { .. } | CoherenceFault::NeverCompletes { .. } | CoherenceFault::Undecided { .. } | CoherenceFault::Unfinished { .. })) => orient_rules(description) == Termination::Oriented,
})]
#[cfg_attr(feature = "hotpath", hotpath::measure)]
pub(crate) fn decide<G>(
    description: &TheoryDesc<G>,
    at: ByteSpan,
    store: &mut CellStore,
    faces: &[(AdmittedFaceIndex, CellId)],
    presented: &mut Maybe<PresentedRules, presented_reading::Absent>,
    circuits: &[CircuitCell],
) -> Result<Coincidence, (ByteSpan, CoherenceFault)>
{
    let rule_span = |index: usize| {
        description
            .rules
            .get(index)
            .map_or(at, |face| located(face.provenance, at))
    };
    if let Termination::Unoriented(index) = orient_rules(description) {
        return Err((rule_span(usize::from(index)), CoherenceFault::Unoriented));
    }
    if let Some((later, earlier)) = second_order_overlap(&description.rules) {
        return Err((
            rule_span(usize::from(later)),
            CoherenceFault::OverlapsSecondOrder {
                first: rule_span(usize::from(earlier)),
            },
        ));
    }
    let budget = NormalizationBudget::from(JOIN_STEPS);
    let rewriting = rewriting_store(store, faces, circuits);
    let mut joining = PairJoining::new();
    let (commands, derived_commands) = match joining.resume(&rewriting, budget) {
        Joinability::Joined(certificates) => (certificates, Vec::new()),
        first @ (Joinability::Diverges { .. } | Joinability::Undecided(_)) => {
            let mut completing = rewriting.into_owned();
            let reading = Reading {
                description,
                faces,
                rule_span: &rule_span,
                at,
            };
            let completed = reading.complete(
                &mut completing,
                joining,
                first,
                PairTerm::Command,
                |command| match read_command(command) {
                    Maybe::Present(term) => Some(term),
                    Maybe::Absent(_) => None,
                },
            )?;
            for derived in &completed.1 {
                if let Maybe::Present(cell) = completing.get(derived.cell) {
                    let _appended = store.insert(cell.clone());
                }
            }
            completed
        },
    };
    let (terms, derived_terms) = match *presented {
        Maybe::Present(ref mut presented) => {
            let mut joining = PairJoining::new();
            let first = joining.resume(&presented.store, budget);
            let reading = Reading {
                description,
                faces: &presented.faces,
                rule_span: &rule_span,
                at,
            };
            reading.complete(
                &mut presented.store,
                joining,
                first,
                PairTerm::Term,
                |term| match term.read() {
                    Maybe::Present(read) => Some(read),
                    Maybe::Absent(_) => None,
                },
            )?
        },
        Maybe::Absent(presented_reading::Absent::NoTermFace) => (Vec::new(), Vec::new()),
    };
    if commands.is_empty() && terms.is_empty() {
        return Ok(Coincidence::Orthogonal);
    }
    Ok(Coincidence::Joined(Certificates {
        commands,
        terms,
        derived_commands,
        derived_terms,
    }))
}

/// The first overlap of a second-order rule of `rules`: the later rule's index
/// and the earlier one's.
///
/// # Specification
/// - ensures: [`Some`] with the larger and the smaller index of the first pair
///   — in order of the outer rule, then of a position of its left side, then of
///   the inner rule, as the kernel reads them — at least one of whose
///   right-hand sides instantiates a variable, where the inner rule's left
///   side, renamed apart, unifies with the outer one's subterm at a position
///   holding no lone variable, other than the root of one rule overlapping
///   itself; [`None`] when no such pair exists.
/// - panics: none.
/// - intension: each left side read as a term once; a pair neither of whose
///   rules instantiates is never unified.
///
/// # Adequacy
/// - hypothesis: L3 — `let`'s rule beside a rule rewriting `let` at a constant
///   overlaps at the root, the same rule beside one rewriting under `let`'s
///   bound term overlaps below it, and `let` beside a first-order rule over
///   other operations does not; reading only first-order pairs, or counting a
///   root self-overlap, changes a verdict.
/// - witness: `coincide::tests::a_second_order_rule_overlapping_another_refuses_the_block`
#[spec(ensures: |ret| ret.is_none_or(|(later, earlier)| earlier <= later && usize::from(later) < rules.len()))]
fn second_order_overlap(rules: &[RuleFace]) -> Option<(RuleIndex, RuleIndex)>
{
    let second_order: Vec<bool> = rules
        .iter()
        .map(|face| bool::from(face.rhs.instantiates()))
        .collect();
    if !second_order.contains(&true) {
        return None;
    }
    let lefts: Vec<Term> = rules.iter().map(|face| Term::from(&face.lhs)).collect();
    let root = TermAlphabet::root_position();
    for (outer, left) in lefts.iter().enumerate() {
        let outer_second = second_order.get(outer).copied().unwrap_or(false);
        for seam in TermAlphabet::command_positions(left) {
            let Maybe::Present(sub) = TermAlphabet::subterm_cmd_at(left, &seam)
            else {
                continue;
            };
            if TermAlphabet::metavariables(&sub).len() == 1
                && TermAlphabet::command_positions(&sub).len() == 1
            {
                continue;
            }
            for ((inner, other), &inner_second) in lefts.iter().enumerate().zip(&second_order) {
                if !(outer_second || inner_second) || (seam == root && inner == outer) {
                    continue;
                }
                let (renamed, _) = TermAlphabet::rename_apart((left, left), (other, other));
                let mut unifier = <TermAlphabet as CellAlphabet>::Subst::default();
                if bool::from(TermAlphabet::unify_cmd(&sub, &renamed, &mut unifier)) {
                    return Some((
                        RuleIndex::from(outer.max(inner)),
                        RuleIndex::from(outer.min(inner)),
                    ));
                }
            }
        }
    }
    None
}

/// A completed reading: one certificate per critical pair, then the rules it
/// derived with theirs.
type Completed<A> = (Vec<Tracelet<A>>, Vec<DerivedRule<A>>);

/// Rules a completion derived, each as its left and right sides.
type Rewrites = Vec<(FreeTerm, FreeTerm)>;

/// Which of a critical pair's two cells is its later face.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Later
{
    /// The overlap's left cell: the pair names its later face first.
    Left,
    /// The overlap's right cell.
    Right,
}

/// Which list of derived rules a rule joined: those that ride the precedence
/// the block's rules induce, or those that rank it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Joined
{
    /// The path order orients the rule over the precedence as it stands.
    Riding,
    /// The rule's calls raise its head in the precedence.
    Ranking,
}

/// One reading of a block's rules, as its completion locates a pair.
struct Reading<'block, G, S>
{
    /// The block's description, its rules oriented.
    description: &'block TheoryDesc<G>,
    /// Each written face the reading admitted, with its cell.
    faces: &'block [(AdmittedFaceIndex, CellId)],
    /// A written face's span, by its index among the description's rules.
    rule_span: &'block S,
    /// The declaration's interval: the span of a cell no face wrote.
    at: ByteSpan,
}

impl<G, S> Reading<'_, G, S>
where
    S: Fn(usize) -> ByteSpan,
{
    /// The span of a pair's later face, the span of its earlier one, and
    /// which of the pair's two cells is the later face.
    ///
    /// # Specification
    /// - ensures: a cell no face wrote stands at the declaration's interval;
    ///   two written faces are ordered by their place among the rules, and any
    ///   other pair is read with its right cell the later one.
    /// - panics: none.
    /// - executable: none — the order reads the receiver's face table, which a
    ///   clause may not walk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`decide`]: a sequent pair is located at its later
    ///   rule, written after or before the earlier one in the overlap, and an
    ///   interior pair of the circle whose later rule is the overlap's left
    ///   cell is located at that rule all the same.
    /// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
    /// - witness: `coincide::tests::two_rules_written_the_other_way_round_are_refused_at_the_later_one_all_the_same`
    /// - witness: `coincide::tests::a_third_cancellation_parts_the_circles_readings`
    fn located(
        &self,
        left: CellId,
        right: CellId,
    ) -> (ByteSpan, ByteSpan, Later)
    {
        let span = |face: Option<AdmittedFaceIndex>| {
            face.map_or(self.at, |index| (self.rule_span)(usize::from(index)))
        };
        match (self.face_of(left), self.face_of(right)) {
            (Some(written_left), Some(written_right)) if written_left > written_right => (
                span(Some(written_left)),
                span(Some(written_right)),
                Later::Left,
            ),
            (written_left, written_right) => {
                (span(written_right), span(written_left), Later::Right)
            },
        }
    }

    /// The written face whose cell `cell` is, by its index among the rules.
    ///
    /// # Specification
    /// trivial.
    fn face_of(
        &self,
        cell: CellId,
    ) -> Option<AdmittedFaceIndex>
    {
        self.faces
            .iter()
            .find(|&&(_, admitted)| admitted == cell)
            .map(|&(index, _)| index)
    }

    /// Complete one reading of a block's rules from `first`, its store's
    /// joinability as `joining` decided it: every critical pair's certificate
    /// and every rule a divergent pair derived, or the fault of the first pair
    /// that neither joins nor completes.
    ///
    /// # Specification
    /// - requires: `first` is what `joining` last answered over `store`; `read`
    ///   writes a term of the reading as the term it denotes.
    /// - ensures: a divergent pair whose two normal forms are both headed by a
    ///   constructor or a results tuple is [`CoherenceFault::Diverges`]; one
    ///   either of whose normal forms writes no term, or which no direction
    ///   with an operation at the left side's head orients — riding the
    ///   precedence the block's rules and the ranking rules derived so far
    ///   induce, or failing that ranking it — is
    ///   [`CoherenceFault::Uncompleted`]; an oriented rule embedding a rule
    ///   derived as one of the pair's cells, which [`rule_keeps_growing`] finds
    ///   it wraps at one point where no left side of the written rules, those
    ///   derived and it rewrites a further wrapping, is
    ///   [`CoherenceFault::NeverCompletes`] naming both; otherwise the oriented
    ///   rule is appended to `store` with its certificate — the pair's two
    ///   paths from the peak, the one reaching the rule's left side then firing
    ///   the rule at the root — and `joining` resumed at the pair that parted,
    ///   so a round decides that pair and the ones after it and no pair already
    ///   joined again. A pair a reduct of which reaches no normal form within
    ///   [`JOIN_STEPS`] steps is [`CoherenceFault::Undecided`], and a divergent
    ///   pair met once [`DERIVED_RULES`] rules are derived is
    ///   [`CoherenceFault::Unfinished`]. Every fault stands at the pair's later
    ///   face naming the earlier one, and its terms are in that order.
    /// - panics: none.
    ///
    /// # Errors
    /// The fault and the span it stands at, as the ensures clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`decide`]: a constructor-headed divergence is
    ///   refused, a group's inverse law completes, and a divergence the order
    ///   leaves apart is uncompleted; a scope-extrusion family is refused at
    ///   its second derived rule, and completes beside a rule flattening its
    ///   third wrapping.
    /// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
    /// - witness: `coincide::tests::a_groups_inverse_law_completes_to_the_rules_it_derives`
    /// - witness: `coincide::tests::a_permuted_call_no_order_orients_is_uncompleted`
    /// - witness: `coincide::tests::a_scope_extrusion_family_never_completes`
    #[spec(captures: before = store.len(), ensures: |ret| ret.as_ref().is_err()
        || ret.as_ref().is_ok_and(|completed| usize::from(store.len()) == usize::from(before).saturating_add(completed.1.len())
            && completed.1.iter().all(|derived| bool::from(derived.replay(store)))))]
    fn complete<A, W, R>(
        &self,
        store: &mut CellStore<A>,
        mut joining: PairJoining<A>,
        first: Joinability<A>,
        wrap: W,
        read: R,
    ) -> Result<Completed<A>, (ByteSpan, CoherenceFault)>
    where
        A: CellAlphabet,
        W: Fn(A::Cmd) -> PairTerm,
        R: Fn(&A::Cmd) -> Option<FreeTerm>,
    {
        let budget = NormalizationBudget::from(JOIN_STEPS);
        let mut joinability = first;
        let mut derived: Vec<DerivedRule<A>> = Vec::new();
        let (mut ranking, mut riding): (Rewrites, Rewrites) = (Vec::new(), Vec::new());
        // The left side of every rule the store holds, and each derived rule's
        // index by its cell.
        let mut lefts: Vec<FreeTerm> = self
            .description
            .rules
            .iter()
            .map(|face| face.lhs.clone())
            .collect();
        let mut parents: BTreeMap<CellId, usize> = BTreeMap::new();
        loop {
            let (overlap, left, left_steps, right, right_steps) = match joinability {
                Joinability::Joined(certificates) => return Ok((certificates, derived)),
                Joinability::Undecided(overlap) => {
                    let (span, first, _) = self.located(overlap.left, overlap.right);
                    return Err((span, CoherenceFault::Undecided {
                        first,
                        peak: Box::new(wrap(overlap.peak)),
                    }));
                },
                Joinability::Diverges {
                    overlap,
                    left,
                    left_steps,
                    right,
                    right_steps,
                } => (overlap, left, left_steps, right, right_steps),
            };
            let (span, first, later_cell) = self.located(overlap.left, overlap.right);
            let terms = (read(&left), read(&right));
            // The pair's peak and two normal forms as the fault names them, the
            // earlier face's normal form first.
            let parted = |overlap: Overlap<A>, left: A::Cmd, right: A::Cmd| {
                let (earlier, later) = match later_cell {
                    Later::Left => (right, left),
                    Later::Right => (left, right),
                };
                (
                    Box::new(wrap(overlap.peak)),
                    Box::new(wrap(earlier)),
                    Box::new(wrap(later)),
                )
            };
            let uncompleted = |overlap, left, right| {
                let (peak, left, right) = parted(overlap, left, right);
                (span, CoherenceFault::Uncompleted {
                    first,
                    peak,
                    left,
                    right,
                })
            };
            let (Some(left_term), Some(right_term)) = terms
            else {
                return Err(uncompleted(overlap, left, right));
            };
            // Two values: both normal forms headed by a constructor or a
            // results tuple, which no rule's left side is headed by.
            if matches!(
                (left_term.view(), right_term.view()),
                (
                    TermView::Ctor { .. } | TermView::Results { .. },
                    TermView::Ctor { .. } | TermView::Results { .. }
                )
            ) {
                let (peak, left, right) = parted(overlap, left, right);
                return Err((span, CoherenceFault::Diverges {
                    first,
                    peak,
                    left,
                    right,
                }));
            }
            if derived.len() >= DERIVED_RULES {
                return Err((span, CoherenceFault::Unfinished {
                    first,
                    peak: Box::new(wrap(overlap.peak)),
                }));
            }
            let Some((direction, joined)) = orient_derived(
                self.description,
                &mut ranking,
                &mut riding,
                left_term,
                right_term,
            )
            else {
                return Err(uncompleted(overlap, left, right));
            };
            let Some(rule) = match joined {
                Joined::Riding => riding.last(),
                Joined::Ranking => ranking.last(),
            }
            .cloned()
            else {
                return Err(uncompleted(overlap, left, right));
            };
            lefts.push(rule.0.clone());
            // A rule wrapping a rule its pair was derived from at one point,
            // where no rule rewrites any further wrapping: completion derives
            // a longer rule every round.
            let repeated = [overlap.left, overlap.right]
                .into_iter()
                .filter_map(|cell| {
                    let &index = parents.get(&cell)?;
                    derived.get(index).map(|earlier| (index, earlier))
                })
                .find(|&(_, earlier)| {
                    bool::from(embeds(&earlier.rule.0, &rule.0))
                        && bool::from(rule_keeps_growing(&earlier.rule, &rule, &lefts))
                });
            if let Some((index, earlier)) = repeated {
                return Err((span, CoherenceFault::NeverCompletes {
                    first,
                    earlier: Box::new(earlier.rule.clone()),
                    earlier_round: DerivedRound::from(index.saturating_add(1)),
                    later: Box::new(rule),
                    later_round: DerivedRound::from(derived.len().saturating_add(1)),
                }));
            }
            let mut path_a = Vec::from([CellApp {
                cell: overlap.left,
                at: A::root_position(),
            }]);
            path_a.extend(left_steps);
            let mut path_b = Vec::from([CellApp {
                cell: overlap.right,
                at: overlap.seam.clone(),
            }]);
            path_b.extend(right_steps);
            let (lhs, rhs, from_lhs) = match direction {
                RuleDirection::LeftToRight => (left, right, &mut path_a),
                RuleDirection::RightToLeft => (right, left, &mut path_b),
            };
            let cell = store.insert(Cell::new(
                lhs,
                rhs.clone(),
                A::derived_orientation(),
                A::derived_provenance(),
            ));
            from_lhs.push(CellApp {
                cell,
                at: A::root_position(),
            });
            let _previous = parents.insert(cell, derived.len());
            derived.push(DerivedRule {
                cell,
                rule,
                joined,
                certificate: Tracelet {
                    overlap,
                    path_a,
                    path_b,
                    joins_at: rhs,
                },
            });
            joinability = joining.resume(store, budget);
        }
    }
}

/// The direction a rule joining `left` and `right` takes, and the list it
/// joined: the rule rides the precedence the block's rules and `ranking`
/// induce when the path order orients it so, left to right before right to
/// left, and otherwise ranks, its head raised above what it calls, in the same
/// order. Its left side is headed by an operation, and in a `data` block,
/// whose operations the kernel reads as rules over constructor patterns, over
/// linear constructor patterns.
///
/// # Specification
/// - ensures: [`Some`] exactly when one direction's left side is headed by an
///   operation, over linear constructor patterns in a `data` block, and
///   [`orient_rules_with`] over `description`, `ranking` and `riding` with that
///   rule pushed onto `riding`, or failing every direction so, onto `ranking`,
///   is [`Termination::Oriented`]; the rule then ends the list it was pushed
///   onto, which is returned with its direction, and both lists are otherwise
///   unchanged, as both are on [`None`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Reading::complete`]: a group's inverse law orients
///   each rule it derives, a derived rule calling an operation that calls its
///   head rides the precedence by the subterm property, a permuted call orients
///   neither way, and a `data` block's derived rule is one the kernel reads.
/// - witness: `coincide::tests::a_groups_inverse_law_completes_to_the_rules_it_derives`
/// - witness: `coincide::tests::a_permuted_call_no_order_orients_is_uncompleted`
/// - witness: `coincide::tests::a_data_blocks_derived_rule_is_a_pattern_rule`
#[spec(captures: before = ranking.len().saturating_add(riding.len()), ensures: |ret|
    ranking.len().saturating_add(riding.len()) == before.saturating_add(usize::from(ret.is_some())))]
fn orient_derived<G>(
    description: &TheoryDesc<G>,
    ranking: &mut Rewrites,
    riding: &mut Rewrites,
    left: FreeTerm,
    right: FreeTerm,
) -> Option<(RuleDirection, Joined)>
{
    // The blocks whose operations the kernel reads as rules: an unparametrised
    // `data` family with constructors.
    let routed = description.polarity == DeclPolarity::Data
        && description.params.is_empty()
        && !description.ctors.is_empty();
    let heads_a_rule = |lhs: &FreeTerm| {
        let TermView::Op { args, .. } = lhs.view()
        else {
            return false;
        };
        let mut bound = BTreeSet::new();
        let mut pending: Vec<TermNode<'_>> = if routed { args.collect() } else { Vec::new() };
        while let Some(node) = pending.pop() {
            match node.view() {
                TermView::Var(name) => {
                    if !bound.insert(name) {
                        return false;
                    }
                },
                TermView::Ctor { args, .. } => pending.extend(args),
                TermView::Op { .. } | TermView::Results { .. } | TermView::Inst { .. } => {
                    return false;
                },
            }
        }
        true
    };
    let mut tried = (left, right);
    for joined in [Joined::Riding, Joined::Ranking] {
        for direction in [RuleDirection::LeftToRight, RuleDirection::RightToLeft] {
            if heads_a_rule(&tried.0) {
                let list = match joined {
                    Joined::Riding => &mut *riding,
                    Joined::Ranking => &mut *ranking,
                };
                list.push(tried);
                if orient_rules_with(description, ranking, riding) == Termination::Oriented {
                    return Some((direction, joined));
                }
                tried = match joined {
                    Joined::Riding => riding.pop()?,
                    Joined::Ranking => ranking.pop()?,
                };
            }
            tried = (tried.1, tried.0);
        }
    }
    None
}

/// The cells of `store` a rewrite reads: every cell but the admitted circuit
/// cells no face shares, in store order.
///
/// # Specification
/// - ensures: `store` itself when no circuit cell is left out; otherwise a
///   store holding the rest in order, so a cell inserted before the first left
///   out keeps its identifier.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a `theory` block's congruence is left out while its faces
///   keep their identifiers, alone and beside a rule's face, and a family with
///   no circuit is read in place.
/// - witness: `coincide::tests::a_congruence_is_no_rewrite_of_its_own`
#[spec(ensures: |ret| usize::from(ret.len()) <= usize::from(store.len()))]
pub(crate) fn rewriting_store<'store>(
    store: &'store CellStore,
    faces: &[(AdmittedFaceIndex, CellId)],
    circuits: &[CircuitCell],
) -> Cow<'store, CellStore>
{
    let shared: BTreeSet<CellId> = faces.iter().map(|&(_, face)| face).collect();
    let left_out: BTreeSet<CellId> = circuits
        .iter()
        .filter_map(|circuit| match *circuit {
            CircuitCell::Admitted { cell, .. } => Some(cell),
            CircuitCell::Refused(_) => None,
        })
        .filter(|cell| !shared.contains(cell))
        .collect();
    if left_out.is_empty() {
        return Cow::Borrowed(store);
    }
    let mut kept = CellStore::new();
    for (id, cell) in store.iter() {
        if !left_out.contains(&id) {
            let _kept = kept.insert(cell.clone());
        }
    }
    Cow::Owned(kept)
}

/// The text of one call in the inspection notation, as a `normalizes` row
/// writes it: `add(Succ(Zero), Zero)`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallText<'text>(&'text str);

impl<'text> From<&'text str> for CallText<'text>
{
    /// The call spelled by `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for CallText<'_>
{
    /// The call's text.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call reads back as the text it was written as.
    /// - witness: `coincide::tests::a_call_lends_the_text_it_was_written_as`
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

/// The normal form a call reaches under a block's rules, with the path that
/// certifies it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NormalForm
{
    /// The call, as read.
    pub call: FreeTerm,
    /// The steps from the call to its normal form, replayed before the normal
    /// form is returned.
    pub path: NormalPath,
    /// The normal form, read back as a term: a constructor term for one
    /// output, the results tuple for several, or the call that no rule
    /// covers.
    pub normal: FreeTerm,
}

/// The steps a call took, in the reading the block's rules are read in.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NormalPath
{
    /// Steps of the sequent reading, from the call's command.
    Commands(Vec<CellApp>),
    /// Steps of a presented type's reading, from the call as a term.
    Terms(Vec<CellApp<TermAlphabet>>),
}

/// Why a normal form writes no term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unwriting
{
    /// The command reads as no term.
    Command(command_reading::Absent),
    /// The term holds what no free term spells.
    Term(term_reading::Absent),
}

impl NormalForm
{
    /// The normal form spelled as `gandr run` spells the value: the
    /// inspection notation, a results tuple as `#{…}`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn spelling(&self) -> String
    {
        spell(&self.normal)
    }
}

/// Why a call has no normal form to report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NormalFormFault
{
    /// The declaration is no family or `theory` block the description route
    /// read, so it has no rules to read the call under.
    Undescribed,
    /// The block's rules were not admitted as one rewriting system, so no
    /// reading of them is the block's.
    Incoherent,
    /// The text is not a term of the inspection notation.
    Unread,
    /// The text names a symbol the block declares neither as a constructor
    /// nor as an operation.
    UnknownSymbol,
    /// The term is no call the block's operations elaborate.
    NotACall(ElaborateError),
    /// The normalization took every step it was allowed.
    Exhausted,
    /// The recorded path does not replay to the normal form.
    Uncertified,
    /// The normal form writes no term.
    Unwritable(Unwriting),
}

impl fmt::Display for NormalFormFault
{
    /// Writes why the call has no normal form.
    ///
    /// # Specification
    /// - ensures: one phrase per fault, naming the step budget when it ran out.
    /// - fails: the formatting sink's error when it refuses the text.
    /// - panics: none.
    /// - executable: none — a formatter exposes no readback of the written
    ///   text.
    ///
    /// # Errors
    /// Propagates a refusal from the formatting sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unread call and a call into a refused block read
    ///   apart.
    /// - witness: `coincide::tests::a_call_reads_its_normal_form_or_says_why_not`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Undescribed => f.write_str("no normal form: the declaration has no rules"),
            Self::Incoherent => f.write_str("no normal form: the block's rules are refused"),
            Self::Unread => f.write_str("no normal form: the call does not read as a term"),
            Self::UnknownSymbol => {
                f.write_str("no normal form: the call names a symbol the block does not declare")
            },
            Self::NotACall(_) => {
                f.write_str("no normal form: the term is no call the block's operations read")
            },
            Self::Exhausted => write!(f, "no normal form within {NORMAL_FORM_STEPS} steps"),
            Self::Uncertified => f.write_str("no normal form: the path does not replay"),
            Self::Unwritable(_) => f.write_str("no normal form: it writes no term"),
        }
    }
}

/// The normal form `call` reaches under the rules of the block `cells` holds,
/// `description` being its description.
///
/// # Specification
/// - requires: `cells` is the cell gate's elaboration of `description`.
/// - ensures: the call read in the inspection notation against the block's
///   constructors and operations; for a presented type, read as a term and
///   normalized under its term store, and otherwise elaborated to the command
///   its faces match and normalized under [`DeclarationCells::rewriting`];
///   within [`NORMAL_FORM_STEPS`] steps, its path replayed to the normal form,
///   and the normal form read back as a term.
/// - fails: [`NormalFormFault::Incoherent`] for a block the coincidence check
///   did not admit; otherwise the first step that fails, in that order.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a one-output and a two-output call read back their
///   values, a word of the circle reads back the word its cancellations leave,
///   a call into a refused block is incoherent before it is read, and an
///   unknown symbol and an unreadable text are told apart; reading the normal
///   form before the replay, normalizing under the store with its congruences,
///   or reading the circle's word in the sequent store changes one of them.
/// - witness: `coincide::tests::a_call_reads_its_normal_form_or_says_why_not`
/// - witness: `coincide::tests::an_overlap_that_joins_is_certified_and_runs_either_way`
/// - witness: `coincide::tests::the_circles_cancellations_join_below_the_root`
#[spec(ensures: |ret| {
    let admitted = matches!(cells.coincidence, Coincidence::Orthogonal | Coincidence::Joined(_));
    match ret.as_ref() {
        Ok(normal) => admitted && read_call(description, call).as_ref() == Ok(&normal.call)
            && matches!(normal.path, NormalPath::Terms(_)) == matches!(cells.presented, Maybe::Present(_)),
        Err(&NormalFormFault::Incoherent) => !admitted,
        Err(&NormalFormFault::Undescribed) => false,
        Err(_) => admitted,
    }
})]
#[inline]
pub fn normal_form<G>(
    description: &TheoryDesc<G>,
    cells: &DeclarationCells,
    call: CallText<'_>,
) -> Result<NormalForm, NormalFormFault>
{
    if !matches!(
        cells.coincidence,
        Coincidence::Orthogonal | Coincidence::Joined(_)
    ) {
        return Err(NormalFormFault::Incoherent);
    }
    let call = read_call(description, call)?;
    let (path, normal) = match cells.presented {
        Maybe::Present(ref presented) => {
            let (path, normal) = certified_normal(&presented.store, &Term::from(&call), |term| {
                match term.read() {
                    Maybe::Present(written) => Ok(written),
                    Maybe::Absent(reason) => Err(Unwriting::Term(reason)),
                }
            })?;
            (NormalPath::Terms(path), normal)
        },
        Maybe::Absent(presented_reading::Absent::NoTermFace) => {
            let command = elaborate_call(&call, description.polarity, &cells.operations)
                .map_err(NormalFormFault::NotACall)?;
            let (path, normal) = certified_normal(&cells.rewriting(), &command, |command| {
                match read_command(command) {
                    Maybe::Present(written) => Ok(written),
                    Maybe::Absent(reason) => Err(Unwriting::Command(reason)),
                }
            })?;
            (NormalPath::Commands(path), normal)
        },
    };
    Ok(NormalForm { call, path, normal })
}

/// The normal form `start` reaches under `store`, its path replayed, read back
/// by `read`.
///
/// # Specification
/// - ensures: the path [`normalize`] takes within [`NORMAL_FORM_STEPS`] steps
///   and the normal form `read` writes.
/// - fails: [`NormalFormFault::Exhausted`] when the budget runs out,
///   [`NormalFormFault::Uncertified`] when the path does not replay, then
///   [`NormalFormFault::Unwritable`] with `read`'s reason.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a sequent call and a circle word each reach their normal
///   form along a path that replays; reading before the replay or dropping the
///   budget check changes them.
/// - witness: `coincide::tests::an_overlap_that_joins_is_certified_and_runs_either_way`
/// - witness: `coincide::tests::the_circles_cancellations_join_below_the_root`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.0.len() <= NORMAL_FORM_STEPS))]
fn certified_normal<A, R>(
    store: &CellStore<A>,
    start: &A::Cmd,
    read: R,
) -> Result<(Vec<CellApp<A>>, FreeTerm), NormalFormFault>
where
    A: CellAlphabet,
    R: FnOnce(&A::Cmd) -> Result<FreeTerm, Unwriting>,
{
    let normalized = normalize(store, start, NormalizationBudget::from(NORMAL_FORM_STEPS));
    if bool::from(normalized.exhausted) {
        return Err(NormalFormFault::Exhausted);
    }
    if !bool::from(replay_path(
        store,
        start,
        &normalized.normal,
        &normalized.path,
    )) {
        return Err(NormalFormFault::Uncertified);
    }
    let normal = read(&normalized.normal).map_err(NormalFormFault::Unwritable)?;
    Ok((normalized.path, normal))
}

/// Read `text` as a term of the inspection notation over `description`'s
/// symbols: a name, or a name applied to terms in parentheses separated by
/// commas, each name a constructor or an operation the description declares.
///
/// # Specification
/// - ensures: the term whose every application is the declared symbol of its
///   name, constructors and operations told apart by the declaration.
/// - fails: [`NormalFormFault::Unread`] when the text is not a whole term of
///   the notation; [`NormalFormFault::UnknownSymbol`] when a name is declared
///   as neither.
/// - panics: none.
/// - intension: one pass over the text with an explicit stack of open
///   applications, so nesting costs no call stack.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — nested and many-argument calls read to the terms whose
///   display they are, and a missing parenthesis, trailing text and an
///   undeclared name are refused apart.
/// - witness: `coincide::tests::a_call_reads_its_normal_form_or_says_why_not`
#[spec(ensures: |ret| ret.as_ref().is_err() || text.0.split_whitespace().collect::<String>()
    == ret.as_ref().map(|term| term.to_string().split_whitespace().collect::<String>()).unwrap_or_default())]
fn read_call<G>(
    description: &TheoryDesc<G>,
    text: CallText<'_>,
) -> Result<FreeTerm, NormalFormFault>
{
    let mut open: Vec<(Symbol<'_>, Vec<FreeTerm>)> = Vec::new();
    let mut rest = text.0.trim_start();
    loop {
        let length = rest
            .find(|character: char| !(character.is_alphanumeric() || "_'′".contains(character)))
            .unwrap_or(rest.len());
        let (name, after) = rest.split_at(length);
        if name.is_empty() {
            return Err(NormalFormFault::Unread);
        }
        let symbol = Symbol::of(description, CallText(name))?;
        rest = after.trim_start();
        if let Some(after) = rest.strip_prefix('(') {
            open.push((symbol, Vec::new()));
            rest = after.trim_start();
            continue;
        }
        let mut done = symbol.apply(Vec::new());
        loop {
            let Some(&mut (_, ref mut arguments)) = open.last_mut()
            else {
                return if rest.is_empty() {
                    Ok(done)
                }
                else {
                    Err(NormalFormFault::Unread)
                };
            };
            arguments.push(done);
            if let Some(after) = rest.strip_prefix(',') {
                rest = after.trim_start();
                break;
            }
            let Some(after) = rest.strip_prefix(')')
            else {
                return Err(NormalFormFault::Unread);
            };
            rest = after.trim_start();
            let Some((symbol, arguments)) = open.pop()
            else {
                return Err(NormalFormFault::Unread);
            };
            done = symbol.apply(arguments);
        }
    }
}

/// A declared symbol a call names.
#[derive(Clone, Copy, Debug)]
enum Symbol<'desc>
{
    /// A constructor.
    Ctor(&'desc Name),
    /// An operation.
    Op(&'desc Name),
}

impl<'desc> Symbol<'desc>
{
    /// The symbol `description` declares under `name`, its constructors before
    /// its operations.
    ///
    /// # Specification
    /// trivial.
    fn of<G>(
        description: &'desc TheoryDesc<G>,
        name: CallText<'_>,
    ) -> Result<Self, NormalFormFault>
    {
        description
            .ctors
            .iter()
            .find(|ctor| ctor.name.as_ref() == name.0)
            .map(|ctor| Self::Ctor(&ctor.name))
            .or_else(|| {
                description
                    .opers
                    .iter()
                    .find(|operation| operation.name.as_ref() == name.0)
                    .map(|operation| Self::Op(&operation.name))
            })
            .ok_or(NormalFormFault::UnknownSymbol)
    }

    /// The symbol applied to `arguments`.
    ///
    /// # Specification
    /// trivial.
    fn apply(
        self,
        arguments: Vec<FreeTerm>,
    ) -> FreeTerm
    {
        match self {
            Self::Ctor(name) => FreeTerm::ctor(name.clone(), arguments),
            Self::Op(name) => FreeTerm::op(name.clone(), arguments),
        }
    }
}

/// `term` in the inspection notation, a results tuple at its root as
/// `(a, b, …)` from two components and `#{a}` at one: the spelling `gandr run`
/// gives the value in its sugared form.
///
/// # Specification
/// trivial.
fn spell(term: &FreeTerm) -> String
{
    match term.view() {
        TermView::Results { args } => {
            let components: Vec<String> = args
                .map(|component| component.to_term().to_string())
                .collect();
            let joined = components.join(", ");
            if components.len() >= 2 {
                format!("({joined})")
            }
            else {
                format!("#{{{joined}}}")
            }
        },
        TermView::Var(_) | TermView::Ctor { .. } | TermView::Op { .. } | TermView::Inst { .. } => {
            term.to_string()
        },
    }
}

#[cfg(test)]
mod tests;
