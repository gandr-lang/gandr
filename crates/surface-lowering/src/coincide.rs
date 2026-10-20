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
//!    that function's crate). The first rule it does not orient is refused as
//!    [`LoweringRefusal::RulesUnoriented`] at that rule.
//! 2. Joinability of every critical pair over the block's own cells
//!    (`join_critical_pairs`). A pair whose normal forms differ is refused as
//!    [`LoweringRefusal::RulesDiverge`] at the later rule, naming the earlier
//!    one, the peak and both normal forms kept in the cell diagnostic
//!    ([`CoherenceFault::Diverges`]). A pair a reduct of which reaches no
//!    normal form within [`JOIN_STEPS`] steps is refused as
//!    [`LoweringRefusal::RulesUndecided`], which reports the budget and no
//!    verdict.
//!
//! A block that passes is orthogonal — no two of its rules overlap — or
//! joined, with one replaying certificate per critical pair
//! ([`Coincidence`]). Witnesses:
//! `coincide::tests::an_overlap_that_joins_is_certified_and_runs_either_way`,
//! `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`,
//! `coincide::tests::a_rule_that_rebuilds_its_own_call_refuses_the_block`.
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
//! **Choice: refuse.** A block whose two readings part is refused whole, as a
//! family: the equational reading is what the rules mean — what a model of
//! the family satisfies, and what a `theory` block's models state as paths —
//! and the decision tree is how they run, so a tree computing what the
//! equations do not is a miscompilation, not a dialect. **Alternatives.**
//! Warning and running first match, the written order read as a disambiguation
//! the author opted into: rule order then means something, reordering two rules
//! changes what a program computes while every equation the family states stays
//! the same, and a model checked against the equations disagrees with the
//! program it models. Completing the rules — adding the derived cell that joins
//! a divergent pair, as completion does — was declined too: a derived cell is
//! an equation the author did not write, and a divergence between two
//! constructor terms would identify them. **Reversal.** A written opt-in to
//! ordered rules — an attribute on the block — makes first match the declared
//! semantics; the equational reading is then the one that changes, to the
//! rules with each one's earlier overlaps subtracted, and this check reads
//! that.
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
//! oriented rule only — left above right — and the declaration's rules keep the
//! written arrow so the printer reads `<=>` back. **Alternative.** Completion
//! choosing a direction per critical pair, which would add equations the
//! author did not write. **Reversal.** The opt-in to ordered rules above:
//! pinning becomes the default again, and `<=>` is sugar for whichever
//! direction the order admits.
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
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::Joinability;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::join_critical_pairs;
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
use gandr_theory_computads::term_reading;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::Precedence;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::RuleIndex;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::Termination;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::derive_cell_var_meta;
use gandr_theory_levitation::orient_rules;
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
    /// The rules terminate and every critical pair joins: one certificate per
    /// pair, in the reading the pair was decided in.
    Joined(Certificates),
    /// The rules' two readings part, or the check could not tell: the report's
    /// diagnostic at this index says why.
    Refused(CellDiagnosticIndex),
}

/// The join certificates of a block's critical pairs, by reading.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Certificates
{
    /// One per critical pair of the sequent reading, each replaying over
    /// [`DeclarationCells::rewriting`].
    pub commands: Vec<Tracelet>,
    /// One per critical pair of the presented reading, interior overlaps
    /// included, each replaying over its term store.
    pub terms: Vec<Tracelet<TermAlphabet>>,
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
    /// The rule and an earlier one overlap at `peak` and rewrite it to two
    /// normal forms.
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
    /// The rule and an earlier one overlap at `peak`, and a reduct reaches no
    /// normal form within [`JOIN_STEPS`] steps.
    Undecided
    {
        /// The earlier rule's written interval.
        first: ByteSpan,
        /// The term both rules match.
        peak: Box<PairTerm>,
    },
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
            Self::Diverges { first, .. } => LoweringRefusal::RulesDiverge { span, first },
            Self::Undecided { first, .. } => LoweringRefusal::RulesUndecided { span, first },
        }
    }
}

impl fmt::Display for CoherenceFault
{
    /// Writes the fault with the terms it names in the inspection notation: the
    /// peak and both normal forms of a divergence, the peak of an undecided
    /// pair.
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
    ///   its peak and both normal forms in order; swapping them or dropping the
    ///   peak changes the witnessed text.
    /// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
    /// - witness: `coincide::tests::a_third_cancellation_parts_the_circles_readings`
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
            Self::Undecided { ref peak, .. } => write!(
                f,
                "both rules rewrite `{}`, and its rewrites reach no normal form within \
                 {JOIN_STEPS} steps",
                Spelled(peak)
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
/// rewriting store and, for a presented type, over its term store.
///
/// # Specification
/// - requires: `store`, `faces`, `presented` and `circuits` are the cell gate's
///   elaboration of `description`, which declined none of its operations, faces
///   or circuit rules; `at` is the declaration's interval.
/// - ensures: the first unoriented rule as [`CoherenceFault::Unoriented`] at
///   its span; else the first critical pair of the sequent reading, then of the
///   presented one, that does not join, at the later rule's span naming the
///   earlier one's; else [`Coincidence::Orthogonal`] when no two cells overlap
///   in either reading and [`Coincidence::Joined`] with every pair's
///   certificate otherwise.
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
///   third cancellation diverges at itself naming the one before; reporting the
///   earlier rule's span, deciding joinability first, or reading the circle in
///   the sequent store alone changes one of them.
/// - witness: `coincide::tests::an_overlap_that_joins_is_certified_and_runs_either_way`
/// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
/// - witness: `coincide::tests::a_rule_that_rebuilds_its_own_call_refuses_the_block`
/// - witness: `coincide::tests::the_circles_cancellations_join_below_the_root`
/// - witness: `coincide::tests::a_third_cancellation_parts_the_circles_readings`
#[spec(ensures: |ret| match ret {
    Ok(Coincidence::Joined(ref certificates)) => !certificates.commands.is_empty() || !certificates.terms.is_empty(),
    Ok(Coincidence::Orthogonal) => true,
    Ok(Coincidence::Unexamined | Coincidence::Refused(_)) => false,
    Err((span, CoherenceFault::Unoriented)) => matches!(orient_rules(description), Termination::Unoriented(_))
        && span.start() >= at.start() && span.end() <= at.end(),
    Err((_, CoherenceFault::Diverges { .. } | CoherenceFault::Undecided { .. })) => orient_rules(description) == Termination::Oriented,
})]
pub(crate) fn decide<G>(
    description: &TheoryDesc<G>,
    at: ByteSpan,
    store: &CellStore,
    faces: &[(AdmittedFaceIndex, CellId)],
    presented: &Maybe<PresentedRules, presented_reading::Absent>,
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
    let budget = NormalizationBudget::from(JOIN_STEPS);
    let rewriting = rewriting_store(store, faces, circuits);
    let commands = certified(
        join_critical_pairs(&rewriting, budget),
        faces,
        &rule_span,
        at,
        PairTerm::Command,
    )?;
    let terms = match *presented {
        Maybe::Present(ref presented) => certified(
            join_critical_pairs(&presented.store, budget),
            &presented.faces,
            &rule_span,
            at,
            PairTerm::Term,
        )?,
        Maybe::Absent(presented_reading::Absent::NoTermFace) => Vec::new(),
    };
    if commands.is_empty() && terms.is_empty() {
        return Ok(Coincidence::Orthogonal);
    }
    Ok(Coincidence::Joined(Certificates { commands, terms }))
}

/// The certificates of one reading's critical pairs, or the fault of its first
/// pair that does not join, at the later rule's span naming the earlier one's.
///
/// # Specification
/// - requires: `faces` pairs each face with its cell in the store `joinability`
///   was decided over; `rule_span` locates a face by index.
/// - ensures: every certificate when every pair joins; otherwise the pair's two
///   cells located at their faces — `at` for a cell no face wrote — the later
///   face carrying the fault and the earlier one named in it, a pair whose
///   faces are written out of store order read in face order.
/// - panics: none.
///
/// # Errors
/// The fault and the span it stands at, as the ensures clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a sequent pair is located at its later rule, written
///   after or before the earlier one in the overlap, and an interior pair of
///   the circle whose later rule is the overlap's left cell is located at that
///   rule all the same; swapping the two spans changes the witnessed text.
/// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
/// - witness: `coincide::tests::two_rules_written_the_other_way_round_are_refused_at_the_later_one_all_the_same`
/// - witness: `coincide::tests::a_third_cancellation_parts_the_circles_readings`
#[spec(captures: joined = match joinability {
    Joinability::Joined(ref all) => Some(all.len()),
    Joinability::Diverges { .. } | Joinability::Undecided(_) => None,
}, ensures: |ret| ret.as_ref().map_or_else(|_| joined.is_none(), |certificates| joined == Some(certificates.len())))]
fn certified<A, S, W>(
    joinability: Joinability<A>,
    faces: &[(AdmittedFaceIndex, CellId)],
    rule_span: &S,
    at: ByteSpan,
    wrap: W,
) -> Result<Vec<Tracelet<A>>, (ByteSpan, CoherenceFault)>
where
    A: CellAlphabet,
    S: Fn(usize) -> ByteSpan,
    W: Fn(A::Cmd) -> PairTerm,
{
    let face_of = |cell: CellId| {
        faces
            .iter()
            .find(|&&(_, admitted)| admitted == cell)
            .map(|&(index, _)| usize::from(index))
    };
    // The span of the later face, the span of the earlier one, and whether the
    // overlap read the later face first.
    let located = |left: CellId, right: CellId| {
        let span = |face: Option<usize>| face.map_or(at, rule_span);
        match (face_of(left), face_of(right)) {
            (Some(written_left), Some(written_right)) if written_left > written_right => {
                (span(Some(written_left)), span(Some(written_right)), true)
            },
            (written_left, written_right) => (span(written_right), span(written_left), false),
        }
    };
    match joinability {
        Joinability::Joined(certificates) => Ok(certificates),
        Joinability::Diverges {
            overlap,
            left,
            right,
        } => {
            let (span, first, swapped) = located(overlap.left, overlap.right);
            let (earlier, later) = if swapped {
                (right, left)
            }
            else {
                (left, right)
            };
            Err((span, CoherenceFault::Diverges {
                first,
                peak: Box::new(wrap(overlap.peak)),
                left: Box::new(wrap(earlier)),
                right: Box::new(wrap(later)),
            }))
        },
        Joinability::Undecided(overlap) => {
            let (span, first, _) = located(overlap.left, overlap.right);
            Err((span, CoherenceFault::Undecided {
                first,
                peak: Box::new(wrap(overlap.peak)),
            }))
        },
    }
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
        TermView::Var(_) | TermView::Ctor { .. } | TermView::Op { .. } => term.to_string(),
    }
}

#[cfg(test)]
mod tests;
