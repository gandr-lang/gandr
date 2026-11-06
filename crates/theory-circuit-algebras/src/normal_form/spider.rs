//! Spiders, and the decision modulo the laws of a special commutative
//! Frobenius algebra.
//!
//! A [`GeneratorSort::Spider`] generator is a spider on the wire sort that its
//! name names. The laws say that a connected composite of spiders of one name
//! equals one spider, whose legs are the open wires of the composite, and that
//! the legs of a spider have no order. [`spider_normal_form`] fuses each such
//! composite and removes each identity spider. [`spider_canonicalize`] gives
//! the fused form the canon of [`canonicalize`], exact under the order of the
//! legs. [`same_modulo_frobenius`] decides equality modulo the laws by those
//! forms, with evidence on both arms. [`canonicalize`] and
//! [`same_diagram`](super::same_diagram) do not change: they read the legs of a
//! spider in the order that the presentation writes.
//!
//! # Boundaries
//!
//! - **Fusion.** A union-find joins two spiders of one name when a wire
//!   connects them. Each class becomes one spider. Its sources are the wires
//!   that enter the class, and its targets are the wires that leave it. A wire
//!   inside the class goes, because the algebra is special.
//! - **Identities.** A spider with one source and one target is the identity.
//!   The form removes it and joins its two wires. A join can connect two
//!   spiders of one name only in a diagram that mixes wire sorts, and then
//!   fusion runs again.
//! - **A loop.** A split that feeds a generator, and a merge that reads the
//!   generator back, fuse into one spider in a loop with the generator. The
//!   laws give that loop, so a [`SpiderNormalForm`] can hold a directed cycle.
//!   It is thus not a [`Wiring`], and [`CanonicalDiagram::to_wiring`] refuses
//!   the form of such a loop.
//! - **Ties.** Each leg of a spider has a key: the far end of its wire. The key
//!   is a boundary position, or the label and the port position of the
//!   generator there. A far spider gives its label only, because its own legs
//!   have no order. Legs of one side of one spider with equal keys are a tie.
//!   Two leaves of one label, generators with that wire as their only port,
//!   trade places by an automorphism, so they are no tie.
//! - **Exactness.** The canon tries every order of every tie and keeps the
//!   least form. An isomorphism of fused forms keeps the keys. Thus it carries
//!   the trials of one form onto the trials of the other, and the least forms
//!   agree.
//! - **Cost.** Ties of sizes `k₁` to `kⱼ` cost `k₁! · … · kⱼ!` trials, one
//!   traversal each. The count is known before the first trial, so a form past
//!   the budget is refused before any trial runs. No exact canon is cheaper in
//!   the worst case: a spider is a vertex, a generator with two ports is a
//!   directed edge, and the canon then decides graph isomorphism.
//!
//! # References
//!
//! - Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and
//!   Fabio Zanasi. "String Diagram Rewrite Theory I: Rewriting with Frobenius
//!   Structure." _Journal of the ACM_ 69, 2 (2022), article 14.
//!   `doi:10.1145/3502719`; preprint `arXiv:2012.01847` — hypergraphs with
//!   interfaces as the symmetric monoidal diagrams modulo special commutative
//!   Frobenius structure, where a connected composite of spiders is one vertex
//!   and the legs of a vertex have no order.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — newest: the ruling that
//!   puts spiders in this crate, exact under the symmetry of their ports, and
//!   the budget of 16 ms at p99 at 2^12 generators with no tie.
//! - `vault:01a178aa-61bf-70f2-a24f-b3a69dfcd199` — newest: the spider form
//!   that canonicalization at the representation decides, in place of
//!   contraction rules that an order orients.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use super::CanonicalDiagram;
use super::Canonicalization;
use super::DiagramDivergence;
use super::Leg;
use super::Outline;
use super::RelabellingDefect;
use super::canonicalize;
use super::divergence_of;
use super::form_divergence;
use crate::interface::Edge;
use crate::interface::Generator;
use crate::interface::GeneratorLabel;
use crate::interface::GeneratorSort;
use crate::interface::Interface;
use crate::interface::Wire;
use crate::interface::WireCount;
use crate::interface::Wiring;
use crate::interface::WiringObstruction;
use crate::interface::assemble_monogamous;
use crate::interface::reorder_ports;

wrapper! {
    /// How many trials a spider canon may run. A trial is one
    /// canonicalization of one order of the tied legs.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct SpiderBudget(usize);
}

wrapper! {
    /// How many trials a spider canon ran, or would run.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct SpiderTrials(usize);
}

/// A diagram whose spiders are fused: no wire joins two spiders of one name,
/// and no spider is the identity.
///
/// It is monogamous and boundary-honest, and it can hold a directed loop
/// through a spider.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct SpiderNormalForm
{
    /// The fused presentation.
    wiring: Wiring,
}

impl SpiderNormalForm
{
    /// The generators, spiders and others, in the order fusion lists them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generators(&self) -> &[Generator]
    {
        self.wiring.generators()
    }

    /// The discrete boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn boundary(&self) -> &Interface
    {
        self.wiring.boundary()
    }

    /// How many wires the form declares.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn wire_count(&self) -> WireCount
    {
        self.wiring.wire_count()
    }
}

/// Why a spider canon or a spider decision gives no answer.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SpiderObstruction
{
    /// The fused presentation failed a local check of a wiring. Fusion keeps
    /// the one producer and the one consumer of each wire, so no fused form
    /// fails one.
    Wiring(WiringObstruction),
    /// The ties need more trials than the budget holds.
    BudgetExhausted
    {
        /// How many trials the ties need.
        needed: SpiderTrials,
        /// How many the budget held.
        budget: SpiderBudget,
    },
}

impl core::fmt::Display for SpiderObstruction
{
    /// Names the refused condition.
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
            Self::Wiring(_) => "the spider normal form failed a local check of a wiring",
            Self::BudgetExhausted { .. } => "the tied legs need more trials than the budget holds",
        })
    }
}

impl core::error::Error for SpiderObstruction
{
}

/// Why a spider canon is not evidence for a diagram.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SpiderDefect
{
    /// The spider normal form of the diagram failed a local check of a
    /// wiring, which no fused form does.
    Wiring(WiringObstruction),
    /// The canon's presentation declares another number of wires than the
    /// fused diagram.
    WireCount,
    /// The canon's presentation carries another boundary than the fused
    /// diagram.
    Boundary,
    /// The canon's presentation holds another number of generators than the
    /// fused diagram.
    GeneratorCount,
    /// The generator at this position is not the fused diagram's generator
    /// there, with the legs of a spider reordered at most.
    Generator
    {
        /// The position that differs.
        at: Edge,
    },
    /// The relabelling of the presentation onto the form does not verify.
    Relabelling(RelabellingDefect),
}

impl core::fmt::Display for SpiderDefect
{
    /// Names the refused condition.
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
            Self::Wiring(_) => "the spider normal form failed a local check of a wiring",
            Self::WireCount => "the presentation declares another number of wires",
            Self::Boundary => "the presentation carries another boundary",
            Self::GeneratorCount => "the presentation holds another number of generators",
            Self::Generator { .. } => "a generator of the presentation is not the fused one",
            Self::Relabelling(_) => "the relabelling of the presentation does not verify",
        })
    }
}

impl core::error::Error for SpiderDefect
{
}

/// The canon of one diagram modulo the Frobenius laws, with its evidence.
///
/// The evidence is the presentation that won: the spider normal form of the
/// diagram with the legs of its spiders in the winning order. Its relabelling
/// onto the form is the one [`canonicalize`] returns.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpiderCanon
{
    /// The fused diagram, its legs in the winning order.
    presented: Wiring,
    /// The canon of that presentation.
    canonicalization: Canonicalization,
    /// How many trials the canon ran.
    trials: SpiderTrials,
}

impl SpiderCanon
{
    /// The canonical form: equal for two diagrams exactly when the laws and a
    /// renumbering carry one onto the other.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn form(&self) -> &CanonicalDiagram
    {
        self.canonicalization.form()
    }

    /// How many trials the canon ran.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn trials(&self) -> SpiderTrials
    {
        self.trials
    }

    /// Checks that this canon is evidence for `diagram`.
    ///
    /// # Specification
    /// - ensures: success exactly when the presentation is the spider normal
    ///   form of `diagram` with the legs of its spiders reordered at most, and
    ///   the relabelling verifies from the presentation onto the form.
    /// - fails: [`SpiderDefect`] naming the first datum that differs, in the
    ///   order wire count, boundary, generator count, generators by position,
    ///   relabelling.
    /// - panics: none.
    /// - intension: fusion runs again on `diagram`, so the check trusts no
    ///   datum of the canon but its relabelling, which it verifies.
    ///
    /// # Errors
    /// - [`SpiderDefect::Wiring`]: the fused form of `diagram` failed a check,
    ///   which no fused form does.
    /// - [`SpiderDefect::WireCount`], [`SpiderDefect::Boundary`],
    ///   [`SpiderDefect::GeneratorCount`] and [`SpiderDefect::Generator`]: the
    ///   presentation is not a reordering of the fused form of `diagram`.
    /// - [`SpiderDefect::Relabelling`]: the relabelling does not verify.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the evidence of each arm verifies against its own
    ///   input, and the evidence of one input is refused against another input
    ///   at the generator where their fused forms part. L1 — the evidence of
    ///   generated pairs verifies on both sides.
    /// - witness: `normal_form::spider::tests::the_evidence_verifies_against_each_input`
    /// - witness: `tests::normal_form::every_frobenius_rewrite_is_the_same_diagram`
    #[spec(ensures: |ref result| result.is_err() || self.presented.generators().len() <= diagram.generators().len())]
    #[inline]
    pub fn verify(
        &self,
        diagram: &Wiring,
    ) -> Result<(), SpiderDefect>
    {
        let fused = spider_normal_form(diagram).map_err(SpiderDefect::Wiring)?;
        check_presentation(&fused.wiring, &self.presented)?;
        self.canonicalization
            .relabelling()
            .verify(&self.presented, self.canonicalization.form())
            .map_err(SpiderDefect::Relabelling)
    }
}

/// Two diagrams that are one diagram modulo the Frobenius laws, with the
/// canon of each.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SharedSpiderCanon
{
    /// The canon of the left diagram.
    left: SpiderCanon,
    /// The canon of the right diagram.
    right: SpiderCanon,
}

impl SharedSpiderCanon
{
    /// The form that both diagrams reach.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn form(&self) -> &CanonicalDiagram
    {
        self.left.form()
    }

    /// The canon of the left diagram.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left(&self) -> &SpiderCanon
    {
        &self.left
    }

    /// The canon of the right diagram.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right(&self) -> &SpiderCanon
    {
        &self.right
    }
}

/// Whether two diagrams are one diagram modulo the Frobenius laws, with the
/// evidence either way.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpiderEquality
{
    /// They are: the canon of each, with one form. The two canons hold a
    /// presentation each, so the arm holds them behind one pointer.
    Same(Box<SharedSpiderCanon>),
    /// They are not: where their fused forms or their canons part.
    Distinct(DiagramDivergence),
}

/// Fuses the spiders of `diagram` and removes its identity spiders.
///
/// # Specification
/// - ensures: no wire joins two spiders of one name, and no spider has one
///   source and one target. Every other generator keeps its label and its ports
///   in their order, renumbered. The boundary keeps its order, and a wire that
///   a removed identity joins stands once on each leg.
/// - fails: [`WiringObstruction`] when the fused presentation fails a local
///   check. Fusion keeps the one producer and the one consumer of each wire, so
///   no wiring reaches it; the checks run rather than assumed.
/// - panics: none.
/// - intension: one union-find pass over the wires, then one over the
///   generators. A further pass runs only when a removed identity joins two
///   spiders of one name.
///
/// # Errors
/// [`WiringObstruction`]: a local refusal of [`Wiring::assemble`], which no
/// fused form reaches.
///
/// # Adequacy
/// - hypothesis: L3 — each law is a pair of sides with one fused form:
///   associativity, the unit, coassociativity, the counit, the Frobenius law,
///   commutativity and speciality. A bubble fuses to a plain wire, a split and
///   a merge around a generator fuse into a loop, two scalar spiders stay two,
///   spiders of two names stay apart, and a removed identity between two
///   spiders of one name fuses them. L1 — generated rewrites by the laws reach
///   one form.
/// - witness: `normal_form::spider::tests::two_merges_in_either_association_are_one_spider`
/// - witness: `normal_form::spider::tests::the_units_and_the_counits_vanish`
/// - witness: `normal_form::spider::tests::the_frobenius_law_holds`
/// - witness: `normal_form::spider::tests::a_bubble_is_a_plain_wire`
/// - witness: `normal_form::spider::tests::a_split_and_a_merge_around_a_generator_fuse_into_a_loop`
/// - witness: `normal_form::spider::tests::two_scalars_stay_two`
/// - witness: `normal_form::spider::tests::spiders_of_two_names_stay_apart`
/// - witness: `normal_form::spider::tests::a_removed_identity_fuses_its_neighbours`
/// - witness: `normal_form::spider::tests::fusion_is_idempotent`
/// - witness: `tests::normal_form::every_frobenius_rewrite_is_the_same_diagram`
#[spec(ensures: |ref result| result.as_ref().is_err() || result.as_ref().is_ok_and(|form|
    first_join(&form.wiring).is_none()
    && form.wiring.generators().iter().all(|generator| role(generator) == Role::Ordered || generator.sources().len() != 1 || generator.targets().len() != 1)
    && form.wiring.boundary().inputs().len() == diagram.boundary().inputs().len()
    && form.wiring.boundary().outputs().len() == diagram.boundary().outputs().len()))]
#[inline]
pub fn spider_normal_form(diagram: &Wiring) -> Result<SpiderNormalForm, WiringObstruction>
{
    let mut wiring = fusion_pass(diagram)?;
    while first_join(&wiring).is_some() {
        wiring = fusion_pass(&wiring)?;
    }
    Ok(SpiderNormalForm { wiring })
}

/// The canon of `diagram` modulo the Frobenius laws.
///
/// # Specification
/// - ensures: the form of the spider normal form of `diagram`, least over every
///   order of its tied legs. Two diagrams reach one form exactly when the laws
///   and a renumbering carry one onto the other. The canon carries its winning
///   presentation and the number of trials it ran.
/// - fails: [`SpiderObstruction::BudgetExhausted`] before any trial, when the
///   ties need more trials than `budget`; [`SpiderObstruction::Wiring`] as
///   [`spider_normal_form`] fails.
/// - panics: none.
/// - intension: one fusion, then one traversal for each trial. A form with no
///   tie runs one trial and copies no presentation.
///
/// # Errors
/// - [`SpiderObstruction::BudgetExhausted`]: the ties need more trials than
///   `budget`.
/// - [`SpiderObstruction::Wiring`]: fusion failed a local check, which no
///   wiring reaches.
///
/// # Adequacy
/// - hypothesis: L3 — two orders of tied legs reach one form, and the trial
///   count is the product of the factorials of the tie sizes. A budget one
///   short of the count is refused, and a budget equal to it is admitted.
///   Leaves of one label are no tie. L1 — generated rewrites by the laws, with
///   every leg order shuffled, reach one form.
/// - witness: `normal_form::spider::tests::tied_legs_have_one_form_in_every_order`
/// - witness: `normal_form::spider::tests::the_budget_is_refused_before_any_trial`
/// - witness: `normal_form::spider::tests::leaves_of_one_label_are_no_tie`
/// - witness: `tests::normal_form::every_frobenius_rewrite_is_the_same_diagram`
#[spec(ensures: |ref result| match *result {
    Ok(ref canon) => usize::from(canon.trials) <= usize::from(budget) && usize::from(canon.trials) >= 1,
    Err(SpiderObstruction::BudgetExhausted { needed, budget: allowed }) => allowed == budget && usize::from(needed) > usize::from(allowed),
    Err(SpiderObstruction::Wiring(_)) => true,
})]
#[inline]
pub fn spider_canonicalize(
    diagram: &Wiring,
    budget: SpiderBudget,
) -> Result<SpiderCanon, SpiderObstruction>
{
    let fused = spider_normal_form(diagram).map_err(SpiderObstruction::Wiring)?;
    canon_of(fused.wiring, budget)
}

/// Decides whether two diagrams are one diagram modulo the Frobenius laws.
///
/// # Specification
/// - ensures: [`SpiderEquality::Same`] exactly when the laws and a renumbering
///   carry one diagram onto the other, with the canon of each; otherwise
///   [`SpiderEquality::Distinct`], naming the first place where the fused forms
///   or their canons part.
/// - fails: [`SpiderObstruction::BudgetExhausted`] when the trials of both
///   canons together need more than `budget`; [`SpiderObstruction::Wiring`] as
///   [`spider_normal_form`] fails.
/// - provides: the decision with evidence on both arms, as
///   [`same_diagram`](super::same_diagram) gives it for the presentation
///   relation.
/// - panics: none.
/// - intension: the counts and the leg arities of the two fused forms are
///   compared before any trial, so a difference there spends no budget. The
///   right canon spends what the left one left.
///
/// # Errors
/// - [`SpiderObstruction::BudgetExhausted`]: the budget ran out.
/// - [`SpiderObstruction::Wiring`]: fusion failed a local check, which no
///   wiring reaches.
///
/// # Adequacy
/// - hypothesis: L3 — each law gives `Same` where the presentation relation
///   gives `Distinct`; a count difference and a record difference are located;
///   the budget is shared by both canons. L1 — generated rewrites by the laws
///   are `Same`, with both canons verified.
/// - witness: `normal_form::spider::tests::two_merges_in_either_association_are_one_spider`
/// - witness: `normal_form::spider::tests::commuted_legs_are_one_spider`
/// - witness: `normal_form::spider::tests::the_decision_locates_where_two_forms_part`
/// - witness: `normal_form::spider::tests::the_budget_is_shared_by_both_canons`
/// - witness: `tests::normal_form::every_frobenius_rewrite_is_the_same_diagram`
#[spec(ensures: |ref result| match *result {
    Ok(SpiderEquality::Same(ref shared)) => shared.left.form() == shared.right.form()
        && usize::from(shared.left.trials).saturating_add(usize::from(shared.right.trials)) <= usize::from(budget),
    Ok(SpiderEquality::Distinct(_)) | Err(_) => true,
})]
#[inline]
pub fn same_modulo_frobenius(
    left: &Wiring,
    right: &Wiring,
    budget: SpiderBudget,
) -> Result<SpiderEquality, SpiderObstruction>
{
    let mine = spider_normal_form(left).map_err(SpiderObstruction::Wiring)?;
    let theirs = spider_normal_form(right).map_err(SpiderObstruction::Wiring)?;
    if let Maybe::Present(divergence) =
        Outline::of_wiring(&mine.wiring).divergence(Outline::of_wiring(&theirs.wiring))
    {
        return Ok(SpiderEquality::Distinct(divergence));
    }
    let mine = canon_of(mine.wiring, budget)?;
    let rest = SpiderBudget(budget.0.saturating_sub(mine.trials.0));
    let theirs = match canon_of(theirs.wiring, rest) {
        Ok(canon) => canon,
        Err(SpiderObstruction::BudgetExhausted { needed, .. }) => {
            return Err(SpiderObstruction::BudgetExhausted {
                needed: SpiderTrials(needed.0.saturating_add(mine.trials.0)),
                budget,
            });
        },
        Err(refusal) => return Err(refusal),
    };
    Ok(match divergence_of(mine.form(), theirs.form()) {
        Maybe::Present(divergence) => SpiderEquality::Distinct(divergence),
        Maybe::Absent(form_divergence::Absent::Equal) => {
            SpiderEquality::Same(Box::new(SharedSpiderCanon {
                left: mine,
                right: theirs,
            }))
        },
    })
}

/// Whether a generator is a spider, whose legs have no order, or a generator
/// that orders its ports.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Role
{
    /// A spider.
    Spider,
    /// A generator that orders its ports.
    Ordered,
}

/// The role of `generator`.
///
/// # Specification
/// trivial.
fn role(generator: &Generator) -> Role
{
    if generator.label().sort() == GeneratorSort::Spider {
        Role::Spider
    }
    else {
        Role::Ordered
    }
}

/// The producer and the consumer of `wire`, when both are spiders of one
/// name.
///
/// # Specification
/// - ensures: the two positions exactly when `wire` has a producer and a
///   consumer, the producer is a spider, and the two carry one label.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two spiders of one name joined by a wire fuse, a spider
///   and a generator of another sort do not, and spiders of two names do not.
/// - witness: `normal_form::spider::tests::two_merges_in_either_association_are_one_spider`
/// - witness: `normal_form::spider::tests::spiders_of_two_names_stay_apart`
#[spec(ensures: |ref result| result.is_none_or(|(producer, consumer)|
    diagram.producer_of(wire) == Maybe::Present(producer) && diagram.consumer_of(wire) == Maybe::Present(consumer)))]
fn joined_spiders(
    diagram: &Wiring,
    wire: Wire,
) -> Option<(Edge, Edge)>
{
    let (Maybe::Present(producer), Maybe::Present(consumer)) =
        (diagram.producer_of(wire), diagram.consumer_of(wire))
    else {
        return None;
    };
    let (Maybe::Present(made), Maybe::Present(used)) =
        (diagram.generator(producer), diagram.generator(consumer))
    else {
        return None;
    };
    (role(made) == Role::Spider && made.label() == used.label()).then_some((producer, consumer))
}

/// The first wire of `diagram` that joins two spiders of one name.
///
/// # Specification
/// - ensures: the lowest such wire, or none when no wire joins two spiders of
///   one name.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a removed identity between two spiders of one name leaves
///   a wire that joins them, and fusion runs again.
/// - witness: `normal_form::spider::tests::a_removed_identity_fuses_its_neighbours`
/// - witness: `normal_form::spider::tests::fusion_is_idempotent`
#[spec(ensures: |ref result| result.is_none_or(|wire| joined_spiders(diagram, wire).is_some()))]
fn first_join(diagram: &Wiring) -> Option<Wire>
{
    diagram
        .wire_count()
        .wires()
        .find(|wire| joined_spiders(diagram, *wire).is_some())
}

/// The representative of the class of `node`, halving the path to it.
///
/// # Specification
/// - ensures: the representative, a node that is its own parent; a node past
///   `parents` is its own representative.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — three spiders in a chain fuse into one class whatever
///   order joins them, and the representative is the lowest position.
/// - witness: `normal_form::spider::tests::two_merges_in_either_association_are_one_spider`
/// - witness: `normal_form::spider::tests::the_frobenius_law_holds`
#[spec(ensures: |root| parents.get(usize::from(root)).is_none_or(|parent| *parent == root))]
fn representative<Node>(
    parents: &mut [Node],
    node: Node,
) -> Node
where
    Node: Copy + Eq,
    usize: From<Node>,
{
    let mut node = node;
    loop {
        let Some(parent) = parents.get(usize::from(node)).copied()
        else {
            return node;
        };
        if parent == node {
            return node;
        }
        let grandparent = parents.get(usize::from(parent)).copied().unwrap_or(parent);
        if let Some(slot) = parents.get_mut(usize::from(node)) {
            *slot = grandparent;
        }
        node = grandparent;
    }
}

/// Joins the classes of `left` and `right`. The lower representative stands
/// for both.
///
/// # Specification
/// - requires: `left` and `right` are positions of `parents`, and every parent
///   stands at or below its node.
/// - ensures: `left` and `right` have one representative, the lower of their
///   two representatives before the call; every parent still stands at or below
///   its node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a class keeps its lowest position as its representative,
///   so a fused spider stands at the position of its first member.
/// - witness: `normal_form::spider::tests::two_merges_in_either_association_are_one_spider`
/// - witness: `normal_form::spider::tests::a_removed_identity_fuses_its_neighbours`
#[spec(requires: usize::from(left) < parents.len() && usize::from(right) < parents.len(),
captures: [length = parents.len(), higher = usize::from(left).max(usize::from(right))],
ensures: |_| parents.len() == length && parents.get(higher).is_some_and(|parent| usize::from(*parent) <= higher))]
fn join<Node>(
    parents: &mut [Node],
    left: Node,
    right: Node,
) where
    Node: Copy + Ord,
    usize: From<Node>,
{
    let left = representative(parents, left);
    let right = representative(parents, right);
    let (low, high) = if left <= right {
        (left, right)
    }
    else {
        (right, left)
    };
    if let Some(slot) = parents.get_mut(usize::from(high)) {
        *slot = low;
    }
}

/// One pass of fusion: each class of spiders that wires join becomes one
/// spider, and each identity class joins its two wires.
///
/// # Specification
/// - ensures: the spiders of each class of `diagram` are one spider at the
///   position of the first member, holding the wires that enter and leave the
///   class in member order. The wires inside a class go, the identity classes
///   go, and the surviving wires are numbered densely in their order.
/// - fails: [`WiringObstruction`] as [`assemble_monogamous`] refuses the
///   result, which no pass reaches.
/// - panics: none.
/// - intension: linear in the ports, with one union-find over the generators
///   and one over the wires.
///
/// # Errors
/// [`WiringObstruction`]: a local refusal, which no pass reaches.
///
/// # Adequacy
/// - hypothesis: L3 — the law fixtures pin the fused spider's legs, the removal
///   of an identity, the join of its wires on both boundary legs, and the
///   renumbering of the surviving wires.
/// - witness: `normal_form::spider::tests::two_merges_in_either_association_are_one_spider`
/// - witness: `normal_form::spider::tests::the_units_and_the_counits_vanish`
/// - witness: `normal_form::spider::tests::a_bubble_is_a_plain_wire`
/// - witness: `normal_form::spider::tests::a_removed_identity_fuses_its_neighbours`
#[spec(ensures: |ref result| result.as_ref().is_err() || result.as_ref().is_ok_and(|fused|
    fused.generators().len() <= diagram.generators().len() && fused.wire_count() <= diagram.wire_count()))]
fn fusion_pass(diagram: &Wiring) -> Result<Wiring, WiringObstruction>
{
    let generators = diagram.generators();
    let wire_total = usize::from(diagram.wire_count());
    let mut classes: Vec<Edge> = (0 .. generators.len()).map(Edge::from).collect();
    let mut inside: Vec<bool> = alloc::vec![false; wire_total];
    for (index, slot) in inside.iter_mut().enumerate() {
        if let Some((producer, consumer)) = joined_spiders(diagram, Wire::from(index)) {
            join(&mut classes, producer, consumer);
            *slot = true;
        }
    }
    let open = |wire: &&Wire| !inside.get(usize::from(**wire)).copied().unwrap_or(false);
    let mut legs: BTreeMap<Edge, (Vec<Wire>, Vec<Wire>)> = BTreeMap::new();
    for (index, generator) in generators.iter().enumerate() {
        if role(generator) == Role::Ordered {
            continue;
        }
        let class = legs
            .entry(representative(&mut classes, Edge::from(index)))
            .or_default();
        class
            .0
            .extend(generator.sources().iter().filter(open).copied());
        class
            .1
            .extend(generator.targets().iter().filter(open).copied());
    }
    let mut aliases: Vec<Wire> = diagram.wire_count().wires().collect();
    legs.retain(|_, class| match (class.0.as_slice(), class.1.as_slice()) {
        (&[source], &[target]) => {
            join(&mut aliases, source, target);
            false
        },
        _ => true,
    });
    let mut numbers: Vec<Option<Wire>> = alloc::vec![None; wire_total];
    let mut survivors = 0_usize;
    for (index, slot) in numbers.iter_mut().enumerate() {
        let wire = Wire::from(index);
        if open(&&wire) && representative(&mut aliases, wire) == wire {
            *slot = Some(Wire::from(survivors));
            survivors = survivors.saturating_add(1);
        }
    }
    let mut renumber = |ports: &[Wire]| -> Vec<Wire> {
        ports
            .iter()
            .filter_map(|wire| {
                numbers
                    .get(usize::from(representative(&mut aliases, *wire)))
                    .copied()
                    .flatten()
            })
            .collect()
    };
    let mut fused: Vec<Generator> = Vec::with_capacity(generators.len());
    for (index, generator) in generators.iter().enumerate() {
        let ports = if role(generator) == Role::Spider {
            legs.get(&Edge::from(index))
                .map(|class| (renumber(&class.0), renumber(&class.1)))
        }
        else {
            Some((renumber(generator.sources()), renumber(generator.targets())))
        };
        if let Some((sources, targets)) = ports {
            fused.push(Generator::new(generator.label().clone(), sources, targets));
        }
    }
    let boundary = Interface::new(
        renumber(diagram.boundary().inputs()),
        renumber(diagram.boundary().outputs()),
    );
    assemble_monogamous(WireCount::from(survivors), fused, boundary)
}

/// The far end of the wire of a spider's leg: the datum of the leg that every
/// renumbering of the fused form keeps.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum FarEnd<'form>
{
    /// A position on the boundary leg of the leg's side.
    Boundary(usize),
    /// A generator whose only port is this wire. Two such legs of one label
    /// trade places by an automorphism, so they never tie.
    Leaf(&'form GeneratorLabel),
    /// A port of a generator that orders its ports: its label and the port's
    /// position.
    Port(&'form GeneratorLabel, usize),
    /// A leg of a spider of another name, whose own legs have no order.
    Spider(&'form GeneratorLabel),
}

/// A spider of the fused form, with its legs in key order and the runs of
/// tied legs that the trials order.
#[derive(Clone, Debug)]
struct Legs
{
    /// The spider's position.
    edge: Edge,
    /// Its sources in key order.
    sources: Vec<Wire>,
    /// Its targets in key order.
    targets: Vec<Wire>,
    /// The runs of tied legs, each in its current order.
    runs: Vec<Run>,
}

/// A run of tied legs on one side of a spider.
#[derive(Clone, Copy, Debug)]
struct Run
{
    /// The side.
    side: Leg,
    /// The first position of the run in the side's key order.
    start: usize,
    /// The position past the run.
    end: usize,
}

/// The spiders of `form`, each with its legs in key order and its ties.
///
/// # Specification
/// - ensures: one entry for each spider of `form`, in position order. Each side
///   holds the spider's legs sorted by far end, a run of equal far ends in
///   ascending wire order, and a run is recorded when it holds two legs or more
///   whose far end is neither a leaf nor the boundary.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — legs to two ports of one generator are ordered by port
///   position, legs to one port position of two generators of one label tie,
///   and legs to two leaves of one label do not.
/// - witness: `normal_form::spider::tests::tied_legs_have_one_form_in_every_order`
/// - witness: `normal_form::spider::tests::leaves_of_one_label_are_no_tie`
#[spec(ensures: |ref legs| legs.len() == form.generators().iter().filter(|generator| role(generator) == Role::Spider).count())]
fn legs_of(form: &Wiring) -> Vec<Legs>
{
    let mut made: BTreeMap<Wire, FarEnd<'_>> = BTreeMap::new();
    let mut used: BTreeMap<Wire, FarEnd<'_>> = BTreeMap::new();
    for (position, wire) in form.boundary().inputs().iter().enumerate() {
        made.insert(*wire, FarEnd::Boundary(position));
    }
    for (position, wire) in form.boundary().outputs().iter().enumerate() {
        used.insert(*wire, FarEnd::Boundary(position));
    }
    for generator in form.generators() {
        let label = generator.label();
        let leaf = generator
            .sources()
            .len()
            .saturating_add(generator.targets().len())
            == 1;
        let end = |position: usize| {
            if leaf {
                FarEnd::Leaf(label)
            }
            else if role(generator) == Role::Spider {
                FarEnd::Spider(label)
            }
            else {
                FarEnd::Port(label, position)
            }
        };
        for (position, wire) in generator.targets().iter().enumerate() {
            made.insert(*wire, end(position));
        }
        for (position, wire) in generator.sources().iter().enumerate() {
            used.insert(*wire, end(position));
        }
    }
    form.generators()
        .iter()
        .enumerate()
        .filter(|entry| role(entry.1) == Role::Spider)
        .map(|(index, generator)| {
            let mut runs = Vec::new();
            let sources = keyed(generator.sources(), &made, Leg::Input, &mut runs);
            let targets = keyed(generator.targets(), &used, Leg::Output, &mut runs);
            Legs {
                edge: Edge::from(index),
                sources,
                targets,
                runs,
            }
        })
        .collect()
}

/// The legs of one side in key order, recording each run of tied legs.
///
/// # Specification
/// - ensures: the legs sorted by far end and then by wire; each run of two or
///   more equal far ends that are neither a leaf nor the boundary is pushed to
///   `runs` on `side`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the tie fixtures pin which runs are recorded.
/// - witness: `normal_form::spider::tests::tied_legs_have_one_form_in_every_order`
/// - witness: `normal_form::spider::tests::leaves_of_one_label_are_no_tie`
#[spec(ensures: |ref ordered| ordered.len() == legs.len())]
fn keyed(
    legs: &[Wire],
    ends: &BTreeMap<Wire, FarEnd<'_>>,
    side: Leg,
    runs: &mut Vec<Run>,
) -> Vec<Wire>
{
    let mut ordered: Vec<(Option<FarEnd<'_>>, Wire)> = legs
        .iter()
        .map(|wire| (ends.get(wire).copied(), *wire))
        .collect();
    ordered.sort_unstable();
    let mut start = 0_usize;
    while let Some(first) = ordered.get(start).map(|entry| entry.0) {
        let end = ordered
            .iter()
            .skip(start)
            .position(|entry| entry.0 != first)
            .map_or(ordered.len(), |offset| start.saturating_add(offset));
        let free = matches!(first, Some(FarEnd::Port(..) | FarEnd::Spider(_)));
        if free && end.saturating_sub(start) > 1 {
            runs.push(Run { side, start, end });
        }
        start = end;
    }
    ordered.into_iter().map(|entry| entry.1).collect()
}

/// The number of orders of the legs of `run`, saturating.
///
/// # Specification
/// trivial.
fn orders(run: Run) -> SpiderTrials
{
    SpiderTrials((2 ..= run.end.saturating_sub(run.start)).fold(1_usize, usize::saturating_mul))
}

/// Whether an odometer of orders stepped to a next order, or carried back to
/// its first order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Odometer
{
    /// It stepped to a next order.
    Stepped,
    /// It carried: every order was tried, and the first order stands again.
    Carried,
}

/// Steps `run` to its next order in lexicographic order.
///
/// # Specification
/// - ensures: [`Odometer::Stepped`] and the next order when one follows;
///   otherwise [`Odometer::Carried`] and the first order, ascending, so an
///   odometer of runs can carry. The run keeps its wires.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a run of three legs steps through its six orders and then
///   returns to the first, so a tie of three costs six trials.
/// - witness: `normal_form::spider::tests::the_budget_is_refused_before_any_trial`
/// - witness: `normal_form::spider::tests::a_run_steps_through_every_order`
#[spec(captures: [length = run.len()], ensures: |step| run.len() == length
    && (step == Odometer::Stepped || run.first() <= run.last()))]
fn next_order(run: &mut [Wire]) -> Odometer
{
    let Some(pivot) = run
        .windows(2)
        .rposition(|pair| matches!(pair, [left, right] if left < right))
    else {
        run.reverse();
        return Odometer::Carried;
    };
    let Some(at_pivot) = run.get(pivot).copied()
    else {
        return Odometer::Carried;
    };
    let Some(successor) = run.iter().rposition(|wire| *wire > at_pivot)
    else {
        return Odometer::Carried;
    };
    run.swap(pivot, successor);
    if let Some(tail) = run.get_mut(pivot.saturating_add(1) ..) {
        tail.reverse();
    }
    Odometer::Stepped
}

/// Steps the odometer of every run of every spider once.
///
/// # Specification
/// - ensures: [`Odometer::Stepped`] when some run stepped to a next order, the
///   runs before it carried back to their first orders; [`Odometer::Carried`]
///   when every run carried, which restores every first order. Each spider
///   keeps its legs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two ties on one spider cost the product of their orders,
///   and every order is tried once.
/// - witness: `normal_form::spider::tests::the_budget_is_refused_before_any_trial`
/// - witness: `normal_form::spider::tests::tied_legs_have_one_form_in_every_order`
#[spec(captures: [count = legs.len()], ensures: |_| legs.len() == count)]
fn advance(legs: &mut [Legs]) -> Odometer
{
    for spider in legs.iter_mut() {
        for run in &spider.runs {
            let side = match run.side {
                Leg::Input => &mut spider.sources,
                Leg::Output => &mut spider.targets,
            };
            if let Some(slice) = side.get_mut(run.start .. run.end)
                && next_order(slice) == Odometer::Stepped
            {
                return Odometer::Stepped;
            }
        }
    }
    Odometer::Carried
}

/// Writes the current order of every spider's legs into `wiring`.
///
/// # Specification
/// trivial.
fn present(
    wiring: &mut Wiring,
    legs: &[Legs],
)
{
    for spider in legs {
        reorder_ports(wiring, spider.edge, &spider.sources, &spider.targets);
    }
}

/// The canon of a fused form: the least canonical form over every order of
/// its ties.
///
/// # Specification
/// - ensures: the least form over the trials, its presentation and the trial
///   count; the count is the product of the orders of every run.
/// - fails: [`SpiderObstruction::BudgetExhausted`] before any trial when the
///   count passes `budget`.
/// - panics: none.
/// - intension: a form with no tie runs one trial and copies nothing.
///
/// # Errors
/// [`SpiderObstruction::BudgetExhausted`]: the count passes `budget`.
///
/// # Adequacy
/// - hypothesis: L3 — the tie and budget fixtures pin the count, the refusal at
///   one short and the least form over two orders.
/// - witness: `normal_form::spider::tests::tied_legs_have_one_form_in_every_order`
/// - witness: `normal_form::spider::tests::the_budget_is_refused_before_any_trial`
#[spec(ensures: |ref result| match *result {
    Ok(ref canon) => usize::from(canon.trials) <= usize::from(budget),
    Err(SpiderObstruction::BudgetExhausted { needed, .. }) => usize::from(needed) > usize::from(budget),
    Err(SpiderObstruction::Wiring(_)) => false,
})]
fn canon_of(
    fused: Wiring,
    budget: SpiderBudget,
) -> Result<SpiderCanon, SpiderObstruction>
{
    let mut legs = legs_of(&fused);
    let needed = legs
        .iter()
        .flat_map(|spider| &spider.runs)
        .fold(1_usize, |count, run| {
            count.saturating_mul(usize::from(orders(*run)))
        });
    if needed > budget.0 {
        return Err(SpiderObstruction::BudgetExhausted {
            needed: SpiderTrials(needed),
            budget,
        });
    }
    let mut presented = fused;
    present(&mut presented, &legs);
    let mut best = canonicalize(&presented);
    if needed > 1 {
        let mut winner = presented.clone();
        while advance(&mut legs) == Odometer::Stepped {
            present(&mut presented, &legs);
            let trial = canonicalize(&presented);
            if trial.form() < best.form() {
                winner.clone_from(&presented);
                best = trial;
            }
        }
        presented = winner;
    }
    Ok(SpiderCanon {
        presented,
        canonicalization: best,
        trials: SpiderTrials(needed),
    })
}

/// Checks that `presented` is `fused` with the legs of its spiders reordered
/// at most.
///
/// # Specification
/// - ensures: success exactly when the two declare one wire count, carry one
///   boundary, hold one number of generators, and agree at each position: one
///   label, the same ports for a generator that orders them, and the same wires
///   on each side for a spider.
/// - fails: [`SpiderDefect`] naming the first datum that differs.
/// - panics: none.
///
/// # Errors
/// [`SpiderDefect::WireCount`], [`SpiderDefect::Boundary`],
/// [`SpiderDefect::GeneratorCount`] or [`SpiderDefect::Generator`].
///
/// # Adequacy
/// - hypothesis: L3 — the evidence of one input is refused against another
///   input at the generator where their fused forms part.
/// - witness: `normal_form::spider::tests::the_evidence_verifies_against_each_input`
#[spec(ensures: |ref result| result.is_err() || (fused.wire_count() == presented.wire_count()
    && fused.boundary() == presented.boundary() && fused.generators().len() == presented.generators().len()))]
fn check_presentation(
    fused: &Wiring,
    presented: &Wiring,
) -> Result<(), SpiderDefect>
{
    if fused.wire_count() != presented.wire_count() {
        return Err(SpiderDefect::WireCount);
    }
    if fused.boundary() != presented.boundary() {
        return Err(SpiderDefect::Boundary);
    }
    if fused.generators().len() != presented.generators().len() {
        return Err(SpiderDefect::GeneratorCount);
    }
    for (index, (expected, found)) in fused
        .generators()
        .iter()
        .zip(presented.generators())
        .enumerate()
    {
        let agrees = expected.label() == found.label()
            && if role(expected) == Role::Spider {
                sorted(expected.sources()) == sorted(found.sources())
                    && sorted(expected.targets()) == sorted(found.targets())
            }
            else {
                expected.sources() == found.sources() && expected.targets() == found.targets()
            };
        if !agrees {
            return Err(SpiderDefect::Generator {
                at: Edge::from(index),
            });
        }
    }
    Ok(())
}

/// The wires of a port list in ascending order.
///
/// # Specification
/// trivial.
fn sorted(ports: &[Wire]) -> Vec<Wire>
{
    let mut ordered = ports.to_vec();
    ordered.sort_unstable();
    ordered
}

#[cfg(test)]
mod tests;
