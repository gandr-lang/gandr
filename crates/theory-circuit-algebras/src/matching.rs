//! Embedding-based matching, with its convexity check and its certificate
//! reader.
//!
//! # Matching is sub-diagram embedding
//!
//! The substrate's one-sided matcher and two-sided unifier are written against
//! a pattern language whose consumer side is a linear spine. A circuit pattern
//! is neither a spine nor a tree: it may have several roots, reconverge, and
//! hold components with no wire between them. Matching one is therefore a
//! sub-diagram embedding problem. An [`Embedding`] is a monomorphism of
//! diagrams: injective on generators and on wires, and label-, arity-,
//! incidence- and port-order-preserving. Injectivity on wires costs nothing
//! extra: two pattern wires incident to generators cannot share an image
//! without giving it in-degree or out-degree two, which the target's monogamy
//! forbids.
//!
//! # One seed per component
//!
//! The search is wire-driven propagation with one nondeterministic seed per
//! connected component of the pattern, and monogamy makes that sufficient. A
//! wire has at most one producer and at most one consumer, so assigning a
//! pattern wire forces the image of the generator on either side of it; from
//! one seed a whole component is determined with no further choice, and the
//! only branching left is each component's seed image. A component with no
//! generator, a bare wire, is seeded on the target's wires. A completed
//! [`Matching`] reports the steps it consumed, which makes the seed economy
//! observable: [`MatchBudget`] bounds them, and a search that would exceed it
//! declines rather than returning a partial enumeration as a total one.
//!
//! # Convexity: two computed routes
//!
//! A match is convex when no directed path leaves its image and returns to it.
//! The condition is global, so it is checked once per completed candidate,
//! and a candidate it refuses is kept as a [`ConvexityRefusal`] naming the wire
//! the path escapes on, the generator outside the image it runs through, and
//! the wire it re-enters on. The route is computed from the pattern, never
//! taken on a caller's word ([`convexity_warrant`]):
//!
//! - **Discharged** ([`ConvexityWarrant::StronglyConnectedOverAcyclicTarget`]):
//!   a pattern whose every input port reaches every output port is convex at
//!   every match into an acyclic target. Suppose a path leaves the image at an
//!   image output and returns at an image input. An image input is the image of
//!   a declared pattern input: its preimage wire has no producer in the pattern
//!   (else that producer, inside the image, would produce the image wire), and
//!   [`Wiring::assemble`] refuses an undeclared open wire. Dually an image
//!   output is the image of a declared pattern output. Strong connectivity
//!   gives a path from that input to that output inside the image; the two
//!   compose to a directed cycle in the target, which [`Wiring::assemble`]
//!   refuses. The argument holds vacuously when either port list is empty, and
//!   a component with no open port contributes neither an image input nor an
//!   image output.
//! - **Swept** ([`ConvexityWarrant::SweptOverTheComplement`]): a directed
//!   reachability walk from every image output through every target generator
//!   outside the image. Nothing is removed from the target first, so the
//!   verdict is convexity of the diagram as given.
//!
//! The discharge is audited rather than asserted: [`embeddings_by_sweep`]
//! sweeps unconditionally, and its agreement with the discharge is a
//! differential the tests run.
//!
//! # A verdict does not travel
//!
//! Convexity is violated by the existence of a path, and re-closing a cut-open
//! diagram only adds edges, so a verdict on the cut-open form says nothing
//! about the re-closed one. Two placements keep it from being read there. A
//! re-closed body is cyclic, and [`Wiring::assemble`] refuses it, so it is
//! never a target. And a verdict is computed per target: [`Matching`] and
//! [`ConvexityRefusal`] have no constructor outside this crate, and an
//! [`Embedding`] claimed from outside carries no verdict — [`Embedding::check`]
//! sweeps the target it is given.
//!
//! # Certificates
//!
//! An [`Embedding`] is evidence its consumer refutes rather than its producer
//! asserts. [`Embedding::check`] re-derives every conjunct the search promises
//! from the two diagrams and the certificate alone, and refuses a forgery at
//! the first conjunct it fails with an [`EmbeddingObstruction`] naming the
//! locus. [`Matching::ambiguity`] reports where several admitted readings of
//! one pattern diverge.
//!
//! # What this module does not do
//!
//! It fires nothing and rewrites nothing, enumerates no overlaps and runs no
//! completion: those are the rewriting engines', over whatever alphabet they
//! are given. No engine depends on this crate; a matcher reaches an engine
//! only through a seam supplied where the engine is instantiated.

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::interface::ComponentIndex;
use crate::interface::Edge;
use crate::interface::EdgeCount;
use crate::interface::PairCount;
use crate::interface::PartialBijection;
use crate::interface::Seam;
use crate::interface::Wire;
use crate::interface::WireCount;
use crate::interface::Wiring;

wrapper! {
    /// How many search steps an embedding search may take. A step is one
    /// pending assignment resolved: a generator paired with a candidate, or a
    /// wire paired with its image.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct MatchBudget(usize);
}

wrapper! {
    /// How many search steps a search consumed.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct SearchSteps(usize);
}

wrapper! {
    /// How many embeddings or refusals a search produced.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct MatchCount(usize);
}

wrapper! {
    /// An index into [`Matching::admitted`]'s enumeration order.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct AdmittedIndex(usize);
}

/// Whether a budget had a step to spend.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Spend
{
    /// One step was spent.
    Spent,
    /// No step was left.
    Exhausted,
}

impl MatchBudget
{
    /// Spends one step.
    ///
    /// # Specification
    /// - ensures: [`Spend::Spent`] and one step fewer when a step is left;
    ///   otherwise [`Spend::Exhausted`] and the budget unchanged.
    /// - panics: none.
    fn spend(&mut self) -> Spend
    {
        match self.0.checked_sub(1) {
            | Some(remaining) => {
                self.0 = remaining;
                Spend::Spent
            },
            | None => Spend::Exhausted,
        }
    }

    /// The steps spent between `start` and this remaining budget.
    ///
    /// # Specification
    /// - requires: this budget is what remains of `start`.
    /// - ensures: `start` less this budget.
    /// - panics: none.
    fn spent_since(
        self,
        start: Self,
    ) -> SearchSteps
    {
        SearchSteps(start.0.saturating_sub(self.0))
    }
}

/// The warrant an embedding's convexity conjunct was granted under.
///
/// The variant names what is checked: one condition on the pattern, strong
/// connectivity, together with the target's acyclicity. It is not
/// left-connectedness, which also asks of a whole rule system that it be
/// left-linear and monogamous acyclic on both sides.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ConvexityWarrant
{
    /// Discharged and never run: the pattern is strongly connected and the
    /// target is acyclic, so no match of it can fail to be convex.
    StronglyConnectedOverAcyclicTarget,
    /// Swept: a directed walk from every image output through every generator
    /// outside the image found no path back to an image input.
    SweptOverTheComplement,
}

/// Whether a pattern is strongly connected: a directed path from every input
/// port to every output port.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Connectivity
{
    /// Every input port reaches every output port.
    StronglyConnected,
    /// One input port does not reach one output port.
    Disconnected
    {
        /// The input port that fails to reach.
        from: Wire,
        /// The output port it does not reach.
        to: Wire,
    },
}

quenchant_shape::reason_enum! {
    /// Why an embedding images no generator for a pattern position.
    pub mod embedding_image {
        /// The reason the lookup finds no image.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The position is at or past the image's length.
            OutOfRange,
        }
    }
}

/// An embedding of a pattern diagram into a target diagram: the certificate a
/// search issues and [`Embedding::check`] reads.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Embedding
{
    /// Pattern generator to target generator, by pattern position.
    image: Box<[Edge]>,
    /// Pattern wire to target wire: total on the pattern's wires, injective.
    wires: PartialBijection,
    /// The seam datum: the interface's two halves, mapped.
    seam: Seam,
    /// The warrant the convexity conjunct was granted under.
    convexity: ConvexityWarrant,
}

impl Embedding
{
    /// The target generator the pattern generator at `edge` maps to.
    ///
    /// # Specification
    /// - provides: [`embedding_image::Absent::OutOfRange`] when `edge` is at or
    ///   past the image's length.
    /// - panics: none.
    #[inline]
    pub fn image_of(
        &self,
        edge: Edge,
    ) -> Maybe<Edge, embedding_image::Absent>
    {
        match self.image.get(usize::from(edge)) {
            | Some(image) => Maybe::Present(*image),
            | None => Maybe::Absent(embedding_image::Absent::OutOfRange),
        }
    }

    /// The image, in pattern generator order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn image(&self) -> &[Edge]
    {
        &self.image
    }

    /// The wire map: total on the pattern's wires.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn wires(&self) -> &PartialBijection
    {
        &self.wires
    }

    /// The seam datum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn seam(&self) -> &Seam
    {
        &self.seam
    }

    /// The warrant the convexity conjunct was granted under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn convexity(&self) -> ConvexityWarrant
    {
        self.convexity
    }

    /// A claimed embedding: the unchecked constructor a certificate from
    /// outside the search enters by.
    ///
    /// A claim asserts nothing. Whether it holds is [`Embedding::check`]'s
    /// verdict against two named diagrams, never this constructor's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn claim<Image>(
        image: Image,
        wires: PartialBijection,
        seam: Seam,
        convexity: ConvexityWarrant,
    ) -> Self
    where
        Image: Into<Box<[Edge]>>,
    {
        Self {
            image: image.into(),
            wires,
            seam,
            convexity,
        }
    }

    /// Re-checks this certificate against the two diagrams it claims to
    /// relate.
    ///
    /// # Specification
    /// - requires: both diagrams are monogamous, boundary-honest and acyclic,
    ///   which every [`Wiring`] is; the certificate is arbitrary.
    /// - ensures: `Ok` with the certificate's own warrant exactly when the
    ///   certificate is a label-, arity-, incidence- and port-order-preserving
    ///   monomorphism of `pattern` into `target`, total on the pattern's wires
    ///   and on nothing else, whose seam is the wire map's restriction to the
    ///   pattern's interface, whose warrant the pattern earns, and whose image
    ///   is convex in `target`.
    /// - fails: [`EmbeddingObstruction`], the first failed conjunct in the
    ///   order below, naming its locus.
    /// - panics: none.
    /// - intension: the conjuncts are checked in a fixed order — the image's
    ///   length; per pattern generator in order, its claimed image's range,
    ///   label, arity and incidence; generator injectivity, at the first
    ///   colliding pair in pattern order; per pattern wire in order, the wire
    ///   map's totality and range; the map's width; the seam, input half first;
    ///   the warrant; the convexity sweep last. The sweep runs whatever the
    ///   claimed warrant, because the discharge is a producer's economy and
    ///   never a reader's assumption; it runs last because it needs a
    ///   structurally valid image.
    ///
    /// # Errors
    /// - [`EmbeddingObstruction::ImageLength`]: the image has the wrong length.
    /// - [`EmbeddingObstruction::ImageOutOfRange`]: a claimed image is not a
    ///   target generator.
    /// - [`EmbeddingObstruction::LabelMismatch`]: a claimed image carries
    ///   another label.
    /// - [`EmbeddingObstruction::ArityMismatch`]: a claimed image has another
    ///   arity.
    /// - [`EmbeddingObstruction::IncidenceMismatch`]: the wire map disagrees
    ///   with a claimed image's ports.
    /// - [`EmbeddingObstruction::NonInjectiveImage`]: two pattern generators
    ///   claim one target generator.
    /// - [`EmbeddingObstruction::WireUnmapped`]: a pattern wire has no image.
    /// - [`EmbeddingObstruction::WireImageOutOfRange`]: a wire image is not a
    ///   target wire.
    /// - [`EmbeddingObstruction::WireMapOverwide`]: the map assigns wires the
    ///   pattern does not have.
    /// - [`EmbeddingObstruction::SeamMismatch`]: the seam is not the map's
    ///   restriction.
    /// - [`EmbeddingObstruction::UnearnedWarrant`]: the discharge is claimed
    ///   for a pattern that is not strongly connected.
    /// - [`EmbeddingObstruction::NotConvex`]: a directed path leaves the image
    ///   and returns.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every certificate the search issues verifies across
    ///   the multi-output, multi-root, reconvergent, disconnected, bare-wire
    ///   and empty fixtures, and each refusal is separated by one targeted
    ///   corruption of a verifying certificate, asserted by its exact variant
    ///   and payload, so a conjunct dropped from the check fails a test rather
    ///   than accepting. The sweep's refusal is checked against the published
    ///   blocking shape, naming the same path the search names.
    /// - witness: `matching::tests::the_searches_certificates_verify_against_their_own_diagrams`
    /// - witness: `matching::tests::a_certificate_with_a_forged_image_length_is_refused`
    /// - witness: `matching::tests::a_certificate_imaged_outside_the_target_is_refused`
    /// - witness: `matching::tests::a_certificate_with_a_relabelled_image_is_refused`
    /// - witness: `matching::tests::a_certificate_with_an_arity_wrong_image_is_refused`
    /// - witness: `matching::tests::a_certificate_with_a_shifted_wire_map_is_refused`
    /// - witness: `matching::tests::a_certificate_sharing_one_generator_is_refused`
    /// - witness: `matching::tests::a_certificate_leaving_a_wire_unmapped_is_refused`
    /// - witness: `matching::tests::a_certificate_imaging_a_wire_outside_the_target_is_refused`
    /// - witness: `matching::tests::a_certificate_mapping_wires_outside_the_pattern_is_refused`
    /// - witness: `matching::tests::a_certificate_with_a_forged_seam_is_refused`
    /// - witness: `matching::tests::a_certificate_with_an_unearned_warrant_is_refused`
    /// - witness: `matching::tests::a_non_convex_certificate_is_refused_with_the_offending_path`
    #[inline]
    pub fn check(
        &self,
        pattern: &Wiring,
        target: &Wiring,
    ) -> Result<ConvexityWarrant, EmbeddingObstruction>
    {
        let claimed_length = EdgeCount::from(self.image.len());
        if claimed_length != pattern.edge_count() {
            return Err(EmbeddingObstruction::ImageLength {
                expected: pattern.edge_count(),
                claimed: claimed_length,
            });
        }
        let claims = pattern.generators().iter().zip(self.image.iter().copied());
        for (position, (from, claimed)) in claims.enumerate() {
            let at = Edge::from(position);
            let Maybe::Present(onto) = target.generator(claimed)
            else {
                return Err(EmbeddingObstruction::ImageOutOfRange { at, claimed });
            };
            if from.label() != onto.label() {
                return Err(EmbeddingObstruction::LabelMismatch { at, claimed });
            }
            if from.sources().len() != onto.sources().len()
                || from.targets().len() != onto.targets().len()
            {
                return Err(EmbeddingObstruction::ArityMismatch { at, claimed });
            }
            let sources = from.sources().iter().zip(onto.sources());
            let targets = from.targets().iter().zip(onto.targets());
            for (wire, expected) in sources.chain(targets) {
                if self.wires.image_of(*wire) != Maybe::Present(*expected) {
                    return Err(EmbeddingObstruction::IncidenceMismatch {
                        at,
                        wire: *wire,
                        expected: *expected,
                    });
                }
            }
        }
        // economy: pairwise over the image, quadratic in the pattern's
        // generator count; a claimed-image map if patterns grow past rule size.
        for (first, left) in self.image.iter().enumerate() {
            let later = self.image.iter().enumerate().skip(first.saturating_add(1));
            for (second, right) in later {
                if left == right {
                    return Err(EmbeddingObstruction::NonInjectiveImage {
                        first: Edge::from(first),
                        second: Edge::from(second),
                        claimed: *left,
                    });
                }
            }
        }
        for wire in pattern.wire_count().wires() {
            let Maybe::Present(claimed) = self.wires.image_of(wire)
            else {
                return Err(EmbeddingObstruction::WireUnmapped { wire });
            };
            if usize::from(claimed) >= usize::from(target.wire_count()) {
                return Err(EmbeddingObstruction::WireImageOutOfRange { wire, claimed });
            }
        }
        let expected_width = PairCount::from(usize::from(pattern.wire_count()));
        if self.wires.pair_count() != expected_width {
            return Err(EmbeddingObstruction::WireMapOverwide {
                expected: pattern.wire_count(),
                claimed: self.wires.pair_count(),
            });
        }
        let derived = seam_of(pattern, &self.wires);
        if derived.inputs() != self.seam.inputs() {
            return Err(EmbeddingObstruction::SeamMismatch {
                half: SeamHalf::Inputs,
            });
        }
        if derived.outputs() != self.seam.outputs() {
            return Err(EmbeddingObstruction::SeamMismatch {
                half: SeamHalf::Outputs,
            });
        }
        if self.convexity == ConvexityWarrant::StronglyConnectedOverAcyclicTarget {
            let computed = connectivity(pattern);
            if computed != Connectivity::StronglyConnected {
                return Err(EmbeddingObstruction::UnearnedWarrant {
                    connectivity: computed,
                });
            }
        }
        let covered: BTreeSet<Edge> = self.image.iter().copied().collect();
        match sweep(target, &covered) {
            | Sweep::Convex => Ok(self.convexity),
            | Sweep::Escapes(detour) => Err(EmbeddingObstruction::NotConvex {
                escape: detour.escape,
                through: detour.through,
                re_entry: detour.re_entry,
            }),
        }
    }
}

/// A candidate the convexity conjunct refused, with the path that refused it.
///
/// Refusal is data, not a filter: a pattern that embeds structurally and is
/// not convex is the published blocking shape, and a caller that cannot see it
/// cannot tell a pattern that does not fit from one that fits and is illegal.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ConvexityRefusal
{
    /// The image the candidate would have had, in pattern generator order.
    image: Box<[Edge]>,
    /// The wire the path leaves the image on: an image output.
    escape: Wire,
    /// A generator outside the image the path runs through.
    through: Edge,
    /// The wire the path re-enters the image on: an image input.
    re_entry: Wire,
}

impl ConvexityRefusal
{
    /// The image the candidate would have had.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn image(&self) -> &[Edge]
    {
        &self.image
    }

    /// The wire the path leaves the image on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn escape(&self) -> Wire
    {
        self.escape
    }

    /// A generator outside the image the path runs through.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn through(&self) -> Edge
    {
        self.through
    }

    /// The wire the path re-enters the image on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn re_entry(&self) -> Wire
    {
        self.re_entry
    }
}

quenchant_shape::reason_enum! {
    /// Why a search reports no ambiguity.
    pub mod ambiguity {
        /// The reason no divergence is reported.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The search admitted no embedding: the pattern is unmatched.
            Unmatched,
            /// The search admitted exactly one embedding.
            Unique,
        }
    }
}

/// What an embedding search found: what it admitted, what it refused, and
/// what it cost.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Matching
{
    /// The embeddings that cleared the convexity conjunct.
    admitted: Vec<Embedding>,
    /// The candidates the convexity conjunct refused.
    refused: Vec<ConvexityRefusal>,
    /// How many pending assignments the search resolved.
    steps: SearchSteps,
}

impl Matching
{
    /// The embeddings that cleared the convexity conjunct, in enumeration
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn admitted(&self) -> &[Embedding]
    {
        &self.admitted
    }

    /// The candidates the convexity conjunct refused, in enumeration order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn refused(&self) -> &[ConvexityRefusal]
    {
        &self.refused
    }

    /// How many embeddings were admitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn admitted_count(&self) -> MatchCount
    {
        MatchCount(self.admitted.len())
    }

    /// How many candidates were refused.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn refused_count(&self) -> MatchCount
    {
        MatchCount(self.refused.len())
    }

    /// How many search steps the search consumed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn steps(&self) -> SearchSteps
    {
        self.steps
    }

    /// The multi-admission diagnostic: where several admitted readings of one
    /// pattern diverge.
    ///
    /// A consumer choosing one of several admitted embeddings silently would
    /// choose arbitrarily; the diagnostic names where the readings diverge.
    ///
    /// # Specification
    /// - ensures: the admission count and one [`Divergence`] per admitted
    ///   embedding past the first, in enumeration order, each naming the first
    ///   assignment on which that embedding disagrees with the first.
    /// - provides: [`ambiguity::Absent::Unmatched`] when nothing was admitted;
    ///   [`ambiguity::Absent::Unique`] when exactly one embedding was.
    /// - panics: none.
    /// - intension: the discriminator is the first differing generator image in
    ///   pattern position order, or, when every generator image agrees, the
    ///   first differing wire image in pattern wire order. Both orders are the
    ///   enumeration's own, so the report is a function of the [`Matching`]
    ///   alone. The search never admits one assignment twice, so every later
    ///   embedding diverges somewhere.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two absences are separated by a unique and a
    ///   matchless search; the two discriminators by a generator-level and a
    ///   wire-level divergence, and by two orderings of port-free generators;
    ///   the representative, the order and the locus are each pinned exactly.
    /// - witness: `matching::tests::a_unique_or_absent_match_reports_no_ambiguity`
    /// - witness: `matching::tests::a_multi_admission_reports_its_first_divergences_in_order`
    /// - witness: `matching::tests::a_bare_wire_ambiguity_discriminates_on_the_wire`
    /// - witness: `matching::tests::two_orderings_of_port_free_generators_diverge_at_the_first_generator`
    #[inline]
    pub fn ambiguity(&self) -> Maybe<Ambiguity, ambiguity::Absent>
    {
        let Some((representative, rest)) = self.admitted.split_first()
        else {
            return Maybe::Absent(ambiguity::Absent::Unmatched);
        };
        if rest.is_empty() {
            return Maybe::Absent(ambiguity::Absent::Unique);
        }
        let mut divergences: Vec<Divergence> = Vec::with_capacity(rest.len());
        for (offset, variant) in rest.iter().enumerate() {
            if let Maybe::Present(discriminator) = first_discriminator(representative, variant) {
                divergences.push(Divergence {
                    admitted: AdmittedIndex(offset.saturating_add(1)),
                    discriminator,
                });
            }
        }
        Maybe::Present(Ambiguity {
            admissions: self.admitted_count(),
            divergences: divergences.into_boxed_slice(),
        })
    }
}

/// Where a later admitted embedding first disagrees with the first.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Discriminator
{
    /// A pattern generator is imaged differently.
    Generator
    {
        /// The pattern generator whose image differs.
        at: Edge,
        /// The image the first embedding assigns.
        representative: Edge,
        /// The image the diverging embedding assigns.
        variant: Edge,
    },
    /// A pattern wire is imaged differently: necessarily a wire no generator
    /// pins, because agreeing generator images force every port's image.
    Wire
    {
        /// The pattern wire whose image differs.
        wire: Wire,
        /// The image the first embedding assigns.
        representative: Wire,
        /// The image the diverging embedding assigns.
        variant: Wire,
    },
}

/// One later embedding's first difference from the first.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Divergence
{
    /// Which admitted embedding diverges.
    admitted: AdmittedIndex,
    /// Where it first diverges.
    discriminator: Discriminator,
}

impl Divergence
{
    /// Which admitted embedding diverges.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn admitted(&self) -> AdmittedIndex
    {
        self.admitted
    }

    /// Where it first diverges from the first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn discriminator(&self) -> Discriminator
    {
        self.discriminator
    }
}

/// What a multi-admission search found, in enumeration order.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Ambiguity
{
    /// How many embeddings the search admitted.
    admissions: MatchCount,
    /// One first difference per admitted embedding past the first.
    divergences: Box<[Divergence]>,
}

impl Ambiguity
{
    /// How many embeddings the search admitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn admissions(&self) -> MatchCount
    {
        self.admissions
    }

    /// One first difference per admitted embedding past the first, in
    /// enumeration order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn divergences(&self) -> &[Divergence]
    {
        &self.divergences
    }
}

quenchant_shape::reason_enum! {
    /// Why two embeddings have no discriminator.
    mod divergence {
        /// The reason no assignment differs.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The two records agree everywhere.
            Identical,
        }
    }
}

/// The first assignment on which `representative` and `variant` disagree.
///
/// # Specification
/// - ensures: the first generator image, in pattern position order, on which
///   the two differ; failing that, the first wire image in pattern wire order.
/// - provides: [`divergence::Absent::Identical`] when the two agree everywhere,
///   which two distinct admissions of one search never do.
/// - panics: none.
fn first_discriminator(
    representative: &Embedding,
    variant: &Embedding,
) -> Maybe<Discriminator, divergence::Absent>
{
    let images = representative.image.iter().zip(variant.image.iter());
    for (position, (first, other)) in images.enumerate() {
        if first != other {
            return Maybe::Present(Discriminator::Generator {
                at: Edge::from(position),
                representative: *first,
                variant: *other,
            });
        }
    }
    let wires = representative.wires.pairs().zip(variant.wires.pairs());
    for ((wire, first), (_, other)) in wires {
        if first != other {
            return Maybe::Present(Discriminator::Wire {
                wire,
                representative: first,
                variant: other,
            });
        }
    }
    Maybe::Absent(divergence::Absent::Identical)
}

/// A declined embedding search.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MatchObstruction
{
    /// The search reached its budget before enumerating every candidate, so
    /// its result would have been a partial enumeration presented as a total
    /// one.
    BudgetExhausted
    {
        /// How many steps were taken before the budget ran out.
        consumed: SearchSteps,
    },
}

impl core::fmt::Display for MatchObstruction
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
            | Self::BudgetExhausted { .. } => {
                "the search budget ran out before every candidate was enumerated"
            },
        })
    }
}

impl core::error::Error for MatchObstruction
{
}

/// Which half of a seam a refusal concerns.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SeamHalf
{
    /// The input half.
    Inputs,
    /// The output half.
    Outputs,
}

/// A certificate refused by [`Embedding::check`]: the conjunct that failed and
/// the locus that failed it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EmbeddingObstruction
{
    /// The image does not hold one slot per pattern generator.
    ImageLength
    {
        /// How many generators the pattern holds.
        expected: EdgeCount,
        /// How many image slots the certificate claims.
        claimed: EdgeCount,
    },
    /// A claimed image is not a generator of the target.
    ImageOutOfRange
    {
        /// The pattern generator whose image is claimed.
        at: Edge,
        /// The claimed image, which the target does not hold.
        claimed: Edge,
    },
    /// A claimed image carries another label: another name, or the same name
    /// in another role.
    LabelMismatch
    {
        /// The pattern generator whose label is not preserved.
        at: Edge,
        /// The claimed image.
        claimed: Edge,
    },
    /// A claimed image has another arity on one side, under the right label.
    ArityMismatch
    {
        /// The pattern generator whose arity is not preserved.
        at: Edge,
        /// The claimed image.
        claimed: Edge,
    },
    /// The wire map sends a pattern port somewhere other than the claimed
    /// image's port at the same position.
    IncidenceMismatch
    {
        /// The pattern generator whose port is mis-mapped.
        at: Edge,
        /// The pattern port wire whose image is wrong.
        wire: Wire,
        /// Where incidence says the wire must go.
        expected: Wire,
    },
    /// Two pattern generators claim one target generator.
    NonInjectiveImage
    {
        /// The first pattern generator making the claim.
        first: Edge,
        /// The second pattern generator making the same claim.
        second: Edge,
        /// The target generator both claim.
        claimed: Edge,
    },
    /// A pattern wire has no image: possible only for a wire no generator is
    /// incident to, since incidence covers every port.
    WireUnmapped
    {
        /// The pattern wire the map forgets.
        wire: Wire,
    },
    /// A pattern wire is mapped outside the target's wires.
    WireImageOutOfRange
    {
        /// The pattern wire whose image is out of range.
        wire: Wire,
        /// The claimed image.
        claimed: Wire,
    },
    /// The wire map assigns wires the pattern does not have. Two certificates
    /// differing only in such pairs would compare unequal while denoting one
    /// embedding, so the pairs are refused rather than ignored.
    WireMapOverwide
    {
        /// How many wires the pattern declares.
        expected: WireCount,
        /// How many pairs the map carries.
        claimed: PairCount,
    },
    /// The seam is not the wire map's restriction to the pattern's interface.
    /// The seam is derived data, so a disagreement is a forgery.
    SeamMismatch
    {
        /// The half that disagrees first.
        half: SeamHalf,
    },
    /// The certificate claims the discharge for a pattern that is not
    /// strongly connected.
    UnearnedWarrant
    {
        /// The pattern's computed connectivity, naming the unreached port pair.
        connectivity: Connectivity,
    },
    /// The image is not convex in the target.
    NotConvex
    {
        /// The wire the path leaves the image on: an image output.
        escape: Wire,
        /// A generator outside the image the path runs through.
        through: Edge,
        /// The wire the path re-enters the image on: an image input.
        re_entry: Wire,
    },
}

impl core::fmt::Display for EmbeddingObstruction
{
    /// Names the failed conjunct.
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
            | Self::ImageLength { .. } => "the image does not hold one slot per pattern generator",
            | Self::ImageOutOfRange { .. } => "a claimed image is not a generator of the target",
            | Self::LabelMismatch { .. } => "a claimed image carries another label",
            | Self::ArityMismatch { .. } => "a claimed image has another arity",
            | Self::IncidenceMismatch { .. } => {
                "the wire map disagrees with a claimed image's ports"
            },
            | Self::NonInjectiveImage { .. } => "two pattern generators claim one target generator",
            | Self::WireUnmapped { .. } => "a pattern wire has no image",
            | Self::WireImageOutOfRange { .. } => "a pattern wire is mapped outside the target",
            | Self::WireMapOverwide { .. } => {
                "the wire map assigns wires the pattern does not have"
            },
            | Self::SeamMismatch { .. } => "the seam is not the wire map's boundary restriction",
            | Self::UnearnedWarrant { .. } => {
                "the discharge is claimed for a pattern that is not strongly connected"
            },
            | Self::NotConvex { .. } => "a directed path leaves the image and returns to it",
        })
    }
}

impl core::error::Error for EmbeddingObstruction
{
}

/// Whether `pattern` is strongly connected.
///
/// # Specification
/// - ensures: [`Connectivity::StronglyConnected`] exactly when every input port
///   reaches every output port by a directed path, which holds vacuously when
///   either list is empty and reflexively for a port on both lists; otherwise
///   the first unreached pair, inputs outer and outputs inner, each in port
///   order.
/// - panics: none.
/// - intension: one explicit forward walk per input port.
///
/// # Adequacy
/// - hypothesis: L3 — a spine (the input reaches the output), a bare wire (a
///   port reaches itself) and a disconnected pair (the first input misses the
///   second output, named exactly) separate the decision.
/// - witness: `matching::tests::a_spine_pattern_is_strongly_connected`
/// - witness: `matching::tests::a_disconnected_pattern_is_not_strongly_connected`
#[inline]
#[must_use]
pub fn connectivity(pattern: &Wiring) -> Connectivity
{
    for from in pattern.boundary().inputs().iter().copied() {
        let reached = reachable_from(pattern, from);
        for to in pattern.boundary().outputs().iter().copied() {
            if !reached.contains(&to) {
                return Connectivity::Disconnected { from, to };
            }
        }
    }
    Connectivity::StronglyConnected
}

/// The convexity route `pattern` earns.
///
/// # Specification
/// - ensures: [`ConvexityWarrant::StronglyConnectedOverAcyclicTarget`] exactly
///   when `pattern` is strongly connected; otherwise
///   [`ConvexityWarrant::SweptOverTheComplement`]. The target half of the
///   warrant, acyclicity, is an invariant of every [`Wiring`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — wherever the discharge is granted, the sweep run as an
///   external oracle over the same pair admits exactly the same embeddings and
///   refuses none, over the fixtures where the discharge's argument is most
///   likely wrong: a component with no open port, and vacuity on either leg. L3
///   — a disconnected pattern loses the discharge.
/// - witness: `matching::tests::the_discharge_and_the_sweep_agree_where_both_apply`
/// - witness: `matching::tests::a_disconnected_pattern_is_not_strongly_connected`
#[inline]
#[must_use]
pub fn convexity_warrant(pattern: &Wiring) -> ConvexityWarrant
{
    match connectivity(pattern) {
        | Connectivity::StronglyConnected => ConvexityWarrant::StronglyConnectedOverAcyclicTarget,
        | Connectivity::Disconnected { .. } => ConvexityWarrant::SweptOverTheComplement,
    }
}

/// Finds every embedding of `pattern` into `target`, convexity decided by the
/// route the pattern earns.
///
/// # Specification
/// - requires: both diagrams monogamous, boundary-honest and acyclic, which
///   every [`Wiring`] is; all three are premises of the discharge.
/// - ensures: every admitted embedding is a label-, arity-, incidence- and
///   port-order-preserving monomorphism, convex in `target`, carrying the seam
///   its wire map restricts to and the warrant it was granted under; every
///   structurally complete candidate that is not convex is refused with its
///   path rather than dropped; the enumeration is complete; [`Matching::steps`]
///   reports the steps consumed.
/// - fails: [`MatchObstruction::BudgetExhausted`] when the search would exceed
///   `budget`; it declines rather than truncating.
/// - panics: none.
/// - intension: one seed per connected component of the pattern, components
///   seeded in pattern generator order and bare wires after them in wire order;
///   candidates in target generator order, or target wire order for a bare
///   wire; a backtracking stack of explicit frames, so nothing recurses on
///   pattern size. A step is one pending assignment resolved. The multi-root
///   fixture's search costs exactly 24 steps.
///
/// # Errors
/// [`MatchObstruction::BudgetExhausted`] when the budget runs out.
///
/// # Adequacy
/// - hypothesis: L1 — every admitted embedding is re-checked by the certificate
///   reader against its two diagrams. L2 — over the spine reading the
///   cut-anchored embedding agrees with the substrate's one-sided matcher on
///   every row, seam rows included, and both verdicts occur. L3 — the published
///   blocking shape is refused with its exact path and its near-miss admitted;
///   the sweep starts from every image output and follows paths through several
///   outside generators; arity, port order, generator injectivity (with and
///   without ports) and a joining wire each separate a non-embedding; a bare
///   wire and the empty pattern pin the degenerate seeds; the delay fence
///   refuses the re-closed form; the multi-root fixture pins [`SearchSteps`] at
///   24, separating one seed per component from a coarser seed set.
/// - witness: `matching::tests::a_multi_output_pattern_embeds`
/// - witness: `matching::tests::a_multi_root_pattern_embeds`
/// - witness: `matching::tests::a_reconvergent_pattern_embeds`
/// - witness: `matching::tests::a_disconnected_pattern_embeds_component_by_component`
/// - witness: `matching::tests::an_arity_mismatch_under_one_label_is_not_an_embedding`
/// - witness: `matching::tests::port_order_is_preserved_so_a_swapped_target_is_not_a_match`
/// - witness: `matching::tests::two_components_never_claim_one_generator`
/// - witness: `matching::tests::two_port_free_components_never_claim_one_generator`
/// - witness: `matching::tests::a_disconnected_pattern_does_not_match_a_wire_that_joins_it`
/// - witness: `matching::tests::a_cut_open_verdict_does_not_travel_to_the_re_closed_form`
/// - witness: `matching::tests::the_embedding_matcher_agrees_with_the_one_sided_matcher_on_the_spine`
/// - witness: `matching::tests::the_blocking_shape_is_refused_on_the_convexity_conjunct`
/// - witness: `matching::tests::the_sweep_starts_from_every_image_output`
/// - witness: `matching::tests::the_sweep_follows_a_path_through_more_than_one_outside_generator`
/// - witness: `matching::tests::the_same_image_is_admitted_without_the_blocking_generator`
/// - witness: `matching::tests::a_bare_wire_pattern_embeds_on_every_target_wire`
/// - witness: `matching::tests::the_empty_pattern_embeds_exactly_once`
/// - witness: `matching::tests::an_embedding_carries_its_seam_as_a_pair_of_partial_bijections`
/// - witness: `matching::tests::an_exhausted_budget_declines_rather_than_truncating`
/// - witness: `matching::tests::the_searches_certificates_verify_against_their_own_diagrams`
#[inline]
pub fn embeddings(
    pattern: &Wiring,
    target: &Wiring,
    budget: MatchBudget,
) -> Result<Matching, MatchObstruction>
{
    search(pattern, target, budget, convexity_warrant(pattern))
}

/// Finds every embedding, always sweeping: the audit route.
///
/// # Specification
/// - ensures: as [`embeddings`], with every candidate swept and every admitted
///   embedding carrying [`ConvexityWarrant::SweptOverTheComplement`].
/// - fails: as [`embeddings`].
/// - panics: none.
/// - intension: never cheaper than [`embeddings`]; it is the oracle the
///   discharge is measured against, not the route a caller takes.
///
/// # Errors
/// [`MatchObstruction::BudgetExhausted`] when the budget runs out.
///
/// # Adequacy
/// - hypothesis: L2 — the reference the discharge route is compared against
///   wherever the discharge applies; L3 — the delay fence's cut-open witness is
///   admitted by the sweep with no escape.
/// - witness: `matching::tests::the_discharge_and_the_sweep_agree_where_both_apply`
/// - witness: `matching::tests::a_cut_open_verdict_does_not_travel_to_the_re_closed_form`
#[inline]
pub fn embeddings_by_sweep(
    pattern: &Wiring,
    target: &Wiring,
    budget: MatchBudget,
) -> Result<Matching, MatchObstruction>
{
    search(
        pattern,
        target,
        budget,
        ConvexityWarrant::SweptOverTheComplement,
    )
}

/// What one component of the pattern is seeded on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Seed
{
    /// A generator: the candidates are the target's generators.
    Generator(Edge),
    /// A wire incident to no generator: the candidates are the target's wires.
    Wire(Wire),
}

/// One pending assignment propagation has still to resolve.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Pending
{
    /// A pattern generator paired with its candidate image.
    Generator(Edge, Edge),
    /// A pattern wire paired with its candidate image.
    Wire(Wire, Wire),
}

/// How a propagation ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Extension
{
    /// Every forced assignment was consistent.
    Consistent,
    /// A forced assignment contradicted one already made, or has no image in
    /// the target.
    Clash,
    /// The budget ran out mid-propagation.
    Exhausted,
}

/// A partial assignment of the pattern into the target.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Assignment
{
    /// Pattern generator to target generator, by pattern position.
    generators: Vec<Option<Edge>>,
    /// The target generators already claimed, which keeps the generator map
    /// injective.
    claimed: BTreeSet<Edge>,
    /// Pattern wire to target wire, injective by construction.
    wires: PartialBijection,
}

/// One choice point of the backtracking search.
#[derive(Clone, Debug)]
struct Frame
{
    /// The seed this frame chooses an image for, by index.
    component: usize,
    /// The next candidate to try for it.
    next: usize,
    /// The assignment as it stood before this seed.
    state: Assignment,
}

/// The wires forward-reachable from `start`, `start` included.
///
/// # Specification
/// - ensures: the reflexive-transitive closure of `start` under "consumed by a
///   generator that produces".
/// - panics: none.
/// - intension: an explicit frontier bounded by a visited set, so the walk
///   neither recurses nor relies on acyclicity.
fn reachable_from(
    diagram: &Wiring,
    start: Wire,
) -> BTreeSet<Wire>
{
    let mut seen: BTreeSet<Wire> = BTreeSet::new();
    let mut frontier: Vec<Wire> = alloc::vec![start];
    while let Some(wire) = frontier.pop() {
        if !seen.insert(wire) {
            continue;
        }
        let Maybe::Present(edge) = diagram.consumer_of(wire)
        else {
            continue;
        };
        if let Maybe::Present(generator) = diagram.generator(edge) {
            frontier.extend(generator.targets().iter().copied());
        }
    }
    seen
}

/// The pattern's seeds: one per connected component.
///
/// # Specification
/// - ensures: one [`Seed::Generator`] per component holding a generator, naming
///   its lowest-positioned member, in component order; then one [`Seed::Wire`]
///   per wire incident to no generator, in wire order.
/// - panics: none.
fn seeds_of(pattern: &Wiring) -> Vec<Seed>
{
    let components = pattern.components();
    let mut seeds: Vec<Seed> = Vec::with_capacity(usize::from(components.count()));
    for index in 0 .. usize::from(components.count()) {
        if let Maybe::Present(members) = components.members(ComponentIndex::from(index))
            && let Some(first) = members.first()
        {
            seeds.push(Seed::Generator(*first));
        }
    }
    for wire in pattern.wire_count().wires() {
        if matches!(pattern.producer_of(wire), Maybe::Absent(_))
            && matches!(pattern.consumer_of(wire), Maybe::Absent(_))
        {
            seeds.push(Seed::Wire(wire));
        }
    }
    seeds
}

/// Resolves one pending assignment and everything it forces.
///
/// # Specification
/// - ensures: [`Extension::Consistent`] leaves `state` extended with `seed` and
///   every assignment monogamy forces from it; [`Extension::Clash`] and
///   [`Extension::Exhausted`] may leave `state` partially extended, which is
///   why the caller works on a copy.
/// - panics: none.
/// - intension: a worklist taken last in, first out; each resolved item spends
///   one step of `budget`, a repeat of an assignment already made included.
fn extend(
    pattern: &Wiring,
    target: &Wiring,
    state: &mut Assignment,
    seed: Pending,
    budget: &mut MatchBudget,
) -> Extension
{
    let mut queue: Vec<Pending> = alloc::vec![seed];
    while let Some(item) = queue.pop() {
        if budget.spend() == Spend::Exhausted {
            return Extension::Exhausted;
        }
        match item {
            | Pending::Generator(source, image) => {
                let Some(slot) = state.generators.get_mut(usize::from(source))
                else {
                    return Extension::Clash;
                };
                if let Some(bound) = *slot {
                    if bound == image {
                        continue;
                    }
                    return Extension::Clash;
                }
                let (Maybe::Present(from), Maybe::Present(onto)) =
                    (pattern.generator(source), target.generator(image))
                else {
                    return Extension::Clash;
                };
                if from.label() != onto.label()
                    || from.sources().len() != onto.sources().len()
                    || from.targets().len() != onto.targets().len()
                    || !state.claimed.insert(image)
                {
                    return Extension::Clash;
                }
                *slot = Some(image);
                for (wire, onto_wire) in from.sources().iter().zip(onto.sources()) {
                    queue.push(Pending::Wire(*wire, *onto_wire));
                }
                for (wire, onto_wire) in from.targets().iter().zip(onto.targets()) {
                    queue.push(Pending::Wire(*wire, *onto_wire));
                }
            },
            | Pending::Wire(source, image) => {
                if state.wires.extend(source, image).is_err() {
                    return Extension::Clash;
                }
                if let Maybe::Present(producer) = pattern.producer_of(source) {
                    let Maybe::Present(onto) = target.producer_of(image)
                    else {
                        return Extension::Clash;
                    };
                    queue.push(Pending::Generator(producer, onto));
                }
                if let Maybe::Present(consumer) = pattern.consumer_of(source) {
                    let Maybe::Present(onto) = target.consumer_of(image)
                    else {
                        return Extension::Clash;
                    };
                    queue.push(Pending::Generator(consumer, onto));
                }
            },
        }
    }
    Extension::Consistent
}

/// A path that leaves an image and returns to it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Detour
{
    /// The image output the path leaves on.
    escape: Wire,
    /// The generator outside the image the path runs through last.
    through: Edge,
    /// The image input the path returns on.
    re_entry: Wire,
}

/// The convexity sweep's verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sweep
{
    /// No directed path leaves the image and returns.
    Convex,
    /// A path does.
    Escapes(Detour),
}

/// Sweeps `target` for a directed path that leaves `image` and returns to it.
///
/// # Specification
/// - requires: `image` is a set of `target`'s generators.
/// - ensures: [`Sweep::Convex`] exactly when no directed path between two of
///   the image's generators leaves the image; otherwise a path's escape wire,
///   the last generator outside the image it runs through, and its re-entry
///   wire, the image outputs tried in image order.
/// - panics: none.
/// - intension: one forward walk through every generator outside the image,
///   from every image output, sharing one visited set: a wire an earlier walk
///   reached without finding an image input reaches none, so each target wire
///   is visited once per sweep. Nothing is removed from the target first. The
///   walk's refusal to step into the image never fires: a wire the walk reaches
///   whose consumer is in the image is an image input, reported as it is
///   reached.
fn sweep(
    target: &Wiring,
    image: &BTreeSet<Edge>,
) -> Sweep
{
    let mut entries: BTreeSet<Wire> = BTreeSet::new();
    let mut exits: Vec<Wire> = Vec::new();
    for edge in image {
        let Maybe::Present(generator) = target.generator(*edge)
        else {
            continue;
        };
        for wire in generator.sources() {
            match target.producer_of(*wire) {
                | Maybe::Present(producer) if image.contains(&producer) => {},
                | Maybe::Present(_) | Maybe::Absent(_) => {
                    entries.insert(*wire);
                },
            }
        }
        for wire in generator.targets() {
            match target.consumer_of(*wire) {
                | Maybe::Present(consumer) if image.contains(&consumer) => {},
                | Maybe::Present(_) | Maybe::Absent(_) => exits.push(*wire),
            }
        }
    }
    let mut seen: BTreeSet<Wire> = BTreeSet::new();
    let mut frontier: Vec<Wire> = Vec::new();
    for escape in exits {
        frontier.push(escape);
        while let Some(wire) = frontier.pop() {
            if !seen.insert(wire) {
                continue;
            }
            let Maybe::Present(through) = target.consumer_of(wire)
            else {
                continue;
            };
            if image.contains(&through) {
                continue;
            }
            let Maybe::Present(generator) = target.generator(through)
            else {
                continue;
            };
            for next in generator.targets() {
                if entries.contains(next) {
                    return Sweep::Escapes(Detour {
                        escape,
                        through,
                        re_entry: *next,
                    });
                }
                frontier.push(*next);
            }
        }
    }
    Sweep::Convex
}

/// The backtracking enumeration, with the convexity route chosen.
///
/// # Specification
/// - ensures: as [`embeddings`], with `warrant` deciding whether each candidate
///   is swept or discharged.
/// - fails: [`MatchObstruction::BudgetExhausted`].
/// - panics: none.
///
/// # Errors
/// [`MatchObstruction::BudgetExhausted`] when the budget runs out.
fn search(
    pattern: &Wiring,
    target: &Wiring,
    budget: MatchBudget,
    warrant: ConvexityWarrant,
) -> Result<Matching, MatchObstruction>
{
    let seeds = seeds_of(pattern);
    let empty = Assignment {
        generators: alloc::vec![None; usize::from(pattern.edge_count())],
        claimed: BTreeSet::new(),
        wires: PartialBijection::new(),
    };
    let mut remaining = budget;
    let mut completions: Vec<Assignment> = Vec::new();
    if seeds.is_empty() {
        completions.push(empty);
    }
    else {
        let mut frames: Vec<Frame> = alloc::vec![Frame {
            component: 0,
            next: 0,
            state: empty,
        }];
        while let Some(frame) = frames.last_mut() {
            let component = frame.component;
            let candidate = frame.next;
            frame.next = frame.next.saturating_add(1);
            let pending = match seeds.get(component).copied() {
                | Some(Seed::Generator(edge)) if candidate < usize::from(target.edge_count()) => {
                    Pending::Generator(edge, Edge::from(candidate))
                },
                | Some(Seed::Wire(wire)) if candidate < usize::from(target.wire_count()) => {
                    Pending::Wire(wire, Wire::from(candidate))
                },
                | Some(Seed::Generator(_) | Seed::Wire(_)) | None => {
                    frames.pop();
                    continue;
                },
            };
            // economy: one assignment copy per candidate seed; an undo trail if
            // seed fan-out on large targets shows in a profile.
            let mut state = frame.state.clone();
            match extend(pattern, target, &mut state, pending, &mut remaining) {
                | Extension::Exhausted => {
                    return Err(MatchObstruction::BudgetExhausted {
                        consumed: remaining.spent_since(budget),
                    });
                },
                | Extension::Clash => {},
                | Extension::Consistent => {
                    let next = component.saturating_add(1);
                    if next >= seeds.len() {
                        completions.push(state);
                    }
                    else {
                        frames.push(Frame {
                            component: next,
                            next: 0,
                            state,
                        });
                    }
                },
            }
        }
    }
    Ok(admit(
        pattern,
        target,
        completions,
        warrant,
        remaining.spent_since(budget),
    ))
}

/// Turns complete assignments into admitted embeddings and refusals.
///
/// # Specification
/// - requires: each assignment is complete for `pattern`.
/// - ensures: an assignment whose generator map is not total is dropped, as no
///   embedding; one whose image is convex, by the discharge or by the sweep, is
///   admitted with its seam and warrant; one whose image is not is refused with
///   the path.
/// - panics: none.
/// - intension: the totality check never fires for the search above, which
///   assigns every generator of every seeded component; it guards a search that
///   stopped doing so.
fn admit(
    pattern: &Wiring,
    target: &Wiring,
    completions: Vec<Assignment>,
    warrant: ConvexityWarrant,
    steps: SearchSteps,
) -> Matching
{
    let mut admitted: Vec<Embedding> = Vec::new();
    let mut refused: Vec<ConvexityRefusal> = Vec::new();
    for completion in completions {
        let image: Option<Vec<Edge>> = completion.generators.iter().copied().collect();
        let Some(image) = image
        else {
            continue;
        };
        let verdict = match warrant {
            | ConvexityWarrant::StronglyConnectedOverAcyclicTarget => Sweep::Convex,
            | ConvexityWarrant::SweptOverTheComplement => {
                sweep(target, &image.iter().copied().collect())
            },
        };
        match verdict {
            | Sweep::Escapes(detour) => refused.push(ConvexityRefusal {
                image: image.into_boxed_slice(),
                escape: detour.escape,
                through: detour.through,
                re_entry: detour.re_entry,
            }),
            | Sweep::Convex => {
                let seam = seam_of(pattern, &completion.wires);
                admitted.push(Embedding {
                    image: image.into_boxed_slice(),
                    wires: completion.wires,
                    seam,
                    convexity: warrant,
                });
            },
        }
    }
    Matching {
        admitted,
        refused,
        steps,
    }
}

/// The seam datum of a wire map: the pattern's interface, both halves.
///
/// # Specification
/// - ensures: each half carries exactly the pattern's ports of that side the
///   wire map assigns.
/// - panics: none.
fn seam_of(
    pattern: &Wiring,
    wires: &PartialBijection,
) -> Seam
{
    Seam::new(
        wires.restricted_to(pattern.boundary().inputs()),
        wires.restricted_to(pattern.boundary().outputs()),
    )
}

#[cfg(test)]
mod tests;
