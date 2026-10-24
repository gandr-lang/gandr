//! **Conversion replay**: the kernel's sequential recheck of a conversion
//! engine's trace, under a three-valued verdict.
//!
//! Term conversion with δ-, β- and η-rules is proof search, and a concurrent
//! search is too large to trust. Courant and Leroy instrument their checker to
//! emit a trace of its decisions and recheck the trace sequentially
//! (Nathanaëlle Courant and Xavier Leroy, "A Lazy, Concurrent Convertibility
//! Checker", POPL 2026, §9, `doi:10.1145/3776695`). [`replay()`] is that
//! recheck: the engine's search stays outside the trusted base, and what the
//! kernel trusts is a loop that fires every step itself and reads the trace
//! only where a rule leaves a choice.
//!
//! # What the replay trusts, and what it does not
//!
//! An engine outside the trusted base decides conversion by a concurrent search
//! and records the derivation it found as a sequence of
//! [`ConversionDecision`]s. The replay takes that sequence, the engine's claim
//! and the two sides, and **re-derives the claim one decision at a time**,
//! firing every step itself: a β-step, a δ-step on the constant the trace
//! names, a force, an η-expansion, a decomposition. A decision chooses among
//! the rules a goal admits; it never stands in for one. Nothing else the engine
//! computed is read, so a wrong engine produces a trace that fails to replay
//! rather than a wrong verdict.
//!
//! # Search-free, by expectation
//!
//! Every goal carries the verdict its derivation owes. A convertibility
//! derivation discharges every premise of a decomposition; a refutation names
//! the one premise that fails by a negative subgoal, and the replay checks only
//! that one. A refutation reached through a frozen constant or through the
//! shortcut over two applications of one constant is not authoritative —
//! failing to convert a frozen pair proves nothing about the unfolded one — so
//! those two decisions are refused under a refutation. Where the vocabulary
//! leaves a rule implicit, the replay applies the rule the two shapes force;
//! where the shapes admit a choice, it reads the next decision and applies only
//! that. Nothing is tried and undone.
//!
//! Both sides are first put in weak head form by the reductions that need no
//! choice — β, a forced thunk, a returner met by a bind, an injection met by a
//! case, a lazy pairing met by a projection, an elimination met by a returned
//! endpoint, never a δ-step — a value of a presented type is read by its
//! normal form under the type's rules ([`Unfoldings::presentations`], crate
//! docs § Presented types), and a cong chain whose functions compose to the
//! identity is read as the `return` of its path (§ A cong chain). Then:
//!
//! | goal | what the replay reads |
//! | --- | --- |
//! | any | `ComparedShared` closes it when the sides are α-equal, or alike once each returned endpoint inside them is read (#695), or rigid and α-distinct |
//! | a defined constant at either head | `Unfold` and the reduction naming its side, with `Postpone` before it; `Freeze`; `ConstShortcut` |
//! | a thunk against a thunk or a neutral value | two `Force`s |
//! | a lambda against a neutral computation | `EtaExpand` on the neutral side |
//! | a lazy pairing against a neutral computation | nothing for the η step: both projections of the neutral are compared with the components; under a refutation, `NegativeSubgoal` picks one |
//! | two neutrals over one head whose binds differ | `Reassociate` on a side stacking two binds, else `ReturnEta` on the side one bind short |
//! | anything else | a leaf decides it or a decomposition pushes its premises; under a refutation, `NegativeSubgoal` picks the one premise |
//!
//! The bind row comes before any decomposition of the pair, explicit or
//! implicit: a pair still owing a commuting conversion of `F` is not in the
//! form its positions compare in, so a `Decompose` there refuses, and a
//! refutation through its positions is never reached.
//!
//! A rigid term is built only of formers, variables and constants without a
//! body: nothing in it can reduce, so two α-distinct rigid terms never convert.
//!
//! A decision anchored at [`ReplayNode::Other`] names no constant, which is
//! how persisted evidence carries its dialogues: the wire keeps a decision's
//! kind and side but no identifier. Every constant decision reads its constant
//! off the shapes where an anchored one would name it. An anchor-free
//! `Unfold`, with the reduction naming its side anchor-free too, unfolds the
//! defined constant the side's head holds; a `Freeze` freezes the defined
//! head of the side it names; a `ConstShortcut` takes the head both sides
//! share, and refuses when they differ; a `Postpone` defers to the `Unfold`
//! that follows it, whose opposite side must hold a defined head. A side
//! headed by anything else refuses the decision. Each step is the one an
//! anchored decision would name, since a side has one head, so the trace
//! still chooses only whether, where and how δ fires.
//!
//! **Alternatives.** Persisting the constant's position in every decision
//! widens the evidence wire for a name the term already holds; keeping
//! `Postpone`, `Freeze` and `ConstShortcut` anchored strands every persisted
//! dialogue that compares two applications of one definition, as an
//! associativity law does. **Reversal.** A decision whose constant the shapes
//! do not determine — a rule over two heads at once that names only one —
//! takes the constant's position on the wire.
//!
//! # The lazy product's η
//!
//! A lazy pairing against a neutral computation is the η law of `C & D`
//! (Levy's computation product): the neutral is the pairing of its two
//! projections, so the goal decomposes into each projection of the neutral
//! against the matching component, left first. The two shapes force the rule
//! and nothing in it is chosen, so no decision names it and the vocabulary is
//! unchanged; a refutation names its premise by `NegativeSubgoal`, as any
//! decomposition's does. `Decompose` is refused there, as at the arrow's η, so
//! the step has one trace.
//!
//! **Alternatives.** Reading `EtaExpand` at the step would give that decision
//! a second meaning: its payload names the fresh variable the arrow's η
//! introduces, and the product's η introduces none. A decision of its own
//! would widen the vocabulary the engine and the kernel share by a step with
//! no choice in it. **Reversal.** A second rule the same two shapes admit
//! would make the step a choice, and the choice would take a decision.
//!
//! # The returned endpoint
//!
//! A returned endpoint stands for the value its pure computation returns, and
//! a pure computation returns `v` exactly when it converts with `return v`. A
//! value goal with a returned endpoint on either side is therefore read as the
//! goal between the endpoint's computation and the other side's: the other
//! endpoint's computation, or the `return` of the other value. An elimination
//! that meets a returned endpoint in weak head form runs its computation
//! first, `E[c] ⇝ c to x. E[x]`, `E` the whole elimination context up to the
//! nearest bind: the applications and projections past the elimination move
//! under the binder with it, so a bind written over the same call compares
//! with the elimination bind for bind. The shapes force both steps, so no
//! decision names them and the vocabulary is unchanged.
//!
//! [`convert`] fires both steps unread and unfolds no constant: the forced loop
//! stays δ-free. A returned endpoint a mode switch's structural type comparison
//! leaves apart is read rather than compared: [`read_endpoints`] normalizes it
//! by the kernel's own evaluator, this module's weak head reduction with one
//! δ-step wherever the computation is stuck at a head naming an admitted
//! definition, and the normal forms go back through [`convert_values`], the one
//! conversion. The reading takes no trace: the reduction of one computation to
//! `return v` chooses nothing — β and the forced steps are determined, and a
//! stuck defined head admits exactly its own δ-step — so a trace could only
//! restate the term. That δ-step is the kernel's own, as readmission's
//! unfolding of a crossed definition is.
//!
//! At reflexivity the endpoint's relation to the point is replayed instead:
//! the `here` carries the engine's dialogue for each endpoint, and [`replay()`]
//! runs it with the admitted definitions unfoldable. The engine holds a
//! returned endpoint at the definition it calls, so the dialogue names each
//! δ-step, the ones under a binder that evaluation never reaches among them.
//!
//! **Alternatives.** A reading without δ would leave every endpoint over a
//! named function — `cong(f, p)` for a defined `f`, every law a model proves —
//! apart from its value. A δ rule inside [`convert`] would make the forced loop
//! choose where to unfold, which is the engine's to say. Normalising the
//! endpoint in the producer would make the producer's normaliser trusted
//! computation. **Reversal.** A mode switch whose comparison the reading cannot
//! settle by normalizing one side — two stuck neutrals equal only after
//! unfolding — carries a dialogue as reflexivity does.
//!
//! A bind in an endpoint's computation over a call stuck at a variable or a
//! constant with no body reads through: the computation is pure, so `c to x.
//! k` returns what `k[⟨c⟩/x]` returns. `wind(Loop(x))`, stuck at `wind(x) to
//! n. return S(n)`, reads as `S(⟨wind(x)⟩)`, and the field goal between
//! `⟨wind(x)⟩` and the other side's call is then an endpoint goal of its own.
//! The engine reads each endpoint it delivers this way, and the kernel mirrors
//! the reading by forced replay: [`Replay::whnf`] takes the innermost
//! such bind whose continuation returns, and the next bind out over both when
//! it does not. A continuation stuck at such a bind of its own is read the
//! same way before it is judged: a decoder's arm `el(a) to x. el(b) to y.
//! return ⌜x ⇒ y⌝`, stuck at both calls, reads as `⌜⟨el(a)⟩ ⇒ ⟨el(b)⟩⌝`. The
//! run is deterministic, so no decision names it and the vocabulary is
//! unchanged. It fires only in a goal [`Replay::open_returned`] opened, and in
//! [`Replay::normalize_returned`]: a computation goal of its own may be
//! effectful, and there the two bind laws stay as the dialogue names them. A
//! call a definition heads is not read through; the dialogue unfolds it first,
//! as it does at reflexivity.
//!
//! A bind whose continuation eliminates its own variable at its head is passed
//! over, as part of the call: it is the bind `E[c] ⇝ c to x. E[x]` builds, and
//! run with the call as a returned endpoint it meets that endpoint again and
//! binds the same call, so it never returns. The engine holds such an
//! elimination of a returned endpoint as one neutral, never a bind.
//!
//! **Alternatives.** A delivery word recording each bind the engine read
//! would let the kernel check a named step rather than re-run it; the run
//! costs the continuation's reduction either way, so the word would restate
//! the term. **Reversal.** A reading that chooses — between two binds, or
//! between a continuation's reduction and an unfolding — or an endpoint read
//! inside a computation goal the kernel replays plainly takes a delivery word.
//!
//! # A decode is read as its code
//!
//! A type `El(⟨c⟩)` over a returned code denotes the type whose quote the
//! code's computation returns, so a mode switch's structural comparison sets
//! it aside against a type of another former rather than separating them, and
//! [`read_endpoints`] reads it: the code normalized as an endpoint is, to a
//! quote, and the quoted type compared with the other side by the same walk. A
//! decode over a code stuck on a binder stays a type of its own, a neutral
//! `Element`, compared with another decode by its code. Only value-type
//! decodes are set aside; a computation-type decode compares structurally.
//! [`read_step`] re-derives an open returned code's step the same way, with
//! no trace: a decoder's arm run over a binder to its quote.
//!
//! **Design.** This is the recorded Tarski data universe: the codes are an
//! ordinary datatype, the decoder a function over them, and a decode a type
//! over a code that is a term, so the kernel gains no node and no type that
//! computes by itself. **Alternatives.** A large elimination into `Type`, a
//! `case` with types for arms in the type language and `Element` erased, was
//! declined in #353. A dialogue for an open step would need the engine's code
//! walk to decide returned endpoints under quotes, which it compares by place.
//! **Reversal.** A universe that stops being a data universe; a model needing
//! a computation-type decode read the same way; the engine deciding codes
//! under quotes, at which point an open step carries a dialogue.
//!
//! # A cong chain
//!
//! `cong(f, p)` is the transport of a reflexivity along `p` in a family whose
//! right endpoint moves by `f`; along a stuck path it is stuck, and so is a
//! cong of it. Functoriality, `cong(g, cong(f, p)) = cong(g ∘ f, p)`, and the
//! identity law, `cong(id, p) = p`, are laws of the path type no reduction
//! reaches. [`Replay::fuse`] decides their composite: a chain — a link of that
//! shape, then binds whose continuations are each one link along the path the
//! bind binds — whose composite right endpoint reads, under the family's
//! binder, as that binder is the `return` of the path it starts from. The
//! composite is read by the evaluator's bodies, the admitted definitions the
//! caller hands over, and by the presentations; no rule of the table unfolds,
//! so the forced loop stays δ-free where it compares. The engine reads the same
//! chain before it plans a pair, so no decision names the step.
//!
//! # The kernel's own conversion
//!
//! [`convert`] is the same loop with no trace: each rule the shapes force —
//! weak head reduction, the two forces, both η laws, the two bind laws, a
//! returned endpoint read as its computation, a cong chain read as its path,
//! a decomposition — fires unread, no constant unfolds and no refutation is
//! certified, and one node on both sides closes convertible before its shape
//! is read, as the engine's shared comparison closes it. It is the equality a
//! judgement the kernel decides alone reads, reflexivity's endpoints first,
//! so the kernel admits what the engine's normalizer admits by the same laws
//! without asking an engine for a trace.
//!
//! # Three verdicts
//!
//! [`KernelVerdict::Convertible`] and [`KernelVerdict::NotConvertible`] are
//! certified: the replay re-derived the claim. [`KernelVerdict::Declined`] is
//! neither — the engine declined, the step budget ran out, or the trace did not
//! replay — and a decline is never read as a refutation. A run the engine's
//! schedule starved declines the same way: the kernel has no search of its own
//! to recover with, and a decline costs completeness, never soundness.
//!
//! # The arena is restored
//!
//! The replay mints its reducts in the caller's arena, past the watermark it
//! found there, and truncates back to that watermark before it returns, so the
//! caller's arena holds exactly what it held before.
//!
//! # Totality
//!
//! Every loop is iterative over an explicit stack, and every step the replay
//! takes is charged to a [`ReplayBudget`], so a trace of any length and a term
//! that reduces forever both end in a verdict.
//!
//! A `ComparedShared` met at a decomposable goal closes that goal when it can
//! and otherwise passes to the first premise; the engine emits an agreeing
//! decomposition it settled equal as that one closing, so the two readings
//! coincide.
//!
//! # Codes and static operators
//!
//! The replay closes a comparison of two codes as the untrusted engine's
//! shared comparison does: α-equal codes convert, codes whose quoted types
//! hold nothing that could still unfold are apart, and any other pair is
//! refused rather than guessed at. Rigidity reads through quoted types and the
//! codes they decode, so the engine's verdict of apart is one the kernel
//! reaches in its own terms.
//!
//! A static definition's certificate unfolds one instance of an operator.
//! [`Unfoldable::Operator`] hands the replay the operator's body with its
//! [`ParameterCount`] binders stripped, the innermost binder its last
//! parameter; unfolding a value headed by it instantiates the binders at the
//! side's first arguments, innermost first, each argument shifted past the
//! parameters still standing outside it, and keeps any further applications
//! over the reduct. A body standing at a static spine keeps the spine. An
//! operator short of its arguments has no reduct and refuses as unreadable. A
//! kernel static lambda would turn this δβ into a δ-step followed by a β-rule
//! at values, owing a reduction the kernel otherwise never fires; stripping
//! the binders keeps the substitution the kernel already trusts for
//! computations as the only rewrite. When a static lambda arrives (see
//! `gandr-kernel-term`), the operator unfolding becomes a body unfolding and
//! the weak head form fires static β like the computational one.
//!
//! # Alternatives and reversal
//!
//! **Alternatives.** Running the engine's search inside the kernel would
//! certify by trusting the search. Trusting the engine's verdict would certify
//! nothing. Replaying a refuted decomposition without its negative subgoal
//! means trying every premise, which is search. Memoizing replayed
//! sub-derivations would let a trace refer back to a shared one; the engine
//! emits a derivation shared by two parents once under each, so the trace is
//! the derivation's expansion as a tree and the replay needs no table.
//!
//! **Reversal.** A back-reference decision, with a replay-side table keyed on
//! the goal it names, replaces the expansion once a measured trace of a deeply
//! shared proof outgrows the replay budget. A closing the kernel cannot
//! reproduce, because the engine's structural equality and the kernel's
//! α-equality disagree on a pair, shows up as a refusal on an engine trace and
//! moves the tie-break into the vocabulary.
//!
//! # Laws and evidence
//!
//! The unit and purity specifications, their named witnesses and the
//! goal-refinement composition shape live on [`replay()`]. [`KernelVerdict`]
//! carries the refusal class table and the certified fragment's
//! partial-equivalence scope. The `replay_laws` integration test generates 256
//! recipes, checking each claim twice and in a cloned arena, with exact
//! unit-law goldens and rollback checks.
//!
//! **Property-test dependency.** Dev-only `proptest` uses the workspace's 1.11
//! version range, defaults off and only `std` for generation, shrinking and
//! persistence. It reuses the workspace's runner without expanding the shipped
//! kernel dependencies. The `quickcheck` crate would add a second runner;
//! hand-written enumeration would lose shrinking of generated term recipes.
//! Reconsider on an unmaintained release, a high-risk advisory or a need the
//! existing strategy API cannot express.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;
use core::iter::Peekable;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::conv::Codomains;
use crate::conv::ConversionGoal;
use crate::conv::Convertibility;
use crate::conv::SetAside;
use crate::conv::convert_values;
use crate::conv::equal_values;
use crate::conv::equal_weakened;
use crate::conv::pending_endpoints;
use crate::element_identity::BinderUse;
use crate::encoding::ContentTable;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_comp_type;
use crate::rewrite::shift_computation;
use crate::rewrite::shift_value;
use crate::rewrite::substitute_computation;
use crate::rewrite::substitute_value;
use crate::support::Reaches;
use crate::support::Reads;

/// What the replay reads of a trace identifier: the constant it names, if
/// any. A caller maps its own identifiers into this before replaying.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplayNode
{
    /// The identifier names the constant at this admission position.
    Constant(ConstantIndex),
    /// The identifier names a node the replay does not read.
    Other,
}

/// Whether a constant has a body the replay may unfold.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unfoldable
{
    /// The constant is defined by this closed value.
    Body(ValueId),
    /// The constant is a type operator: a value under `parameters` static
    /// binders, the innermost binder its last parameter, closed beyond them.
    ///
    /// The kernel has no static lambda, so an operator's body is handed over
    /// with its binders stripped, and unfolding it at a static application
    /// instantiates them at the application's arguments: the δβ-step a static
    /// definition's certificate replays.
    Operator
    {
        /// How many static binders the body stands under.
        parameters: ParameterCount,
        /// The body, with its parameters as its innermost free variables.
        body: ValueId,
    },
    /// The constant has no body: an axiom, an atom, or a declaration the
    /// replay was not given.
    Opaque,
}

/// How many static parameters an operator's body stands under.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParameterCount(u32);

impl From<u32> for ParameterCount
{
    /// The parameter count of a raw count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<ParameterCount> for u32
{
    /// The raw count of a parameter count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ParameterCount) -> Self
    {
        count.0
    }
}

/// The definitions a replay may unfold, by admission position, the presented
/// types whose terms it rewrites, and the relations lawful atoms read their
/// identities as.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Unfoldings
{
    /// The unfolding of each constant, at its admission position.
    bodies: Vec<Unfoldable>,
    /// The rules of every presented type the replay's terms may hold.
    presentations: crate::presented::Presentations,
    /// The relation of each lawful atom, at its admission position.
    identities: BTreeMap<ConstantIndex, ValueId>,
}

impl Unfoldings
{
    /// The unfoldings `bodies` lists, the constant at each position defined by
    /// the entry at that position.
    ///
    /// # Specification
    /// - requires: every body is a value in the arena the replay runs in,
    ///   minted below the watermark the replay finds: closed for
    ///   [`Unfoldable::Body`], closed beyond its parameters for
    ///   [`Unfoldable::Operator`].
    /// - ensures: [`Self::unfolding`] answers the entry at a constant's
    ///   position, and [`Unfoldable::Opaque`] past the end.
    /// - provides: the δ- and δβ-rules a replay may fire; a constant left
    ///   opaque is compared by name only.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — provenance and closure require the replay arena,
    ///   which construction does not receive; lookup is the executable observer
    ///   of the transferred vector.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sole surface is the position lookup, separated by
    ///   a listed constant and one past the end.
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    #[inline]
    #[must_use]
    pub fn new(bodies: Vec<Unfoldable>) -> Self
    {
        Self {
            bodies,
            presentations: crate::presented::Presentations::default(),
            identities: BTreeMap::new(),
        }
    }

    /// These unfoldings, the replay rewriting every presented type's terms by
    /// `presentations`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn presenting(
        self,
        presentations: crate::presented::Presentations,
    ) -> Self
    {
        Self {
            presentations,
            ..self
        }
    }

    /// The presented types the replay rewrites by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn presentations(&self) -> &crate::presented::Presentations
    {
        &self.presentations
    }

    /// These unfoldings, the replay reading the identity of every lawful atom
    /// among `entries` through the atom's relation.
    ///
    /// # Specification
    /// - requires: `entries` is the admission log the replay's terms were
    ///   admitted in.
    /// - ensures: [`Self::identity`] answers the relation of each abstract type
    ///   among `entries` whose interface states its law, at its admission
    ///   position, and nothing at any other position.
    /// - provides: where a transport along a lawful atom's evidence reads the
    ///   fibre the relation returns.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause quantifies over every entry of the
    ///   admission log, which a predicate may not iterate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a transport along a lawful atom's evidence into the
    ///   fibre its relation reads as the unit type returns the unit once the
    ///   atom is identified, and sticks before.
    /// - witness: `element_identity::bridge_tests::j_along_a_lawful_atom_s_evidence_into_a_unit_fibre_returns_the_unit_1937`
    #[inline]
    #[must_use]
    pub fn identifying(
        self,
        entries: &crate::env::Entries,
    ) -> Self
    {
        let mut identities = BTreeMap::new();
        for (position, entry) in entries.iter().enumerate() {
            if let gandr_kernel_term::DeclarationContent::AbstractType {
                interface: quenchant_shape::shape::Maybe::Present(interface),
                ..
            } = *entry.content()
                && let quenchant_shape::shape::Maybe::Present(_) = interface.law()
            {
                let _previous =
                    identities.insert(ConstantIndex::from(position), interface.relation());
            }
        }
        Self { identities, ..self }
    }

    /// The relation the lawful atom at `atom` reads its identity as, when it
    /// is identified.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn identity(
        &self,
        atom: ConstantIndex,
    ) -> Option<ValueId>
    {
        self.identities.get(&atom).copied()
    }

    /// How the constant `constant` unfolds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entry at `constant`'s position, or [`Unfoldable::Opaque`]
    ///   when the list does not reach it.
    /// - provides: the δ-rule lookup the replay runs before every unfolding.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::new`].
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    #[spec(ensures: |ret| ret == self.bodies.get(usize::from(constant)).copied().unwrap_or(Unfoldable::Opaque))]
    #[inline]
    #[must_use]
    pub fn unfolding(
        &self,
        constant: ConstantIndex,
    ) -> Unfoldable
    {
        self.bodies
            .get(usize::from(constant))
            .copied()
            .unwrap_or(Unfoldable::Opaque)
    }
}

/// The two sides a replay compares, of one polarity.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplaySides
{
    /// Two values.
    Values(ValueId, ValueId),
    /// Two computations.
    Computations(ComputationId, ComputationId),
}

/// The verdict an engine claims for the trace it hands over.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EngineClaim
{
    /// The engine found a convertibility derivation.
    Convertible,
    /// The engine found a refutation.
    NotConvertible,
    /// The engine reached no verdict.
    Declined,
}

/// The most steps one replay takes before it declines.
///
/// A step is one turn of the replay's goal loop or one weak head reduction
/// step, so the budget bounds both a long trace and a term that reduces
/// forever.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ReplayBudget(u64);

impl ReplayBudget
{
    /// A budget no well-sized conversion exhausts.
    pub const DEFAULT: Self = Self(0x0010_0000);
}

impl Default for ReplayBudget
{
    /// The [`Self::DEFAULT`] budget.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `ret == ReplayBudget::DEFAULT`.
    /// - provides: the budget a caller with no measured bound passes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: accepted, contradicted, and malformed finite traces
    ///   run with the default budget; the numerical default is not pinned.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
    #[spec(ensures: |ret| ret.0 == Self::DEFAULT.0)]
    #[inline]
    fn default() -> Self
    {
        Self::DEFAULT
    }
}

impl From<u64> for ReplayBudget
{
    /// A budget of `steps` steps.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `u64::from(ret) == steps`.
    /// - provides: the budget's construction.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: zero, one, and maximum budgets preserve the admission
    ///   boundary through the public count wrapper.
    /// - witness: `replay::tests::budget_exhaustion_survives_the_counter_ceiling`
    #[spec(ensures: |ret| ret.0 == steps)]
    #[inline]
    fn from(steps: u64) -> Self
    {
        Self(steps)
    }
}

impl From<ReplayBudget> for u64
{
    /// The steps `budget` allows.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: inverse of `ReplayBudget::from`.
    /// - provides: the budget's count.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: zero, one, and maximum budgets preserve the admission
    ///   boundary through the public count wrapper.
    /// - witness: `replay::tests::budget_exhaustion_survives_the_counter_ceiling`
    #[spec(ensures: |ret| ret == budget.0)]
    #[inline]
    fn from(budget: ReplayBudget) -> Self
    {
        budget.0
    }
}

/// Where a decision stands in a trace, counted from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TracePosition(usize);

impl From<usize> for TracePosition
{
    /// The decision at `position`, counted from zero.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `usize::from(ret) == position`.
    /// - provides: the position's construction.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: refusals at positions zero, one, and two retain their
    ///   exact decision index; no larger trace is claimed.
    /// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    #[spec(ensures: |ret| ret.0 == position)]
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<TracePosition> for usize
{
    /// The count `position` carries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: inverse of `TracePosition::from`.
    /// - provides: the position's count.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: consuming a decision at the position ceiling cannot
    ///   wrap its reported index; consuming the end leaves it unchanged.
    /// - witness: `replay::tests::trace_consumption_preserves_the_end_and_position_ceiling`
    #[spec(ensures: |ret| ret == position.0)]
    #[inline]
    fn from(position: TracePosition) -> Self
    {
        position.0
    }
}

/// Why a trace failed to replay.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplayRefusal
{
    /// The trace ended while a goal still needed a decision.
    Exhausted,
    /// Every goal closed with decisions still unread, the first at `at`.
    Leftover
    {
        /// The first unread decision.
        at: TracePosition,
    },
    /// The decision at `at` names a rule the goal it was read at does not
    /// admit.
    Inapplicable
    {
        /// The decision that does not apply.
        at: TracePosition,
    },
    /// The decision at `at` would carry a refutation through a frozen constant
    /// or a shortcut, which proves nothing.
    NonAuthoritative
    {
        /// The decision that cannot refute.
        at: TracePosition,
    },
    /// A goal closed against the verdict its derivation owes.
    Contradicted
    {
        /// The next unread decision when the goal closed.
        at: TracePosition,
    },
    /// A term the replay reached does not resolve in the arena, or is in no
    /// shape a rule reads.
    Unreadable,
}

impl ReplayRefusal
{
    /// What the refusal says of the dialogue: a question with no answer, an
    /// answer outside its question's answers, or a well-posed dialogue that
    /// reaches no verdict or the wrong one.
    ///
    /// # Specification
    /// - ensures: [`RefusalClass::IllFormedQuery`] for
    ///   [`ReplayRefusal::Unreadable`]; [`RefusalClass::ForeignAnswer`] for
    ///   [`ReplayRefusal::Inapplicable`] and
    ///   [`ReplayRefusal::NonAuthoritative`];
    ///   [`RefusalClass::PathDisagreement`] for
    ///   [`ReplayRefusal::Contradicted`], [`ReplayRefusal::Exhausted`] and
    ///   [`ReplayRefusal::Leftover`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one replay input per refusal variant, each reaching
    ///   its variant through the public replay, is classed as the table on
    ///   [`KernelVerdict`] states; moving any variant to another class changes
    ///   a row.
    /// - witness: `tests::replay_laws::every_replay_refusal_carries_its_pinned_class`
    #[spec(ensures: |ret| match self {
        Self::Unreadable => matches!(ret, RefusalClass::IllFormedQuery),
        Self::Inapplicable { .. } | Self::NonAuthoritative { .. } => matches!(ret, RefusalClass::ForeignAnswer),
        Self::Contradicted { .. } | Self::Exhausted | Self::Leftover { .. } => matches!(ret, RefusalClass::PathDisagreement),
    })]
    #[inline]
    #[must_use]
    pub const fn class(self) -> RefusalClass
    {
        match self {
            Self::Unreadable => RefusalClass::IllFormedQuery,
            Self::Inapplicable { .. } | Self::NonAuthoritative { .. } => {
                RefusalClass::ForeignAnswer
            },
            Self::Contradicted { .. } | Self::Exhausted | Self::Leftover { .. } => {
                RefusalClass::PathDisagreement
            },
        }
    }
}

impl fmt::Display for ReplayRefusal
{
    /// The refusal's class, then what the replay met.
    ///
    /// # Specification
    /// - ensures: writes [`ReplayRefusal::class`] first, then the refusal's own
    ///   account, naming the decision's position where the refusal has one.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter owns the emitted text.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ill-formed query and a path disagreement write
    ///   different diagnostics, each led by its class.
    /// - witness: `tests::replay_laws::an_ill_formed_query_and_a_path_disagreement_are_two_diagnostics`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}: ", self.class())?;
        match *self {
            Self::Unreadable => {
                f.write_str("the replay reached a term the arena does not resolve or no rule reads")
            },
            Self::Inapplicable { at } => write!(
                f,
                "decision {} names a rule the goal it is read at does not admit",
                usize::from(at)
            ),
            Self::NonAuthoritative { at } => write!(
                f,
                "decision {} refutes through a frozen constant or a shortcut, which proves \
                 nothing",
                usize::from(at)
            ),
            Self::Contradicted { at } => write!(
                f,
                "a goal closed against the verdict its derivation owes, before decision {}",
                usize::from(at)
            ),
            Self::Exhausted => f.write_str("the trace ended while a goal still needed a decision"),
            Self::Leftover { at } => write!(
                f,
                "every goal closed with decision {} still unread",
                usize::from(at)
            ),
        }
    }
}

/// What a refused trace's refusal says of its dialogue.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RefusalClass
{
    /// A question with no answer: the replay reached a term it cannot read.
    /// Asked, such a query would certify anything, so the replay refuses it
    /// before reading another decision.
    IllFormedQuery,
    /// A recorded answer outside the answers its question admits: a decision
    /// naming a rule the goal does not admit, or a refutation through a frozen
    /// constant or a shortcut.
    ForeignAnswer,
    /// A well-posed dialogue that reaches no verdict or the wrong one: the
    /// trace ran out, ran over, or closed a goal against the verdict it owes.
    PathDisagreement,
}

impl fmt::Display for RefusalClass
{
    /// The class's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::IllFormedQuery => "an ill-formed query",
            Self::ForeignAnswer => "a foreign answer",
            Self::PathDisagreement => "a path disagreement",
        })
    }
}

/// Why the kernel declined a claim.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplayDecline
{
    /// The engine claimed no verdict, so there is nothing to replay.
    EngineDeclined,
    /// The replay's step budget ran out.
    Budget,
    /// A fixpoint without termination evidence stood at its unfolding gate:
    /// conversion never unfolds a partial fixpoint, so it neither converts
    /// nor refutes.
    PartialFixpoint,
    /// The trace did not replay.
    Refused(ReplayRefusal),
}

impl fmt::Display for ReplayDecline
{
    /// Why the kernel declined: no dialogue, the budget, a partial fixpoint,
    /// or the trace's refusal.
    ///
    /// # Specification
    /// - ensures: a refused trace writes its [`ReplayRefusal`]; every other
    ///   decline writes its own account.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter owns the emitted text.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReplayRefusal`]'s display, reached through the
    ///   decline that carries it.
    /// - witness: `tests::replay_laws::an_ill_formed_query_and_a_path_disagreement_are_two_diagnostics`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::EngineDeclined => f.write_str("no dialogue: the engine claimed no verdict"),
            Self::Budget => f.write_str("the replay's step budget ran out before a verdict"),
            Self::PartialFixpoint => {
                f.write_str("a fixpoint without termination evidence stood at its unfolding gate")
            },
            Self::Refused(refusal) => refusal.fmt(f),
        }
    }
}

/// The kernel's verdict on a replayed claim.
///
/// # Specification
/// - provides: two certified verdicts and a decline carrying its reason. For
///   fixed sides, unfoldings and budget, traces carrying the same claim are
///   equivalent evidence only when both replay to a certified verdict. A
///   declining trace is not equivalent to itself: this is a partial
///   equivalence, distinct from this enum's Rust equality. The unit and
///   composition laws quantify over certified verdicts only. Purity also
///   preserves declines, without making them certified evidence.
/// - executable: none — evidence equivalence needs two traces and their replay
///   context, not one stored verdict.
///
/// | Class | Verdict or reason |
/// | --- | --- |
/// | Ill-formed query | `Refused(Unreadable)` |
/// | Foreign answer | `Refused(Inapplicable { at })`, `Refused(NonAuthoritative { at })` |
/// | Path disagreement | `Refused(Contradicted { at })`, `Refused(Exhausted)`, `Refused(Leftover { at })` |
/// | No dialogue | `EngineDeclined` |
/// | Budget | `Budget` |
/// | Partial recursion | `PartialFixpoint` |
/// | Certified negative | `NotConvertible`: an element, never a refusal |
///
/// Refused reasons are [`ReplayRefusal`] variants inside
/// [`ReplayDecline::Refused`], their class [`ReplayRefusal::class`]; every
/// decline is inside [`Self::Declined`].
///
/// # Adequacy
/// - hypothesis: L3 — a pinned table of replay inputs separates every refusal
///   variant; the unit witnesses distinguish both certified answers from
///   disagreement and budget exhaustion.
/// - witness: `tests::replay_laws::every_replay_refusal_carries_its_pinned_class`
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
/// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum KernelVerdict
{
    /// Certified: the replay re-derived convertibility.
    Convertible,
    /// Certified: the replay re-derived a refutation.
    NotConvertible,
    /// No verdict, and no evidence for either.
    Declined(ReplayDecline),
}

/// Replay `trace` against `claim` for the two `sides`, firing every step in
/// `arena` and unfolding only what `unfoldings` defines.
///
/// A trace composes by goal refinement: decisions rewriting a goal precede the
/// rewritten goal's dialogue, and a decomposed pair's dialogue is its first
/// component's then its second's. A leading `ComparedShared` instead closes an
/// alpha-equal pair whole. There is no transitive composite: traces for
/// `a = b` and `b = c` do not supply a trace for `a = c`.
///
/// # Specification
/// - requires: the two sides and every body in `unfoldings` live in `arena`.
/// - ensures: [`KernelVerdict::Convertible`] or
///   [`KernelVerdict::NotConvertible`] exactly when `trace` replays as a
///   derivation of `claim`: every decision applies, in order, to the goal it is
///   read at, every goal closes at the verdict its derivation owes, and no
///   decision is left over. An engine decline answers
///   [`ReplayDecline::EngineDeclined`] without reading the trace; a budget
///   exhausted answers [`ReplayDecline::Budget`]; anything else answers the
///   refusal. `arena` holds what it held on entry.
/// - ensures: unit — on the budget-terminating fragment, the one-decision trace
///   `[ComparedShared]` certifies `Convertible` on alpha-equal sides and
///   `NotConvertible` on rigid alpha-distinct sides, under the matching claim.
///   Weak head reduction precedes that decision; a divergent side declines with
///   [`ReplayDecline::Budget`], even against itself.
/// - ensures: purity — the verdict depends only on the sides' content,
///   unfoldings, claim, trace and budget. Replaying twice or in a cloned arena
///   gives the same verdict and restores the entry watermark on every return.
///   No verdict adds data to the classified object.
/// - ensures: composition — a pair whose components each replay `Convertible`
///   on their own traces replays `Convertible` on the first component's trace
///   followed by the second's; read the other way round, the second's trace
///   answers the first component's goal and is refused as
///   [`ReplayRefusal::Inapplicable`] at its first decision that does not apply
///   there. An alpha-equal pair also closes whole on `[ComparedShared]`,
///   leaving any further decision [`ReplayRefusal::Leftover`].
/// - provides: the certified recheck of an untrusted engine's conversion
///   verdict, search-free and sequential.
/// - fails: never — a refusal is a verdict.
/// - panics: none.
/// - intension: each active replay uses a fresh content table and no memo
///   shared with another call; temporary reducts are discarded.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the rule table's rows, the refusal kinds
///   and the two decline sources, each separated by a hand-written trace that
///   takes it. The traces an engine produces are replayed end to end by that
///   engine's own tests, which sit above this crate. L2/L3 — generated rigid
///   terms, beta redexes, static unfoldings and a divergent term exercise
///   repeat/clone invariance and rollback, with independent unit-law goldens
///   preventing agreement on a constant verdict.
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
/// - witness: `replay::tests::the_replay_reduces_before_it_reads_a_decision`
/// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
/// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
/// - witness: `replay::tests::a_frozen_branch_cannot_carry_a_refutation`
/// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
/// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
/// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
/// - witness: `tests::replay_laws::replay_is_pure_across_repeated_and_cloned_arenas`
/// - witness: `tests::replay_laws::a_pair_replays_as_its_components_traces_in_order`
/// - witness: `replay::tests::engine_decline_and_zero_budget_do_not_read_the_trace`
/// - witness: `replay::tests::reduced_heads_retain_application_and_bind_frames`
// Unit and cross-run purity are witnessed relations, not predicates over one
// result. The executable clause checks their per-call boundary: rollback and
// preservation of the claimed verdict, including the no-dialogue case.
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && match (claim, ret) {
        (EngineClaim::Declined, KernelVerdict::Declined(ReplayDecline::EngineDeclined)) => true,
        (EngineClaim::Declined, _) | (_, KernelVerdict::Declined(ReplayDecline::EngineDeclined)) => false,
        (EngineClaim::Convertible, KernelVerdict::Convertible)
        | (EngineClaim::NotConvertible, KernelVerdict::NotConvertible)
        | (_, KernelVerdict::Declined(ReplayDecline::Refused(_) | ReplayDecline::PartialFixpoint)) => budget.0 > 0,
        (_, KernelVerdict::Declined(ReplayDecline::Budget)) => true,
        _ => false,
    },
)]
#[inline]
#[must_use]
pub fn replay<I>(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    sides: ReplaySides,
    claim: EngineClaim,
    trace: I,
    budget: ReplayBudget,
) -> KernelVerdict
where
    I: IntoIterator<Item = ConversionDecision<ReplayNode>>,
{
    let expect = match claim {
        EngineClaim::Convertible => Expect::Convertible,
        EngineClaim::NotConvertible => Expect::NotConvertible,
        EngineClaim::Declined => return KernelVerdict::Declined(ReplayDecline::EngineDeclined),
    };
    let (left, right) = terms(sides);
    let watermark = arena.watermark();
    let mut run = Replay {
        arena,
        unfoldings,
        evaluator: unfoldings,
        trace: trace.into_iter().peekable(),
        reading: Reading::Recorded,
        position: 0,
        spent: 0,
        budget: u64::from(budget),
        table: ContentTable::new(),
        memo: NullMemo,
    };
    let outcome = run.drive(Goal::premise(Premise { left, right }, expect));
    run.arena.truncate_to(watermark);
    concluded(outcome, expect)
}

/// The kernel's own conversion of two terms: the replay with no trace, every
/// rule the shapes force fired unread.
///
/// The rules that fire are the ones no choice stands behind: weak head
/// reduction, a presented type's terms rewritten to normal form by
/// `unfoldings`' presentations, a cong chain whose functions compose to the
/// identity read as its path, forcing two thunks, η for a lambda against a
/// neutral, the two commuting conversions of `F`, a returned endpoint taken
/// as its computation, and every structural decomposition. No rule of the
/// table unfolds a constant, so a constant is compared by name, and no
/// refutation is certified: a pair this cannot relate declines rather than
/// separating. `unfoldings`' bodies are read only by the kernel's own
/// evaluator, inside the cong chain's reading ([`Replay::fuse`]).
///
/// # Specification
/// - requires: the two sides, and every body in `unfoldings`, live in `arena`.
/// - ensures: [`KernelVerdict::Convertible`] exactly when the forced rules
///   derive the two sides convertible within `budget`; otherwise a
///   [`KernelVerdict::Declined`], never [`KernelVerdict::NotConvertible`].
///   `arena` holds what it held on entry.
/// - provides: the conversion a judgement the kernel decides by itself reads,
///   with no engine to supply a trace: reflexivity's endpoints first of all.
/// - fails: never — a decline is a verdict.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an η-expanded pair, a reassociated pair and a pair apart
///   in one continuation separate a conversion that fires the forced rules from
///   one that compares syntax, and from one that relates everything.
/// - witness: `replay::tests::the_kernel_converts_by_the_forced_rules_alone`
/// - witness: `element_identity::tests::reflexivity_converts_its_endpoints_by_the_laws_of_bind`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && ret != KernelVerdict::NotConvertible,
)]
#[inline]
#[must_use]
pub fn convert(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    sides: ReplaySides,
    budget: ReplayBudget,
) -> KernelVerdict
{
    let (left, right) = terms(sides);
    let watermark = arena.watermark();
    let rules = Unfoldings::default().presenting(unfoldings.presentations().clone());
    let mut run = Replay {
        arena,
        unfoldings: &rules,
        evaluator: unfoldings,
        trace: core::iter::empty().peekable(),
        reading: Reading::Forced,
        position: 0,
        spent: 0,
        budget: u64::from(budget),
        table: ContentTable::new(),
        memo: NullMemo,
    };
    let outcome = run.drive(Goal::premise(Premise { left, right }, Expect::Convertible));
    run.arena.truncate_to(watermark);
    concluded(outcome, Expect::Convertible)
}

/// The kernel's own conversion of two terms with definitions unfolding.
///
/// The forced rules of [`convert`] apply, and at a head naming a definition
/// `unfoldings` holds, the one δ-step it admits, the left side's first.
///
/// This is the conversion an obligation the record decides "by conversion"
/// asks for, where a side runs a definition the other side states by what it
/// computes: a case's loop obligation, whose loop arm may answer with a call
/// at the transported point. Every step, the δ-steps among them, is charged to
/// `budget`, and a run past it is declined as
/// [`ReplayDecline::Budget`], never read as apart.
///
/// # Specification
/// - requires: the two sides, and every body in `unfoldings`, live in `arena`.
/// - ensures: [`KernelVerdict::Convertible`] exactly when the forced rules and
///   the δ-steps derive the two sides convertible within `budget`;
///   [`KernelVerdict::Declined`] with [`ReplayDecline::Budget`] when the run
///   outruns it, and some other decline otherwise; never
///   [`KernelVerdict::NotConvertible`]. `arena` holds what it held on entry.
/// - provides: the conversion a loop obligation is decided by.
/// - fails: never — a decline is a verdict.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a definition run at a head converts with what it computes
///   here and declines under [`convert`], and a definition that unfolds to
///   itself runs past a small budget and is declined as such.
/// - witness: `replay::tests::the_kernel_unfolds_a_defined_head_within_its_budget`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && ret != KernelVerdict::NotConvertible,
)]
#[inline]
#[must_use]
pub fn convert_unfolding(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    sides: ReplaySides,
    budget: ReplayBudget,
) -> KernelVerdict
{
    let (left, right) = terms(sides);
    let watermark = arena.watermark();
    let mut run = Replay {
        arena,
        unfoldings,
        evaluator: unfoldings,
        trace: core::iter::empty().peekable(),
        reading: Reading::Unfolding,
        position: 0,
        spent: 0,
        budget: u64::from(budget),
        table: ContentTable::new(),
        memo: NullMemo,
    };
    let outcome = run.drive(Goal::premise(Premise { left, right }, Expect::Convertible));
    run.arena.truncate_to(watermark);
    concluded(outcome, Expect::Convertible)
}

/// The kernel's own reading of the step `left` to `right`.
///
/// Each side is read as a returned endpoint is: its computation normalized
/// by this module's weak head reduction with one δ-step wherever it sticks
/// at a head naming a definition `unfoldings` holds, and the normal forms
/// converted by the one conversion — two quotes by the structural walk over
/// their types, whose own returned endpoints and decodes are read the same
/// way.
///
/// The reading takes no trace: the reduction of a pure computation to
/// `return v` chooses nothing, so a dialogue could only restate the term.
/// It is the re-derivation of a step that runs a code over a binder to the
/// quote it returns: that quote holds the calls its arms make on the binder,
/// which an engine compares by place and never by what they run to, so no
/// engine dialogue relates the two sides.
///
/// # Specification
/// - requires: the two values, and every body in `unfoldings`, live in `arena`.
/// - ensures: [`KernelVerdict::Convertible`] exactly when [`read_endpoints`]
///   converts the pair within `budget`; otherwise
///   [`ReplayRefusal::Contradicted`] at the empty trace's first position, never
///   [`KernelVerdict::NotConvertible`]: a reading that stops short of a value
///   certifies nothing. `arena` holds what it held on entry.
/// - provides: the readmission's re-derivation of an open returned code's step.
/// - fails: never — a decline is a verdict.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an open decode read through its decoder's arm converts
///   with the quote over the calls the arm makes, and a forged quote stays
///   apart; a reading that compared the two syntactically separates the first.
/// - witness: `replay::tests::a_decode_reads_as_the_quote_its_code_returns`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && ret != KernelVerdict::NotConvertible,
)]
#[inline]
#[must_use]
pub fn read_step(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    left: ValueId,
    right: ValueId,
    budget: ReplayBudget,
) -> KernelVerdict
{
    match read_endpoints(arena, unfoldings, &[SetAside::Values(left, right)], budget) {
        EndpointReading::Converts => KernelVerdict::Convertible,
        EndpointReading::Apart => {
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Contradicted {
                at: TracePosition::default(),
            }))
        },
    }
}

/// What reading a goal's returned endpoints comes to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EndpointReading
{
    /// Every pair converts once its returned endpoints are read.
    Converts,
    /// Some pair stays apart.
    Apart,
}

/// What `pending` comes to once its returned endpoints, decodes and codomains
/// are read: each side of a value pair normalized as
/// [`Replay::normalize_returned`] gives it and the normal forms converted by
/// [`convert_values`], the kernel's one conversion; two normal forms that are
/// both stuck endpoints compared by the structural walk over their
/// computations, whose own set-aside pairs — the endpoints the stuck heads
/// carry, which the evaluator does not run — are read in turn (#698); a
/// decode's code normalized to the quote it returns, and the type it quotes
/// compared with the other side by the same walk; a dependent arrow's codomain
/// compared by that walk with a plain arrow's weakened past the dependent
/// binder (#577).
///
/// # Specification
/// - requires: every pair's values and types, and every body in `unfoldings`,
///   live in `arena`.
/// - ensures: [`EndpointReading::Converts`] exactly when, within `budget`,
///   every value pair's normal forms convert under [`convert_values`] — or,
///   when both are quotes, their quoted types converge under the walk with
///   every pair it sets aside read the same way, or, when both are stuck
///   endpoints, their computations converge the same way — and every decode's
///   code normalizes to a quote whose quoted type converges with the other side
///   the same way, and every dependent codomain converges the same way with its
///   plain codomain weakened by one binder. A normalization that stops short of
///   a value — budget, a partial fixpoint, an unreadable node — leaves its pair
///   apart, and so does a decode whose code reads to no quote and a pair whose
///   normal forms do not convert. `arena` holds what it held on entry.
/// - provides: the checker's reading of a returned endpoint, and of the type a
///   returned code denotes, at a mode switch.
/// - fails: never — a normalization that stops is an apart answer.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` loop over a worklist of set-aside pairs, not
///   recursion.
/// - measure: the budget left. A pair adds to the worklist only after reading a
///   returned code, reading two returned endpoints or weakening a codomain,
///   each of which charges the budget at least one step, and the walk over one
///   type or computation adds finitely many pairs.
///
/// # Adequacy
/// - hypothesis: L3 — an endpoint returning its value through a definition
///   converts, a stuck endpoint converts only with an equal one, and an
///   endpoint returning a different value stays apart; two stuck endpoints
///   carrying endpoints that read alike, one through a definition and one
///   through a β-redex, convert, and stay apart when what they carry reads
///   apart; a decode whose code returns the other side's quote converts, one
///   whose code returns another quote or stays stuck does not; a dependent
///   codomain that ignores its binder converts with the plain one and one that
///   names it does not; the arena's watermark is restored.
/// - witness: `element_identity::tests::a_returned_endpoint_reads_at_a_mode_switch`
/// - witness: `element_identity::tests::a_certificate_with_a_returned_endpoint_decodes_checks_and_replays`
/// - witness: `replay::tests::a_decode_reads_as_the_quote_its_code_returns`
/// - witness: `conv::tests::a_vacuous_dependent_arrow_is_the_plain_arrow_577`
/// - witness: `replay::tests::endpoints_a_stuck_endpoint_carries_are_read_in_turn_698`
#[spec(captures: before = arena.watermark(), ensures: arena.watermark() == before)]
#[must_use]
pub(crate) fn read_endpoints(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    pending: &[SetAside],
    budget: ReplayBudget,
) -> EndpointReading
{
    let watermark = arena.watermark();
    let mut run = Replay {
        arena,
        unfoldings,
        evaluator: unfoldings,
        trace: core::iter::empty().peekable(),
        reading: Reading::Forced,
        position: 0,
        spent: 0,
        budget: u64::from(budget),
        table: ContentTable::new(),
        memo: NullMemo,
    };
    let mut reading = EndpointReading::Converts;
    let mut worklist = pending.to_vec();
    while let Some(set_aside) = worklist.pop() {
        let goal = match set_aside {
            SetAside::Values(left, right) => {
                let (Ok(left_normal), Ok(right_normal)) =
                    (run.normalize_returned(left), run.normalize_returned(right))
                else {
                    reading = EndpointReading::Apart;
                    break;
                };
                if convert_values(
                    run.arena,
                    run.unfoldings.presentations(),
                    left_normal,
                    right_normal,
                ) == Convertibility::Convertible
                {
                    continue;
                }
                match (run.arena.value(left_normal), run.arena.value(right_normal)) {
                    (Some(&Value::Quote(one)), Some(&Value::Quote(other))) => {
                        ConversionGoal::ValueType(one, other)
                    },
                    // The evaluator stops at a stuck head and leaves the
                    // endpoints its arguments carry unrun: compare the heads by
                    // structure and read those endpoints in turn.
                    (Some(&Value::Returned(one)), Some(&Value::Returned(other))) => {
                        ConversionGoal::Computation(one, other)
                    },
                    _ => {
                        reading = EndpointReading::Apart;
                        break;
                    },
                }
            },
            SetAside::Decoded { code, other } => {
                let Ok(normal) = run.normalize_returned(code)
                else {
                    reading = EndpointReading::Apart;
                    break;
                };
                let Some(&Value::Quote(quoted)) = run.arena.value(normal)
                else {
                    reading = EndpointReading::Apart;
                    break;
                };
                ConversionGoal::ValueType(quoted, other)
            },
            SetAside::Codomains(Codomains { dependent, plain }) => {
                let Ok(()) = run.charge()
                else {
                    reading = EndpointReading::Apart;
                    break;
                };
                let weakened = shift_comp_type(
                    run.arena,
                    &mut run.table,
                    &mut run.memo,
                    plain,
                    BinderDepth::NONE,
                    BinderDepth::from(1_u32),
                );
                ConversionGoal::CompType(dependent, weakened)
            },
        };
        if pending_endpoints(
            run.arena,
            run.unfoldings.presentations(),
            goal,
            &mut worklist,
        ) != Convertibility::Convertible
        {
            reading = EndpointReading::Apart;
            break;
        }
    }
    run.arena.truncate_to(watermark);
    reading
}

/// The type the decode of `code` denotes, read as [`read_endpoints`] reads a
/// decode: `code` normalized as [`Replay::normalize_returned`] gives it, and
/// the type its normal form quotes.
///
/// # Specification
/// - requires: `code`, and every body in `unfoldings`, live in `arena`.
/// - ensures: `Some(quoted)` exactly when `code` normalizes within `budget` to
///   a quote of `quoted`, which then lives in `arena` with every node the
///   reading minted for it; `None` otherwise, with `arena` holding what it held
///   on entry.
/// - provides: the check's reading of a decode it must see the head of — the
///   fibre a pair's second component checks at, instantiated at a first
///   component a code calls into (#721) — kept beside the conversion's reading
///   so both read a returned code by the one evaluator.
/// - fails: never — a normalization that stops reads to no type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a decode whose code calls a thunk returning `⌜Unit⌝`
///   reads to the unit type and admits `()`; one whose code returns `⌜Integer⌝`
///   reads to the integers and refuses it.
/// - witness: `check::tests::a_pair_checks_at_a_fibre_decoding_a_call_into_its_first_component_721`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| ret.map_or_else(|| arena.watermark() == before, |quoted| arena.value_type(quoted).is_some()),
)]
#[must_use]
pub(crate) fn read_decode(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    code: ValueId,
    budget: ReplayBudget,
) -> Option<ValueTypeId>
{
    let watermark = arena.watermark();
    let mut run = Replay {
        arena,
        unfoldings,
        evaluator: unfoldings,
        trace: core::iter::empty().peekable(),
        reading: Reading::Forced,
        position: 0,
        spent: 0,
        budget: u64::from(budget),
        table: ContentTable::new(),
        memo: NullMemo,
    };
    if let Ok(normal) = run.normalize_returned(code)
        && let Some(&Value::Quote(quoted)) = run.arena.value(normal)
    {
        return Some(quoted);
    }
    run.arena.truncate_to(watermark);
    None
}

/// The two sides as goal terms.
///
/// # Specification
/// trivial.
const fn terms(sides: ReplaySides) -> (Term, Term)
{
    match sides {
        ReplaySides::Values(left, right) => (Term::Value(left), Term::Value(right)),
        ReplaySides::Computations(left, right) => {
            (Term::Computation(left), Term::Computation(right))
        },
    }
}

/// The verdict a finished run owes `expect`.
///
/// # Specification
/// trivial.
const fn concluded(
    outcome: Result<(), Stop>,
    expect: Expect,
) -> KernelVerdict
{
    match outcome {
        Ok(()) => match expect {
            Expect::Convertible => KernelVerdict::Convertible,
            Expect::NotConvertible => KernelVerdict::NotConvertible,
        },
        Err(Stop::Budget) => KernelVerdict::Declined(ReplayDecline::Budget),
        Err(Stop::PartialFixpoint) => KernelVerdict::Declined(ReplayDecline::PartialFixpoint),
        Err(Stop::Refused(refusal)) => KernelVerdict::Declined(ReplayDecline::Refused(refusal)),
    }
}

/// Why a replay stopped short of a certified verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stop
{
    /// The step budget ran out.
    Budget,
    /// A partial fixpoint stood at its unfolding gate.
    PartialFixpoint,
    /// The trace did not replay.
    Refused(ReplayRefusal),
}

/// One side of a goal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Term
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
}

/// The verdict a goal's derivation owes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Expect
{
    /// The derivation proves the sides convertible.
    Convertible,
    /// The derivation refutes them.
    NotConvertible,
}

/// The constants each side has frozen since its goal's last decomposition.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Frozen
{
    /// The left side's frozen constants.
    left: Vec<ConstantIndex>,
    /// The right side's frozen constants.
    right: Vec<ConstantIndex>,
}

impl Frozen
{
    /// The constants `side` has frozen.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the list [`Self::freeze`] built for `side`.
    /// - provides: the frozen test a head's status reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: a defined head is frozen only on the selected side,
    ///   while an opaque head stays opaque on both sides.
    /// - witness: `replay::tests::frozen_heads_are_side_local_and_opacity_takes_precedence`
    #[spec(ensures: |ret| {
        let selected = match side {
            ConversionSide::Left => &self.left,
            ConversionSide::Right => &self.right,
        };
        ret.len() == selected.len() && core::ptr::eq(ret.as_ptr(), selected.as_ptr())
    })]
    fn side(
        &self,
        side: ConversionSide,
    ) -> &[ConstantIndex]
    {
        match side {
            ConversionSide::Left => &self.left,
            ConversionSide::Right => &self.right,
        }
    }

    /// Freeze `constant` on `side`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `self.side(side)` contains `constant`.
    /// - provides: the effect of a `Freeze` decision.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: freezing either side changes only that side of a
    ///   defined head; freezing an opaque head cannot make it unfoldable. A
    ///   freeze appends, so the predicate reads the side's length and its last
    ///   constant rather than searching it.
    /// - witness: `replay::tests::frozen_heads_are_side_local_and_opacity_takes_precedence`
    #[spec(
        captures: [own_count = self.side(side).len(), other_count = self.side(opposite(side)).len()],
        ensures: self.side(side).len() == own_count.saturating_add(1)
            && self.side(side).last() == Some(&constant)
            && self.side(opposite(side)).len() == other_count,
    )]
    fn freeze(
        &mut self,
        side: ConversionSide,
        constant: ConstantIndex,
    )
    {
        match side {
            ConversionSide::Left => self.left.push(constant),
            ConversionSide::Right => self.right.push(constant),
        }
    }
}

/// Two terms of one polarity, compared.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Premise
{
    /// The left side.
    left: Term,
    /// The right side.
    right: Term,
}

impl Premise
{
    /// Two values.
    ///
    /// # Specification
    /// trivial.
    const fn values(
        left: ValueId,
        right: ValueId,
    ) -> Self
    {
        Self {
            left: Term::Value(left),
            right: Term::Value(right),
        }
    }

    /// Two computations.
    ///
    /// # Specification
    /// trivial.
    const fn computations(
        left: ComputationId,
        right: ComputationId,
    ) -> Self
    {
        Self {
            left: Term::Computation(left),
            right: Term::Computation(right),
        }
    }
}

/// A goal awaiting its derivation.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Goal
{
    /// The left side.
    left: Term,
    /// The right side.
    right: Term,
    /// What each side froze since the goal's last decomposition.
    frozen: Frozen,
    /// The verdict the derivation owes.
    expect: Expect,
    /// How the goal's computations reduce: as returned endpoints' once
    /// [`Replay::open_returned`] has read the goal as their computations.
    reduction: Reduction,
}

/// How a computation reduces to weak head form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reduction
{
    /// By the search-free steps every computation takes.
    Plain,
    /// As a returned endpoint's computation, which is pure: a bind over a
    /// call stuck at a variable or an opaque head also reads as what its
    /// continuation returns with the call as its value ([`Replay::whnf`]).
    Endpoint,
}

/// A bind an endpoint reading tries in [`Replay::whnf`], kept while its
/// continuation reduces.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Attempt
{
    /// The frames outside the bind, innermost last.
    outer: Vec<Frame>,
    /// The call the bind binds: the stuck focus under the frames inside it.
    call: ComputationId,
    /// The bind's continuation.
    body: ComputationId,
    /// What the reduction had come to before the attempt.
    progress: Progress,
}

/// A plain reading [`Replay::whnf`] suspends while the computation of a
/// returned endpoint it met is read as an endpoint.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Suspended
{
    /// What met the endpoint: an elimination over it, or a fixpoint applied to
    /// it.
    elimination: ComputationId,
    /// The endpoint, as the node `elimination` inspects.
    endpoint: ValueId,
    /// The endpoint's computation.
    returned: ComputationId,
    /// The frames outside `elimination`, innermost last.
    frames: Vec<Frame>,
}

impl Goal
{
    /// A fresh goal over `premise`, with nothing frozen.
    ///
    /// # Specification
    /// trivial.
    fn premise(
        premise: Premise,
        expect: Expect,
    ) -> Self
    {
        Self {
            left: premise.left,
            right: premise.right,
            frozen: Frozen::default(),
            expect,
            reduction: Reduction::Plain,
        }
    }

    /// The term on `side`.
    ///
    /// # Specification
    /// trivial.
    const fn side(
        &self,
        side: ConversionSide,
    ) -> Term
    {
        match side {
            ConversionSide::Left => self.left,
            ConversionSide::Right => self.right,
        }
    }

    /// Replace the term on `side` with `term`.
    ///
    /// # Specification
    /// trivial.
    const fn set(
        &mut self,
        side: ConversionSide,
        term: Term,
    )
    {
        match side {
            ConversionSide::Left => self.left = term,
            ConversionSide::Right => self.right = term,
        }
    }
}

/// How a constant at a head may be read on one side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Status
{
    /// It has a body, and the side has not frozen it.
    Defined,
    /// It has a body the side froze.
    Frozen,
    /// It has no body.
    Opaque,
}

/// The head of a neutral term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Head
{
    /// A bound variable.
    Variable(DeBruijnIndex),
    /// A constant, with its status on the side it stands on.
    Constant(ConstantIndex, Status),
}

/// One elimination of a neutral's spine.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Elimination
{
    /// Nominal elimination; the arena node retains its motive and branches.
    DataCase(ComputationId),
    /// Dependent split; the arena node retains its motive and body. Only the
    /// body is compared: the motive is a typing annotation that no reduction
    /// reads.
    SigmaSplit(ComputationId),
    /// Record projection; the arena node retains its exact label.
    RecordProjection(ComputationId),
    /// Tuple projection; the arena node retains its component.
    TupleProjection(ComputationId),
    /// Lazy product projection of this component.
    Project(gandr_kernel_term::Component),
    /// Transport under a neutral path head, retaining its operand.
    Transport(ValueId),
    /// Product transport waiting for a neutral pair operand.
    ProductTransport(ValueId),
    /// A ride along a neutral flow head; the arena node retains its motive
    /// and its value.
    Ride(ComputationId),
    /// A path transport along a neutral path head; the arena node retains
    /// its motive and its value.
    PathTransport(ComputationId),
    /// The head forced.
    Force,
    /// An application to this argument.
    Apply(ValueId),
    /// A bind into this continuation.
    Bind(ComputationId),
    /// A sum case; the arena node retains its branches, none for the empty
    /// sum's elimination.
    Case(ComputationId),
    /// A native List fold's branches; checked element and result annotations
    /// erase.
    ListFold(ComputationId, ComputationId),
    /// A native List case's branches; the checked element annotation erases.
    ListCase(ComputationId, ComputationId),
    /// A static application to this code: the one value elimination.
    StaticApply(ValueId),
    /// A fixpoint applied, past its leading arguments, to the neutral head;
    /// the arena node is the fixpoint applied to those leading arguments, `fix
    /// a₀ … aₖ₋₁`, the fixpoint itself when it has none.
    Fixpoint(ComputationId),
}

/// A side's shape in weak head form.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Shape
{
    /// A unit, literal, pair, injection, lift or code.
    Former,
    /// A thunk of this computation.
    Thunk(ComputationId),
    /// A lambda over this body.
    Lambda(ComputationId),
    /// A lazy pairing of these components.
    With(alloc::boxed::Box<[ComputationId]>),
    /// A fixpoint over this body, standing at no gate, applied to these
    /// leading arguments, first to last.
    Fixpoint(ComputationId, Vec<ValueId>),
    /// A returner of this value.
    Return(ValueId),
    /// A head under its spine, innermost elimination first; a value's spine
    /// holds static applications only.
    Neutral(Head, Vec<Elimination>),
}

/// The rule a goal's two shapes select.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rule
{
    /// A defined constant stands at a head: the trace chooses a δ-rule.
    Constants,
    /// A thunk meets a thunk or a neutral value: both sides are forced.
    Force,
    /// A lambda meets a neutral computation on this side: it is η-expanded.
    Eta(ConversionSide),
    /// A lazy pairing meets a neutral computation on this side: the neutral
    /// is projected on both sides and each projection compared with the
    /// pairing's component.
    ProductEta(ConversionSide),
    /// Neither side admits a choice: a leaf or a decomposition.
    Structural,
}

/// What a structural rule makes of a goal.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Structure
{
    /// The goal closes at this verdict.
    Leaf(Expect),
    /// The goal holds exactly when every premise does; never empty.
    Premises(Vec<Premise>),
}

impl Structure
{
    /// The decomposition into `premises`, a leaf when there are none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Leaf(Convertible)` when `premises` is empty, `Premises`
    ///   otherwise.
    /// - provides: the invariant that a decomposition always has a premise to
    ///   refute through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: empty neutral spines close positively, while ordered
    ///   case and application premises admit only the selected refuting
    ///   subgoal.
    /// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
    #[spec(
        captures: count = premises.len(),
        ensures: |ret| match ret {
            Self::Leaf(Expect::Convertible) => count == 0,
            Self::Premises(ref children) => count > 0 && children.len() == count,
            Self::Leaf(Expect::NotConvertible) => false,
        },
    )]
    fn of(premises: Vec<Premise>) -> Self
    {
        if premises.is_empty() {
            return Self::Leaf(Expect::Convertible);
        }
        Self::Premises(premises)
    }
}

/// What a compared pair closes to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Compared
{
    /// The sides are α-equal.
    Equal,
    /// The sides are rigid and α-distinct.
    Separated,
    /// Neither: the comparison decides nothing.
    Open,
}

/// Whether a term can reduce anywhere inside it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rigidity
{
    /// Built only of formers, variables and constants without a body.
    Rigid,
    /// It holds a thunk, a binder or a defined constant.
    Flexible,
}

/// What a bind's continuation does at its head with the variable it binds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Continuation
{
    /// It eliminates the variable there: the continuation `E[x]` of a bind
    /// that a returned endpoint's elimination was rebuilt into.
    Eliminates,
    /// It returns the variable as it is, `return x`: the η-expansion of `F`
    /// that [`BindRule::ReturnEta`] builds, which reading through only folds
    /// back into the call it expanded.
    Returns,
    /// Anything else.
    Other,
}

/// A constant the trace postponed, awaiting the unfolding on the other side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Postponed
{
    /// No postponement is pending.
    Nothing,
    /// The other side's head constant was postponed.
    Constant(ConstantIndex),
    /// An anchor-free postponement: the unfolding that follows names its
    /// side, and the other side's head, whichever defined constant it holds,
    /// is the one postponed.
    Opposite,
}

/// The next decision, or the trace's end.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Next
{
    /// The decision at the current position.
    Decision(ConversionDecision<ReplayNode>),
    /// The trace is spent.
    End,
}

/// A frame on a computation's head path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Frame
{
    /// An application to this argument.
    Apply(ValueId),
    /// A bind into this continuation.
    Bind(ComputationId),
    /// A projection of this component of a lazy pairing.
    Project(gandr_kernel_term::Component),
}

/// Where a goal's forced one-sided rewrites are read from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// The trace names each one, and a missing or different name refuses.
    Recorded,
    /// Each fires where the shapes force it, reading nothing: the kernel's own
    /// conversion, which has no trace.
    Forced,
    /// As [`Reading::Forced`], and a defined head unfolds by the one δ-step it
    /// admits, the left side's first: the kernel's own conversion where its
    /// evaluator reads definitions, as an obligation decided by conversion
    /// asks ([`convert_unfolding`]).
    Unfolding,
}

/// A one-sided rewrite the shapes force, as the trace names it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Forced
{
    /// One side of a thunk goal forced.
    Force,
    /// The neutral side of a lambda goal applied to a fresh variable.
    Eta(ConversionSide),
    /// The side read as its bind into `return`.
    ReturnEta(ConversionSide),
    /// The two binds nearest the side's head made one.
    Reassociate(ConversionSide),
}

/// Which commuting conversion of `F` two neutral shapes over one head still
/// owe before their spines decompose.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BindRule
{
    /// Neither spine stacks two binds in a row, and neither stops one bind
    /// short of the other: the spines compare position by position.
    Normal,
    /// The side whose spine stacks two binds in a row, the left first.
    Reassociate(ConversionSide),
    /// The side whose spine stops one bind short of the other's.
    ReturnEta(ConversionSide),
}

/// What stands at a fixpoint's unfolding gate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Gate
{
    /// An application to a constructor: the `<` direction at data.
    Constructor,
    /// An application to another canonical value.
    Canonical,
    /// A bind or a projection observing the fixpoint's result: the `>`
    /// direction.
    Observed,
    /// No elimination, or an application to a neutral value.
    Shut,
}

/// Whether a weak head walk reduced anything.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Progress
{
    /// The term was already in weak head form.
    Unchanged,
    /// At least one step fired.
    Reduced,
}

/// What a constants step did to its goal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Flow
{
    /// The goal stays, rewritten.
    Continue,
    /// The goal closed or decomposed.
    Settled,
}

/// The other side.
///
/// # Specification
/// trivial.
const fn opposite(side: ConversionSide) -> ConversionSide
{
    match side {
        ConversionSide::Left => ConversionSide::Right,
        ConversionSide::Right => ConversionSide::Left,
    }
}

/// The refusal for an unreadable term.
///
/// # Specification
/// trivial.
const fn unreadable() -> Stop
{
    Stop::Refused(ReplayRefusal::Unreadable)
}

/// What reading a transport's family as a cong link's gave.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Linked
{
    /// A path type whose carrier and left endpoint ignore the binder: its
    /// right endpoint, under the binder.
    Right(ValueId),
    /// Any other family.
    Other,
}

/// What a cong chain's composite right endpoint reads as.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Composite
{
    /// The variable the family binds: the chain's functions compose to the
    /// identity.
    Bound,
    /// Anything else.
    Other,
}

/// One replay in flight.
struct Replay<'run, I>
where
    I: Iterator<Item = ConversionDecision<ReplayNode>>,
{
    /// The arena reducts are minted in.
    arena: &'run mut TermArena,
    /// The δ-rules the replay may fire.
    unfoldings: &'run Unfoldings,
    /// The bodies the kernel's own evaluator unfolds inside a cong chain's
    /// reading ([`Self::fuse`]): `unfoldings` itself in a recorded replay and
    /// at a mode switch, the admitted definitions in the forced loop, whose
    /// rule table unfolds none.
    evaluator: &'run Unfoldings,
    /// The decisions still unread.
    trace: Peekable<I>,
    /// Whether forced rewrites are read off the trace or fired unread.
    reading: Reading,
    /// The position of the next unread decision.
    position: usize,
    /// The steps taken.
    spent: u64,
    /// The steps allowed.
    budget: u64,
    /// The content table the rewrite machines run against.
    table: ContentTable,
    /// The rewrite memo: off, since nothing here reuses a rewrite.
    memo: NullMemo,
}

impl<I> Replay<'_, I>
where
    I: Iterator<Item = ConversionDecision<ReplayNode>>,
{
    /// Replay the derivation of `root`, then require the trace spent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when every goal closed at its owed verdict and
    ///   no decision is left.
    /// - provides: the replay's driver.
    /// - fails: [`Stop::Budget`] or the first refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Budget`] when the steps run out; [`Stop::Refused`] when the
    /// trace does not replay.
    ///
    /// # Termination
    /// - reason: the `while let Some(goal) = goals.pop()` loop over an explicit
    ///   stack of goals, not recursion.
    /// - measure: the budget left: every goal's settling charges at least one
    ///   step, and the loop stops at the first charge past the budget.
    ///
    /// # Adequacy
    /// - hypothesis: L3: accepted finite traces, leftover decisions,
    ///   contradictory claims, and a diverging term separate the driver
    ///   outcomes; the bound is the charged steps, not elapsed time.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
    /// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
    #[spec(ensures: |ret| match ret {
        Ok(()) => self.trace.size_hint() == (0, Some(0)),
        Err(Stop::Refused(ReplayRefusal::Leftover { at })) => at.0 == self.position && self.trace.size_hint().0 > 0,
        Err(Stop::Budget) => self.spent >= self.budget,
        Err(Stop::Refused(_) | Stop::PartialFixpoint) => true,
    })]
    fn drive(
        &mut self,
        root: Goal,
    ) -> Result<(), Stop>
    {
        let mut goals = Vec::from([root]);
        while let Some(goal) = goals.pop() {
            self.settle(goal, &mut goals)?;
        }
        match self.peek() {
            Next::End => Ok(()),
            Next::Decision(_) => Err(Stop::Refused(ReplayRefusal::Leftover { at: self.at() })),
        }
    }

    /// Replay one goal until it closes or decomposes into `goals`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` when the goal closed at its owed verdict or pushed the
    ///   premises its derivation owes. A value goal with a returned endpoint on
    ///   either side is first read as the goal between computations
    ///   ([`Self::open_returned`]), and each side's weak head form is read
    ///   through the presentations and as a cong chain ([`Self::fuse`]), forced
    ///   steps no decision records. In the forced loop one node on both sides
    ///   closes convertible there.
    /// - provides: one goal's turn through the rule table.
    /// - fails: [`Stop::Budget`] or the first refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::drive`].
    ///
    /// # Termination
    /// - reason: the `loop` below, which rewrites the goal in place, not
    ///   recursion.
    /// - measure: the budget left: every iteration charges one step.
    ///
    /// # Adequacy
    /// - hypothesis: L3: shared comparison, force, eta, and positive or
    ///   negative decomposition preserve the owed verdict of every scheduled
    ///   premise; finite traces and the budget witness do not establish
    ///   completeness of conversion.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
    /// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
    /// - witness: `replay::tests::a_cong_chain_composing_to_the_identity_replays_as_its_path`
    /// - witness: `replay::tests::the_laws_of_bind_replay_by_name`
    #[spec(
        captures: before = (self.spent, goals.len(), goal.expect),
        ensures: |ret| {
            let (spent, previous_goals, owed) = before;
            self.spent >= spent
                && (!matches!(ret, Err(Stop::Budget)) || self.spent >= self.budget)
                && (ret.is_err() || (self.spent > spent && self.spent <= self.budget
                    && goals.get(previous_goals..).is_some_and(|pending| pending.iter().all(|next| next.expect == owed))))
        },
    )]
    fn settle(
        &mut self,
        mut goal: Goal,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        let mut postponed = Postponed::Nothing;
        loop {
            self.charge()?;
            self.open_returned(&mut goal);
            let left = self.whnf(goal.left, goal.reduction)?;
            let right = self.whnf(goal.right, goal.reduction)?;
            goal.left = self.present(left)?;
            goal.right = self.present(right)?;
            goal.left = self.fuse(goal.left)?;
            goal.right = self.fuse(goal.right)?;
            // A presented constructor whose rules rewrite it to one of its
            // returned leaves (`S(P(plus(a, x)))` to `plus(a, x)`) presents as
            // that leaf: read it by its computation, as a goal's returned
            // endpoint is read on entry, before its shape.
            if let (Term::Value(left), Term::Value(right)) = (goal.left, goal.right)
                && [left, right]
                    .into_iter()
                    .any(|side| matches!(self.arena.value(side), Some(&Value::Returned(_))))
            {
                continue;
            }
            // `return (returned c)` against a side that returns nothing yet is
            // `c` itself, as a pure computation returns `v` exactly when it
            // converts with `return v`: a sum whose case answers its summand
            // (`plus(wind(q), Z)` to `return wind(q)`) is read on as the call
            // it returned. Two returns still decompose by their values.
            if let Some((side, computation)) = self.returned_return(&goal) {
                goal.set(side, Term::Computation(computation));
                continue;
            }
            // One node on both sides converts by reflexivity: the forced loop
            // closes it as an engine's shared comparison would, rather than
            // descend into a term its shapes may not read.
            if self.reading != Reading::Recorded && goal.left == goal.right {
                return self.close(goal.expect, Expect::Convertible);
            }
            let left_shape = self.shape(goal.left, &goal.frozen, ConversionSide::Left)?;
            let right_shape = self.shape(goal.right, &goal.frozen, ConversionSide::Right)?;
            let next = self.peek();
            if postponed != Postponed::Nothing
                && !matches!(next, Next::Decision(ConversionDecision::Unfold { .. }))
            {
                return Err(self.refuse(next));
            }
            // Every call of the fragment returns, so an unread one is the
            // continuation it binds: the trace names the side it drops, and a
            // refutation may not leave one standing.
            if self
                .discard(&mut goal, [&left_shape, &right_shape], next)?
                .is_some()
            {
                continue;
            }
            let bind = bind_rule(&left_shape, &right_shape);
            if matches!(next, Next::Decision(ConversionDecision::Decompose)) {
                if !matches!(rule(&left_shape, &right_shape), Rule::Structural)
                    || bind != BindRule::Normal
                {
                    return Err(self.refuse(next));
                }
                return self.structural(&goal, &left_shape, &right_shape, goals);
            }
            if matches!(
                next,
                Next::Decision(ConversionDecision::ComparedShared { .. })
            ) {
                let compared = self.compared(&goal)?;
                match compared {
                    Compared::Equal => {
                        self.take();
                        return self.close(goal.expect, Expect::Convertible);
                    },
                    Compared::Separated => {
                        self.take();
                        return self.close(goal.expect, Expect::NotConvertible);
                    },
                    Compared::Open => {},
                }
            }
            match bind {
                BindRule::Normal => {},
                BindRule::Reassociate(side) => {
                    let held = match side {
                        ConversionSide::Left => &left_shape,
                        ConversionSide::Right => &right_shape,
                    };
                    let Shape::Neutral(_, ref spine) = *held
                    else {
                        return Err(unreadable());
                    };
                    self.reassociate(&mut goal, side, spine)?;
                    continue;
                },
                BindRule::ReturnEta(side) => {
                    self.return_eta(&mut goal, side)?;
                    continue;
                },
            }
            match rule(&left_shape, &right_shape) {
                Rule::Constants if self.reading == Reading::Unfolding => {
                    self.unfold_defined(&mut goal, [&left_shape, &right_shape])?;
                },
                Rule::Constants => {
                    let flow = self.constants(
                        &mut goal,
                        [&left_shape, &right_shape],
                        &mut postponed,
                        goals,
                    )?;
                    if flow == Flow::Settled {
                        return Ok(());
                    }
                },
                Rule::Force => self.force(&mut goal)?,
                Rule::Eta(side) => self.eta(&mut goal, side)?,
                Rule::ProductEta(side) => return self.product_eta(&goal, side, goals),
                Rule::Structural => {
                    return self.structural(&goal, &left_shape, &right_shape, goals);
                },
            }
        }
    }

    /// Read a value goal with a returned endpoint on either side as the goal
    /// between computations: a returned endpoint by its computation, any
    /// other value by its `return`.
    ///
    /// A pure computation returns `v` exactly when it converts with
    /// `return v`, so the rewritten goal owes the verdict the value goal owed,
    /// and no rule leaves a choice: the step is forced, and no decision of the
    /// trace vocabulary records it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a goal between two values, one of them a returned endpoint,
    ///   becomes the goal between two computations, each side its returned
    ///   endpoint's computation or the `return` of its value; every other goal
    ///   is unchanged, and so is the owed verdict.
    /// - provides: the replay's reading of the returned endpoint.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a returned endpoint against its value, against
    ///   another returned endpoint and against a different value separate the
    ///   two rewrites from an untouched goal.
    /// - witness: `element_identity::tests::a_returned_endpoint_replays_as_its_computation`
    #[spec(
        captures: before = (goal.left, goal.right, goal.expect),
        ensures: goal.expect == before.2 && match before {
            (Term::Value(left), Term::Value(right), _)
                if matches!(self.arena.value(left), Some(&Value::Returned(_)))
                    || matches!(self.arena.value(right), Some(&Value::Returned(_))) =>
                matches!((goal.left, goal.right), (Term::Computation(_), Term::Computation(_))),
            _ => goal.left == before.0 && goal.right == before.1,
        },
    )]
    fn open_returned(
        &mut self,
        goal: &mut Goal,
    )
    {
        let (Term::Value(left), Term::Value(right)) = (goal.left, goal.right)
        else {
            return;
        };
        let returned = |arena: &TermArena, value| match arena.value(value) {
            Some(&Value::Returned(computation)) => Some(computation),
            _ => None,
        };
        if returned(self.arena, left).is_none() && returned(self.arena, right).is_none() {
            return;
        }
        for (side, value) in [(ConversionSide::Left, left), (ConversionSide::Right, right)] {
            let computation = match returned(self.arena, value) {
                Some(computation) => computation,
                None => self.arena.computation_return(value),
            };
            goal.set(side, Term::Computation(computation));
        }
        goal.reduction = Reduction::Endpoint;
    }

    /// The side of a computation goal that returns a returned endpoint while
    /// the other side returns nothing yet, with that endpoint's computation.
    ///
    /// `return (returned c)` converts with `c`, as a pure computation returns
    /// `v` exactly when it converts with `return v`; reading it so is forced,
    /// and no decision of the trace vocabulary records it. Two returns are left
    /// to decompose by their values, as the engine's trace does.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some((side, c))` exactly when the goal's `side` is a
    ///   computation `return v` with `v` the returned endpoint of `c`, and the
    ///   other side is a computation that is no `return`, the left side first;
    ///   `None` otherwise.
    /// - provides: the replay's reading of a returned endpoint a computation
    ///   returns.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `return (returned (force f))` converts with `force f`
    ///   on either side and not with `force g`; without this reading the forced
    ///   loop contradicts at its first step.
    /// - witness: `element_identity::tests::a_returned_endpoint_a_computation_returns_replays_as_its_computation`
    #[spec(ensures: |ret| match ret {
        Some((side, computation)) => {
            let (own, other) = match side {
                ConversionSide::Left => (goal.left, goal.right),
                ConversionSide::Right => (goal.right, goal.left),
            };
            matches!(own, Term::Computation(id) if matches!(self.arena.computation(id),
                Some(&Computation::Return(value)) if self.arena.value(value) == Some(&Value::Returned(computation))))
                && matches!(other, Term::Computation(id) if !matches!(self.arena.computation(id), Some(&Computation::Return(_))))
        },
        None => true,
    })]
    fn returned_return(
        &self,
        goal: &Goal,
    ) -> Option<(ConversionSide, ComputationId)>
    {
        let returned = |term: Term| match term {
            Term::Computation(id) => match self.arena.computation(id) {
                Some(&Computation::Return(value)) => match self.arena.value(value) {
                    Some(&Value::Returned(computation)) => Some(Some(computation)),
                    _ => Some(None),
                },
                _ => None,
            },
            Term::Value(_) => Some(None),
        };
        match (returned(goal.left), returned(goal.right)) {
            (Some(Some(computation)), None) => Some((ConversionSide::Left, computation)),
            (None, Some(Some(computation))) => Some((ConversionSide::Right, computation)),
            _ => None,
        }
    }

    /// A value headed by a constructor of a presented type, rewritten to its
    /// normal form once its returned leaves are read; every other term
    /// unchanged.
    ///
    /// The rules are the type's definition, applied by one fixed strategy, and
    /// a returned leaf reads by the kernel's own evaluator, so the step chooses
    /// nothing and no decision of the trace records it. Normalizing at
    /// evaluation instead, so that a presented constructor is never built
    /// unreduced, would let a `case` see a different term in the kernel than
    /// in the producer's evaluator.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`crate::presented::normal_form`] under the unfoldings'
    ///   presentations of what [`Self::read_returned_leaves`] gives a value, a
    ///   computation unchanged; every node the rewriting compared or copied,
    ///   and every step the reading took, charged to the budget.
    /// - provides: the presented half of weak head form, before any rule of the
    ///   table reads a value goal.
    /// - fails: [`Stop::Budget`] when the rewriting outruns the budget; as
    ///   [`Self::read_returned_leaves`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's words convert by their normal forms in
    ///   the forced loop, which compares a free type's constructors as before.
    /// - witness: `presented::tests::the_forced_loop_converts_circle_words_by_their_normal_forms`
    /// - witness: `replay::tests::a_returned_leaf_of_a_presented_term_reads_before_the_rules`
    #[spec(
        captures: before = self.spent,
        ensures: |ret| self.spent >= before
            && (!matches!(term, Term::Computation(_)) || ret == Ok(term))
            && (!matches!(ret, Err(Stop::Budget)) || self.spent >= self.budget),
    )]
    fn present(
        &mut self,
        term: Term,
    ) -> Result<Term, Stop>
    {
        let Term::Value(value) = term
        else {
            return Ok(term);
        };
        let value = self.read_returned_leaves(value)?;
        let mut fuel = RewriteFuel::from(self.budget.saturating_sub(self.spent));
        let before = u64::from(fuel);
        let normal = crate::presented::normal_form(
            self.arena,
            self.unfoldings.presentations(),
            value,
            &mut fuel,
        );
        self.spent = self
            .spent
            .saturating_add(before.saturating_sub(u64::from(fuel)));
        let Ok(normal) = normal
        else {
            self.spent = self.budget;
            return Err(Stop::Budget);
        };
        Ok(Term::Value(normal))
    }

    /// A cong chain whose functions compose to the identity, read as the
    /// `return` of its path; every other term unchanged.
    ///
    /// A **link** is a transport of a reflexivity in a family `y. Path(D, l,
    /// r)` whose carrier and left endpoint never read `y`; a **chain** is a
    /// link along a path `p`, under binds whose continuations are each one
    /// link along the path the bind binds, the family reading no other index.
    /// The chain is the path `p` when its composite right endpoint `rₙ[y :=
    /// … r₁]` reads as `y` — normalized by [`Self::normalize_returned`], the
    /// kernel's own evaluator, and taken to its presented normal form by
    /// [`Self::present`]: transport along `cong(f, p)` is transport along `p`
    /// in the family pulled back along `f`, and a family whose right endpoint
    /// is its binder is the singleton, whose transport of a reflexivity is
    /// the path.
    ///
    /// **Choice.** The chain is read as the engine reads it, by the forced
    /// replay of its composite: the reading chooses nothing — the evaluator
    /// fires the one step each head admits — so no decision of the trace
    /// records it, and the forced loop of [`convert`] reads it as the
    /// recorded one does. **Alternatives.** A decision naming the fusion,
    /// which would restate a reduction the kernel re-derives anyway; fusing to
    /// a composite family rather than to the identity, which needs a family
    /// rebuilt by substitution and compared by its function. **Reversal.** A
    /// fusion whose reading would need a search, or one to a composite other
    /// than the identity, takes a decision of its own.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `return p` when `term` is a computation that is a chain over
    ///   `p` whose composite right endpoint normalizes, within the budget and
    ///   with no refusal, to the family's bound variable; `term` itself
    ///   otherwise, a value among them. Every step of the reading is charged to
    ///   the budget.
    /// - provides: cong fusion to the identity in the replay's weak head form,
    ///   before any rule of the table reads a computation goal.
    /// - fails: [`Stop::Budget`] when the reading outruns the budget.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: the `while let` loop peeling binds and the `for` loop over the
    ///   continuations, not recursion; each normalization is bounded by the
    ///   budget.
    /// - measure: the binds still to peel, then the continuations still to
    ///   compose.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over the presented circle, `run q <- cong(unlooped,
    ///   p); cong(looped, q)` converts with `return p` in the forced loop with
    ///   the two definitions unfoldable, and a chain composing to `looped ∘
    ///   looped` does not.
    /// - witness: `replay::tests::a_cong_chain_composing_to_the_identity_replays_as_its_path`
    #[spec(
        captures: before = self.spent,
        ensures: |ret| self.spent >= before
            && (!matches!(term, Term::Value(_)) || ret == Ok(term))
            && (!matches!(ret, Err(Stop::Budget)) || self.spent >= self.budget),
    )]
    fn fuse(
        &mut self,
        term: Term,
    ) -> Result<Term, Stop>
    {
        let Term::Computation(computation) = term
        else {
            return Ok(term);
        };
        let mut continuations = Vec::new();
        let mut focus = computation;
        while let Some(&Computation::Bind(bound, body)) = self.arena.computation(focus) {
            continuations.push(body);
            focus = bound;
        }
        let Some(&Computation::PathTransport {
            motive,
            path,
            value,
        }) = self.arena.computation(focus)
        else {
            return Ok(term);
        };
        if !matches!(self.arena.value(value), Some(&Value::Here { .. })) {
            return Ok(term);
        }
        let Linked::Right(mut image) = self.link(motive)
        else {
            return Ok(term);
        };
        let bound = DeBruijnIndex::from(0_u32);
        for body in continuations.into_iter().rev() {
            let Some(&Computation::PathTransport {
                motive,
                path: along,
                value,
            }) = self.arena.computation(body)
            else {
                return Ok(term);
            };
            if !matches!(self.arena.value(along), Some(&Value::Variable(index)) if index == bound)
                || !matches!(self.arena.value(value), Some(&Value::Here { .. }))
            {
                return Ok(term);
            }
            // The family reads the path the bind binds only past its own
            // binder: closed off there, it must ignore its innermost index.
            let closed = self.arena.value_unit();
            let probe = crate::rewrite::substitute_value_type(
                self.arena,
                &mut self.table,
                &mut self.memo,
                motive,
                closed,
            );
            if crate::element_identity::binder_use(
                self.arena,
                &mut self.table,
                &mut self.memo,
                crate::element_identity::Family::Type(probe),
            ) == crate::element_identity::BinderUse::Read
            {
                return Ok(term);
            }
            let opened = self.instantiate(body, path);
            let Some(&Computation::PathTransport { motive, .. }) = self.arena.computation(opened)
            else {
                return Ok(term);
            };
            let Linked::Right(right) = self.link(motive)
            else {
                return Ok(term);
            };
            let lifted = shift_value(
                self.arena,
                &mut self.table,
                &mut self.memo,
                right,
                BinderDepth::NONE.deeper(),
                BinderDepth::NONE.deeper(),
            );
            image = substitute_value(self.arena, &mut self.table, &mut self.memo, lifted, image);
        }
        // The composite is read by the evaluator's bodies, the rule table's
        // restored whatever the reading ends in.
        let rules = self.unfoldings;
        self.unfoldings = self.evaluator;
        let read = self.composite(image);
        self.unfoldings = rules;
        match read? {
            Composite::Bound => Ok(Term::Computation(self.arena.computation_return(path))),
            Composite::Other => Ok(term),
        }
    }

    /// What `image`, a cong chain's composite right endpoint under the
    /// family's binder, reads as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Composite::Bound`] exactly when
    ///   [`Self::normalize_returned`] and then [`Self::present`] take `image`
    ///   to the variable the family binds; [`Composite::Other`] for any other
    ///   normal form, and for a reading refused or stopped at a partial
    ///   fixpoint. Every step is charged to the budget.
    /// - provides: the identity test of [`Self::fuse`].
    /// - fails: [`Stop::Budget`] when the reading outruns the budget.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::fuse`].
    /// - witness: `replay::tests::a_cong_chain_composing_to_the_identity_replays_as_its_path`
    #[spec(
        captures: before = self.spent,
        ensures: |ret| self.spent >= before
            && (!matches!(ret, Err(Stop::Budget)) || self.spent >= self.budget),
    )]
    fn composite(
        &mut self,
        image: ValueId,
    ) -> Result<Composite, Stop>
    {
        let read = match self.normalize_returned(image) {
            Ok(read) => read,
            Err(Stop::Budget) => return Err(Stop::Budget),
            Err(Stop::Refused(_) | Stop::PartialFixpoint) => return Ok(Composite::Other),
        };
        let normal = match self.present(Term::Value(read)) {
            Ok(Term::Value(normal)) => normal,
            Err(Stop::Budget) => return Err(Stop::Budget),
            Ok(Term::Computation(_)) | Err(Stop::Refused(_) | Stop::PartialFixpoint) => {
                return Ok(Composite::Other);
            },
        };
        Ok(
            if matches!(self.arena.value(normal), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
            {
                Composite::Bound
            }
            else {
                Composite::Other
            },
        )
    }

    /// `family`, a value type under one binder, read as a link's family.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Linked::Right`] with its right endpoint exactly when
    ///   `family` is a path type whose carrier and left endpoint provably
    ///   ignore its binder; [`Linked::Other`] otherwise.
    /// - provides: the shape every link of [`Self::fuse`]'s chain shares.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::fuse`].
    /// - witness: `replay::tests::a_cong_chain_composing_to_the_identity_replays_as_its_path`
    #[spec(ensures: |ret| match ret {
        Linked::Right(endpoint) => matches!(self.arena.value_type(family), Some(&ValueType::Path { right, .. }) if right == endpoint),
        Linked::Other => true,
    })]
    fn link(
        &mut self,
        family: gandr_kernel_term::ValueTypeId,
    ) -> Linked
    {
        let Some(&ValueType::Path {
            domain,
            left,
            right,
        }) = self.arena.value_type(family)
        else {
            return Linked::Other;
        };
        let ignored = |run: &mut Self, family| {
            crate::element_identity::binder_use(run.arena, &mut run.table, &mut run.memo, family)
                == crate::element_identity::BinderUse::Ignored
        };
        if ignored(self, crate::element_identity::Family::Type(domain))
            && ignored(self, crate::element_identity::Family::Value(left))
        {
            Linked::Right(right)
        }
        else {
            Linked::Other
        }
    }

    /// `value` with every returned endpoint standing as a leaf of its presented
    /// constructor term read by [`Self::normalize_returned`].
    ///
    /// A presented type's normal form reads no definition: [`normal_form`] in
    /// [`crate::presented`] carries every leaf as written. A returned endpoint
    /// standing as a leaf is the one exception, read here before the rules run
    /// so a rewrite a call hides — `S(unturn(n))` once `unturn(n)` returns
    /// `P(n)` — fires. The conversion machine reads the same leaves, held
    /// endpoints it runs as an unheld evaluation would, so both sides rewrite
    /// one term.
    ///
    /// **Choice.** A returned leaf under a presented constructor is read by
    /// forced replay: the kernel's own evaluator, [`Self::normalize_returned`],
    /// re-derives what the endpoint returns by the one step each head admits,
    /// with no search and no decision, budgeted like every normalization.
    /// **Alternatives.** A recorded decision at the leaf's position, which
    /// needs a trace address for a position under a constructor and a rule
    /// that follows it, for no gain in what the kernel trusts. **Reversal.** A
    /// leaf whose reading would need a search, or would outrun the normalizer's
    /// budget, takes the recorded route.
    ///
    /// [`normal_form`]: crate::presented::normal_form
    ///
    /// # Specification
    /// - requires: `value` lives in the arena.
    /// - ensures: `value` itself when it is no constructor of a presented type;
    ///   otherwise its constructor term, flattened through its own
    ///   declaration's constructors, with each leaf that is a returned endpoint
    ///   whose normal form is no returned endpoint replaced by that normal form
    ///   and read again in turn, every constructor whose fields are unchanged
    ///   kept at its own id.
    /// - provides: the leaf half of [`Self::present`].
    /// - fails: as [`Self::normalize_returned`]; [`ReplayRefusal::Unreadable`]
    ///   on a dangling node.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: the `while let` loop over the walk, not recursion.
    /// - measure: the budget left, which every reading charges, then the
    ///   constructor nodes still to visit and rebuild.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `loop(⟨force wound⟩)` over the presented circle, with
    ///   `wound` returning `unloop(base)`, reads as `base` once the leaf is
    ///   read, and the same term over a free circle stays apart from `base`.
    /// - witness: `replay::tests::a_returned_leaf_of_a_presented_term_reads_before_the_rules`
    #[spec(
        captures: before = self.spent,
        ensures: |ret| self.spent >= before
            && ret.as_ref().map_or(true, |read| *read == value || self.arena.value(*read).is_some()),
    )]
    fn read_returned_leaves(
        &mut self,
        value: ValueId,
    ) -> Result<ValueId, Stop>
    {
        /// One step of the walk.
        enum Walk
        {
            /// Read the node at this id.
            Visit(ValueId),
            /// Rebuild the constructor at this id over the fields read last.
            Rebuild(ValueId),
        }
        let Some(&Value::Constructor { datatype, .. }) = self.arena.value(value)
        else {
            return Ok(value);
        };
        let Some(&ValueType::Data {
            declaration: own, ..
        }) = self.arena.value_type(datatype)
        else {
            return Ok(value);
        };
        if self.unfoldings.presentations().presented(own).is_none() {
            return Ok(value);
        }
        let owned = |arena: &TermArena, datatype| {
            matches!(
                arena.value_type(datatype),
                Some(&ValueType::Data { declaration, .. }) if declaration == own
            )
        };
        let mut walk = Vec::from([Walk::Visit(value)]);
        let mut built: Vec<ValueId> = Vec::new();
        while let Some(step) = walk.pop() {
            match step {
                Walk::Visit(id) => match self.arena.value(id) {
                    Some(&Value::Constructor {
                        datatype,
                        ref fields,
                        ..
                    }) if owned(self.arena, datatype) => {
                        walk.push(Walk::Rebuild(id));
                        walk.extend(fields.iter().rev().map(|&field| Walk::Visit(field)));
                    },
                    Some(&Value::Returned(_)) => {
                        let read = self.normalize_returned(id)?;
                        if matches!(self.arena.value(read), Some(&Value::Returned(_))) {
                            built.push(id);
                        }
                        else {
                            walk.push(Walk::Visit(read));
                        }
                    },
                    Some(_) => built.push(id),
                    None => return Err(unreadable()),
                },
                Walk::Rebuild(id) => {
                    let Some(&Value::Constructor {
                        datatype,
                        tag,
                        ref fields,
                    }) = self.arena.value(id)
                    else {
                        return Err(unreadable());
                    };
                    let start = built
                        .len()
                        .checked_sub(fields.len())
                        .ok_or_else(unreadable)?;
                    if built.get(start ..) == Some(fields.as_slice()) {
                        built.truncate(start);
                        built.push(id);
                    }
                    else {
                        let read = built.split_off(start);
                        let rebuilt = self.arena.value_constructor(datatype, tag, read);
                        built.push(rebuilt);
                    }
                },
            }
        }
        built.pop().ok_or_else(unreadable)
    }

    /// Unfold a defined head by the one δ-step it admits, the left side's if
    /// it has one, the right side's otherwise: the constant rule of
    /// [`Reading::Unfolding`], which reads no decision.
    ///
    /// **Choice.** The left side unfolds first and nothing is frozen or
    /// shortcut: a forced conversion takes no decision, so it reads each side
    /// down to a head no definition stands at, and only then compares them by
    /// name or structure. **Alternatives.** Shortcutting two sides headed by
    /// one constant by their spines, which is a choice a trace records, and a
    /// refutation through it is not authoritative. **Reversal.** An obligation
    /// whose sides only meet by a shortcut, and diverge when unfolded, takes a
    /// recorded dialogue.
    ///
    /// # Specification
    /// - requires: `shapes` are the goal's left and right shapes, at least one
    ///   with a defined head.
    /// - ensures: the side whose head is defined, the left one first, replaced
    ///   by its δ-reduct as [`Self::unfold`] gives it; the other side
    ///   unchanged.
    /// - provides: the δ-step of the kernel's unfolding conversion.
    /// - fails: as [`Self::unfold`]; [`ReplayRefusal::Unreadable`] when neither
    ///   shape has a defined head.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a side running a definition at its head unfolds it
    ///   and meets the other side, while the δ-free conversion compares the
    ///   definition's name and declines.
    /// - witness: `replay::tests::the_kernel_unfolds_a_defined_head_within_its_budget`
    #[spec(
        captures: before = (goal.left, goal.right),
        ensures: |ret| ret.is_err() || goal.left != before.0 || goal.right != before.1,
    )]
    fn unfold_defined(
        &mut self,
        goal: &mut Goal,
        shapes: [&Shape; 2],
    ) -> Result<(), Stop>
    {
        let (side, constant) = match shapes {
            [
                &Shape::Neutral(Head::Constant(constant, Status::Defined), _),
                _,
            ] => (ConversionSide::Left, constant),
            [
                _,
                &Shape::Neutral(Head::Constant(constant, Status::Defined), _),
            ] => (ConversionSide::Right, constant),
            _ => return Err(unreadable()),
        };
        self.unfold(goal, side, constant)
    }

    /// The δ-step a reading takes at `term`'s defined head `constant`, with a
    /// recursive definition's own recursion refolded to its name.
    ///
    /// A recursive definition's body is a suspended fixpoint, and its gate
    /// opens it with the fixpoint itself for its recursive calls, so a call
    /// that reads through one level leaves `fix f x` where the source wrote
    /// `f(x)`. The evaluator reads that recursion back as the call its source
    /// wrote. This step unfolds the head to the same fixpoint with its body's
    /// recursion bound to the constant instead — `fix _. b[f ↦ c]` for `fix f.
    /// b` — which opens at the same gate and computes the same value, so a
    /// recursive call `spin(x)` stays the call its source wrote, which
    /// [`Self::shut_recursion`] then reads through. Everywhere else it is
    /// [`Self::unfold_term`]'s step.
    ///
    /// # Specification
    /// - requires: `term`'s head is `constant`, defined.
    /// - ensures: for a computation whose head, under application, bind and
    ///   projection frames, forces `constant`, whose body is a suspended
    ///   fixpoint, the fixpoint refolded — its body opened at the constant and
    ///   weakened past the binder it does not read, its evidence kept — under
    ///   those frames; otherwise [`Self::unfold_term`]'s reduct.
    /// - provides: the δ-step of [`Self::normalize_returned`] and
    ///   [`Self::run_held_operand`].
    /// - fails: as [`Self::unfold_term`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `loop` descending the head path and the `while let` loop
    ///   rebuilding it, not recursion.
    /// - measure: the focus's arena position while descending, then the frames
    ///   left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `spin(S(x)) then spin(a)` against `loop ∷ (spin(x)
    ///   then spin(a))` at the mode switch: unfolded to the bare fixpoint, the
    ///   recursive call reads `fix f x` and the sides stay apart.
    /// - witness: `tests::native_formers::a_recursive_call_stuck_at_a_variable_reads_as_its_call_473`
    #[spec(ensures: |ret| ret.map_or(true, |reduct| matches!((term, reduct), (Term::Value(_), Term::Value(_)) | (Term::Computation(_), Term::Computation(_)))))]
    fn unfold_refolded(
        &mut self,
        term: Term,
        constant: ConstantIndex,
    ) -> Result<Term, Stop>
    {
        let Term::Computation(start) = term
        else {
            return self.unfold_term(term, constant);
        };
        let Unfoldable::Body(body) = self.unfoldings.unfolding(constant)
        else {
            return self.unfold_term(term, constant);
        };
        let Some(&Value::Thunk(suspended)) = self.arena.value(body)
        else {
            return self.unfold_term(term, constant);
        };
        let Some(&Computation::Fixpoint {
            body: open,
            evidence,
        }) = self.arena.computation(suspended)
        else {
            return self.unfold_term(term, constant);
        };
        let mut frames = Vec::new();
        let mut focus = start;
        loop {
            match self.arena.computation(focus) {
                Some(&Computation::Application(function, argument)) => {
                    frames.push(Frame::Apply(argument));
                    focus = function;
                },
                Some(&Computation::Bind(bound, next)) => {
                    frames.push(Frame::Bind(next));
                    focus = bound;
                },
                Some(&Computation::Project(component, pair)) => {
                    frames.push(Frame::Project(component));
                    focus = pair;
                },
                Some(&Computation::Force(forced))
                    if self.arena.value(forced) == Some(&Value::Constant(constant)) =>
                {
                    break;
                },
                Some(_) | None => return self.unfold_term(term, constant),
            }
        }
        let named = self.arena.value_constant(constant);
        let opened = self.instantiate(open, named);
        let weakened = crate::rewrite::shift_computation(
            self.arena,
            &mut self.table,
            &mut self.memo,
            opened,
            BinderDepth::NONE,
            BinderDepth::from(1_u32),
        );
        let mut rebuilt = self.arena.computation_fixpoint(weakened, evidence);
        while let Some(frame) = frames.pop() {
            rebuilt = self.wrap(rebuilt, frame);
        }
        Ok(Term::Computation(rebuilt))
    }

    /// Apply the δ-rule decision the trace names at a goal with a defined
    /// head.
    ///
    /// # Specification
    /// - requires: `shapes` are the goal's left and right shapes, at least one
    ///   with a defined head.
    /// - ensures: an `Unfold` and its reduction replace that side's head by its
    ///   body; a `Postpone` waits for the unfolding on the other side; a
    ///   `Freeze` freezes a defined head; a `ConstShortcut` over one constant
    ///   with agreeing spines pushes the spines' premises into `goals`. An
    ///   anchor-free decision names the constant the shapes hold where an
    ///   anchored one would name it: the unfolded or frozen side's head, the
    ///   head the two shortcut sides share, and for a `Postpone` the head
    ///   opposite the unfolding that follows.
    /// - provides: the replay of every two-sided constant rule.
    /// - fails: a refusal when the decision does not apply, or would refute
    ///   through a freeze or a shortcut.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: named-head unfolding and postponed-head traces
    ///   distinguish side and name mismatches; freeze and shortcut traces
    ///   reject negative authority before consumption; anchor-free freeze,
    ///   postponement and shortcut replay the anchored chain and refuse a side
    ///   with no defined head or two heads that differ. These fixtures bound
    ///   dispatch, not every possible spine.
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    /// - witness: `replay::tests::a_frozen_branch_cannot_carry_a_refutation`
    /// - witness: `replay::tests::anchor_free_constant_decisions_read_their_constant_off_the_shapes`
    #[spec(
        requires: shapes.iter().any(|shape| matches!(shape, &&Shape::Neutral(Head::Constant(_, Status::Defined), _))),
        captures: before = (self.position, goals.len()),
        ensures: |ret| self.position >= before.0 && self.position <= before.0.saturating_add(2)
            && match ret {
                Ok(Flow::Settled) => goal.expect == Expect::Convertible
                    && self.position == before.0.saturating_add(1)
                    && goals.get(before.1..).is_some_and(|pending| pending.iter().all(|next| next.expect == Expect::Convertible)),
                Ok(Flow::Continue) => self.position > before.0
                    && (self.position != before.0.saturating_add(2) || *postponed == Postponed::Nothing),
                Err(Stop::Refused(ReplayRefusal::NonAuthoritative { at })) =>
                    goal.expect == Expect::NotConvertible && at.0 == before.0 && self.position == before.0,
                Err(_) => true,
            },
    )]
    fn constants(
        &mut self,
        goal: &mut Goal,
        shapes: [&Shape; 2],
        postponed: &mut Postponed,
        goals: &mut Vec<Goal>,
    ) -> Result<Flow, Stop>
    {
        let [left, right] = shapes;
        let shape_of = |side: ConversionSide| match side {
            ConversionSide::Left => left,
            ConversionSide::Right => right,
        };
        let next = self.peek();
        let Next::Decision(decision) = next
        else {
            return Err(self.refuse(next));
        };
        match decision {
            ConversionDecision::Unfold { constant } => {
                self.take();
                let reduction = self.peek();
                let side = match reduction {
                    Next::Decision(ConversionDecision::ReduceLeft { redex })
                        if redex == constant =>
                    {
                        ConversionSide::Left
                    },
                    Next::Decision(ConversionDecision::ReduceRight { redex })
                        if redex == constant =>
                    {
                        ConversionSide::Right
                    },
                    Next::Decision(_) | Next::End => return Err(self.refuse(reduction)),
                };
                // An anchor-free decision, as persisted evidence carries it,
                // names no constant: it unfolds the one the side's head holds.
                let name = match (constant, shape_of(side)) {
                    (ReplayNode::Constant(name), _)
                    | (
                        ReplayNode::Other,
                        &Shape::Neutral(Head::Constant(name, Status::Defined), _),
                    ) => name,
                    (ReplayNode::Other, _) => return Err(self.refuse(reduction)),
                };
                let unfolds = matches!(shape_of(side), &Shape::Neutral(Head::Constant(head, Status::Defined), _) if head == name);
                let waits = match *postponed {
                    Postponed::Nothing => true,
                    Postponed::Constant(other) => matches!(
                        shape_of(opposite(side)),
                        &Shape::Neutral(Head::Constant(head, Status::Defined), _) if head == other
                    ),
                    Postponed::Opposite => matches!(
                        shape_of(opposite(side)),
                        &Shape::Neutral(Head::Constant(_, Status::Defined), _)
                    ),
                };
                if !(unfolds && waits) {
                    return Err(self.refuse(reduction));
                }
                self.take();
                self.unfold(goal, side, name)?;
                *postponed = Postponed::Nothing;
                Ok(Flow::Continue)
            },
            ConversionDecision::Postpone { constant } if *postponed == Postponed::Nothing => {
                self.take();
                *postponed = match constant {
                    ReplayNode::Constant(name) => Postponed::Constant(name),
                    ReplayNode::Other => Postponed::Opposite,
                };
                Ok(Flow::Continue)
            },
            ConversionDecision::Freeze { constant, side } => {
                if goal.expect == Expect::NotConvertible {
                    return Err(Stop::Refused(ReplayRefusal::NonAuthoritative {
                        at: self.at(),
                    }));
                }
                let &Shape::Neutral(Head::Constant(head, Status::Defined), _) = shape_of(side)
                else {
                    return Err(self.refuse(next));
                };
                if matches!(constant, ReplayNode::Constant(name) if name != head) {
                    return Err(self.refuse(next));
                }
                self.take();
                goal.frozen.freeze(side, head);
                Ok(Flow::Continue)
            },
            ConversionDecision::ConstShortcut { constant } => {
                if goal.expect == Expect::NotConvertible {
                    return Err(Stop::Refused(ReplayRefusal::NonAuthoritative {
                        at: self.at(),
                    }));
                }
                let (
                    &Shape::Neutral(
                        Head::Constant(left_head, Status::Defined | Status::Frozen),
                        ref left_spine,
                    ),
                    &Shape::Neutral(
                        Head::Constant(right_head, Status::Defined | Status::Frozen),
                        ref right_spine,
                    ),
                ) = (left, right)
                else {
                    return Err(self.refuse(next));
                };
                let named = match constant {
                    ReplayNode::Constant(name) => name == left_head,
                    ReplayNode::Other => true,
                };
                if !named || left_head != right_head {
                    return Err(self.refuse(next));
                }
                self.take();
                let premises = match spines(self.arena, left_spine, right_spine)? {
                    Structure::Leaf(verdict) => {
                        return self.close(goal.expect, verdict).map(|()| Flow::Settled);
                    },
                    Structure::Premises(premises) => premises,
                };
                goals.extend(
                    premises
                        .into_iter()
                        .rev()
                        .map(|premise| Goal::premise(premise, Expect::Convertible)),
                );
                Ok(Flow::Settled)
            },
            ConversionDecision::ReduceLeft { .. }
            | ConversionDecision::ReduceRight { .. }
            | ConversionDecision::Postpone { .. }
            | ConversionDecision::EtaExpand { .. }
            | ConversionDecision::ReturnEta { .. }
            | ConversionDecision::Reassociate { .. }
            | ConversionDecision::Discard { .. }
            | ConversionDecision::Force { .. }
            | ConversionDecision::ComparedShared { .. }
            | ConversionDecision::Decompose
            | ConversionDecision::NegativeSubgoal { .. } => Err(self.refuse(next)),
        }
    }

    /// Force both sides of a thunk goal on the trace's two `Force`s.
    ///
    /// # Specification
    /// - requires: the goal is a thunk against a thunk or a neutral value.
    /// - ensures: a thunk side becomes its body, a neutral side its force.
    /// - provides: the replay of the force rule.
    /// - fails: a refusal unless the next two decisions are `Force`s.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a thunk against a neutral consumes two force decisions
    ///   before eta; a wrong second decision refuses at its position without
    ///   replacing either side.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    #[spec(
        captures: before = (self.position, goal.left, goal.right),
        ensures: |ret| if ret.is_ok() {
            let agrees = |source, result| match (source, result) {
                (Term::Value(value), Term::Computation(computation)) => match self.arena.value(value) {
                    Some(&Value::Thunk(body)) => computation == body,
                    Some(&(Value::Variable(_) | Value::Constant(_))) => self.arena.computation(computation) == Some(&Computation::Force(value)),
                    _ => false,
                },
                _ => false,
            };
            self.position == before.0.saturating_add(match self.reading { Reading::Recorded => 2, Reading::Forced | Reading::Unfolding => 0 })
                && agrees(before.1, goal.left) && agrees(before.2, goal.right)
        } else {
            goal.left == before.1 && goal.right == before.2
                && self.position >= before.0 && self.position <= before.0.saturating_add(2)
        },
    )]
    fn force(
        &mut self,
        goal: &mut Goal,
    ) -> Result<(), Stop>
    {
        for _ in [ConversionSide::Left, ConversionSide::Right] {
            self.read(Forced::Force)?;
        }
        let left = self.forced(goal.left)?;
        let right = self.forced(goal.right)?;
        goal.left = left;
        goal.right = right;
        Ok(())
    }

    /// The computation `term` runs when forced.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a thunk's body, or the force of a variable or a constant.
    /// - provides: one side of the force rule.
    /// - fails: [`ReplayRefusal::Unreadable`] on any other term.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: replaying a suspended lambda against a free variable
    ///   distinguishes opening a thunk from allocating a neutral force; other
    ///   root classes are bounded by the executable local match.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `path_universe::tests::no_k`
    #[spec(ensures: |ret| match term {
        Term::Value(value) => match self.arena.value(value) {
            Some(&Value::Thunk(body)) => ret == Ok(Term::Computation(body)),
            Some(&(Value::Variable(_) | Value::Constant(_))) => matches!(ret, Ok(Term::Computation(computation)) if self.arena.computation(computation) == Some(&Computation::Force(value))),
            _ => ret == Err(unreadable()),
        },
        Term::Computation(_) => ret == Err(unreadable()),
    })]
    fn forced(
        &mut self,
        term: Term,
    ) -> Result<Term, Stop>
    {
        let Term::Value(value) = term
        else {
            return Err(unreadable());
        };
        match self.arena.value(value) {
            Some(&Value::Thunk(body)) => Ok(Term::Computation(body)),
            Some(&(Value::Variable(_) | Value::Constant(_))) => {
                Ok(Term::Computation(self.arena.computation_force(value)))
            },
            Some(
                &(Value::PathRefl(_)
                | Value::Constructor { .. }
                | Value::Record(_)
                | Value::PathProduct(..)
                | Value::SessionPath { .. }
                | Value::SessionFlow { .. }
                | Value::PathEquiv { .. }
                | Value::Univalence { .. }
                | Value::Here { .. }
                | Value::Stay { .. }
                | Value::ForwardFlow { .. }
                | Value::FunctionFlow { .. }
                | Value::Then { .. }
                | Value::FlowProduct(..)
                | Value::Higher { .. }
                | Value::HigherEvaluation { .. }
                | Value::QuantifiedEvaluation { .. }
                | Value::Literal(_)
                | Value::Tuple(..)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Injection(..)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticApplication(..)
                | Value::Returned(_)),
            )
            | None => Err(unreadable()),
        }
    }

    /// η-expand the neutral `side` of a lambda goal on the trace's
    /// `EtaExpand`.
    ///
    /// # Specification
    /// - requires: `side` is a neutral computation and the other side a lambda.
    /// - ensures: the neutral side becomes its shift applied to the fresh
    ///   variable, and the lambda side its body.
    /// - provides: the replay of the η rule.
    /// - fails: a refusal unless the next decision is an `EtaExpand` naming
    ///   `side`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: eta on the neutral side opens the opposite lambda and
    ///   introduces variable zero; a missing or wrong-side decision refuses
    ///   after the same force prefix. The witness does not cover arbitrary open
    ///   binder depths.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    #[spec(
        captures: before = (self.position, goal.side(side), goal.side(opposite(side))),
        ensures: |ret| if ret.is_ok() {
            self.position == before.0.saturating_add(match self.reading { Reading::Recorded => 1, Reading::Forced | Reading::Unfolding => 0 })
                && match (before.2, goal.side(opposite(side)), goal.side(side)) {
                    (Term::Computation(lambda), Term::Computation(body), Term::Computation(applied)) =>
                        self.arena.computation(lambda) == Some(&Computation::Lambda(body))
                        && matches!(self.arena.computation(applied), Some(&Computation::Application(_, variable))
                            if self.arena.value(variable) == Some(&Value::Variable(DeBruijnIndex::from(0)))),
                    _ => false,
                }
        } else {
            self.position == before.0 && goal.side(side) == before.1 && goal.side(opposite(side)) == before.2
        },
    )]
    fn eta(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
    ) -> Result<(), Stop>
    {
        let (Term::Computation(neutral), Term::Computation(lambda)) =
            (goal.side(side), goal.side(opposite(side)))
        else {
            return Err(unreadable());
        };
        let Some(&Computation::Lambda(body)) = self.arena.computation(lambda)
        else {
            return Err(unreadable());
        };
        self.read(Forced::Eta(side))?;
        let shifted = shift_computation(
            self.arena,
            &mut self.table,
            &mut self.memo,
            neutral,
            BinderDepth::default(),
            BinderDepth::from(1),
        );
        let variable = self.arena.value_variable(DeBruijnIndex::from(0));
        let applied = self.arena.computation_application(shifted, variable);
        goal.set(side, Term::Computation(applied));
        goal.set(opposite(side), Term::Computation(body));
        Ok(())
    }

    /// Decompose a lazy pairing goal by projecting its neutral `side` on both
    /// sides of the lazy product.
    ///
    /// # Specification
    /// - requires: `side` is a neutral computation and the other side a lazy
    ///   pairing.
    /// - ensures: the premises are the neutral's left projection against the
    ///   pairing's left component, then its right projection against the right
    ///   component, each kept on the goal's own sides, scheduled as
    ///   [`Self::schedule`] states. No decision names the η step: the two
    ///   shapes force it and nothing about it is chosen.
    /// - provides: the replay of the lazy product's η rule, `M = ⟨π₁ M, π₂ M⟩`.
    /// - fails: [`ReplayRefusal::Unreadable`] when the sides are not a
    ///   computation and a lazy pairing; a refusal when a refutation's next
    ///   decision is not a `NegativeSubgoal` naming one of the two premises.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: the pairing of a variable's projections converts with
    ///   that variable on either side with an empty trace; a pairing whose last
    ///   component differs refutes through `NegativeSubgoal` at that position
    ///   and not at position zero; an `EtaExpand` there is never read and is
    ///   left over, and a `Decompose` there is inapplicable.
    /// - witness: `replay::tests::a_lazy_pairing_meets_a_neutral_by_its_projections`
    #[spec(
        captures: [before = goals.len(), width = match goal.side(opposite(side)) {
            Term::Computation(pairing) => match self.arena.computation(pairing) {
                Some(&Computation::With(ref components)) => components.len(),
                _ => 0_usize,
            },
            Term::Value(_) => 0_usize,
        }],
        ensures: |ret| match ret {
            Ok(()) => goals.get(before..).is_some_and(|pending| {
                pending.len() == match goal.expect { Expect::Convertible => width, Expect::NotConvertible => 1_usize }
                    && pending.iter().all(|next| next.expect == goal.expect && matches!(next.side(side), Term::Computation(projected)
                        if matches!(self.arena.computation(projected), Some(&Computation::Project(_, neutral)) if goal.side(side) == Term::Computation(neutral))))
            }),
            Err(_) => goals.len() == before,
        },
    )]
    fn product_eta(
        &mut self,
        goal: &Goal,
        side: ConversionSide,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        let (Term::Computation(neutral), Term::Computation(pairing)) =
            (goal.side(side), goal.side(opposite(side)))
        else {
            return Err(unreadable());
        };
        let Some(&Computation::With(ref components)) = self.arena.computation(pairing)
        else {
            return Err(unreadable());
        };
        let components = components.clone();
        let mut premises = Vec::with_capacity(components.len());
        for (position, &component) in components.iter().enumerate() {
            let projection = self
                .arena
                .computation_project(gandr_kernel_term::Component::from(position), neutral);
            premises.push(match side {
                ConversionSide::Left => Premise::computations(projection, component),
                ConversionSide::Right => Premise::computations(component, projection),
            });
        }
        self.schedule(goal.expect, premises, goals)
    }

    /// Read the decision naming `wanted` off the trace, or fire it unread.
    ///
    /// # Specification
    /// - requires: the shapes force `wanted` at the current goal.
    /// - ensures: under [`Reading::Recorded`], `Ok` after consuming exactly one
    ///   decision when the next one names `wanted`, side and all; under
    ///   [`Reading::Forced`] and [`Reading::Unfolding`], `Ok` without reading.
    /// - provides: the one place a forced rewrite meets the trace.
    /// - fails: a refusal when the trace names anything else or has ended.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a missing or wrong-side decision refuses where the
    ///   recorded replay reads it, and the forced conversion relates the same
    ///   pair with no trace at all.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::the_laws_of_bind_replay_by_name`
    /// - witness: `replay::tests::the_kernel_converts_by_the_forced_rules_alone`
    #[spec(
        captures: before = self.position,
        ensures: |ret| match (self.reading, ret) {
            (Reading::Forced | Reading::Unfolding, Ok(())) | (Reading::Recorded, Err(_)) => self.position == before,
            (Reading::Recorded, Ok(())) => self.position == before.saturating_add(1),
            (Reading::Forced | Reading::Unfolding, Err(_)) => false,
        },
    )]
    fn read(
        &mut self,
        wanted: Forced,
    ) -> Result<(), Stop>
    {
        if self.reading != Reading::Recorded {
            return Ok(());
        }
        let next = self.peek();
        let named = match (wanted, next) {
            (Forced::Force, Next::Decision(ConversionDecision::Force { .. })) => true,
            (
                Forced::Eta(side),
                Next::Decision(ConversionDecision::EtaExpand { side: named, .. }),
            )
            | (
                Forced::ReturnEta(side),
                Next::Decision(ConversionDecision::ReturnEta { side: named }),
            )
            | (
                Forced::Reassociate(side),
                Next::Decision(ConversionDecision::Reassociate { side: named }),
            ) => named == side,
            (
                Forced::Force | Forced::Eta(_) | Forced::ReturnEta(_) | Forced::Reassociate(_),
                Next::Decision(_) | Next::End,
            ) => false,
        };
        if !named {
            return Err(self.refuse(next));
        }
        self.take();
        Ok(())
    }

    /// Read the computation on `side` as its bind into `return`.
    ///
    /// # Specification
    /// - requires: [`bind_rule`] answered [`BindRule::ReturnEta`] naming
    ///   `side`.
    /// - ensures: `side` becomes `M to x. return x` over the `M` it held, the
    ///   other side unchanged.
    /// - provides: the replay of the η-rule of `F`.
    /// - fails: a refusal unless the trace names `ReturnEta` on `side`, or when
    ///   the side is not a computation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a neutral against its own bind into `return` converts
    ///   only through this rewrite, and the same trace naming the other side
    ///   refuses.
    /// - witness: `replay::tests::the_laws_of_bind_replay_by_name`
    #[spec(
        captures: before = (goal.side(side), goal.side(opposite(side))),
        ensures: |ret| goal.side(opposite(side)) == before.1 && if ret.is_ok() {
            matches!((before.0, goal.side(side)), (Term::Computation(held), Term::Computation(expanded))
                if matches!(self.arena.computation(expanded), Some(&Computation::Bind(bound, returned))
                    if bound == held && matches!(self.arena.computation(returned), Some(&Computation::Return(variable))
                        if self.arena.value(variable) == Some(&Value::Variable(DeBruijnIndex::from(0))))))
        } else {
            goal.side(side) == before.0
        },
    )]
    fn return_eta(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
    ) -> Result<(), Stop>
    {
        let Term::Computation(held) = goal.side(side)
        else {
            return Err(unreadable());
        };
        self.read(Forced::ReturnEta(side))?;
        let variable = self.arena.value_variable(DeBruijnIndex::from(0));
        let returned = self.arena.computation_return(variable);
        let expanded = self.arena.computation_bind(held, returned);
        goal.set(side, Term::Computation(expanded));
        Ok(())
    }

    /// Make the two binds nearest the head of `side` one.
    ///
    /// # Specification
    /// - requires: [`bind_rule`] answered [`BindRule::Reassociate`] naming
    ///   `side`, and `spine` is that side's spine.
    /// - ensures: the node `(M to x. N) to y. P` that holds the pair becomes `M
    ///   to x. (N to y. P')`, with `P'` the continuation shifted past the new
    ///   binder, and every application, bind and projection above it is rebuilt
    ///   unchanged; the other side is unchanged.
    /// - provides: the replay of bind associativity.
    /// - fails: a refusal unless the trace names `Reassociate` on `side`, or
    ///   when the side's term does not hold the pair the spine says it does.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `for` loops below walk a bounded count of frames, not
    ///   recursion.
    /// - measure: the frames between the root and the pair, fewer than the
    ///   spine's length.
    ///
    /// # Adequacy
    /// - hypothesis: L3: a left-nested pair of binds under an application
    ///   converts to its right-nested twin only through this rewrite, and a
    ///   continuation reading the outer binder separates a shift from none.
    /// - witness: `replay::tests::the_laws_of_bind_replay_by_name`
    #[spec(
        captures: before = (goal.side(side), goal.side(opposite(side))),
        ensures: |ret| goal.side(opposite(side)) == before.1
            && (ret.is_ok() || goal.side(side) == before.0),
    )]
    fn reassociate(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
        spine: &[Elimination],
    ) -> Result<(), Stop>
    {
        let Term::Computation(root) = goal.side(side)
        else {
            return Err(unreadable());
        };
        let pair = spine
            .windows(2)
            .position(|pair| matches!(pair, &[Elimination::Bind(_), Elimination::Bind(_)]))
            .ok_or_else(unreadable)?;
        let above = spine
            .len()
            .checked_sub(pair)
            .and_then(|rest| rest.checked_sub(2))
            .ok_or_else(unreadable)?;
        let mut frames = Vec::with_capacity(above);
        let mut focus = root;
        for _ in 0 .. above {
            match self.arena.computation(focus) {
                Some(&Computation::Application(head, argument)) => {
                    frames.push(Frame::Apply(argument));
                    focus = head;
                },
                Some(&Computation::Bind(bound, body)) => {
                    frames.push(Frame::Bind(body));
                    focus = bound;
                },
                Some(&Computation::Project(projected, pair)) => {
                    frames.push(Frame::Project(projected));
                    focus = pair;
                },
                Some(_) | None => return Err(unreadable()),
            }
        }
        let Some(&Computation::Bind(inner, outer)) = self.arena.computation(focus)
        else {
            return Err(unreadable());
        };
        let Some(&Computation::Bind(head, first)) = self.arena.computation(inner)
        else {
            return Err(unreadable());
        };
        self.read(Forced::Reassociate(side))?;
        let then = shift_computation(
            self.arena,
            &mut self.table,
            &mut self.memo,
            outer,
            BinderDepth::from(1),
            BinderDepth::from(1),
        );
        let fused = self.arena.computation_bind(first, then);
        let mut rebuilt = self.arena.computation_bind(head, fused);
        for &frame in frames.iter().rev() {
            rebuilt = self.wrap(rebuilt, frame);
        }
        goal.set(side, Term::Computation(rebuilt));
        Ok(())
    }

    /// Read an unread call on one side as the continuation it binds.
    ///
    /// # Specification
    /// - requires: `shapes` are the goal's left and right shapes, and `next`
    ///   the trace's next decision.
    /// - ensures: under [`Reading::Recorded`], when `next` is `Discard` naming
    ///   a side whose shape [`unread_call`] reads, that decision is consumed
    ///   and the side becomes the continuation with its unread binder dropped;
    ///   `None` and nothing changed when `next` is no `Discard` and the goal is
    ///   owed convertible, or no side holds an unread call. Under
    ///   [`Reading::Forced`] and [`Reading::Unfolding`], the left side's unread
    ///   call is dropped before the right's, reading nothing.
    /// - provides: the replay of the discard, `M to x. N ≡ N` when `x` is not
    ///   free in `N` and `M` is a call of a variable.
    /// - fails: a refusal when the trace names a `Discard` on a side that holds
    ///   no unread call, or names anything else at a goal owed apart while a
    ///   side holds one.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: an unread call against its continuation converts on
    ///   either side by the named decision and by the forced reading alone; a
    ///   decision naming the side with no call refuses, and so does a
    ///   refutation that decomposes past a call it could drop.
    /// - witness: `replay::tests::an_unread_call_replays_as_its_continuation`
    #[spec(
        captures: before = (self.position, goal.side(ConversionSide::Left), goal.side(ConversionSide::Right)),
        ensures: |ret| match ret {
            Ok(None) => self.position == before.0
                && goal.side(ConversionSide::Left) == before.1
                && goal.side(ConversionSide::Right) == before.2,
            Ok(Some(side)) => goal.side(opposite(side)) == match opposite(side) {
                ConversionSide::Left => before.1,
                ConversionSide::Right => before.2,
            },
            Err(_) => self.position == before.0,
        },
    )]
    fn discard(
        &mut self,
        goal: &mut Goal,
        shapes: [&Shape; 2],
        next: Next,
    ) -> Result<Option<ConversionSide>, Stop>
    {
        let [left, right] = shapes;
        let mut reads = Reaches::<Reads>::new();
        let mut unread = |shape: &Shape| {
            unread_call(shape).filter(|&continuation| {
                reads.comp_reach(self.arena, continuation).innermost() == BinderUse::Ignored
            })
        };
        let calls = [
            (ConversionSide::Left, unread(left)),
            (ConversionSide::Right, unread(right)),
        ];
        let chosen = match (self.reading, next) {
            (Reading::Recorded, Next::Decision(ConversionDecision::Discard { side })) => {
                let Some(&(_, Some(continuation))) = calls.iter().find(|&&(at, _)| at == side)
                else {
                    return Err(self.refuse(next));
                };
                self.take();
                (side, continuation)
            },
            (Reading::Recorded, Next::Decision(_) | Next::End) => {
                if goal.expect == Expect::NotConvertible
                    && calls.iter().any(|&(_, call)| call.is_some())
                {
                    return Err(self.refuse(next));
                }
                return Ok(None);
            },
            (Reading::Forced | Reading::Unfolding, _) => {
                let Some(&(side, Some(continuation))) =
                    calls.iter().find(|&&(_, call)| call.is_some())
                else {
                    return Ok(None);
                };
                (side, continuation)
            },
        };
        let (side, continuation) = chosen;
        let dropped = self.arena.value_unit();
        let opened = self.instantiate(continuation, dropped);
        goal.set(side, Term::Computation(opened));
        Ok(Some(side))
    }

    /// Close or decompose a goal no decision is needed to rewrite.
    ///
    /// # Specification
    /// - requires: the goal selected [`Rule::Structural`].
    /// - ensures: a leaf closes at its verdict without consuming a decision. A
    ///   decomposition may consume a leading `Decompose`; one owing
    ///   convertibility pushes every premise, and one owing a refutation also
    ///   consumes the `NegativeSubgoal` naming its selected premise. A refused
    ///   negative subgoal leaves an already consumed `Decompose` consumed.
    /// - provides: implicit structural rules and their optional trace marker.
    /// - fails: a refusal on a leaf against the owed verdict, or a refutation
    ///   without its negative subgoal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a pair and a case/application spine distinguish
    ///   selecting the refuting premise from accepting a positive sibling or an
    ///   out-of-range position; newly scheduled goals owe the parent verdict.
    ///   Native path and flow fixtures separate an explicit decomposition from
    ///   its subsequent refusal without restoring the consumed prefix.
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
    /// - witness: `path_universe::tests::it_computes_through_a_former`
    /// - witness: `flow_universe::tests::formation_boundaries_refuse`
    /// - witness: `replay::tests::a_refutation_at_a_presented_term_is_not_authoritative`
    #[spec(
        requires: rule(left, right) == Rule::Structural,
        captures: before = (goals.len(), self.position),
        ensures: |ret| self.position >= before.1 && if ret.is_ok() {
            goals.get(before.0..).is_some_and(|pending| {
                pending.iter().all(|next| next.expect == goal.expect && next.frozen.left.is_empty() && next.frozen.right.is_empty())
                    && if pending.is_empty() {
                        self.position == before.1
                    } else {
                        match goal.expect {
                            Expect::Convertible => self.position <= before.1.saturating_add(1),
                            Expect::NotConvertible => pending.len() == 1
                                && self.position >= before.1.saturating_add(1)
                                && self.position <= before.1.saturating_add(2),
                        }
                    }
            })
        } else {
            goals.len() == before.0 && self.position <= before.1.saturating_add(1)
        },
    )]
    fn structural(
        &mut self,
        goal: &Goal,
        left: &Shape,
        right: &Shape,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        let structure = self.decompose(goal, left, right)?;
        let next = self.peek();
        if matches!(next, Next::Decision(ConversionDecision::Decompose)) {
            if !matches!(structure, Structure::Premises(_)) {
                return Err(self.refuse(next));
            }
            self.take();
        }
        // A refutation over a presented type's term is not authoritative: a
        // leaf of its normal form may unfold into a redex, so two normal forms
        // apart here may still be one term.
        let presentations = self.unfoldings.presentations();
        let presented = |term: Term| match term {
            Term::Value(value) => match self.arena.value(value) {
                Some(&Value::Constructor { datatype, .. }) => matches!(
                    self.arena.value_type(datatype),
                    Some(&ValueType::Data { declaration, .. })
                        if presentations.presented(declaration).is_some()
                ),
                _ => false,
            },
            Term::Computation(_) => false,
        };
        if goal.expect == Expect::NotConvertible
            && structure == Structure::Leaf(Expect::NotConvertible)
            && (presented(goal.left) || presented(goal.right))
        {
            return Err(Stop::Refused(ReplayRefusal::NonAuthoritative {
                at: self.at(),
            }));
        }
        let premises = match structure {
            Structure::Leaf(verdict) => return self.close(goal.expect, verdict),
            Structure::Premises(premises) => premises,
        };
        self.schedule(goal.expect, premises, goals)
    }

    /// Schedule a decomposition's premises at the verdict its goal owes.
    ///
    /// # Specification
    /// - requires: `premises` is non-empty.
    /// - ensures: owing convertibility, every premise is pushed, the first on
    ///   top, and no decision is read; owing a refutation, the premise the next
    ///   `NegativeSubgoal` names is pushed alone and that decision consumed.
    ///   Every pushed goal owes `expect` with nothing frozen.
    /// - provides: the premise half shared by structural decomposition and the
    ///   lazy product's η.
    /// - fails: a refusal when a refutation's next decision is not a
    ///   `NegativeSubgoal` naming one of `premises`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a pair and a lazy pairing against a neutral
    ///   distinguish selecting the refuting premise from accepting a positive
    ///   sibling or an out-of-range position, and a missing `NegativeSubgoal`
    ///   from a present one.
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::a_lazy_pairing_meets_a_neutral_by_its_projections`
    #[spec(
        captures: before = (goals.len(), self.position, premises.len()),
        ensures: |ret| match ret {
            Ok(()) => goals.get(before.0..).is_some_and(|pending| {
                pending.iter().all(|next| next.expect == expect && next.frozen == Frozen::default())
                    && match expect {
                        Expect::Convertible => pending.len() == before.2 && self.position == before.1,
                        Expect::NotConvertible => pending.len() == 1_usize && self.position == before.1.saturating_add(1),
                    }
            }),
            Err(_) => goals.len() == before.0 && self.position == before.1,
        },
    )]
    fn schedule(
        &mut self,
        expect: Expect,
        premises: Vec<Premise>,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        match expect {
            Expect::Convertible => {
                goals.extend(
                    premises
                        .into_iter()
                        .rev()
                        .map(|premise| Goal::premise(premise, Expect::Convertible)),
                );
                Ok(())
            },
            Expect::NotConvertible => {
                let next = self.peek();
                let Next::Decision(ConversionDecision::NegativeSubgoal { position }) = next
                else {
                    return Err(self.refuse(next));
                };
                let Some(&premise) = usize::try_from(u32::from(position))
                    .ok()
                    .and_then(|index| premises.get(index))
                else {
                    return Err(self.refuse(next));
                };
                self.take();
                goals.push(Goal::premise(premise, Expect::NotConvertible));
                Ok(())
            },
        }
    }

    /// The structural rule two shapes force.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: two formers of one kind decompose child by child, or close on
    ///   their payloads; two codes close on α-equality or rigid separation; two
    ///   returners, two lambdas, two lazy pairings, and two neutrals with one
    ///   head and agreeing spines decompose; a non-empty tuple or record
    ///   against a neutral decomposes into its components or fields against the
    ///   neutral's projections; every other pair is a refuting leaf.
    /// - provides: the leaf and decomposition rules.
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling former.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: return, lambda, lazy pairing, pair, and neutral-spine
    ///   fixtures distinguish ordered same-polarity premises from rigidly
    ///   distinct leaves. The observer is the replayed positive or selected
    ///   negative derivation, not a general normalization proof.
    /// - witness: `replay::tests::the_replay_reduces_before_it_reads_a_decision`
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
    /// - witness: `replay::tests::a_lazy_pairing_meets_a_neutral_by_its_projections`
    /// - witness: `replay::tests::a_tuple_meets_a_neutral_by_its_projections_715`
    #[spec(ensures: |ret| match (left, right) {
        (&Shape::Return(one), &Shape::Return(other)) => matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one, other)]),
        (&Shape::Lambda(one), &Shape::Lambda(other)) => matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::computations(one, other)]),
        (&Shape::Fixpoint(one, ref ones), &Shape::Fixpoint(other, ref others)) => if ones.len() == others.len() {
            matches!(ret, Ok(Structure::Premises(ref premises)) if premises.first() == Some(&Premise::computations(one, other)) && Some(premises.len()) == ones.len().checked_add(1_usize))
        } else {
            ret == Ok(Structure::Leaf(Expect::NotConvertible))
        },
        (&Shape::With(ref ones), &Shape::With(ref others)) => if ones.len() == others.len() {
            matches!(ret, Ok(Structure::Premises(ref premises))
                if premises.iter().copied().eq(ones.iter().zip(others.iter()).map(|(&one, &other)| Premise::computations(one, other))))
        } else {
            ret == Ok(Structure::Leaf(Expect::NotConvertible))
        },
        (&Shape::Former | &Shape::Neutral(..), &Shape::Former)
        | (&Shape::Former, &Shape::Neutral(..)) => true,
        (&Shape::Neutral(one, _), &Shape::Neutral(other, _)) if one == other => match ret {
            Ok(Structure::Premises(ref premises)) => !premises.is_empty() && premises.iter().all(|premise|
                matches!((premise.left, premise.right), (Term::Value(_), Term::Value(_)) | (Term::Computation(_), Term::Computation(_)))),
            Ok(Structure::Leaf(_)) | Err(Stop::Refused(ReplayRefusal::Unreadable)) => true,
            Err(_) => false,
        },
        _ => ret == Ok(Structure::Leaf(Expect::NotConvertible)),
    })]
    fn decompose(
        &mut self,
        goal: &Goal,
        left: &Shape,
        right: &Shape,
    ) -> Result<Structure, Stop>
    {
        let structure = match (left, right) {
            (&Shape::Former, &Shape::Former) => {
                let (Term::Value(left_value), Term::Value(right_value)) = (goal.left, goal.right)
                else {
                    return Err(unreadable());
                };
                return self.formers(left_value, right_value);
            },
            (&Shape::Return(left_value), &Shape::Return(right_value)) => {
                Structure::of(Vec::from([Premise::values(left_value, right_value)]))
            },
            (&Shape::Lambda(left_body), &Shape::Lambda(right_body)) => {
                Structure::of(Vec::from([Premise::computations(left_body, right_body)]))
            },
            // Two fixpoints compare by their bodies, then by the leading
            // arguments each has taken, pairwise; a different count is apart.
            (
                &Shape::Fixpoint(left_body, ref left_leading),
                &Shape::Fixpoint(right_body, ref right_leading),
            ) => {
                if left_leading.len() != right_leading.len() {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
                let mut premises = Vec::with_capacity(left_leading.len().saturating_add(1));
                premises.push(Premise::computations(left_body, right_body));
                premises.extend(
                    left_leading
                        .iter()
                        .zip(right_leading)
                        .map(|(&one, &other)| Premise::values(one, other)),
                );
                Structure::of(premises)
            },
            // Two pairings compare componentwise; a different arity is apart.
            (&Shape::With(ref ones), &Shape::With(ref others)) => {
                if ones.len() != others.len() {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
                Structure::of(
                    ones.iter()
                        .zip(others.iter())
                        .map(|(&one, &other)| Premise::computations(one, other))
                        .collect(),
                )
            },
            (
                &Shape::Neutral(left_head, ref left_spine),
                &Shape::Neutral(right_head, ref right_spine),
            ) if left_head == right_head => spines(self.arena, left_spine, right_spine)?,
            (&Shape::Former, &Shape::Neutral(..)) => {
                self.projections(goal.left, goal.right, ConversionSide::Right)?
            },
            (&Shape::Neutral(..), &Shape::Former) => {
                self.projections(goal.right, goal.left, ConversionSide::Left)?
            },
            (
                &(Shape::Former
                | Shape::Thunk(_)
                | Shape::Lambda(_)
                | Shape::With(..)
                | Shape::Fixpoint(..)
                | Shape::Return(_)
                | Shape::Neutral(..)),
                _,
            ) => Structure::Leaf(Expect::NotConvertible),
        };
        Ok(structure)
    }

    /// The η premises of a tuple or a record against a neutral: each component
    /// or field against the neutral's projection at it, in the order the tuple
    /// or the record's labels hold them, the neutral on `side`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a non-empty tuple or record value against a neutral
    ///   value, one value premise per component or field, its other side the
    ///   returned projection of the neutral at its position or label, in order;
    ///   a refuting leaf for any other pair.
    /// - provides: η for products and records.
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling former.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple or record of a neutral's own projections
    ///   replays convertible on either side, and swapped components refute at
    ///   the first.
    /// - witness: `replay::tests::a_tuple_meets_a_neutral_by_its_projections_715`
    #[spec(ensures: |ret| match ret {
        Ok(Structure::Premises(ref premises)) => premises.iter().all(|premise| {
            let (held, projected) = match side {
                ConversionSide::Left => (premise.right, premise.left),
                ConversionSide::Right => (premise.left, premise.right),
            };
            matches!((held, projected), (Term::Value(_), Term::Value(value))
                if matches!(self.arena.value(value), Some(&Value::Returned(_))))
        }),
        Ok(Structure::Leaf(verdict)) => verdict == Expect::NotConvertible,
        Err(_) => true,
    })]
    fn projections(
        &mut self,
        former: Term,
        neutral: Term,
        side: ConversionSide,
    ) -> Result<Structure, Stop>
    {
        let (Term::Value(former), Term::Value(neutral)) = (former, neutral)
        else {
            return Ok(Structure::Leaf(Expect::NotConvertible));
        };
        let mut premises = Vec::new();
        let premise = |held: ValueId, projected: ValueId| match side {
            ConversionSide::Left => Premise::values(projected, held),
            ConversionSide::Right => Premise::values(held, projected),
        };
        let held = self.arena.value(former).ok_or_else(unreadable)?;
        if let Value::Tuple(ref components) = *held
            && !components.is_empty()
        {
            let components = components.to_vec();
            for (position, held) in components.into_iter().enumerate() {
                let projection = self.arena.computation_tuple_projection(
                    neutral,
                    gandr_kernel_term::Component::from(position),
                );
                premises.push(premise(held, self.arena.value_returned(projection)));
            }
        }
        else if let Value::Record(ref fields) = *held
            && !fields.is_empty()
        {
            let fields: Vec<_> = fields
                .iter()
                .map(|(label, &held)| (label.clone(), held))
                .collect();
            for (label, held) in fields {
                let projection = self.arena.computation_record_projection(neutral, label);
                premises.push(premise(held, self.arena.value_returned(projection)));
            }
        }
        else {
            return Ok(Structure::Leaf(Expect::NotConvertible));
        }
        Ok(Structure::of(premises))
    }

    /// The structural rule over two value formers.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::decompose`], over the value formers; two
    ///   reflexivities decompose to their points. A returned endpoint never
    ///   reaches here: [`Self::settle`] reads it first.
    /// - provides: the former half of [`Self::decompose`].
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling id or a returned
    ///   endpoint.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: pair refutations select the differing component and
    ///   reject a positive sibling or an absent index; unit and distinct rigid
    ///   leaves close at opposite verdicts; two reflexivities one unfolding
    ///   apart convert by the unfolding their points need and refuse it read on
    ///   the other side. Quotes and larger former combinations are not claimed
    ///   by these fixtures. Native path witnesses separate evidence from
    ///   syntax; their predicate observes identity and root family without
    ///   repeating conversion.
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
    /// - witness: `replay::tests::two_reflexivities_decompose_to_their_points`
    /// - witness: `replay::tests::the_forced_loop_compares_children_only_where_the_shapes_agree`
    #[spec(ensures: |ret| { let (matched_left_value, matched_right_value) = (self.arena.value(left), self.arena.value(right));
if let Some(matched_left_node) = matched_left_value && let Value::Constructor { datatype:a,tag:a_tag,fields:ref a_fields } = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Value::Constructor { datatype:b,tag:b_tag,fields:ref b_fields } = *matched_right_node { {
            if a_tag != b_tag || a_fields.len() != b_fields.len() { ret == Ok(Structure::Leaf(Expect::NotConvertible)) }
            else { matches!(&ret,Ok(Structure::Premises(premises)) if premises.len() == a_fields.len().saturating_add(1_usize)
                && premises.first().is_some_and(|premise| matches!((premise.left,premise.right), (Term::Value(left),Term::Value(right)) if self.arena.value(left) == Some(&Value::Quote(a)) && self.arena.value(right) == Some(&Value::Quote(b))))
                && premises.iter().skip(1).copied().eq(a_fields.iter().zip(b_fields).map(|(a,b)| Premise::values(*a,*b)))) }
        } }
 else if let Some(matched_left_node) = matched_left_value && let Value::Record(ref a) = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Value::Record(ref b) = *matched_right_node { {
            if a.keys().eq(b.keys()) { ret == Ok(Structure::of(a.values().zip(b.values()).map(|(a,b)| Premise::values(*a,*b)).collect())) } else { ret == Ok(Structure::Leaf(Expect::NotConvertible)) }
        } }
 else if matched_left_value.is_none() || matched_right_value.is_none() || matches!(matched_left_value, Some(&Value::Returned(_))) || matches!(matched_right_value, Some(&Value::Returned(_))) { ret == Err(unreadable()) }
 else if let (Some(&Value::Here { point: one_point, .. }), Some(&Value::Here { point: other_point, .. })) = (matched_left_value, matched_right_value) { matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one_point, other_point)]) }
 else if let (Some(&Value::Univalence(one)), Some(&Value::Univalence(other))) = (matched_left_value, matched_right_value) { matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one, other)]) }
 else if let Some(matched_left_node) = matched_left_value && let ref one @ (Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here { .. } | Value::Stay { .. } | Value::ForwardFlow { .. } | Value::FunctionFlow { .. } | Value::Then { .. } | Value::FlowProduct(..) | Value::Higher { .. } | Value::HigherEvaluation { .. } | Value::QuantifiedEvaluation { .. }) = *matched_left_node && let Some(other) = matched_right_value { matches!(ret, Ok(Structure::Leaf(verdict)) if (left != right || verdict == Expect::Convertible)
                && (core::mem::discriminant(one) == core::mem::discriminant(other) || verdict == Expect::NotConvertible)) }
 else if matches!((matched_left_value, matched_right_value), (Some(&Value::ListNil), Some(&Value::ListNil))) { ret == Ok(Structure::Leaf(Expect::Convertible)) }
 else if let (Some(one), Some(other)) = (matched_left_value.and_then(Value::components), matched_right_value.and_then(Value::components)) { if one.len() == other.len() { ret == Ok(Structure::of(one.iter().zip(other.iter()).map(|(&a, &b)| Premise::values(a, b)).collect())) } else { ret == Ok(Structure::Leaf(Expect::NotConvertible)) } }
 else if let Some(matched_left_node) = matched_left_value && let ref one @ Value::Literal(_) = *matched_left_node && let Some(matched_right_node) = matched_right_value && let ref other @ Value::Literal(_) = *matched_right_node { ret == Ok(Structure::Leaf(if one == other { Expect::Convertible } else { Expect::NotConvertible })) }
 else if let (Some(&Value::ListCons(one_first, one_second)), Some(&Value::ListCons(other_first, other_second))) = (matched_left_value, matched_right_value) { matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one_first, other_first), Premise::values(one_second, other_second)]) }
 else if let Some(matched_left_node) = matched_left_value && let Value::Injection(one_side, one_body) = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Value::Injection(other_side, other_body) = *matched_right_node && (one_side == other_side) { matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one_body, other_body)]) }
 else if let Some(matched_left_node) = matched_left_value && let Value::Lift { target: ref one_target, body: one_body } = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Value::Lift { target: ref other_target, body: other_body } = *matched_right_node && (one_target == other_target) { matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one_body, other_body)]) }
 else if (matched_left_value.is_some_and(|node| matches!(*node, Value::Quote(_))) && matched_right_value.is_some_and(|node| matches!(*node, Value::Quote(_)))) || (matched_left_value.is_some_and(|node| matches!(*node, Value::QuoteComputation(_))) && matched_right_value.is_some_and(|node| matches!(*node, Value::QuoteComputation(_)))) { matches!(ret, Ok(Structure::Leaf(_)) | Err(Stop::Refused(ReplayRefusal::Unreadable))) }
 else { ret == Ok(Structure::Leaf(Expect::NotConvertible)) }
})]
    fn formers(
        &mut self,
        left: ValueId,
        right: ValueId,
    ) -> Result<Structure, Stop>
    {
        let (Some(one), Some(other)) = (self.arena.value(left), self.arena.value(right))
        else {
            return Err(unreadable());
        };
        let structure = match (one, other) {
            (&Value::Returned(_), _) | (_, &Value::Returned(_)) => return Err(unreadable()),
            (
                &Value::Constructor {
                    datatype: a,
                    tag: one_tag,
                    fields: ref a_fields,
                },
                &Value::Constructor {
                    datatype: b,
                    tag: other_tag,
                    fields: ref b_fields,
                },
            ) => {
                if one_tag != other_tag || a_fields.len() != b_fields.len() {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
                let count = a_fields.len();
                let a_quote = self.arena.value_quote(a);
                let b_quote = self.arena.value_quote(b);
                let mut premises = Vec::with_capacity(count.saturating_add(1_usize));
                premises.push(Premise::values(a_quote, b_quote));
                let (Some(left_node), Some(right_node)) =
                    (self.arena.value(left), self.arena.value(right))
                else {
                    return Err(unreadable());
                };
                let Value::Constructor {
                    fields: ref a_fields,
                    ..
                } = *left_node
                else {
                    return Err(unreadable());
                };
                let Value::Constructor {
                    fields: ref b_fields,
                    ..
                } = *right_node
                else {
                    return Err(unreadable());
                };
                premises.extend(
                    a_fields
                        .iter()
                        .zip(b_fields)
                        .map(|(a, b)| Premise::values(*a, *b)),
                );
                Structure::of(premises)
            },
            (&Value::Record(ref a), &Value::Record(ref b)) => {
                if a.len() != b.len() || !a.keys().eq(b.keys()) {
                    Structure::Leaf(Expect::NotConvertible)
                }
                else {
                    Structure::of(
                        a.values()
                            .zip(b.values())
                            .map(|(a, b)| Premise::values(*a, *b))
                            .collect(),
                    )
                }
            },
            // Two reflexivities convert exactly when their points do; the
            // dialogues they carry are evidence for their endpoints, never
            // part of the value.
            (
                &Value::Here {
                    point: left_point, ..
                },
                &Value::Here {
                    point: right_point, ..
                },
            ) => Structure::of(Vec::from([Premise::values(left_point, right_point)])),
            // Two univalences convert exactly when their records do, the laws
            // included: the record is the term.
            (&Value::Univalence(one), &Value::Univalence(other)) => {
                Structure::of(Vec::from([Premise::values(one, other)]))
            },
            (
                &(Value::PathRefl(_)
                | Value::PathProduct(..)
                | Value::SessionPath { .. }
                | Value::SessionFlow { .. }
                | Value::PathEquiv { .. }
                | Value::Univalence { .. }
                | Value::Here { .. }
                | Value::Stay { .. }
                | Value::ForwardFlow { .. }
                | Value::FunctionFlow { .. }
                | Value::Then { .. }
                | Value::FlowProduct(..)
                | Value::Higher { .. }
                | Value::HigherEvaluation { .. }
                | Value::QuantifiedEvaluation { .. }),
                _,
            ) => Structure::Leaf(
                if equal_values(self.arena, left, right) == Convertibility::Convertible {
                    Expect::Convertible
                }
                else {
                    Expect::NotConvertible
                },
            ),
            (&Value::ListNil, &Value::ListNil) => Structure::Leaf(Expect::Convertible),
            // Two tuples of one arity compare component by component; a
            // different arity separates them.
            (&Value::Tuple(ref left), &Value::Tuple(ref right)) => {
                if left.len() == right.len() {
                    Structure::of(
                        left.iter()
                            .zip(right.iter())
                            .map(|(&left, &right)| Premise::values(left, right))
                            .collect(),
                    )
                }
                else {
                    Structure::Leaf(Expect::NotConvertible)
                }
            },
            (&Value::Literal(_), &Value::Literal(_)) if one == other => {
                Structure::Leaf(Expect::Convertible)
            },
            (
                &Value::ListCons(left_first, left_second),
                &Value::ListCons(right_first, right_second),
            ) => Structure::of(Vec::from([
                Premise::values(left_first, right_first),
                Premise::values(left_second, right_second),
            ])),
            (
                &Value::Injection(left_side, left_body),
                &Value::Injection(right_side, right_body),
            ) if left_side == right_side => {
                Structure::of(Vec::from([Premise::values(left_body, right_body)]))
            },
            (
                &Value::Lift {
                    target: ref left_target,
                    body: left_body,
                },
                &Value::Lift {
                    target: ref right_target,
                    body: right_body,
                },
            ) if left_target == right_target => {
                Structure::of(Vec::from([Premise::values(left_body, right_body)]))
            },
            // A code's children are types, which no value premise can carry,
            // so a pair of codes closes here as the shared comparison would:
            // α-equal codes convert — a dependent arrow whose codomain ignores
            // its binder being the plain arrow (#577) — rigid α-distinct codes
            // are apart, and a pair neither settles is refused rather than
            // guessed at.
            (&Value::Quote(_), &Value::Quote(_))
            | (&Value::QuoteComputation(_), &Value::QuoteComputation(_)) => {
                if equal_weakened(self.arena, ConversionGoal::Value(left, right))
                    == Convertibility::Convertible
                {
                    Structure::Leaf(Expect::Convertible)
                }
                else if matches!(
                    (
                        self.rigidity(Term::Value(left)),
                        self.rigidity(Term::Value(right))
                    ),
                    (Rigidity::Rigid, Rigidity::Rigid)
                ) {
                    Structure::Leaf(Expect::NotConvertible)
                }
                else {
                    return Err(unreadable());
                }
            },
            (
                &(Value::Variable(_)
                | Value::Constructor { .. }
                | Value::Record(_)
                | Value::Constant(_)
                | Value::Literal(_)
                | Value::Tuple(..)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Injection(..)
                | Value::Thunk(_)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticApplication(..)),
                _,
            ) => Structure::Leaf(Expect::NotConvertible),
        };
        Ok(structure)
    }

    /// Close a `ComparedShared` goal, or report that it decides nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Compared::Equal`] when the sides are α-equal under
    ///   [`equal_weakened`], or converge under [`pending_endpoints`] with every
    ///   pair it sets aside alike once read by [`Self::endpoints_alike`] — a
    ///   reading that stops leaves the pair open, as [`read_endpoints`] leaves
    ///   it apart; [`Compared::Separated`] when both are rigid and neither
    ///   holds, [`Compared::Open`] otherwise.
    /// - provides: the replay of a closing on two shared nodes.
    /// - fails: [`ReplayRefusal::Unreadable`] on sides of two polarities.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: equal pairs, distinct rigid variables, thunks, and
    ///   defined constants separate equality, rigid separation, and undecided
    ///   comparison under both engine claims; a call over a returned endpoint
    ///   closes with the call over what the endpoint returns, and not with the
    ///   call over another value (#695); two reflexivities whose points one
    ///   presented rule relates close, and not over a free type (#1723). Only
    ///   root identity and polarity are executable here; the recursive relation
    ///   is not rerun.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `replay::tests::a_compared_pair_reads_a_returned_endpoint_the_engine_read_through_695`
    /// - witness: `replay::tests::a_compared_pair_reads_presented_points_by_their_rules_1723`
    #[spec(ensures: |ret| match (goal.left, goal.right) {
        (Term::Value(left), Term::Value(right)) if left == right =>
            ret == Ok(if self.arena.value(left).is_some() { Compared::Equal } else { Compared::Open }),
        (Term::Computation(left), Term::Computation(right)) if left == right =>
            ret == Ok(if self.arena.computation(left).is_some() { Compared::Equal } else { Compared::Open }),
        (Term::Value(_), Term::Computation(_)) | (Term::Computation(_), Term::Value(_)) => ret == Err(unreadable()),
        _ => ret.is_ok(),
    })]
    fn compared(
        &mut self,
        goal: &Goal,
    ) -> Result<Compared, Stop>
    {
        let pair = match (goal.left, goal.right) {
            (Term::Value(left), Term::Value(right)) => ConversionGoal::Value(left, right),
            (Term::Computation(left), Term::Computation(right)) => {
                ConversionGoal::Computation(left, right)
            },
            (Term::Value(_), Term::Computation(_)) | (Term::Computation(_), Term::Value(_)) => {
                return Err(unreadable());
            },
        };
        if equal_weakened(self.arena, pair) == Convertibility::Convertible {
            return Ok(Compared::Equal);
        }
        // The engine compares a returned endpoint by what its computation
        // returned, so two sides alike but for an endpoint it read through,
        // `⟨(λe. return ua(e)) e⟩` against `ua(e)` beneath one held call, are
        // the shared pair it found once each endpoint set aside is read (#695).
        let mut pending = Vec::new();
        if pending_endpoints(
            self.arena,
            self.unfoldings.presentations(),
            pair,
            &mut pending,
        ) == Convertibility::Convertible
            && !pending.is_empty()
            && self.endpoints_alike(pending, goal.reduction) == Ok(Convertibility::Convertible)
        {
            return Ok(Compared::Equal);
        }
        match (self.rigidity(goal.left), self.rigidity(goal.right)) {
            (Rigidity::Rigid, Rigidity::Rigid) => Ok(Compared::Separated),
            (Rigidity::Rigid | Rigidity::Flexible, _) => Ok(Compared::Open),
        }
    }

    /// Whether every pair `pending` holds is alike once each returned endpoint
    /// in it is read by the reduction the goal takes, and each constructor of a
    /// presented type by the type's rules.
    ///
    /// A side reads to the value its computation returns, through every
    /// `return` it reaches by `reduction`, and then to its normal form under
    /// the presentations ([`Self::present`]), as a goal's root reads before
    /// its shape; no definition unfolds, as no decision names one. A pair that
    /// read to something is walked again, its own set-aside pairs read in
    /// turn; a pair neither side of which reads to anything compares by
    /// [`equal_weakened`].
    ///
    /// # Specification
    /// - requires: every pair's values live in the arena.
    /// - ensures: [`Convertibility::Convertible`] exactly when every pair is
    ///   alike so; [`Convertibility::Distinct`] at the first that is not, and
    ///   at any set-aside decode or codomain, which this reading does not read.
    /// - provides: the endpoint reading [`Self::compared`] closes on.
    /// - fails: [`Stop::Budget`] past the budget; as [`Self::whnf`] otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Termination
    /// - reason: the `while let` over the worklist and the inner `while let`
    ///   over one side's chain of returned values, not recursion.
    /// - measure: the budget left: a side reads one step of its chain per
    ///   charge, its rewriting charges every node it compares or copies, and a
    ///   pair returns to the worklist only after one of its sides read to
    ///   something — a normal form reads to itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call over an endpoint returning the other side's
    ///   argument is alike, and over one returning another variable is not;
    ///   leaving the endpoints unread changes the first, and answering every
    ///   read pair alike the second. Two points one presented rule relates are
    ///   alike, and two no rule relates are not (#1723); leaving the rules
    ///   unread changes the first.
    /// - witness: `replay::tests::a_compared_pair_reads_a_returned_endpoint_the_engine_read_through_695`
    /// - witness: `replay::tests::a_compared_pair_reads_presented_points_by_their_rules_1723`
    #[spec(captures: before = self.spent, ensures: |ret| self.spent >= before
        && (!matches!(ret, Err(Stop::Budget)) || self.spent >= self.budget))]
    fn endpoints_alike(
        &mut self,
        mut pending: Vec<SetAside>,
        reduction: Reduction,
    ) -> Result<Convertibility, Stop>
    {
        while let Some(set_aside) = pending.pop() {
            let SetAside::Values(left, right) = set_aside
            else {
                return Ok(Convertibility::Distinct);
            };
            let mut read = [left, right];
            for side in &mut read {
                while let Some(&Value::Returned(computation)) = self.arena.value(*side) {
                    self.charge()?;
                    let Term::Computation(reduced) =
                        self.whnf(Term::Computation(computation), reduction)?
                    else {
                        return Err(unreadable());
                    };
                    let Some(&Computation::Return(returned)) = self.arena.computation(reduced)
                    else {
                        break;
                    };
                    *side = returned;
                }
                // A constructor of a presented type is set aside for its
                // normal form: read it by the type's rules.
                let Term::Value(normal) = self.present(Term::Value(*side))?
                else {
                    return Err(unreadable());
                };
                *side = normal;
            }
            let [one, other] = read;
            let walked = if (one, other) == (left, right) {
                equal_weakened(self.arena, ConversionGoal::Value(one, other))
            }
            else {
                pending_endpoints(
                    self.arena,
                    self.unfoldings.presentations(),
                    ConversionGoal::Value(one, other),
                    &mut pending,
                )
            };
            if walked == Convertibility::Distinct {
                return Ok(Convertibility::Distinct);
            }
        }
        Ok(Convertibility::Convertible)
    }

    /// Whether anything inside `term` can reduce.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: native path introductions are rigid records: comparison never
    ///   descends into their translator programs. Every other term is rigid
    ///   exactly when it resolves throughout and contains no reducible thunk,
    ///   returned endpoint, lambda, bind, case, transport or defined constant,
    ///   including through quoted types, decoded codes and static application
    ///   operands. A static application over an opaque head is rigid.
    /// - provides: the separation half of [`Self::compared`].
    /// - fails: never — a dangling id is flexible.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `while let Some(next) = work.pop()` loop over an explicit
    ///   worklist, not recursion.
    /// - measure: the multiset of arena positions on the worklist: a node is
    ///   replaced by its children, which the arena minted before it within a
    ///   family; a crossing between families is to a node the quote or the
    ///   decode holds, and the arena is finite and acyclic across them.
    ///
    /// # Adequacy
    /// - hypothesis: L3: units and distinct variables are rigid while thunks
    ///   and defined constants prevent a shared comparison from closing
    ///   negatively. This observer covers the root barriers and named pair
    ///   fixtures, not every quoted type graph.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
    #[spec(ensures: |ret| match term {
        Term::Value(value) => match self.arena.value(value) {
            Some(&(Value::Literal(_) | Value::Variable(_) | Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here { .. } | Value::Stay { .. } | Value::ForwardFlow { .. } | Value::FunctionFlow { .. } | Value::Then { .. } | Value::FlowProduct(..) | Value::Higher { .. } | Value::HigherEvaluation { .. } | Value::QuantifiedEvaluation { .. })) => ret == Rigidity::Rigid,
            Some(held) if held.components() == Some(&[]) => ret == Rigidity::Rigid,
            Some(&Value::Constant(constant)) => (ret == Rigidity::Rigid) == (self.unfoldings.unfolding(constant) == Unfoldable::Opaque),
            Some(&(Value::Thunk(_) | Value::Returned(_))) | None => ret == Rigidity::Flexible,
            _ => true,
        },
        Term::Computation(computation) => match self.arena.computation(computation) {
            Some(&(Computation::Transport(..) | Computation::PathTransport { .. } | Computation::TelescopeTransport { .. } | Computation::Ride { .. } | Computation::TelescopeRide { .. } | Computation::RelatedApplication { .. } | Computation::Lambda(_) | Computation::Bind(..) | Computation::Case { .. } | Computation::With(..) | Computation::Project(..))) | None => ret == Rigidity::Flexible,
            _ => true,
        },
    })]
    fn rigidity(
        &self,
        term: Term,
    ) -> Rigidity
    {
        let mut work = Vec::from([match term {
            Term::Value(value) => AnyNode::Value(value),
            Term::Computation(computation) => AnyNode::Computation(computation),
        }]);
        while let Some(next) = work.pop() {
            match next {
                AnyNode::Value(value) => match self.arena.value(value) {
                    Some(&Value::Constructor {
                        datatype,
                        ref fields,
                        ..
                    }) => {
                        // A presented type's constructor may be a redex, or
                        // become one when a leaf unfolds.
                        if let Some(&ValueType::Data { declaration, .. }) =
                            self.arena.value_type(datatype)
                            && self
                                .unfoldings
                                .presentations()
                                .presented(declaration)
                                .is_some()
                        {
                            return Rigidity::Flexible;
                        }
                        work.extend(
                            core::iter::once(AnyNode::ValueType(datatype))
                                .chain(fields.iter().copied().map(AnyNode::Value)),
                        );
                    },
                    Some(&Value::Record(ref fields)) => {
                        work.extend(fields.values().copied().map(AnyNode::Value));
                    },
                    Some(&Value::Univalence(equivalence)) => {
                        work.push(AnyNode::Value(equivalence));
                    },
                    Some(
                        &(Value::Literal(_)
                        | Value::ListNil
                        | Value::Variable(_)
                        | Value::PathRefl(_)
                        | Value::PathProduct(..)
                        | Value::SessionPath { .. }
                        | Value::SessionFlow { .. }
                        | Value::PathEquiv { .. }
                        | Value::Here { .. }
                        | Value::Stay { .. }
                        | Value::ForwardFlow { .. }
                        | Value::FunctionFlow { .. }
                        | Value::Then { .. }
                        | Value::FlowProduct(..)
                        | Value::Higher { .. }
                        | Value::HigherEvaluation { .. }
                        | Value::QuantifiedEvaluation { .. }),
                    ) => {},
                    Some(
                        &(Value::ListCons(first, second) | Value::StaticApplication(first, second)),
                    ) => {
                        work.extend([AnyNode::Value(first), AnyNode::Value(second)]);
                    },
                    Some(&Value::Tuple(ref components)) => {
                        work.extend(components.iter().copied().map(AnyNode::Value));
                    },
                    Some(&(Value::Injection(_, body) | Value::Lift { body, .. })) => {
                        work.push(AnyNode::Value(body));
                    },
                    Some(&Value::Constant(constant)) => {
                        if self.unfoldings.unfolding(constant) != Unfoldable::Opaque {
                            return Rigidity::Flexible;
                        }
                    },
                    Some(&Value::Quote(quoted)) => work.push(AnyNode::ValueType(quoted)),
                    Some(&Value::QuoteComputation(quoted)) => {
                        work.push(AnyNode::CompType(quoted));
                    },
                    Some(&(Value::Thunk(_) | Value::Returned(_))) | None => {
                        return Rigidity::Flexible;
                    },
                },
                AnyNode::Computation(computation) => match self.arena.computation(computation) {
                    Some(&(Computation::Return(value) | Computation::Force(value))) => {
                        work.push(AnyNode::Value(value));
                    },
                    Some(&Computation::Application(head, argument)) => {
                        work.extend([AnyNode::Computation(head), AnyNode::Value(argument)]);
                    },
                    Some(
                        &(Computation::Transport(..)
                        | Computation::PathTransport { .. }
                        | Computation::TelescopeTransport { .. }
                        | Computation::Ride { .. }
                        | Computation::TelescopeRide { .. }
                        | Computation::RelatedApplication { .. }
                        | Computation::DataCase { .. }
                        | Computation::SigmaSplit { .. }
                        | Computation::RecordProjection(..)
                        | Computation::TupleProjection(..)
                        | Computation::Lambda(_)
                        | Computation::Fixpoint { .. }
                        | Computation::ListFold { .. }
                        | Computation::ListCase { .. }
                        | Computation::Bind(..)
                        | Computation::Case { .. }
                        | Computation::With(..)
                        | Computation::Project(..)),
                    )
                    | None => {
                        return Rigidity::Flexible;
                    },
                },
                AnyNode::ValueType(value_type) => match self.arena.value_type(value_type) {
                    Some(&ValueType::Data { ref arguments, .. }) => {
                        work.extend(arguments.iter().copied().map(AnyNode::Value));
                    },
                    Some(&ValueType::Record(ref fields)) => {
                        work.extend(fields.values().copied().map(AnyNode::ValueType));
                    },
                    Some(
                        &(ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_)),
                    ) => {},
                    Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                        work.extend(parts.iter().copied().map(AnyNode::ValueType));
                    },
                    Some(
                        &ValueType::PathUniverse(source, target)
                        | &ValueType::FlowUniverse(source, target),
                    ) => {
                        work.extend([AnyNode::Value(source), AnyNode::Value(target)]);
                    },
                    Some(
                        &ValueType::Path {
                            domain,
                            left,
                            right,
                        }
                        | &ValueType::Flow {
                            domain,
                            source: left,
                            target: right,
                        }
                        | &ValueType::Bridge {
                            domain,
                            left,
                            right,
                        },
                    ) => {
                        work.extend([
                            AnyNode::ValueType(domain),
                            AnyNode::Value(left),
                            AnyNode::Value(right),
                        ]);
                    },
                    Some(
                        &ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        }
                        | &ValueType::Sigma { first, second },
                    ) => {
                        work.extend([AnyNode::ValueType(first), AnyNode::ValueType(second)]);
                    },
                    Some(&ValueType::Thunk(body)) => work.push(AnyNode::CompType(body)),
                    Some(
                        &ValueType::Session {
                            payloads: inner, ..
                        }
                        | &ValueType::Lift { inner, .. }
                        | &ValueType::List(inner)
                        | &ValueType::Staged { base: inner, .. },
                    ) => {
                        work.push(AnyNode::ValueType(inner));
                    },
                    Some(&ValueType::Element { code, .. }) => work.push(AnyNode::Value(code)),
                    None => return Rigidity::Flexible,
                },
                AnyNode::CompType(comp_type) => match self.arena.comp_type(comp_type) {
                    Some(&CompType::Returner(result)) => work.push(AnyNode::ValueType(result)),
                    Some(
                        &(CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain }),
                    ) => {
                        work.extend([AnyNode::ValueType(domain), AnyNode::CompType(codomain)]);
                    },
                    Some(&CompType::Element { code, .. }) => work.push(AnyNode::Value(code)),
                    Some(&CompType::With(ref components)) => {
                        work.extend(components.iter().copied().map(AnyNode::CompType));
                    },
                    Some(&CompType::Codata { ref arguments, .. }) => {
                        work.extend(arguments.iter().copied().map(AnyNode::Value));
                    },
                    None => return Rigidity::Flexible,
                },
            }
        }
        Rigidity::Rigid
    }

    /// The shape of `term` in weak head form, with each constant head's status
    /// on `side`.
    ///
    /// # Specification
    /// - requires: `term` is in weak head form.
    /// - ensures: a value's former, thunk, or head under its static
    ///   applications, innermost first; a computation's lambda, lazy pairing,
    ///   returner, or head under its spine, innermost first. A transport's path
    ///   and a ride's flow stand at the head of their elimination.
    /// - provides: what the rule table dispatches on.
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling id, a head no rule
    ///   reads, or a returned endpoint, which [`Self::settle`] reads first.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `loop` below, which descends a computation's head path,
    ///   and the `while let` loop descending a value's static applications, not
    ///   recursion.
    /// - measure: the arena position of the focus, which falls at every descent
    ///   because a child is minted before its parent.
    ///
    /// # Adequacy
    /// - hypothesis: L3: force/eta traces and neutral case/application spines
    ///   distinguish head classes and the order of their premises; static
    ///   operator traces cover static application heads; a ride over a named
    ///   flow offers that flow's unfolding on its own side only. The executable
    ///   observer checks root shape and the outermost elimination without
    ///   repeating the head walk.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    /// - witness: `path_universe::tests::refl_collapses`
    /// - witness: `replay::tests::a_projection_runs_its_side_of_a_pairing`
    /// - witness: `replay::tests::a_ride_unfolds_its_flow_where_the_dialogue_names_it`
    /// - witness: `replay::tests::an_introduction_under_a_spine_is_unreadable`
    #[spec(ensures: |ret| match term {
        Term::Value(value) => match self.arena.value(value) {
            Some(&Value::Variable(index)) => matches!(ret, Ok(Shape::Neutral(Head::Variable(found), ref spine)) if found == index && spine.is_empty()),
            Some(&Value::Constant(constant)) => matches!(ret, Ok(Shape::Neutral(head, ref spine)) if head == self.head(constant, frozen, side) && spine.is_empty()),
            Some(&Value::Thunk(body)) => ret == Ok(Shape::Thunk(body)),
            Some(&Value::Returned(_)) | None => ret == Err(unreadable()),
            Some(&Value::StaticApplication(_, argument)) => match ret {
                Ok(Shape::Neutral(_, ref spine)) => spine.last() == Some(&Elimination::StaticApply(argument))
                    && spine.iter().all(|elimination| matches!(elimination, &Elimination::StaticApply(_))),
                Err(Stop::Refused(ReplayRefusal::Unreadable)) => true,
                _ => false,
            },
            Some(_) => ret == Ok(Shape::Former),
        },
        Term::Computation(computation) => match self.arena.computation(computation) {
            Some(&Computation::Lambda(body)) => ret == Ok(Shape::Lambda(body)),
            Some(&Computation::With(ref components)) => ret == Ok(Shape::With(components.clone())),
            Some(&Computation::Fixpoint { body, .. }) => ret == Ok(Shape::Fixpoint(body, Vec::new())),
            Some(&Computation::Return(value)) => ret == Ok(Shape::Return(value)),
            Some(node) => match ret {
                Ok(Shape::Fixpoint(_, ref leading)) => matches!(*node, Computation::Application(_, argument) if leading.last() == Some(&argument)),
                Ok(Shape::Neutral(_, ref spine)) => match *node {
                    Computation::Application(head, argument) => spine.last() == Some(&Elimination::Apply(argument))
                        || spine.last() == Some(&Elimination::Fixpoint(head)),
                    Computation::Bind(_, body) => spine.last() == Some(&Elimination::Bind(body)),
                    Computation::Force(_) => spine.as_slice() == [Elimination::Force],
                    Computation::Transport(path, value) => if matches!(self.arena.value(path), Some(&Value::PathProduct(..))) {
                        spine.as_slice() == [Elimination::ProductTransport(path)]
                    } else { spine.as_slice() == [Elimination::Transport(value)] },
                    Computation::Ride { .. } => spine.as_slice() == [Elimination::Ride(computation)],
                    Computation::PathTransport { .. } => spine.as_slice() == [Elimination::PathTransport(computation)],
                    Computation::Case { .. } => spine.as_slice() == [Elimination::Case(computation)],
                    Computation::DataCase { .. } => spine.as_slice() == [Elimination::DataCase(computation)],
                    Computation::SigmaSplit { .. } => spine.as_slice() == [Elimination::SigmaSplit(computation)],
                    Computation::RecordProjection(..) => spine.as_slice() == [Elimination::RecordProjection(computation)],
                    Computation::TupleProjection(..) => spine.as_slice() == [Elimination::TupleProjection(computation)],
                    Computation::Project(side, _) => spine.last() == Some(&Elimination::Project(side)),
                    Computation::ListFold { on_nil, on_cons, .. } => spine.as_slice() == [Elimination::ListFold(on_nil, on_cons)],
                    Computation::ListCase { on_nil, on_cons, .. } => spine.as_slice() == [Elimination::ListCase(on_nil, on_cons)],
                    Computation::Lambda(_) | Computation::Return(_) | Computation::TelescopeTransport { .. } | Computation::TelescopeRide { .. } | Computation::RelatedApplication { .. } | Computation::With(..) | Computation::Fixpoint { .. } => false,
                },
                Err(Stop::Refused(ReplayRefusal::Unreadable)) => true,
                _ => false,
            },
            None => ret == Err(unreadable()),
        },
    })]
    fn shape(
        &self,
        term: Term,
        frozen: &Frozen,
        side: ConversionSide,
    ) -> Result<Shape, Stop>
    {
        let start = match term {
            Term::Value(value) => {
                return match self.arena.value(value) {
                    Some(&Value::Variable(index)) => {
                        Ok(Shape::Neutral(Head::Variable(index), Vec::new()))
                    },
                    Some(&Value::Constant(constant)) => Ok(Shape::Neutral(
                        self.head(constant, frozen, side),
                        Vec::new(),
                    )),
                    Some(&Value::Thunk(body)) => Ok(Shape::Thunk(body)),
                    Some(&Value::Returned(_)) | None => Err(unreadable()),
                    Some(&Value::StaticApplication(..)) => {
                        let mut spine = Vec::new();
                        let mut focus = value;
                        while let Some(&Value::StaticApplication(head, argument)) =
                            self.arena.value(focus)
                        {
                            spine.push(Elimination::StaticApply(argument));
                            focus = head;
                        }
                        spine.reverse();
                        let head = self.value_head(focus, frozen, side)?;
                        Ok(Shape::Neutral(head, spine))
                    },
                    Some(
                        &(Value::PathRefl(_)
                        | Value::Constructor { .. }
                        | Value::Record(_)
                        | Value::PathProduct(..)
                        | Value::SessionPath { .. }
                        | Value::SessionFlow { .. }
                        | Value::PathEquiv { .. }
                        | Value::Univalence { .. }
                        | Value::Literal(_)
                        | Value::Tuple(..)
                        | Value::ListNil
                        | Value::ListCons(..)
                        | Value::Injection(..)
                        | Value::Lift { .. }
                        | Value::Quote(_)
                        | Value::QuoteComputation(_)
                        | Value::Here { .. }
                        | Value::Stay { .. }
                        | Value::ForwardFlow { .. }
                        | Value::FunctionFlow { .. }
                        | Value::Then { .. }
                        | Value::FlowProduct(..)
                        | Value::Higher { .. }
                        | Value::HigherEvaluation { .. }
                        | Value::QuantifiedEvaluation { .. }),
                    ) => Ok(Shape::Former),
                };
            },
            Term::Computation(computation) => computation,
        };
        let mut spine = Vec::new();
        // The application node over each `Apply` the spine holds, in step:
        // a stuck fixpoint's elimination names the one over its last leading
        // argument.
        let mut applications = Vec::new();
        let mut focus = start;
        let head = loop {
            match self.arena.computation(focus) {
                Some(&Computation::DataCase { scrutinee, .. }) => {
                    spine.push(Elimination::DataCase(focus));
                    break self.value_head(scrutinee, frozen, side)?;
                },
                Some(&Computation::SigmaSplit { scrutinee, .. }) => {
                    spine.push(Elimination::SigmaSplit(focus));
                    break self.value_head(scrutinee, frozen, side)?;
                },
                Some(&Computation::RecordProjection(record, _)) => {
                    spine.push(Elimination::RecordProjection(focus));
                    break self.value_head(record, frozen, side)?;
                },
                Some(&Computation::TupleProjection(tuple, _)) => {
                    spine.push(Elimination::TupleProjection(focus));
                    break self.value_head(tuple, frozen, side)?;
                },
                Some(&Computation::ListFold {
                    list,
                    on_nil,
                    on_cons,
                    ..
                }) => {
                    spine.push(Elimination::ListFold(on_nil, on_cons));
                    break self.value_head(list, frozen, side)?;
                },
                Some(&Computation::ListCase {
                    list,
                    on_nil,
                    on_cons,
                    ..
                }) => {
                    spine.push(Elimination::ListCase(on_nil, on_cons));
                    break self.value_head(list, frozen, side)?;
                },
                Some(&Computation::Transport(path, value)) => {
                    if matches!(self.arena.value(path), Some(&Value::PathProduct(..))) {
                        spine.push(Elimination::ProductTransport(path));
                        break self.value_head(value, frozen, side)?;
                    }
                    spine.push(Elimination::Transport(value));
                    break self.value_head(path, frozen, side)?;
                },
                // A ride stuck at the table stands on its flow: a defined
                // flow unfolds where the dialogue names it, as a transport's
                // path does.
                Some(&Computation::Ride { flow, .. }) => {
                    spine.push(Elimination::Ride(focus));
                    break self.value_head(flow, frozen, side)?;
                },
                // A path transport stuck at the table stands on its path, as
                // a ride stands on its flow.
                Some(&Computation::PathTransport { path, .. }) => {
                    spine.push(Elimination::PathTransport(focus));
                    break self.value_head(path, frozen, side)?;
                },
                Some(&Computation::Lambda(body)) if spine.is_empty() => {
                    return Ok(Shape::Lambda(body));
                },
                Some(&Computation::With(ref components)) if spine.is_empty() => {
                    return Ok(Shape::With(components.clone()));
                },
                Some(&Computation::Fixpoint { body, .. }) if spine.is_empty() => {
                    return Ok(Shape::Fixpoint(body, Vec::new()));
                },
                // A fixpoint takes its leading arguments, the applications
                // directly over it; applied past them to a neutral argument it
                // is stuck on that argument's head: the application over its
                // last leading argument becomes the fixpoint's elimination, and
                // the argument's head the neutral's. Short of its staged
                // argument it stands at no gate.
                Some(&Computation::Fixpoint { body, evidence }) => {
                    let staged = match evidence {
                        FixpointEvidence::Staged { position } => usize::from(position),
                        FixpointEvidence::Partial | FixpointEvidence::StructuralDescent => 0,
                    };
                    let mut leading = Vec::with_capacity(staged);
                    let mut applied = focus;
                    while leading.len() < staged {
                        match spine.pop() {
                            Some(Elimination::Apply(argument)) => {
                                leading.push(argument);
                                applied = applications.pop().ok_or_else(unreadable)?;
                            },
                            None => return Ok(Shape::Fixpoint(body, leading)),
                            Some(_) => return Err(unreadable()),
                        }
                    }
                    let argument = match spine.pop() {
                        Some(Elimination::Apply(argument)) => argument,
                        None => return Ok(Shape::Fixpoint(body, leading)),
                        Some(_) => return Err(unreadable()),
                    };
                    spine.push(Elimination::Fixpoint(applied));
                    break self.value_head(argument, frozen, side)?;
                },
                Some(&Computation::Return(value)) if spine.is_empty() => {
                    return Ok(Shape::Return(value));
                },
                Some(&Computation::Application(head, argument)) => {
                    spine.push(Elimination::Apply(argument));
                    applications.push(focus);
                    focus = head;
                },
                Some(&Computation::Bind(bound, body)) => {
                    spine.push(Elimination::Bind(body));
                    focus = bound;
                },
                Some(&Computation::Project(component, pair)) => {
                    spine.push(Elimination::Project(component));
                    focus = pair;
                },
                Some(&Computation::Force(value)) => {
                    spine.push(Elimination::Force);
                    let head = self.value_head(value, frozen, side)?;
                    break head;
                },
                Some(&Computation::Case { scrutinee, .. }) => {
                    spine.push(Elimination::Case(focus));
                    let head = self.value_head(scrutinee, frozen, side)?;
                    break head;
                },
                // A telescope transport, a telescope ride or a related
                // application that did not reduce has no trace alphabet of its
                // own: the replay reads it as unreadable.
                Some(
                    &(Computation::Lambda(_)
                    | Computation::With(..)
                    | Computation::Return(_)
                    | Computation::TelescopeTransport { .. }
                    | Computation::TelescopeRide { .. }
                    | Computation::RelatedApplication { .. }),
                )
                | None => {
                    return Err(unreadable());
                },
            }
        };
        spine.reverse();
        Ok(Shape::Neutral(head, spine))
    }

    /// The head a forced, scrutinized or statically applied value stands for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a variable's or a constant's head.
    /// - provides: the head half of [`Self::shape`].
    /// - fails: [`ReplayRefusal::Unreadable`] on any other value.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a forced variable and a statically applied defined
    ///   constant replay as neutral heads; a non-head value is refused by the
    ///   local observer. The witnesses distinguish variable identity from the
    ///   named constant rule.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    /// - witness: `path_universe::tests::no_k`
    #[spec(ensures: |ret| ret == match self.arena.value(value) {
        Some(&Value::Variable(index)) => Ok(Head::Variable(index)),
        Some(&Value::Constant(constant)) => Ok(self.head(constant, frozen, side)),
        _ => Err(unreadable()),
    })]
    fn value_head(
        &self,
        value: ValueId,
        frozen: &Frozen,
        side: ConversionSide,
    ) -> Result<Head, Stop>
    {
        match self.arena.value(value) {
            Some(&Value::Variable(index)) => Ok(Head::Variable(index)),
            Some(&Value::Constant(constant)) => Ok(self.head(constant, frozen, side)),
            Some(
                &(Value::PathRefl(_)
                | Value::Constructor { .. }
                | Value::Record(_)
                | Value::PathProduct(..)
                | Value::SessionPath { .. }
                | Value::SessionFlow { .. }
                | Value::PathEquiv { .. }
                | Value::Univalence { .. }
                | Value::Literal(_)
                | Value::Tuple(..)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Injection(..)
                | Value::Thunk(_)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticApplication(..)
                | Value::Here { .. }
                | Value::Stay { .. }
                | Value::ForwardFlow { .. }
                | Value::FunctionFlow { .. }
                | Value::Then { .. }
                | Value::FlowProduct(..)
                | Value::Higher { .. }
                | Value::HigherEvaluation { .. }
                | Value::QuantifiedEvaluation { .. }
                | Value::Returned(_)),
            )
            | None => Err(unreadable()),
        }
    }

    /// The head `constant` makes on `side`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Status::Opaque`] without a body, [`Status::Frozen`] when
    ///   `side` froze it, [`Status::Defined`] otherwise; an operator body is a
    ///   body.
    /// - provides: the status the constant rules read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: body, operator, explicit opaque, and out-of-range
    ///   entries are observed on both sides before and after freezing; opacity
    ///   takes precedence over frozen membership.
    /// - witness: `replay::tests::frozen_heads_are_side_local_and_opacity_takes_precedence`
    #[spec(ensures: |ret| ret == Head::Constant(constant,
        if self.unfoldings.unfolding(constant) == Unfoldable::Opaque { Status::Opaque }
        else if frozen.side(side).contains(&constant) { Status::Frozen }
        else { Status::Defined }))]
    fn head(
        &self,
        constant: ConstantIndex,
        frozen: &Frozen,
        side: ConversionSide,
    ) -> Head
    {
        let status = match self.unfoldings.unfolding(constant) {
            Unfoldable::Opaque => Status::Opaque,
            Unfoldable::Body(_) | Unfoldable::Operator { .. }
                if frozen.side(side).contains(&constant) =>
            {
                Status::Frozen
            },
            Unfoldable::Body(_) | Unfoldable::Operator { .. } => Status::Defined,
        };
        Head::Constant(constant, status)
    }

    /// Replace the head constant `constant` on `side` by its body.
    ///
    /// # Specification
    /// - requires: `side`'s head is `constant`, defined.
    /// - ensures: a value side becomes its δ- or δβ-reduct, as
    ///   [`Self::unfold_value`] gives it; a computation side keeps its spine
    ///   over the body.
    /// - provides: the δ-step, and the δβ-step of a static definition.
    /// - fails: a refusal when `constant` has no body, the side has no head, or
    ///   an operator heads a computation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: named-head traces distinguish the rewritten side and
    ///   preserve the opposite side; operator instantiation preserves parameter
    ///   order and ambient indices. The postcondition frames polarity and the
    ///   untouched side without replaying substitution.
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    #[spec(
        captures: before = (goal.side(side), goal.side(opposite(side))),
        ensures: |ret| goal.side(opposite(side)) == before.1 && if ret.is_ok() {
            self.unfoldings.unfolding(constant) != Unfoldable::Opaque
                && matches!((before.0, goal.side(side)), (Term::Value(_), Term::Value(_)) | (Term::Computation(_), Term::Computation(_)))
        } else { goal.side(side) == before.0 },
    )]
    fn unfold(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
        constant: ConstantIndex,
    ) -> Result<(), Stop>
    {
        let reduct = self.unfold_term(goal.side(side), constant)?;
        goal.set(side, reduct);
        Ok(())
    }

    /// The δ- or δβ-reduct of `term`, whose head is the defined `constant`:
    /// the one δ-step a trace's `Unfold` and the endpoint reading both fire.
    ///
    /// # Specification
    /// - requires: `term`'s head is `constant`, defined.
    /// - ensures: a value its δ- or δβ-reduct, as [`Self::unfold_value`] gives
    ///   it; a computation its spine over the body, a ride's body standing as
    ///   its flow and a path transport's path its δ-reduct; of `term`'s
    ///   polarity either way.
    /// - provides: the term half of [`Self::unfold`], shared with
    ///   [`Self::normalize_returned`].
    /// - fails: as [`Self::unfold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `loop` descending the head path and the `while let` loop
    ///   rebuilding it, not recursion.
    /// - measure: the focus's arena position while descending, and the frames
    ///   left while rebuilding.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the trace's named-head unfoldings of
    ///   [`Self::unfold`], a ride's named flow among them, and a definition at
    ///   a returned endpoint's head, read at a mode switch.
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    /// - witness: `replay::tests::a_ride_unfolds_its_flow_where_the_dialogue_names_it`
    /// - witness: `replay::tests::a_path_transport_unfolds_its_path_where_the_dialogue_names_it`
    /// - witness: `element_identity::tests::a_certificate_with_a_returned_endpoint_decodes_checks_and_replays`
    #[spec(ensures: |ret| match ret {
        Ok(reduct) => self.unfoldings.unfolding(constant) != Unfoldable::Opaque
            && matches!((term, reduct), (Term::Value(_), Term::Value(_)) | (Term::Computation(_), Term::Computation(_))),
        Err(_) => true,
    })]
    fn unfold_term(
        &mut self,
        term: Term,
        constant: ConstantIndex,
    ) -> Result<Term, Stop>
    {
        let unfolding = self.unfoldings.unfolding(constant);
        let start = match term {
            Term::Value(value) => return Ok(Term::Value(self.unfold_value(value, unfolding)?)),
            Term::Computation(computation) => computation,
        };
        // An operator classifies codes, so it is never forced or scrutinized:
        // only a body stands at a computation's head.
        let Unfoldable::Body(body) = unfolding
        else {
            return Err(unreadable());
        };
        let mut frames = Vec::new();
        let mut focus = start;
        let mut rebuilt = loop {
            match self.arena.computation(focus) {
                Some(&Computation::DataCase {
                    motive,
                    ref branches,
                    equations,
                    ..
                }) => {
                    break self.arena.computation_data_case_with_equations(
                        body,
                        motive,
                        branches.clone(),
                        equations,
                    );
                },
                Some(&Computation::SigmaSplit {
                    motive,
                    body: split,
                    ..
                }) => {
                    break self.arena.computation_sigma_split(body, motive, split);
                },
                Some(&Computation::RecordProjection(_, ref label)) => {
                    break self
                        .arena
                        .computation_record_projection(body, label.clone());
                },
                Some(&Computation::TupleProjection(_, component)) => {
                    break self.arena.computation_tuple_projection(body, component);
                },
                Some(&Computation::ListFold {
                    element,
                    result,
                    on_nil,
                    on_cons,
                    ..
                }) => {
                    break self
                        .arena
                        .computation_list_fold(element, result, body, on_nil, on_cons);
                },
                Some(&Computation::ListCase {
                    on_nil, on_cons, ..
                }) => {
                    break self.arena.computation_list_case(body, on_nil, on_cons);
                },
                Some(&Computation::Transport(path, value)) => {
                    break if matches!(self.arena.value(path), Some(&Value::PathProduct(..))) {
                        self.arena.computation_transport(path, body)
                    }
                    else {
                        self.arena.computation_transport(body, value)
                    };
                },
                Some(&Computation::Ride { motive, value, .. }) => {
                    break self.arena.computation_ride(motive, body, value);
                },
                // A transport stands on its path, as [`Self::shape`] reads it.
                Some(&Computation::PathTransport {
                    motive,
                    path,
                    value,
                }) => {
                    let path = self.unfold_value(path, unfolding)?;
                    break self.arena.computation_path_transport(motive, path, value);
                },
                Some(&Computation::Application(head, argument)) => {
                    frames.push(Frame::Apply(argument));
                    focus = head;
                },
                Some(&Computation::Bind(bound, next)) => {
                    frames.push(Frame::Bind(next));
                    focus = bound;
                },
                Some(&Computation::Project(component, pair)) => {
                    frames.push(Frame::Project(component));
                    focus = pair;
                },
                Some(&Computation::Force(_)) => break self.arena.computation_force(body),
                Some(&Computation::Case { ref branches, .. }) => {
                    let branches = branches.clone();
                    break self.arena.computation_case(body, &branches);
                },
                // A stuck fixpoint's head is its argument: the constant
                // unfolds in the application directly over the fixpoint.
                Some(&Computation::Fixpoint { .. }) => {
                    let Some(Frame::Apply(_)) = frames.pop()
                    else {
                        return Err(unreadable());
                    };
                    break self.arena.computation_application(focus, body);
                },
                Some(
                    &(Computation::Lambda(_)
                    | Computation::With(..)
                    | Computation::Return(_)
                    | Computation::TelescopeTransport { .. }
                    | Computation::TelescopeRide { .. }
                    | Computation::RelatedApplication { .. }),
                )
                | None => {
                    return Err(unreadable());
                },
            }
        };
        while let Some(frame) = frames.pop() {
            rebuilt = self.wrap(rebuilt, frame);
        }
        Ok(Term::Computation(rebuilt))
    }

    /// The reduct of a value side headed by a defined constant, under the
    /// side's static applications.
    ///
    /// # Specification
    /// - requires: `unfolding` is how the constant at `value`'s head unfolds.
    /// - ensures: for a body, the body under every static application of the
    ///   side, in order; for an operator of `n` parameters, its body with its
    ///   binders instantiated at the side's first `n` arguments — the last
    ///   argument at the innermost binder, each argument shifted past the
    ///   binders still standing outside it — under the remaining applications.
    /// - provides: δ at a value, and the δβ-step of a static definition: one
    ///   saturated instance of the operator, reduced by substitution.
    /// - fails: [`ReplayRefusal::Unreadable`] when the head is not a constant,
    ///   the constant is opaque, or an operator has fewer arguments than
    ///   parameters.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `while let` loop descending the head path and the two
    ///   `for` loops over finite argument slices, not recursion.
    /// - measure: the focus's arena position while descending; then the
    ///   arguments left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by an operator of two parameters at its two
    ///   arguments, in order and swapped, at an argument open in the ambient
    ///   context, through an alias whose body stands under the spine, and short
    ///   of its arguments.
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    #[spec(ensures: |ret| match ret {
        | Ok(reduct) => self.arena.value(reduct).is_some(),
        | Err(_) => true,
    })]
    fn unfold_value(
        &mut self,
        value: ValueId,
        unfolding: Unfoldable,
    ) -> Result<ValueId, Stop>
    {
        let mut arguments = Vec::new();
        let mut focus = value;
        while let Some(&Value::StaticApplication(head, argument)) = self.arena.value(focus) {
            arguments.push(argument);
            focus = head;
        }
        arguments.reverse();
        if !matches!(self.arena.value(focus), Some(&Value::Constant(_))) {
            return Err(unreadable());
        }
        let (mut reduct, consumed) = match unfolding {
            Unfoldable::Opaque => return Err(unreadable()),
            Unfoldable::Body(body) => (body, 0_usize),
            Unfoldable::Operator { parameters, body } => {
                let count =
                    usize::try_from(u32::from(parameters)).map_err(|_overflow| unreadable())?;
                let Some(instantiated) = arguments.get(.. count)
                else {
                    return Err(unreadable());
                };
                let mut reduct = body;
                for (outside, &argument) in instantiated.iter().enumerate().rev() {
                    let binders = u32::try_from(outside).map_err(|_overflow| unreadable())?;
                    let carried = shift_value(
                        self.arena,
                        &mut self.table,
                        &mut self.memo,
                        argument,
                        BinderDepth::default(),
                        BinderDepth::from(binders),
                    );
                    reduct = substitute_value(
                        self.arena,
                        &mut self.table,
                        &mut self.memo,
                        reduct,
                        carried,
                    );
                }
                (reduct, count)
            },
        };
        for &argument in arguments.get(consumed ..).unwrap_or_default() {
            reduct = self.arena.value_static_application(reduct, argument);
        }
        Ok(reduct)
    }

    /// Put `term` in weak head form by the reductions that need no choice.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a value unchanged; a computation reduced by β, a forced
    ///   thunk, a returner met by a bind, an injection met by a case, a lazy
    ///   pairing met by a projection, a fixpoint carrying replayed
    ///   structural-descent evidence applied to a constructor, an elimination
    ///   met by a returned endpoint — a fixpoint applied to one among them —
    ///   which binds the endpoint's computation and eliminates what it returns,
    ///   that computation read first under [`Reduction::Endpoint`] when the
    ///   reading is plain — a reading stopped at a call a definition heads
    ///   bound once over the whole term, so every occurrence of that endpoint
    ///   node reads the one value the call returns — and the element-identity
    ///   transport and related application steps of
    ///   [`crate::element_identity`], and under [`Reduction::Endpoint`] a bind
    ///   over a call stuck at a variable or an opaque head read through: the
    ///   innermost such bind whose continuation, run with the call as a
    ///   returned endpoint for its value, returns or stops at a call a
    ///   definition heads, which then stands as the reading — a continuation
    ///   stuck at such a bind of its own read the same way first, a bind whose
    ///   continuation eliminates its own variable at its head passed over, and
    ///   the next bind out tried over both when it does neither — until none
    ///   fires at its head, and the original id when none fired at all.
    /// - provides: the search-free reductions the trace never records.
    /// - fails: [`Stop::Budget`] on a term that reduces past the budget;
    ///   [`Stop::PartialFixpoint`] when a fixpoint without evidence stands at
    ///   its gate — applied to a canonical argument, under a bind or under a
    ///   projection; [`ReplayRefusal::Unreadable`] on a dangling computation or
    ///   a value inspected by its reduction; a value root itself is left for
    ///   shape checking.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Budget`], [`Stop::PartialFixpoint`] or [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the inner `loop` below, which takes one step per iteration;
    ///   the `'reading` loop, which re-enters it to run a bind's continuation
    ///   and after each reading; the `loop` choosing the next bind, which pops
    ///   one attempt per failed turn, passes one bind frame per bind passed
    ///   over, and ends at a push or at the last pop; the `'endpoints` loop,
    ///   which resumes a plain reading once its met endpoint is read, and an
    ///   endpoint reading suspends none; and the `while let` loops rebuilding
    ///   the head path.
    /// - measure: the budget left, which every inner iteration charges and
    ///   every `'reading` iteration enters; then the attempts held, finite
    ///   because each was pushed by a charged iteration; then the frames left;
    ///   then the one suspended reading.
    ///
    /// # Adequacy
    /// - hypothesis: L3: beta, force, bind, and injection reductions settle
    ///   before decisions; a reduced head retains application and bind frames,
    ///   while a self-application exhausts a finite budget. These observations
    ///   bound weak-head behavior, not normalization completeness.
    /// - witness: `replay::tests::the_replay_reduces_before_it_reads_a_decision`
    /// - witness: `replay::tests::reduced_heads_retain_application_and_bind_frames`
    /// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
    /// - witness: `tests::recursive_data::a_fixpoint_computes_at_a_constructor_and_replays`
    /// - witness: `tests::recursive_data::a_partial_fixpoint_declines_at_its_gate`
    /// - witness: `path_universe::tests::transport_computes`
    /// - witness: `path_universe::tests::refl_collapses`
    /// - witness: `replay::tests::native_list_fold_reduces_without_capturing_outer_variables`
    /// - witness: `replay::tests::a_projection_runs_its_side_of_a_pairing`
    /// - witness: `replay::tests::an_endpoint_reads_a_bind_through_its_stuck_call`
    /// - witness: `replay::tests::an_endpoint_reads_a_bind_handing_its_stuck_call_to_a_definition_761`
    /// - witness: `replay::tests::an_endpoint_passes_over_a_bind_its_own_elimination_built`
    /// - witness: `replay::tests::a_decode_reads_as_the_quote_its_code_returns`
    /// - witness: `replay::tests::an_endpoint_continuation_is_spent_only_with_its_frames`
    /// - witness: `replay::tests::an_eliminated_endpoint_reads_a_bind_through_its_stuck_call`
    /// - witness: `replay::tests::an_endpoint_read_twice_runs_its_call_once_1747`
    #[spec(
        captures: before = self.spent,
        ensures: |ret| match term {
            Term::Value(_) => ret == Ok(term) && self.spent == before,
            Term::Computation(_) => match ret {
                Ok(Term::Computation(computation)) => self.spent > before && self.spent <= self.budget && self.arena.computation(computation).is_some(),
                Err(Stop::Budget) => self.spent >= self.budget,
                Err(Stop::Refused(_) | Stop::PartialFixpoint) => true,
                Ok(Term::Value(_)) => false,
            },
        },
    )]
    fn whnf(
        &mut self,
        term: Term,
        reduction: Reduction,
    ) -> Result<Term, Stop>
    {
        let Term::Computation(start) = term
        else {
            return Ok(term);
        };
        let mut frames: Vec<Frame> = Vec::new();
        let mut focus = start;
        let mut progress = Progress::Unchanged;
        // The binds an endpoint reading is trying, outermost first, while the
        // innermost one's continuation reduces in `focus` and `frames`. A
        // continuation stuck at a bind of its own is read the same way, one
        // attempt deeper.
        let mut attempts: Vec<Attempt> = Vec::new();
        // A plain reading waiting while the computation of a returned endpoint
        // it met is read as an endpoint: that computation is pure, so a bind
        // over a stuck call in it reads through, as the producer's evaluator
        // reads the value the endpoint stands for. An endpoint reading never
        // suspends, so one is held at most.
        let mut reduction = reduction;
        let mut suspended: Option<Suspended> = None;
        'endpoints: loop {
            'reading: loop {
                loop {
                    self.charge()?;
                    // An elimination meeting a returned endpoint runs the endpoint's
                    // computation and eliminates what it returns: `E[c] ⇝ c to x. E[x]`.
                    if let Some(
                        &(Computation::DataCase {
                            scrutinee: inspected,
                            ..
                        }
                        | Computation::Case {
                            scrutinee: inspected,
                            ..
                        }
                        | Computation::SigmaSplit {
                            scrutinee: inspected,
                            ..
                        }
                        | Computation::ListFold {
                            list: inspected, ..
                        }
                        | Computation::ListCase {
                            list: inspected, ..
                        }
                        | Computation::RecordProjection(inspected, _)
                        | Computation::TupleProjection(inspected, _)
                        | Computation::Force(inspected)),
                    ) = self.arena.computation(focus)
                        && let Some(&Value::Returned(returned)) = self.arena.value(inspected)
                    {
                        if reduction == Reduction::Plain {
                            suspended = Some(Suspended {
                                elimination: focus,
                                endpoint: inspected,
                                returned,
                                frames: core::mem::take(&mut frames),
                            });
                            reduction = Reduction::Endpoint;
                            focus = returned;
                            progress = Progress::Unchanged;
                            continue;
                        }
                        let bind = self.bind_returned(focus, returned)?;
                        focus = self.absorbed(bind, &mut frames)?;
                        progress = Progress::Reduced;
                        continue;
                    }
                    match self.arena.computation(focus) {
                        Some(&Computation::DataCase {
                            scrutinee,
                            ref branches,
                            equations,
                            ..
                        }) => match self.arena.value(scrutinee) {
                            Some(&Value::Constructor {
                                datatype,
                                tag,
                                ref fields,
                            }) => {
                                let branch =
                                    *branches.get(usize::from(tag)).ok_or_else(unreadable)?;
                                let field_count = fields.len();
                                focus = branch;
                                for position in 0 .. field_count {
                                    self.charge()?;
                                    let Some(matched_native_node) = self.arena.value(scrutinee)
                                    else {
                                        return Err(unreadable());
                                    };
                                    let Value::Constructor { ref fields, .. } =
                                        *matched_native_node
                                    else {
                                        return Err(unreadable());
                                    };
                                    let field = *fields.get(position).ok_or_else(unreadable)?;
                                    focus = self.arena.computation_application(focus, field);
                                }
                                // Each index equation is reflexivity at the
                                // constructor's own index, which its datatype
                                // states after the parameters.
                                let Some(&ValueType::Data { ref arguments, .. }) =
                                    self.arena.value_type(datatype)
                                else {
                                    return Err(unreadable());
                                };
                                let first = arguments
                                    .len()
                                    .checked_sub(usize::from(equations))
                                    .ok_or_else(unreadable)?;
                                let points =
                                    arguments.get(first ..).ok_or_else(unreadable)?.to_vec();
                                for point in points {
                                    self.charge()?;
                                    let reflexive = self.arena.value_here(point);
                                    focus = self.arena.computation_application(focus, reflexive);
                                }
                                progress = Progress::Reduced;
                            },
                            Some(_) => break,
                            None => return Err(unreadable()),
                        },
                        // A dependent split of a pair enters its body with the two
                        // components for its two binders, the outer binder first.
                        Some(&Computation::SigmaSplit {
                            scrutinee, body, ..
                        }) => match self.arena.value(scrutinee).map(Value::components) {
                            Some(Some(&[first, second])) => {
                                let opened = crate::rewrite::substitute_fold_head(
                                    self.arena,
                                    &mut self.table,
                                    &mut self.memo,
                                    body,
                                    first,
                                );
                                focus = self.instantiate(opened, second);
                                progress = Progress::Reduced;
                            },
                            Some(None) => break,
                            Some(Some(_)) | None => return Err(unreadable()),
                        },
                        Some(&Computation::RecordProjection(record, ref label)) => {
                            match self.arena.value(record) {
                                Some(&Value::Record(ref fields)) => {
                                    let value = *fields.get(label).ok_or_else(unreadable)?;
                                    focus = self.arena.computation_return(value);
                                    progress = Progress::Reduced;
                                },
                                Some(_) => break,
                                None => return Err(unreadable()),
                            }
                        },
                        Some(&Computation::TupleProjection(tuple, component)) => {
                            match self.arena.value(tuple).map(Value::components) {
                                Some(Some(components)) => {
                                    let value = *components
                                        .get(usize::from(component))
                                        .ok_or_else(unreadable)?;
                                    focus = self.arena.computation_return(value);
                                    progress = Progress::Reduced;
                                },
                                Some(None) => break,
                                None => return Err(unreadable()),
                            }
                        },
                        Some(&Computation::ListFold {
                            element,
                            result,
                            list,
                            on_nil,
                            on_cons,
                        }) => match self.arena.value(list) {
                            Some(&Value::ListNil) => {
                                focus = on_nil;
                                progress = Progress::Reduced;
                            },
                            Some(&Value::ListCons(head, tail)) => {
                                let branch = crate::rewrite::substitute_fold_head(
                                    self.arena,
                                    &mut self.table,
                                    &mut self.memo,
                                    on_cons,
                                    head,
                                );
                                frames.push(Frame::Bind(branch));
                                focus = self
                                    .arena
                                    .computation_list_fold(element, result, tail, on_nil, on_cons);
                                progress = Progress::Reduced;
                            },
                            Some(_) => break,
                            None => return Err(unreadable()),
                        },
                        // A list case on a cell enters its cell branch with the head
                        // and the tail for its two binders, the head outermost.
                        Some(&Computation::ListCase {
                            list,
                            on_nil,
                            on_cons,
                            ..
                        }) => match self.arena.value(list) {
                            Some(&Value::ListNil) => {
                                focus = on_nil;
                                progress = Progress::Reduced;
                            },
                            Some(&Value::ListCons(head, tail)) => {
                                let opened = crate::rewrite::substitute_fold_head(
                                    self.arena,
                                    &mut self.table,
                                    &mut self.memo,
                                    on_cons,
                                    head,
                                );
                                focus = self.instantiate(opened, tail);
                                progress = Progress::Reduced;
                            },
                            Some(_) => break,
                            None => return Err(unreadable()),
                        },
                        Some(&Computation::Transport(path, value)) => {
                            match crate::path_universe::beta(
                                self.arena,
                                crate::path_universe::Transport { path, value },
                            )
                            .map_err(|_unreadable_term| unreadable())?
                            {
                                crate::path_universe::Reduction::Reduced(reduct) => {
                                    focus = reduct;
                                    progress = Progress::Reduced;
                                },
                                crate::path_universe::Reduction::Stuck => break,
                            }
                        },
                        Some(&Computation::PathTransport {
                            motive,
                            path,
                            value,
                        }) => {
                            let term = crate::element_identity::ElementTransport {
                                motive,
                                path,
                                value,
                            };
                            match crate::element_identity::transport_beta(
                                self.arena,
                                &mut self.table,
                                &mut self.memo,
                                term,
                            )
                            .map_err(|_unreadable_term| unreadable())?
                            {
                                crate::path_universe::Reduction::Reduced(reduct) => {
                                    focus = reduct;
                                    progress = Progress::Reduced;
                                },
                                crate::path_universe::Reduction::Stuck => {
                                    match self.transport_along_word(term)? {
                                        crate::path_universe::Reduction::Reduced(reduct) => {
                                            focus = reduct;
                                            progress = Progress::Reduced;
                                        },
                                        crate::path_universe::Reduction::Stuck => break,
                                    }
                                },
                            }
                        },
                        Some(&Computation::TelescopeTransport {
                            motive,
                            path,
                            start,
                            over,
                            value,
                        }) => {
                            let term = crate::element_identity::TelescopeStep {
                                motive,
                                path,
                                start,
                                over,
                                value,
                            };
                            match crate::element_identity::telescope_beta(
                                self.arena,
                                &mut self.table,
                                &mut self.memo,
                                term,
                            )
                            .map_err(|_unreadable_term| unreadable())?
                            {
                                crate::path_universe::Reduction::Reduced(reduct) => {
                                    focus = reduct;
                                    progress = Progress::Reduced;
                                },
                                crate::path_universe::Reduction::Stuck => {
                                    match crate::element_identity::unit_fibre_beta(
                                        self.arena,
                                        self.unfoldings,
                                        term,
                                    )
                                    .map_err(|_unreadable_term| unreadable())?
                                    {
                                        crate::path_universe::Reduction::Reduced(reduct) => {
                                            focus = reduct;
                                            progress = Progress::Reduced;
                                        },
                                        crate::path_universe::Reduction::Stuck => break,
                                    }
                                },
                            }
                        },
                        Some(&Computation::Ride {
                            motive,
                            flow,
                            value,
                        }) => {
                            let term = crate::flow_universe::reduce::RideStep {
                                motive,
                                flow,
                                value,
                            };
                            match crate::flow_universe::reduce::ride_beta(
                                self.arena,
                                &mut self.table,
                                &mut self.memo,
                                term,
                            )
                            .map_err(|_unreadable_term| unreadable())?
                            {
                                crate::path_universe::Reduction::Reduced(reduct) => {
                                    focus = reduct;
                                    progress = Progress::Reduced;
                                },
                                crate::path_universe::Reduction::Stuck => break,
                            }
                        },
                        Some(&Computation::TelescopeRide {
                            motive,
                            flow,
                            over,
                            value,
                            ..
                        }) => {
                            let term = crate::flow_universe::reduce::TelescopeRideStep {
                                motive,
                                flow,
                                over,
                                value,
                            };
                            match crate::flow_universe::reduce::telescope_ride_beta(
                                self.arena,
                                &mut self.table,
                                &mut self.memo,
                                term,
                            )
                            .map_err(|_unreadable_term| unreadable())?
                            {
                                crate::path_universe::Reduction::Reduced(reduct) => {
                                    focus = reduct;
                                    progress = Progress::Reduced;
                                },
                                crate::path_universe::Reduction::Stuck => break,
                            }
                        },
                        Some(&Computation::RelatedApplication {
                            path,
                            left,
                            right,
                            body,
                            ..
                        }) => {
                            let term = crate::element_identity::RelatedStep {
                                path,
                                left,
                                right,
                                body,
                            };
                            match crate::element_identity::related_beta(
                                self.arena,
                                &mut self.table,
                                &mut self.memo,
                                term,
                            )
                            .map_err(|_unreadable_term| unreadable())?
                            {
                                crate::path_universe::Reduction::Reduced(reduct) => {
                                    focus = reduct;
                                    progress = Progress::Reduced;
                                },
                                crate::path_universe::Reduction::Stuck => break,
                            }
                        },
                        Some(&Computation::Application(head, argument)) => {
                            frames.push(Frame::Apply(argument));
                            focus = head;
                        },
                        Some(&Computation::Bind(bound, body)) => {
                            frames.push(Frame::Bind(body));
                            focus = bound;
                        },
                        Some(&Computation::Project(component, pair)) => {
                            frames.push(Frame::Project(component));
                            focus = pair;
                        },
                        // A projection of a lazy pairing runs the component it
                        // names; a pairing under no projection is in weak head
                        // form.
                        Some(&Computation::With(ref components)) => match frames.last() {
                            Some(&Frame::Project(component)) => {
                                let Some(&selected) = components.get(usize::from(component))
                                else {
                                    return Err(unreadable());
                                };
                                frames.pop();
                                focus = selected;
                                progress = Progress::Reduced;
                            },
                            Some(&(Frame::Apply(_) | Frame::Bind(_))) | None => break,
                        },
                        Some(&Computation::Force(value)) => match self.arena.value(value) {
                            Some(&Value::Thunk(body)) => {
                                focus = body;
                                progress = Progress::Reduced;
                            },
                            Some(_) => break,
                            None => return Err(unreadable()),
                        },
                        // A case over an injection selects the branch its summand
                        // names; the empty sum's elimination has none and stays stuck.
                        Some(&Computation::Case {
                            scrutinee,
                            ref branches,
                        }) => match self.arena.value(scrutinee) {
                            Some(&Value::Injection(summand, payload)) => {
                                let Some(&branch) = branches.get(usize::from(summand))
                                else {
                                    break;
                                };
                                focus = self.instantiate(branch, payload);
                                progress = Progress::Reduced;
                            },
                            Some(_) => break,
                            None => return Err(unreadable()),
                        },
                        Some(&Computation::Lambda(body)) => match frames.last() {
                            Some(&Frame::Apply(argument)) => {
                                frames.pop();
                                focus = self.instantiate(body, argument);
                                progress = Progress::Reduced;
                            },
                            Some(&(Frame::Bind(_) | Frame::Project(_))) | None => break,
                        },
                        // A fixpoint unfolds at its gate: applied to a canonical
                        // argument at its staged position, the `<` direction, or
                        // under a bind or a projection observing its result, the
                        // `>` direction. Conversion unfolds only a structural
                        // fixpoint, and only at a constructor; at a partial
                        // fixpoint's gate it declines rather than refutes.
                        Some(&Computation::Fixpoint { body, evidence }) => {
                            let position = match evidence {
                                FixpointEvidence::Staged { position } => usize::from(position),
                                FixpointEvidence::Partial | FixpointEvidence::StructuralDescent => {
                                    0
                                },
                            };
                            // The argument at the staged position: that many
                            // applications down the stack, every frame above it an
                            // application too.
                            let mut reached = None;
                            let mut observed = false;
                            for (offset, frame) in frames.iter().rev().enumerate() {
                                match *frame {
                                    Frame::Apply(argument) => {
                                        if offset == position {
                                            reached = Some((offset, argument));
                                            break;
                                        }
                                    },
                                    Frame::Bind(_) | Frame::Project(_) => {
                                        observed = true;
                                        break;
                                    },
                                }
                            }
                            // A fixpoint's gate inspects its argument, so a returned
                            // endpoint there runs first: `fix f c ⇝ c to x. fix f x`.
                            if let Some((offset, argument)) = reached
                                && let Some(&Value::Returned(returned)) = self.arena.value(argument)
                            {
                                let mut applied = focus;
                                for _argument in 0 ..= offset {
                                    let Some(Frame::Apply(argument)) = frames.pop()
                                    else {
                                        return Err(unreadable());
                                    };
                                    applied = self.arena.computation_application(applied, argument);
                                }
                                if reduction == Reduction::Plain {
                                    suspended = Some(Suspended {
                                        elimination: applied,
                                        endpoint: argument,
                                        returned,
                                        frames: core::mem::take(&mut frames),
                                    });
                                    reduction = Reduction::Endpoint;
                                    focus = returned;
                                    progress = Progress::Unchanged;
                                    continue;
                                }
                                let bind = self.bind_returned(applied, returned)?;
                                focus = self.absorbed(bind, &mut frames)?;
                                progress = Progress::Reduced;
                                continue;
                            }
                            let gate = match reached {
                                Some((_, argument)) => match self.arena.value(argument) {
                                    Some(&Value::Constructor { .. }) => Gate::Constructor,
                                    Some(
                                        &(Value::Variable(_)
                                        | Value::Constant(_)
                                        | Value::StaticApplication(..)),
                                    ) => Gate::Shut,
                                    Some(_) => Gate::Canonical,
                                    None => return Err(unreadable()),
                                },
                                None if observed => Gate::Observed,
                                None => Gate::Shut,
                            };
                            match (evidence, gate) {
                                (
                                    FixpointEvidence::StructuralDescent
                                    | FixpointEvidence::Staged { .. },
                                    Gate::Constructor,
                                ) => {
                                    let recursive = self.arena.value_thunk(focus);
                                    focus = self.instantiate(body, recursive);
                                    progress = Progress::Reduced;
                                },
                                (
                                    FixpointEvidence::Partial,
                                    Gate::Constructor | Gate::Canonical | Gate::Observed,
                                ) => return Err(Stop::PartialFixpoint),
                                (
                                    FixpointEvidence::StructuralDescent
                                    | FixpointEvidence::Staged { .. },
                                    Gate::Canonical | Gate::Observed | Gate::Shut,
                                )
                                | (FixpointEvidence::Partial, Gate::Shut) => break,
                            }
                        },
                        Some(&Computation::Return(value)) => match frames.last() {
                            Some(&Frame::Bind(body)) => {
                                frames.pop();
                                focus = self.instantiate(body, value);
                                progress = Progress::Reduced;
                            },
                            Some(&(Frame::Apply(_) | Frame::Project(_))) | None => break,
                        },
                        None => return Err(unreadable()),
                    }
                }
                let mut next = match attempts.last() {
                    Some(_)
                        if frames.is_empty()
                            && matches!(
                                self.arena.computation(focus),
                                Some(&Computation::Return(_))
                            ) =>
                    {
                        // The continuation returned: its bind is spent.
                        if let Some(tried) = attempts.pop() {
                            frames = tried.outer;
                        }
                        progress = Progress::Reduced;
                        continue;
                    },
                    Some(_) | None if reduction == Reduction::Endpoint => {
                        (focus, core::mem::take(&mut frames), progress, true)
                    },
                    Some(_) | None => break,
                };
                loop {
                    let (call, mut outer, before, first) = next;
                    let (call, bind) = self.next_bind(call, &mut outer);
                    match bind {
                        // A stuck transport chained into another transport is a
                        // `cong` chain, left whole for `fuse` to compose: reading
                        // through it rebuilds the chain over its own returned leaf
                        // without end.
                        Some(body)
                            if !first
                                || matches!(
                                    self.shape(
                                        Term::Computation(call),
                                        &Frozen::default(),
                                        ConversionSide::Left
                                    ),
                                    Ok(Shape::Neutral(
                                        Head::Variable(_) | Head::Constant(_, Status::Opaque),
                                        ref spine
                                    )) if !(matches!(spine.as_slice(), [.., Elimination::PathTransport(_)])
                                        && matches!(
                                            self.arena.computation(body),
                                            Some(&Computation::PathTransport { .. })
                                        ))
                                )
                                || self.reading == Reading::Forced
                                    && self.shut_recursion(call).is_some() =>
                        {
                            if matches!(
                                self.continuation_of(body),
                                Continuation::Eliminates | Continuation::Returns
                            ) {
                                // Read through, this bind restores the elimination
                                // of a returned endpoint it came from, which binds
                                // the same call again: it never returns; or it is
                                // the call's own η-expansion, which the goal reads
                                // back as the call and expands again. It stays
                                // over its call, and the next bind out is tried
                                // over both.
                                let call = self.arena.computation_bind(call, body);
                                next = (call, outer, before, false);
                                continue;
                            }
                            let leaf = self.arena.value_returned(call);
                            focus = self.instantiate(body, leaf);
                            attempts.push(Attempt {
                                outer,
                                call,
                                body,
                                progress: before,
                            });
                            continue 'reading;
                        },
                        unread => {
                            // No bind is left, or a definition heads the call:
                            // this reading stands as it is.
                            if let Some(body) = unread {
                                outer.push(Frame::Bind(body));
                            }
                            let Some(tried) = attempts.pop()
                            else {
                                frames = outer;
                                focus = call;
                                progress = before;
                                break 'reading;
                            };
                            // The enclosing continuation stopped at a call a
                            // definition heads: the reading is that call, under
                            // the eliminations outside the bind, and the
                            // conversion unfolds it by a recorded step.
                            if matches!(
                                self.shape(
                                    Term::Computation(call),
                                    &Frozen::default(),
                                    ConversionSide::Left
                                ),
                                Ok(Shape::Neutral(Head::Constant(_, Status::Defined), _))
                            ) {
                                frames = tried.outer;
                                frames.append(&mut outer);
                                focus = call;
                                progress = Progress::Reduced;
                                continue 'reading;
                            }
                            // The enclosing continuation did not return: its bind
                            // stays over its call, and the next bind out is tried
                            // over both.
                            let call = self.arena.computation_bind(tried.call, tried.body);
                            next = (call, tried.outer, tried.progress, false);
                        },
                    }
                }
            }
            // The endpoint's computation is read: the suspended plain reading binds
            // what it came to and goes on. A reading stopped at a call a definition
            // heads waits for the conversion to unfold that call by a recorded
            // step, so it is bound once over the whole term, every occurrence of
            // the endpoint's node reading the bind's variable: the call then runs
            // once for all of them, as the producer's held endpoint keeps its one
            // unfolding for every elimination of it.
            let Some(held) = suspended.take()
            else {
                break 'endpoints;
            };
            let read = if progress == Progress::Unchanged {
                held.returned
            }
            else {
                while let Some(frame) = frames.pop() {
                    focus = self.wrap(focus, frame);
                }
                focus
            };
            if matches!(
                self.shape(
                    Term::Computation(read),
                    &Frozen::default(),
                    ConversionSide::Left
                ),
                Ok(Shape::Neutral(Head::Constant(_, Status::Defined), _))
            ) {
                let mut whole = held.elimination;
                let mut outer = held.frames;
                while let Some(frame) = outer.pop() {
                    whole = self.wrap(whole, frame);
                }
                let shared = crate::rewrite::share_endpoint(
                    self.arena,
                    &mut self.table,
                    &mut self.memo,
                    whole,
                    held.endpoint,
                );
                focus = self.arena.computation_bind(read, shared);
                frames = Vec::new();
            }
            else {
                let bind = self.bind_returned(held.elimination, read)?;
                frames = held.frames;
                focus = self.absorbed(bind, &mut frames)?;
            }
            reduction = Reduction::Plain;
            progress = Progress::Reduced;
        }
        if progress == Progress::Unchanged {
            return Ok(term);
        }
        while let Some(frame) = frames.pop() {
            focus = self.wrap(focus, frame);
        }
        Ok(Term::Computation(focus))
    }

    /// The innermost bind among `outer`, popped, with `call` under the frames
    /// inside it; or, with no bind among them, `call` under all of them.
    ///
    /// # Specification
    /// - requires: `outer` holds the frames over `call`, innermost last.
    /// - ensures: the call under every frame popped before the bind, and the
    ///   bind's body; with no bind, `outer` empty.
    /// - provides: the next bind out an endpoint reading tries in
    ///   [`Self::whnf`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `while let` loop popping `outer`, not recursion.
    /// - measure: the frames left in `outer`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an endpoint's bind over a fixpoint stuck at a
    ///   variable reads with the call under the application inside the bind;
    ///   reading the fixpoint alone as the call leaves the endpoint apart.
    /// - witness: `replay::tests::an_endpoint_reads_a_bind_through_its_stuck_call`
    #[spec(
        captures: entry = outer.len(),
        ensures: |ret| (ret.1.is_some() && outer.len() < entry) || (ret.1.is_none() && outer.is_empty()),
    )]
    fn next_bind(
        &mut self,
        call: ComputationId,
        outer: &mut Vec<Frame>,
    ) -> (ComputationId, Option<ComputationId>)
    {
        let mut call = call;
        while let Some(frame) = outer.pop() {
            if let Frame::Bind(body) = frame {
                return (call, Some(body));
            }
            call = self.wrap(call, frame);
        }
        (call, None)
    }

    /// What `body` does with its own bound variable at its head: eliminates
    /// it, as the continuation `E[x]` of a bind [`Self::bind_returned`]
    /// builds, returns it as it is, or anything else.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Continuation::Eliminates`] exactly when `body`, under any
    ///   applications whose head is no fixpoint and any projections of a lazy
    ///   pairing — the context [`Self::absorbed`] moves under the bind — is a
    ///   force, a projection, a case, a data case, a dependent split or a list
    ///   fold inspecting the innermost variable, a fixpoint applied to it, or a
    ///   transport along it or of it — the continuation the transport rows
    ///   build when they run a returned path or operand;
    ///   [`Continuation::Returns`] exactly when `body` is `return` of the
    ///   innermost variable.
    /// - provides: the binds an endpoint reading in [`Self::whnf`] passes over:
    ///   run with the call as a returned endpoint, an eliminating continuation
    ///   meets that endpoint at its head and binds the same call again, so it
    ///   never returns, and a reading nested into it would never end; read
    ///   through, a returning one is the call's η-expansion folded back, which
    ///   the goal expands again without end.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an endpoint whose recursive call waits on another
    ///   call stuck at a variable reads as its arm's constructor over both, as
    ///   the engine reads it; nesting into the bind a fixpoint's gate builds
    ///   loops until the budget declines the endpoint.
    /// - witness: `replay::tests::an_endpoint_passes_over_a_bind_its_own_elimination_built`
    /// - witness: `replay::tests::an_endpoint_stays_over_the_eta_expansion_of_its_stuck_call_473`
    /// - witness: `replay::tests::an_endpoint_stays_over_the_run_of_its_transported_operand_473`
    #[spec(ensures: |ret| ret == Continuation::Other || self.arena.computation(body).is_some())]
    fn continuation_of(
        &self,
        body: ComputationId,
    ) -> Continuation
    {
        let mut body = body;
        loop {
            match self.arena.computation(body) {
                Some(&Computation::Application(head, _))
                    if !matches!(
                        self.arena.computation(head),
                        Some(&Computation::Fixpoint { .. })
                    ) =>
                {
                    body = head;
                },
                Some(&Computation::Project(_, inner)) => body = inner,
                _ => break,
            }
        }
        let inspected = if let Some(
            &(Computation::DataCase {
                scrutinee: inspected,
                ..
            }
            | Computation::Case {
                scrutinee: inspected,
                ..
            }
            | Computation::SigmaSplit {
                scrutinee: inspected,
                ..
            }
            | Computation::ListFold {
                list: inspected, ..
            }
            | Computation::RecordProjection(inspected, _)
            | Computation::TupleProjection(inspected, _)
            | Computation::Force(inspected)),
        ) = self.arena.computation(body)
        {
            inspected
        }
        else if let Some(&Computation::Application(head, argument)) = self.arena.computation(body)
            && let Some(&Computation::Fixpoint { .. }) = self.arena.computation(head)
        {
            argument
        }
        else if let Some(&Computation::PathTransport { path, value, .. }) =
            self.arena.computation(body)
        {
            let bound = Some(&Value::Variable(DeBruijnIndex::from(0_u32)));
            if self.arena.value(path) == bound || self.arena.value(value) == bound {
                return Continuation::Eliminates;
            }
            return Continuation::Other;
        }
        else if let Some(&Computation::Return(returned)) = self.arena.computation(body) {
            if self.arena.value(returned) == Some(&Value::Variable(DeBruijnIndex::from(0_u32))) {
                return Continuation::Returns;
            }
            return Continuation::Other;
        }
        else {
            return Continuation::Other;
        };
        if self.arena.value(inspected) == Some(&Value::Variable(DeBruijnIndex::from(0_u32))) {
            Continuation::Eliminates
        }
        else {
            Continuation::Other
        }
    }

    /// `body` with its innermost binder instantiated at `value`.
    ///
    /// # Specification
    /// trivial.
    fn instantiate(
        &mut self,
        body: ComputationId,
        value: ValueId,
    ) -> ComputationId
    {
        substitute_computation(self.arena, &mut self.table, &mut self.memo, body, value)
    }

    /// `elimination`, whose inspected value is a returned endpoint, as the
    /// bind running `returned` and eliminating what it returns.
    ///
    /// # Specification
    /// - requires: `elimination` is a force, a case, a data case, a dependent
    ///   split, a list fold, a projection or a fixpoint's application, and
    ///   `returned` the computation of the returned endpoint it inspects.
    /// - ensures: `returned to x. E[x]`, where `E` is the elimination shifted
    ///   past the new binder and `x` stands where the endpoint stood.
    /// - provides: the elimination rule of a returned endpoint: a pure
    ///   returner's value is the one its computation binds.
    /// - fails: [`ReplayRefusal::Unreadable`] when `elimination` is no such
    ///   form.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a force and a case over a returned endpoint reduce to
    ///   what forcing or casing its returned value gives, and a stuck one stays
    ///   the bind; a fixpoint applied to a call it waits on unfolds that call.
    /// - witness: `element_identity::tests::a_returned_endpoint_replays_as_its_computation`
    /// - witness: `replay::tests::a_fixpoint_at_a_returned_endpoint_runs_the_endpoint_first`
    /// - witness: `replay::tests::each_elimination_runs_the_returned_endpoint_it_meets`
    #[spec(ensures: |ret| match ret {
        Ok(bind) => matches!(self.arena.computation(bind), Some(&Computation::Bind(bound, _)) if bound == returned),
        Err(_) => true,
    })]
    fn bind_returned(
        &mut self,
        elimination: ComputationId,
        returned: ComputationId,
    ) -> Result<ComputationId, Stop>
    {
        let shifted = shift_computation(
            self.arena,
            &mut self.table,
            &mut self.memo,
            elimination,
            BinderDepth::NONE,
            BinderDepth::NONE.deeper(),
        );
        let bound = self.arena.value_variable(DeBruijnIndex::from(0_u32));
        let continuation = match self.arena.computation(shifted) {
            Some(&Computation::Force(_)) => self.arena.computation_force(bound),
            Some(&Computation::RecordProjection(_, ref label)) => {
                let label = label.clone();
                self.arena.computation_record_projection(bound, label)
            },
            Some(&Computation::TupleProjection(_, component)) => {
                self.arena.computation_tuple_projection(bound, component)
            },
            Some(&Computation::Case { ref branches, .. }) => {
                let branches = branches.clone();
                self.arena.computation_case(bound, &branches)
            },
            Some(&Computation::DataCase {
                motive,
                ref branches,
                equations,
                ..
            }) => {
                let branches = branches.clone();
                self.arena
                    .computation_data_case_with_equations(bound, motive, branches, equations)
            },
            Some(&Computation::SigmaSplit { motive, body, .. }) => {
                self.arena.computation_sigma_split(bound, motive, body)
            },
            Some(&Computation::ListFold {
                element,
                result,
                on_nil,
                on_cons,
                ..
            }) => self
                .arena
                .computation_list_fold(element, result, bound, on_nil, on_cons),
            Some(&Computation::Application(head, _)) => {
                self.arena.computation_application(head, bound)
            },
            _ => return Err(unreadable()),
        };
        Ok(self.arena.computation_bind(returned, continuation))
    }

    /// `bind`, a bind [`Self::bind_returned`] built, with the applications and
    /// projections innermost on `frames` moved under its binder after the
    /// elimination: `E[c] ⇝ c to x. E[x]` over the whole elimination context,
    /// up to the first bind frame.
    ///
    /// # Specification
    /// - requires: `bind` is a bind.
    /// - ensures: `bind` itself when no application or projection is innermost
    ///   on `frames`; otherwise a bind over the same computation whose
    ///   continuation is `bind`'s under those frames, each shifted past the
    ///   binder, innermost first, and `frames` without them.
    /// - provides: the elimination rule of a returned endpoint read whole, so a
    ///   bind written over the same call compares with it as a bind.
    /// - fails: [`ReplayRefusal::Unreadable`] when `bind` is no bind.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a returned endpoint forced and applied converts with
    ///   a bind written over its call whose continuation forces and applies the
    ///   bound value.
    /// - witness: `replay::tests::a_forced_applied_endpoint_converts_with_a_bind_over_its_call_2326`
    #[spec(ensures: |ret| ret.is_err() || frames.last().is_none_or(|frame| matches!(frame, Frame::Bind(_))))]
    fn absorbed(
        &mut self,
        bind: ComputationId,
        frames: &mut Vec<Frame>,
    ) -> Result<ComputationId, Stop>
    {
        let Some(&Computation::Bind(bound, mut continuation)) = self.arena.computation(bind)
        else {
            return Err(unreadable());
        };
        let mut moved = false;
        while let Some(&frame) = frames.last() {
            let shifted = match frame {
                Frame::Apply(argument) => Frame::Apply(shift_value(
                    self.arena,
                    &mut self.table,
                    &mut self.memo,
                    argument,
                    BinderDepth::NONE,
                    BinderDepth::NONE.deeper(),
                )),
                Frame::Project(component) => Frame::Project(component),
                Frame::Bind(_) => break,
            };
            let _popped = frames.pop();
            continuation = self.wrap(continuation, shifted);
            moved = true;
        }
        if !moved {
            return Ok(bind);
        }
        Ok(self.arena.computation_bind(bound, continuation))
    }

    /// The normal form of `value` as an endpoint: a returned endpoint is what
    /// its computation returns, normalized again, and any other value itself.
    ///
    /// The computation reduces by [`Self::whnf`]'s search-free steps; at a
    /// stuck head naming a definition it takes the δ-step [`Self::unfold_term`]
    /// fires, the one step the head admits. This is the kernel's own
    /// evaluator, not a conversion: the normal form goes on to
    /// [`convert_values`]. A computation that reaches no `return` stays a
    /// returned endpoint, over what it reduced to.
    ///
    /// # Specification
    /// - requires: `value` lives in the arena.
    /// - ensures: the first value that is no returned endpoint along the chain
    ///   of returned values, or a returned endpoint whose computation is stuck
    ///   at no defined head; `value` itself when nothing reduced.
    /// - provides: the normal form [`read_endpoints`] converts.
    /// - fails: [`Stop::Budget`] past the budget; [`Stop::PartialFixpoint`] at
    ///   a partial fixpoint's gate; [`ReplayRefusal::Unreadable`] on a dangling
    ///   node or a definition that does not unfold.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Termination
    /// - reason: the outer `while let` over the chain of returned values and
    ///   the inner `loop` over one computation's reduction, not recursion.
    /// - measure: the budget left, which every inner iteration charges, and the
    ///   outer loop advances only after an inner one.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an endpoint returning through a definition reads as
    ///   its value, a stuck endpoint reads as itself, and a definition the
    ///   reading may not unfold leaves the endpoint apart from its value.
    /// - witness: `element_identity::tests::a_returned_endpoint_reads_at_a_mode_switch`
    /// - witness: `element_identity::tests::a_certificate_with_a_returned_endpoint_decodes_checks_and_replays`
    /// - witness: `replay::tests::a_stuck_endpoint_reads_as_what_it_reduced_to`
    #[spec(ensures: |ret| match ret {
        Ok(read) => self.arena.value(read).is_some(),
        Err(Stop::Budget) => self.spent >= self.budget,
        Err(_) => true,
    })]
    fn normalize_returned(
        &mut self,
        value: ValueId,
    ) -> Result<ValueId, Stop>
    {
        let mut value = value;
        while let Some(&Value::Returned(computation)) = self.arena.value(value) {
            let mut term = Term::Computation(computation);
            loop {
                self.charge()?;
                term = self.whnf(term, Reduction::Endpoint)?;
                let Term::Computation(reduced) = term
                else {
                    return Err(unreadable());
                };
                if let Some(&Computation::Return(returned)) = self.arena.computation(reduced) {
                    value = returned;
                    break;
                }
                if let Ok(Shape::Neutral(Head::Constant(constant, Status::Defined), _)) =
                    self.shape(term, &Frozen::default(), ConversionSide::Left)
                {
                    term = self.unfold_refolded(term, constant)?;
                    continue;
                }
                return Ok(if reduced == computation {
                    value
                }
                else {
                    self.arena.value_returned(reduced)
                });
            }
        }
        Ok(value)
    }

    /// The definition `call` recurses into when its head forces a recursive
    /// definition whose gate no constructor opens: `spin(x)` for a variable
    /// `x`.
    ///
    /// Such a call is stuck at a variable as surely as one headed by it: a
    /// δ-step only reaches the same fixpoint stuck at the same argument. The
    /// evaluator holds it as the call its source wrote, and the forced
    /// reading, which follows no trace, reads through a bind over it as it
    /// reads through one over a variable's call, rather than leave the δ-step
    /// in its normal form.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(k)` exactly when `call`, under its applications, forces
    ///   the constant `k`, `k`'s body is a suspended fixpoint, and the argument
    ///   at the fixpoint's gate is a variable, a constant or a static
    ///   application; `None` otherwise.
    /// - provides: the forced reading's read-through test in [`Self::whnf`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `while let` loop down the application spine, not
    ///   recursion.
    /// - measure: the focus's arena position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `spin(S(x)) then spin(a)` reads at the mode switch as
    ///   `loop ∷ (spin(x) then spin(a))`, the recursive call held as written;
    ///   δ-stepped, it reads as the bare fixpoint at `x` and the sides stay
    ///   apart.
    /// - witness: `tests::native_formers::a_recursive_call_stuck_at_a_variable_reads_as_its_call_473`
    #[spec(ensures: |ret| ret.is_none_or(|constant| self.unfoldings.unfolding(constant) != Unfoldable::Opaque))]
    fn shut_recursion(
        &self,
        call: ComputationId,
    ) -> Option<ConstantIndex>
    {
        let mut arguments = Vec::new();
        let mut head = call;
        while let Some(&Computation::Application(function, argument)) = self.arena.computation(head)
        {
            arguments.push(argument);
            head = function;
        }
        let Some(&Computation::Force(forced)) = self.arena.computation(head)
        else {
            return None;
        };
        let Some(&Value::Constant(constant)) = self.arena.value(forced)
        else {
            return None;
        };
        let Unfoldable::Body(body) = self.unfoldings.unfolding(constant)
        else {
            return None;
        };
        let Some(&Value::Thunk(suspended)) = self.arena.value(body)
        else {
            return None;
        };
        let Some(&Computation::Fixpoint { evidence, .. }) = self.arena.computation(suspended)
        else {
            return None;
        };
        let position = match evidence {
            FixpointEvidence::Staged { position } => usize::from(position),
            FixpointEvidence::Partial | FixpointEvidence::StructuralDescent => 0,
        };
        let gate = arguments
            .len()
            .checked_sub(position.saturating_add(1))
            .and_then(|at| arguments.get(at).copied())?;
        match self.arena.value(gate) {
            Some(&(Value::Variable(_) | Value::Constant(_) | Value::StaticApplication(..))) => {
                Some(constant)
            },
            Some(_) | None => None,
        }
    }

    /// `term` with its held operand, where the append rows read one, taken the
    /// one δ-step its defined head admits.
    ///
    /// The evaluator's append runs a held operand — a call such as `spin(Z)`,
    /// held as an endpoint — before it reads the operand's word, unfolding
    /// what the run meets, and records no decision for it: the dialogue under
    /// a stuck transport names no unfolding. The replay takes the same step
    /// here, by [`Self::unfold_term`], and the weak head loop runs the reduct
    /// as the returned operand it stands for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `term` with its operand `⟨c⟩` replaced by `⟨c'⟩`, `c'` the
    ///   δ-reduct of `c`, exactly when [`crate::words::held_operand`] reads `c`
    ///   and `c` is stuck at a defined head; `term` itself otherwise.
    /// - provides: the replay's reading of the evaluator's held-operand run.
    /// - fails: as [`Self::unfold_term`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `spin(Z) then spin(a)` replays as `spin(a)`; left
    ///   held, the call sticks the bind that runs it and the replay refuses
    ///   what the checker accepted.
    /// - witness: `tests::native_formers::a_composite_over_a_call_to_the_empty_word_is_its_second_word_473`
    #[spec(ensures: |ret| match ret {
        Ok(read) => self.arena.value(read.value).is_some(),
        Err(_) => true,
    })]
    fn run_held_operand(
        &mut self,
        term: crate::element_identity::ElementTransport,
    ) -> Result<crate::element_identity::ElementTransport, Stop>
    {
        let Some(held) = crate::words::held_operand(
            self.arena,
            (&mut self.table, &mut self.memo),
            self.evaluator,
            term,
        )
        else {
            return Ok(term);
        };
        let Ok(Shape::Neutral(Head::Constant(constant, Status::Defined), _)) = self.shape(
            Term::Computation(held),
            &Frozen::default(),
            ConversionSide::Left,
        )
        else {
            return Ok(term);
        };
        // A recursive definition's run stays held at a gate no constructor
        // opens, `spin(x)` for a variable `x`: the evaluator's run answers
        // nothing there and leaves the operand as it is, and so does this.
        if let Unfoldable::Body(body) = self.unfoldings.unfolding(constant)
            && let Some(&Value::Thunk(suspended)) = self.arena.value(body)
            && let Some(&Computation::Fixpoint { evidence, .. }) = self.arena.computation(suspended)
        {
            let position = match evidence {
                FixpointEvidence::Staged { position } => usize::from(position),
                FixpointEvidence::Partial | FixpointEvidence::StructuralDescent => 0,
            };
            let mut arguments = Vec::new();
            let mut head = held;
            while let Some(&Computation::Application(function, argument)) =
                self.arena.computation(head)
            {
                arguments.push(argument);
                head = function;
            }
            let gate = arguments
                .len()
                .checked_sub(position.saturating_add(1))
                .and_then(|at| arguments.get(at).copied());
            if !gate.is_some_and(|argument| {
                matches!(self.arena.value(argument), Some(&Value::Constructor { .. }))
            }) {
                return Ok(term);
            }
        }
        let Term::Computation(unfolded) =
            self.unfold_refolded(Term::Computation(held), constant)?
        else {
            return Err(unreadable());
        };
        Ok(crate::element_identity::ElementTransport {
            value: self.arena.value_returned(unfolded),
            ..term
        })
    }

    /// One transport step along a word where
    /// [`crate::element_identity::transport_beta`] sticks: the held operand
    /// run, then a held path read by the append rows, then
    /// [`crate::words::transport_word`].
    ///
    /// The evaluator holds an endpoint's call at the first definition it is
    /// stuck on, and a held path never runs: its append reads the operand's
    /// word, `tr(P, ⟨spin(a)⟩, loop ∷ p) ⇝ loop ∷ ⟨tr(P, ⟨spin(a)⟩, p)⟩`. A
    /// returned path whose computation a definition heads is that held path,
    /// so it takes [`crate::words::appended`]'s rows before
    /// [`crate::words::transport_word`] would run it first; any other
    /// returned path runs first, as the evaluator runs every value it does
    /// not hold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`crate::words::appended`]'s reduct when, after
    ///   [`Self::run_held_operand`], the path is `⟨c⟩` with `c` stuck at a
    ///   defined head and the append rows read the operand;
    ///   [`crate::words::transport_word`]'s answer otherwise.
    /// - provides: the replay's reading of transport along a word.
    /// - fails: as [`Self::run_held_operand`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `spin(S(x)) then spin(a)` replays as `loop ∷ (spin(x)
    ///   then spin(a))`, as the checker reads it; run first, the held `spin(a)`
    ///   sticks the bind and the replay refuses what the checker accepted.
    /// - witness: `tests::native_formers::a_composite_over_a_call_to_the_empty_word_is_its_second_word_473`
    #[spec(ensures: |ret| match ret {
        Ok(crate::path_universe::Reduction::Reduced(reduct)) => self.arena.computation(reduct).is_some(),
        Ok(crate::path_universe::Reduction::Stuck) | Err(_) => true,
    })]
    fn transport_along_word(
        &mut self,
        term: crate::element_identity::ElementTransport,
    ) -> Result<crate::path_universe::Reduction, Stop>
    {
        let term = self.run_held_operand(term)?;
        if let Some(&Value::Returned(along)) = self.arena.value(term.path)
            && let Ok(Shape::Neutral(Head::Constant(_, Status::Defined), _)) = self.shape(
                Term::Computation(along),
                &Frozen::default(),
                ConversionSide::Left,
            )
            && let crate::path_universe::Reduction::Reduced(reduct) = crate::words::appended(
                self.arena,
                (&mut self.table, &mut self.memo),
                self.evaluator,
                term,
            )
        {
            return Ok(crate::path_universe::Reduction::Reduced(reduct));
        }
        Ok(crate::words::transport_word(
            self.arena,
            &mut self.table,
            &mut self.memo,
            self.evaluator,
            term,
        ))
    }

    /// `computation` under `frame`.
    ///
    /// # Specification
    /// - requires: the computation and the frame children live in the arena.
    /// - ensures: an application keeps the computation as its head and the
    ///   frame argument; a bind keeps it as the bound term and the frame body;
    ///   a projection keeps it as the projected pairing and the frame side.
    /// - provides: reconstruction of the unreduced outer elimination path.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: a beta-reduced head under an application, a bind or a
    ///   projection remains convertible to the explicitly retained frame;
    ///   dropping or exchanging the frame changes that verdict.
    /// - witness: `replay::tests::reduced_heads_retain_application_and_bind_frames`
    /// - witness: `replay::tests::a_projection_runs_its_side_of_a_pairing`
    #[spec(ensures: |ret| self.arena.computation(ret) == Some(&match frame {
        Frame::Apply(argument) => Computation::Application(computation, argument),
        Frame::Bind(body) => Computation::Bind(computation, body),
        Frame::Project(component) => Computation::Project(component, computation),
    }))]
    fn wrap(
        &mut self,
        computation: ComputationId,
        frame: Frame,
    ) -> ComputationId
    {
        match frame {
            Frame::Apply(argument) => self.arena.computation_application(computation, argument),
            Frame::Bind(body) => self.arena.computation_bind(computation, body),
            Frame::Project(component) => self.arena.computation_project(component, computation),
        }
    }

    /// Close a goal owing `owed` at `verdict`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when the two agree.
    /// - provides: every leaf's check against its owed verdict.
    /// - fails: [`ReplayRefusal::Contradicted`] when they differ.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: the same equal and rigidly separated pairs are
    ///   replayed under both claims, distinguishing acceptance from a
    ///   contradiction at the consumed decision.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    #[spec(ensures: |ret| ret == if owed == verdict {
        Ok(())
    } else {
        Err(Stop::Refused(ReplayRefusal::Contradicted { at: self.at() }))
    })]
    fn close(
        &self,
        owed: Expect,
        verdict: Expect,
    ) -> Result<(), Stop>
    {
        if owed == verdict {
            return Ok(());
        }
        Err(Stop::Refused(ReplayRefusal::Contradicted { at: self.at() }))
    }

    /// Charge one step.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an available step is charged exactly once; an exhausted
    ///   budget is refused without changing the successful-step count.
    /// - provides: the replay's single bound.
    /// - fails: [`Stop::Budget`] when no step remains, including at the counter
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Budget`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: zero, one, and maximum budgets distinguish the last
    ///   admitted step from every subsequent refusal; this bounds the counter
    ///   transition, not the work within a replay step.
    /// - witness: `replay::tests::budget_exhaustion_survives_the_counter_ceiling`
    #[spec(
        captures: before = self.spent,
        ensures: |ret| if before < self.budget {
            ret == Ok(()) && self.spent == before.saturating_add(1)
        } else {
            ret == Err(Stop::Budget) && self.spent == before
        },
    )]
    fn charge(&mut self) -> Result<(), Stop>
    {
        if self.spent >= self.budget {
            return Err(Stop::Budget);
        }
        self.spent = self.spent.saturating_add(1);
        Ok(())
    }

    /// The next decision, unread.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the next decision is observed without advancing its position.
    /// - provides: lookahead shared by dispatch and refusal attribution.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: repeated lookahead preserves both a pending decision
    ///   and the trace end; the reported position cannot wrap.
    /// - witness: `replay::tests::trace_consumption_preserves_the_end_and_position_ceiling`
    #[spec(
        captures: before = self.position,
        ensures: |ret| self.position == before && match ret {
            Next::End => self.trace.size_hint() == (0, Some(0)),
            Next::Decision(_) => self.trace.size_hint().0 > 0,
        },
    )]
    fn peek(&mut self) -> Next
    {
        match self.trace.peek() {
            Some(&decision) => Next::Decision(decision),
            None => Next::End,
        }
    }

    /// Read past the next decision.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a present decision advances the position with saturation; an
    ///   exhausted trace leaves the position unchanged.
    /// - provides: the consumed-prefix index carried by refusals.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: consuming the last decision and then the end separates
    ///   advancement from exhaustion, including at the position ceiling.
    /// - witness: `replay::tests::trace_consumption_preserves_the_end_and_position_ceiling`
    #[spec(
        captures: before = self.position,
        ensures: self.position >= before && self.position <= before.saturating_add(1),
    )]
    fn take(&mut self)
    {
        if self.trace.next().is_some() {
            self.position = self.position.saturating_add(1);
        }
    }

    /// The position of the next unread decision.
    ///
    /// # Specification
    /// trivial.
    const fn at(&self) -> TracePosition
    {
        TracePosition(self.position)
    }

    /// The refusal for `next` read where it does not apply.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an available decision is inapplicable at this position; an
    ///   absent decision is exhausted rather than attributed to a slot.
    /// - provides: the distinction between a wrong decision and a missing one.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: a missing eta decision and a wrong-side eta decision
    ///   produce different refusals after the same force prefix.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    #[spec(ensures: |ret| match (next, ret) {
        (Next::Decision(_), Stop::Refused(ReplayRefusal::Inapplicable { at })) => at.0 == self.position,
        (Next::End, Stop::Refused(ReplayRefusal::Exhausted)) => true,
        _ => false,
    })]
    const fn refuse(
        &self,
        next: Next,
    ) -> Stop
    {
        match next {
            Next::Decision(_) => Stop::Refused(ReplayRefusal::Inapplicable { at: self.at() }),
            Next::End => Stop::Refused(ReplayRefusal::Exhausted),
        }
    }
}

/// The rule two shapes select.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Rule::Constants`] when either head is a defined constant; else
///   [`Rule::Force`] for a thunk against a thunk or a neutral; [`Rule::Eta`]
///   for a lambda against a neutral; [`Rule::ProductEta`] for a lazy pairing
///   against a neutral; else [`Rule::Structural`].
/// - provides: the rule table's dispatch, in the engine's order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3: the finite product of former, thunk, lambda, lazy pairing,
///   return, and variable or constant head statuses observes constant priority,
///   force priority, both eta sides, and structural fallback independently of
///   term depth.
/// - witness: `replay::tests::rule_dispatch_respects_constant_priority_and_eta_side`
#[spec(ensures: |ret| {
    let defined = [left, right].iter().any(|shape| matches!(shape, &&Shape::Neutral(Head::Constant(_, Status::Defined), _)));
    let force = matches!((left, right), (&Shape::Thunk(_), &(Shape::Thunk(_) | Shape::Neutral(..))) | (&Shape::Neutral(..), &Shape::Thunk(_)));
    let eta_left = matches!((left, right), (&Shape::Neutral(..), &Shape::Lambda(_)));
    let eta_right = matches!((left, right), (&Shape::Lambda(_), &Shape::Neutral(..)));
    let pairing_left = matches!((left, right), (&Shape::Neutral(..), &Shape::With(..)));
    let pairing_right = matches!((left, right), (&Shape::With(..), &Shape::Neutral(..)));
    match ret {
        Rule::Constants => defined,
        Rule::Force => !defined && force,
        Rule::Eta(ConversionSide::Left) => !defined && !force && eta_left,
        Rule::Eta(ConversionSide::Right) => !defined && !force && eta_right,
        Rule::ProductEta(ConversionSide::Left) => !defined && pairing_left,
        Rule::ProductEta(ConversionSide::Right) => !defined && pairing_right,
        Rule::Structural => !defined && !force && !eta_left && !eta_right && !pairing_left && !pairing_right,
    }
})]
fn rule(
    left: &Shape,
    right: &Shape,
) -> Rule
{
    let defined = |shape: &Shape| {
        matches!(
            shape,
            &Shape::Neutral(Head::Constant(_, Status::Defined), _)
        )
    };
    if defined(left) || defined(right) {
        return Rule::Constants;
    }
    match (left, right) {
        (&Shape::Thunk(_), &(Shape::Thunk(_) | Shape::Neutral(..)))
        | (&Shape::Neutral(..), &Shape::Thunk(_)) => Rule::Force,
        (&Shape::Lambda(_), &Shape::Neutral(..)) => Rule::Eta(ConversionSide::Right),
        (&Shape::Neutral(..), &Shape::Lambda(_)) => Rule::Eta(ConversionSide::Left),
        (&Shape::With(..), &Shape::Neutral(..)) => Rule::ProductEta(ConversionSide::Right),
        (&Shape::Neutral(..), &Shape::With(..)) => Rule::ProductEta(ConversionSide::Left),
        (
            &(Shape::Former
            | Shape::Thunk(_)
            | Shape::Lambda(_)
            | Shape::With(..)
            | Shape::Fixpoint(..)
            | Shape::Return(_)
            | Shape::Neutral(..)),
            _,
        ) => Rule::Structural,
    }
}

/// The commuting conversion of `F` two shapes still owe.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`BindRule::Normal`] unless both shapes are neutral over one head
///   no δ-rule can unfold; otherwise [`BindRule::Reassociate`] naming the first
///   side whose spine stacks two binds in a row, the left before the right;
///   else [`BindRule::ReturnEta`] naming the side whose spine is one
///   elimination shorter than the other's when the other's ends in a bind; else
///   [`BindRule::Normal`].
/// - provides: the order both the engine and the replay normalize a pair's
///   binds in, so the trace names each rewrite where the replay meets it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3: a stacked pair on either side, a spine one bind short on
///   either side, and a pair already normal each select a different rule;
///   reading the right side first or expanding a spine more than one bind short
///   changes the trace the engine's derivation must name.
/// - witness: `replay::tests::the_laws_of_bind_replay_by_name`
/// - witness: `replay::tests::a_bind_rule_rewrites_only_under_one_settled_head`
#[spec(ensures: |ret| {
    let stacked = |spine: &[Elimination]| spine.windows(2).any(|pair| matches!(pair, &[Elimination::Bind(_), Elimination::Bind(_)]));
    let ends = |spine: &[Elimination]| matches!(spine.last(), Some(&Elimination::Bind(_)));
    match (left, right) {
        (&Shape::Neutral(one, ref left_spine), &Shape::Neutral(other, ref right_spine))
            if one == other && !matches!(one, Head::Constant(_, Status::Defined)) =>
            ret == if stacked(left_spine) {
                BindRule::Reassociate(ConversionSide::Left)
            } else if stacked(right_spine) {
                BindRule::Reassociate(ConversionSide::Right)
            } else if left_spine.len().checked_add(1) == Some(right_spine.len()) && ends(right_spine) {
                BindRule::ReturnEta(ConversionSide::Left)
            } else if right_spine.len().checked_add(1) == Some(left_spine.len()) && ends(left_spine) {
                BindRule::ReturnEta(ConversionSide::Right)
            } else {
                BindRule::Normal
            },
        _ => ret == BindRule::Normal,
    }
})]
fn bind_rule(
    left: &Shape,
    right: &Shape,
) -> BindRule
{
    let (&Shape::Neutral(one, ref left_spine), &Shape::Neutral(other, ref right_spine)) =
        (left, right)
    else {
        return BindRule::Normal;
    };
    if one != other || matches!(one, Head::Constant(_, Status::Defined)) {
        return BindRule::Normal;
    }
    let stacked = |spine: &[Elimination]| {
        spine
            .windows(2)
            .any(|pair| matches!(pair, &[Elimination::Bind(_), Elimination::Bind(_)]))
    };
    let ends = |spine: &[Elimination]| matches!(spine.last(), Some(&Elimination::Bind(_)));
    if stacked(left_spine) {
        return BindRule::Reassociate(ConversionSide::Left);
    }
    if stacked(right_spine) {
        return BindRule::Reassociate(ConversionSide::Right);
    }
    if left_spine.len().checked_add(1) == Some(right_spine.len()) && ends(right_spine) {
        return BindRule::ReturnEta(ConversionSide::Left);
    }
    if right_spine.len().checked_add(1) == Some(left_spine.len()) && ends(left_spine) {
        return BindRule::ReturnEta(ConversionSide::Right);
    }
    BindRule::Normal
}

/// The continuation a call bound last into stands under, when `shape` is one:
/// a variable forced, applied and projected, then bound.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some(continuation)` exactly when `shape` is a neutral headed by
///   a variable whose spine's last elimination is a bind into `continuation`
///   and whose other eliminations force, apply or project; `None` otherwise.
///   Whether the continuation reads its binder is the caller's question.
/// - provides: the shape half of the discard.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Replay::discard`].
/// - witness: `replay::tests::an_unread_call_replays_as_its_continuation`
#[spec(ensures: |ret| ret.is_none() || matches!(*shape, Shape::Neutral(Head::Variable(_), ref spine)
    if matches!(spine.last(), Some(&Elimination::Bind(continuation)) if ret == Some(continuation))))]
fn unread_call(shape: &Shape) -> Option<ComputationId>
{
    let Shape::Neutral(Head::Variable(_), ref spine) = *shape
    else {
        return None;
    };
    let (&Elimination::Bind(continuation), prefix) = spine.split_last()?
    else {
        return None;
    };
    prefix
        .iter()
        .all(|elimination| {
            matches!(
                *elimination,
                Elimination::Force | Elimination::Apply(_) | Elimination::Project(_)
            )
        })
        .then_some(continuation)
}

/// The premises two spines decompose into, innermost elimination first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a refuting leaf when the spines differ in length or in any
///   elimination's kind, or two stuck fixpoints in the number of leading
///   arguments they hold; else an application's or a static application's
///   arguments, a bind's continuations, a sum case's two branches and a
///   dependent split's bodies, in spine order. A native data case first
///   compares its quoted motive, then its ordinary branch functions; a ride or
///   a path transport compares its quoted motive, then its value; a stuck
///   fixpoint compares its fixpoint, then its leading arguments in order; a
///   force, a matching record projection or a projection of one lazy-product
///   side contributes none.
/// - provides: the decomposition of two neutrals over one head.
/// - fails: unreadable native metadata when a retained source is missing or
///   malformed.
/// - panics: none.
///
/// # Errors
/// Returns an unreadable replay refusal for missing or ill-shaped native
/// sources.
///
/// # Adequacy
/// - hypothesis: L3: case branches followed by an application distinguish
///   subgoal order; two rides along one flow refute at their values' subgoal,
///   not their motives'; two path transports along one path whose motives close
///   over different environments convert by their premises; unequal spine
///   lengths and application-versus-bind kinds refute without a decision; empty
///   spines close positively. The fixtures do not enumerate all mixed spines.
/// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
/// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
/// - witness: `path_universe::tests::refl_collapses`
/// - witness: `replay::tests::a_lazy_pairing_meets_a_neutral_by_its_projections`
/// - witness: `replay::tests::a_ride_unfolds_its_flow_where_the_dialogue_names_it`
/// - witness: `replay::tests::two_stuck_path_transports_compare_by_motive_and_value`
/// - witness: `replay::tests::the_forced_loop_compares_children_only_where_the_shapes_agree`
/// - witness: `replay::tests::a_stuck_fixpoint_compares_its_leading_arguments_626`
#[spec(ensures: |ret| {
    let compatible = left.len() == right.len() && left.iter().zip(right).all(|(one, other)| match (*one,*other) {
        (Elimination::RecordProjection(a),Elimination::RecordProjection(b)) => matches!((arena.computation(a),arena.computation(b)), (Some(Computation::RecordProjection(_,a)),Some(Computation::RecordProjection(_,b))) if a == b),
        (Elimination::TupleProjection(a),Elimination::TupleProjection(b)) => matches!((arena.computation(a),arena.computation(b)), (Some(Computation::TupleProjection(_,a)),Some(Computation::TupleProjection(_,b))) if a == b),
        (Elimination::DataCase(a),Elimination::DataCase(b)) => matches!((arena.computation(a),arena.computation(b)), (Some(Computation::DataCase{branches:a,..}),Some(Computation::DataCase{branches:b,..})) if a.len() == b.len()),
        (Elimination::Case(a),Elimination::Case(b)) => {
            let width = |case: ComputationId| match *arena.computation(case)? { Computation::Case { ref branches, .. } => Some(branches.len()), Computation::DataCase { .. } | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Lambda(_) | Computation::Application(..) | Computation::Return(_) | Computation::Bind(..) | Computation::Force(_) | Computation::SigmaSplit { .. } | Computation::ListFold { .. } | Computation::ListCase { .. } | Computation::Transport(..) | Computation::PathTransport { .. } | Computation::TelescopeTransport { .. } | Computation::Ride { .. } | Computation::TelescopeRide { .. } | Computation::RelatedApplication { .. } | Computation::With(..) | Computation::Project(..) | Computation::Fixpoint { .. } => None };
            width(a).is_some() && width(a) == width(b)
        },
        (Elimination::Project(a), Elimination::Project(b)) => a == b,
        (Elimination::Fixpoint(a), Elimination::Fixpoint(b)) => matches!((fixpoint_chain(arena, a), fixpoint_chain(arena, b)), (Some((_, ref ones)), Some((_, ref others))) if ones.len() == others.len()),
        _ => core::mem::discriminant(one) == core::mem::discriminant(other),
    });
    match ret {
Err(Stop::Refused(ReplayRefusal::Unreadable)) => true,
Err(_) => false,
Ok(Structure::Leaf(Expect::NotConvertible)) => !compatible,
Ok(Structure::Leaf(Expect::Convertible)) => compatible && left.iter().all(|one| matches!(*one, Elimination::Force | Elimination::RecordProjection(_) | Elimination::TupleProjection(_) | Elimination::Project(_)) || matches!(*one, Elimination::Case(case) if arena.computation(case).is_some_and(|node| matches!(*node, Computation::Case { ref branches, .. } if branches.is_empty())))),
Ok(Structure::Premises(ref premises)) => compatible && !premises.is_empty() && {
            let mut pending = premises.iter();
            let ordered = left.iter().zip(right).all(|(one, other)| match (*one, *other) {
                (Elimination::Force, Elimination::Force) | (Elimination::RecordProjection(_),Elimination::RecordProjection(_)) | (Elimination::TupleProjection(_),Elimination::TupleProjection(_)) | (Elimination::Project(_), Elimination::Project(_)) => true,
                (Elimination::Case(a),Elimination::Case(b)) => {
if let Some(left_node) = arena.computation(a) && let Computation::Case{branches:ref a,..} = *left_node && let Some(right_node) = arena.computation(b) && let Computation::Case{branches:ref b,..} = *right_node { a.iter().zip(b.iter()).all(|(a,b)| pending.next() == Some(&Premise::computations(*a,*b))) }
 else { false }
},
                (Elimination::DataCase(a),Elimination::DataCase(b)) => { let (matched_left_value, matched_right_value) = (arena.computation(a),arena.computation(b));
if let Some(matched_left_node) = matched_left_value && let Computation::DataCase{motive:ref a_motive,branches:ref a,..} = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Computation::DataCase{motive:ref b_motive,branches:ref b,..} = *matched_right_node { pending.next().is_some_and(|premise| matches!((premise.left,premise.right),(Term::Value(left),Term::Value(right)) if arena.value(left) == Some(&Value::QuoteComputation(*a_motive)) && arena.value(right) == Some(&Value::QuoteComputation(*b_motive)))) && a.iter().zip(b).all(|(a,b)| pending.next() == Some(&Premise::computations(*a,*b))) }
 else { false }
},
                (Elimination::Ride(a), Elimination::Ride(b)) => if let (Some(&Computation::Ride { motive: a_motive, value: a_value, .. }), Some(&Computation::Ride { motive: b_motive, value: b_value, .. })) = (arena.computation(a), arena.computation(b)) {
                    pending.next().is_some_and(|premise| matches!((premise.left, premise.right), (Term::Value(left), Term::Value(right)) if arena.value(left) == Some(&Value::Quote(a_motive)) && arena.value(right) == Some(&Value::Quote(b_motive))))
                        && pending.next() == Some(&Premise::values(a_value, b_value))
                } else { false },
                (Elimination::PathTransport(a), Elimination::PathTransport(b)) => if let (Some(&Computation::PathTransport { motive: a_motive, value: a_value, .. }), Some(&Computation::PathTransport { motive: b_motive, value: b_value, .. })) = (arena.computation(a), arena.computation(b)) {
                    pending.next().is_some_and(|premise| matches!((premise.left, premise.right), (Term::Value(left), Term::Value(right)) if arena.value(left) == Some(&Value::Quote(a_motive)) && arena.value(right) == Some(&Value::Quote(b_motive))))
                        && pending.next() == Some(&Premise::values(a_value, b_value))
                } else { false },
                (Elimination::Transport(one), Elimination::Transport(other)) | (Elimination::ProductTransport(one), Elimination::ProductTransport(other)) | (Elimination::Apply(one), Elimination::Apply(other)) | (Elimination::StaticApply(one), Elimination::StaticApply(other)) => pending.next() == Some(&Premise::values(one, other)),
                (Elimination::Bind(one), Elimination::Bind(other)) => pending.next() == Some(&Premise::computations(one, other)),
                (Elimination::Fixpoint(one), Elimination::Fixpoint(other)) => matches!((fixpoint_chain(arena, one), fixpoint_chain(arena, other)), (Some((one, ref ones)), Some((other, ref others)))
                    if pending.next() == Some(&Premise::computations(one, other)) && ones.iter().zip(others).all(|(&a, &b)| pending.next() == Some(&Premise::values(a, b)))),
                (Elimination::SigmaSplit(a), Elimination::SigmaSplit(b)) => matches!((arena.computation(a), arena.computation(b)), (Some(&Computation::SigmaSplit { body: one, .. }), Some(&Computation::SigmaSplit { body: other, .. })) if pending.next() == Some(&Premise::computations(one, other))),
                (Elimination::ListFold(one_left, one_right), Elimination::ListFold(other_left, other_right))
                | (Elimination::ListCase(one_left, one_right), Elimination::ListCase(other_left, other_right)) =>
                    pending.next() == Some(&Premise::computations(one_left, other_left)) && pending.next() == Some(&Premise::computations(one_right, other_right)),
                _ => false,
            });
            ordered && pending.next().is_none()
        },
}
})]
fn spines(
    arena: &mut TermArena,
    left: &[Elimination],
    right: &[Elimination],
) -> Result<Structure, Stop>
{
    if left.len() != right.len() {
        return Ok(Structure::Leaf(Expect::NotConvertible));
    }
    let mut premises = Vec::new();
    for (&one, &other) in left.iter().zip(right) {
        match (one, other) {
            (Elimination::DataCase(a_case), Elimination::DataCase(b_case)) => {
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a_case), arena.computation(b_case))
                else {
                    return Err(unreadable());
                };
                let Computation::DataCase {
                    motive: ref a_motive,
                    branches: ref a,
                    ..
                } = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::DataCase {
                    motive: ref b_motive,
                    branches: ref b,
                    ..
                } = *right_node
                else {
                    return Err(unreadable());
                };
                if a.len() != b.len() {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
                let (a_motive, b_motive) = (*a_motive, *b_motive);
                let a_quote = arena.value_quote_computation(a_motive);
                let b_quote = arena.value_quote_computation(b_motive);
                premises.push(Premise::values(a_quote, b_quote));
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a_case), arena.computation(b_case))
                else {
                    return Err(unreadable());
                };
                let Computation::DataCase {
                    branches: ref a, ..
                } = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::DataCase {
                    branches: ref b, ..
                } = *right_node
                else {
                    return Err(unreadable());
                };
                premises.extend(a.iter().zip(b).map(|(a, b)| Premise::computations(*a, *b)));
            },
            (Elimination::RecordProjection(a), Elimination::RecordProjection(b)) => {
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a), arena.computation(b))
                else {
                    return Err(unreadable());
                };
                let Computation::RecordProjection(_, ref a) = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::RecordProjection(_, ref b) = *right_node
                else {
                    return Err(unreadable());
                };
                if a != b {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
            },
            (Elimination::TupleProjection(a), Elimination::TupleProjection(b)) => {
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a), arena.computation(b))
                else {
                    return Err(unreadable());
                };
                let Computation::TupleProjection(_, a) = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::TupleProjection(_, b) = *right_node
                else {
                    return Err(unreadable());
                };
                if a != b {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
            },
            // Two sum cases of one arity compare branch by branch; the empty
            // sum's elimination contributes nothing.
            (Elimination::Case(a_case), Elimination::Case(b_case)) => {
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a_case), arena.computation(b_case))
                else {
                    return Err(unreadable());
                };
                let Computation::Case {
                    branches: ref a, ..
                } = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::Case {
                    branches: ref b, ..
                } = *right_node
                else {
                    return Err(unreadable());
                };
                if a.len() != b.len() {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
                premises.extend(a.iter().zip(b).map(|(a, b)| Premise::computations(*a, *b)));
            },
            (Elimination::Force, Elimination::Force) => {},
            (Elimination::Transport(a), Elimination::Transport(b))
            | (Elimination::ProductTransport(a), Elimination::ProductTransport(b))
            | (Elimination::Apply(a), Elimination::Apply(b))
            | (Elimination::StaticApply(a), Elimination::StaticApply(b)) => {
                premises.push(Premise::values(a, b));
            },
            // Two rides along one neutral flow compare their motives as
            // codes, as the engine's spines compare them, then their values.
            (Elimination::Ride(a), Elimination::Ride(b)) => {
                let (
                    Some(&Computation::Ride {
                        motive: a_motive,
                        value: a_value,
                        ..
                    }),
                    Some(&Computation::Ride {
                        motive: b_motive,
                        value: b_value,
                        ..
                    }),
                ) = (arena.computation(a), arena.computation(b))
                else {
                    return Err(unreadable());
                };
                let a_quote = arena.value_quote(a_motive);
                let b_quote = arena.value_quote(b_motive);
                premises.extend([
                    Premise::values(a_quote, b_quote),
                    Premise::values(a_value, b_value),
                ]);
            },
            // Two path transports along one neutral path compare as two rides
            // do: their motives as codes, then their values.
            (Elimination::PathTransport(a), Elimination::PathTransport(b)) => {
                let (
                    Some(&Computation::PathTransport {
                        motive: a_motive,
                        value: a_value,
                        ..
                    }),
                    Some(&Computation::PathTransport {
                        motive: b_motive,
                        value: b_value,
                        ..
                    }),
                ) = (arena.computation(a), arena.computation(b))
                else {
                    return Err(unreadable());
                };
                let a_quote = arena.value_quote(a_motive);
                let b_quote = arena.value_quote(b_motive);
                premises.extend([
                    Premise::values(a_quote, b_quote),
                    Premise::values(a_value, b_value),
                ]);
            },
            (Elimination::Bind(a), Elimination::Bind(b)) => {
                premises.push(Premise::computations(a, b));
            },
            (Elimination::Fixpoint(a), Elimination::Fixpoint(b)) => {
                let (Some((one, ones)), Some((other, others))) =
                    (fixpoint_chain(arena, a), fixpoint_chain(arena, b))
                else {
                    return Err(unreadable());
                };
                if ones.len() != others.len() {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
                premises.push(Premise::computations(one, other));
                premises.extend(
                    ones.iter()
                        .zip(&others)
                        .map(|(&first, &second)| Premise::values(first, second)),
                );
            },
            (Elimination::ListFold(a, b), Elimination::ListFold(c, d))
            | (Elimination::ListCase(a, b), Elimination::ListCase(c, d)) => {
                premises.extend([Premise::computations(a, c), Premise::computations(b, d)]);
            },
            // Two dependent splits compare by their bodies under the two
            // component binders; the motives are annotations no reduction
            // reads.
            (Elimination::SigmaSplit(a), Elimination::SigmaSplit(b)) => {
                let (
                    Some(&Computation::SigmaSplit { body: one, .. }),
                    Some(&Computation::SigmaSplit { body: other, .. }),
                ) = (arena.computation(a), arena.computation(b))
                else {
                    return Err(unreadable());
                };
                premises.push(Premise::computations(one, other));
            },
            // Two projections of one side add no premise; the two sides of
            // the lazy product are apart.
            (Elimination::Project(a), Elimination::Project(b)) => {
                if a != b {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
            },
            (
                Elimination::DataCase(_)
                | Elimination::SigmaSplit(_)
                | Elimination::RecordProjection(_)
                | Elimination::TupleProjection(_)
                | Elimination::Project(_)
                | Elimination::Transport(_)
                | Elimination::ProductTransport(_)
                | Elimination::Ride(_)
                | Elimination::PathTransport(_)
                | Elimination::Force
                | Elimination::Apply(_)
                | Elimination::Bind(_)
                | Elimination::Case(..)
                | Elimination::ListFold(..)
                | Elimination::ListCase(..)
                | Elimination::StaticApply(_)
                | Elimination::Fixpoint(_),
                _,
            ) => return Ok(Structure::Leaf(Expect::NotConvertible)),
        }
    }
    Ok(Structure::of(premises))
}

/// The fixpoint a stuck fixpoint's elimination stands on and the leading
/// arguments it holds, first to last: `fix a₀ … aₖ₋₁` read as `fix` and `[a₀,
/// …, aₖ₋₁]`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` exactly when `applied` is a fixpoint under zero or more
///   applications, with that fixpoint and the applications' arguments in the
///   order they apply; `None` for a dangling node or another head.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `loop` below, which descends application heads, not recursion.
/// - measure: the arena position of the focus, which falls at every descent
///   because a child is minted before its parent.
///
/// # Adequacy
/// - hypothesis: L3 — a fixpoint staged at its second binder, stuck on a
///   variable past a leading argument, compares its leading argument after its
///   fixpoint, and two such stuck forms with different leading arguments are
///   apart.
/// - witness: `replay::tests::a_stuck_fixpoint_compares_its_leading_arguments_626`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|&(fixpoint, _)| matches!(arena.computation(fixpoint), Some(&Computation::Fixpoint { .. }))))]
fn fixpoint_chain(
    arena: &TermArena,
    applied: ComputationId,
) -> Option<(ComputationId, Vec<ValueId>)>
{
    let mut leading = Vec::new();
    let mut focus = applied;
    loop {
        let node = arena.computation(focus)?;
        if let &Computation::Application(head, argument) = node {
            leading.push(argument);
            focus = head;
            continue;
        }
        if !matches!(*node, Computation::Fixpoint { .. }) {
            return None;
        }
        leading.reverse();
        return Some((focus, leading));
    }
}

#[cfg(test)]
mod tests;
