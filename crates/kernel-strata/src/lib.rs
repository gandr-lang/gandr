//! The certified kernel's **level oracle**: the universe-level algebra over
//! zero, level variables, successor and binary maximum, held in
//! always-canonical form, with an order oracle that returns checkable evidence
//! in both directions.
//!
//! The crate holds **levels only** — no terms, no types, and not even the
//! universe rule, which is one call into [`Level::lt`] and belongs to the
//! kernel proper. It is `no_std` over `core` and `alloc`, the sharpest form of
//! the trusted base's dependency wall, and depends on no other workspace crate.
//!
//! # The algebra and its canonical form
//!
//! A level is a term over zero, level variables, successor and binary maximum,
//! interpreted over the naturals. Every such term is semantically a finite join
//! `max(c, x_1 + o_1, …, x_k + o_k)` of a constant part and per-variable
//! offsets, and that shape — dominated components removed, atoms keyed by
//! variable — is a **sorted canonical form**: two levels denote the same
//! function of their variables exactly when their canonical forms are
//! identical. [`Level`] *is* that canonical form, and the smart constructors
//! maintain it, so a non-canonical level is unrepresentable rather than merely
//! rejected.
//!
//! # The order oracle and its evidence
//!
//! `l ≤ m` over all valuations is decided by **domination**: every atom of `l`
//! must be dominated by a same-variable atom of `m`, and `l`'s constant part by
//! `m`'s value at the zero valuation. The oracle returns checkable evidence in
//! both directions — a [`LeqWitness`] pairing each left atom with its
//! dominating bound, or a [`LeqRefutation`] carrying a concrete
//! counter-valuation — and [`validate_witness`] and [`validate_refutation`]
//! check either against the two levels. Trust concentrates in the validators,
//! so the decision procedure is self-incriminating under mutation.
//!
//! # The landmark poset and entailment
//!
//! A fixed, declared set of order constraints over level variables — the
//! **landmark poset** — is admitted by loop-checking, which is a dichotomy with
//! evidence on both sides: [`LandmarkPoset::admit`] returns either an admitted
//! poset carrying a [`ConsistencyWitness`], an explicit homomorphism into `ℕ`
//! checked by evaluating every constraint under it, or a [`LoopWitness`], a
//! replayable pumping derivation showing no such homomorphism can exist.
//! Entailment under an admitted poset —
//! [`LandmarkPoset::entails_leq_with_evidence`] and
//! [`LandmarkPoset::entails_lt_with_evidence`] — returns a forward-derivation
//! [`EntailmentWitness`] or an [`EntailmentCountermodel`], each with its
//! validator.
//!
//! Declared constraints are **variable-only**, and query constants ride a
//! pinned bottom generator internal to the encoding; the landmark-poset module
//! carries the soundness argument. With no constraints declared, entailment
//! agrees with the free-fragment oracle on every input, which the property
//! differential pins.
//!
//! # Evidence and its validators
//!
//! Evidence types keep their fields private, so a witness is unforgeable
//! outside the oracle. Each validator recomputes what the evidence claims
//! rather than trusting it.
//!
//! A derivation records only clause index and shift for each step; a
//! validator recomputes every conclusion. Clause indices refer to one
//! documented, deterministic compilation (declaration order, ascending
//! variable order within a constraint), so an index means the same thing to
//! the oracle, the validators and a reviewer.
//!
//! The firing log behind a derivation carries, at each step, the atom its
//! instance concluded. Truncating the log to the prefix that covers the goals
//! therefore needs neither a clause lookup nor arithmetic, and its one `None`
//! means exactly that the log does not cover the goals.
//!
//! Saturation reports divergence from the resulting model, not only from
//! updates made during the current run. An infinite seed is therefore
//! divergent even with no clauses and no firing log. The executable
//! postcondition checks this model/status correspondence, and a zero-update
//! witness preserves both the infinite component and its finite sibling.
//! Counting only newly infinite updates would misclassify that admitted seed.
//!
//! [`EvidenceSubject`] names what a seed or goal refers to: a declared level
//! variable, or the pinned bottom generator that carries constants. The
//! crate's `Option` returns — `Level::offset_of`, `ModelValue::as_finite` and
//! the model lookups — are genuine absence, and each specification says so. A
//! violated constraint is reported by [`ConstraintIndex`].
//!
//! Order shifts and counter-valuation spikes use checked addition, never
//! saturation: truncating a natural-number successor would change the relation
//! in the level algebra. An unrepresentable shift routes to refusal; a
//! validator rejects an insufficient atom or constant bound. The comparison's
//! zero-valuation overflow branch is unreachable because its components are
//! u64-wide and its arithmetic is u128-wide. Widening components requires a
//! distinct overflow carrier before that exclusion changes: a zero valuation
//! does not refute every unrepresentable-spike case. The alternative,
//! saturating the widened sums, hides that obligation. Ceiling witnesses check
//! strict irreflexivity, a spike exactly one past `u64::MAX` and rejection of a
//! forged strict bound; they do not claim to exercise an unreachable u128
//! overflow.
//!
//! # The level language
//!
//! Query constants ride a pinned bottom generator `⊥`, ordered below every
//! in-scope variable by clauses added at query time. That encoding is sound,
//! conservative and loop-immune because no declared clause mentions `⊥`.
//!
//! The stratification design excludes level inference and unification,
//! generalization, displacement, constraint hypotheses beyond the declared
//! landmark poset, `imax`, and cumulativity.
//!
//! # Specification attributes
//!
//! The `# Specification` prose states each obligation. Executable
//! `#[spec(...)]` predicates check canonical constructors, exact arithmetic
//! and refusal boundaries, comparison modes, evidence validity, compilation
//! inputs and replay conclusions. Private algorithm helpers and the
//! differential suites' generators, evaluators and assertion helpers carry the
//! same discipline as public entry points.
//!
//! Each nontrivial item has a `# Adequacy` hypothesis naming its input domain,
//! observer and defect classes, with links to runnable witnesses. The evidence
//! includes independent semantic and entailment differentials, adversarial
//! certificates, numeric ceilings, empty domains, exact derivation limits and
//! the first covering log prefix. Replay establishes coverage; the
//! shortest-prefix witness separately establishes minimality.
//!
//! The predicates run under `--cfg anodized_panic`; normal builds do not
//! repeat their checking traversals. Admission and replay check the portions
//! of their postconditions available from retained data rather than taking
//! owned snapshots of consumed inputs. Least-model identity and termination
//! remain mathematical obligations, with termination stated in
//! `- intension:` clauses.
//!
//! Const-compatible predicates check cross-domain shifts, finite-model
//! projection and strictness without removing compile-time availability.
//! Explicit `- executable: none` clauses explain the remaining boundaries:
//! opaque iterators cannot be consumed by a postcondition; a strategy's full
//! support concerns future draws; and data-item invariants are not checked at
//! construction or relate the value to external operands. Their adequacy
//! witnesses still apply.
//!
//! # Differential suites
//!
//! The property suites generate free level terms as a flat, id-addressed
//! arena: a node vector in topological order, every child an index into an
//! earlier slot, the root at the last slot. Reference evaluation,
//! canonical-form construction and successor counting are each one forward
//! pass over that vector, so the suites carry no recursive type and no
//! explicit frame stack. A shared node denotes one value, so sharing is
//! semantically transparent.
//!
//! # Relationship to `gandr-theory-orders`
//!
//! The two crates share no machinery, and the kernel takes no dependency on
//! the theory crate. `gandr-theory-orders` maintains a total order over opaque
//! handles for constant-time comparison. This crate decides a partial order
//! over level terms, quantified over all valuations, and returns a certificate
//! either way. Neither operation is expressible in the other's vocabulary, and
//! the trusted base depends on no workspace crate outside the kernel category.
//!
//! The papers the crate draws on are in its `README.md`, § References.

// Module documentation that predates the shape lint: 10 headings outside the
// vocabulary and 2 budgets exceeded. Each allow leaves with the rewrite that
// clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

mod entail;
mod horn;
mod level;
mod order;
mod poset;

pub use crate::entail::Entailment;
pub use crate::entail::EntailmentCountermodel;
pub use crate::entail::EntailmentHolds;
pub use crate::entail::EntailmentWitness;
pub use crate::entail::validate_entailment_countermodel;
pub use crate::entail::validate_entailment_witness;
pub use crate::horn::ClauseIndex;
pub use crate::horn::HornOffset;
pub use crate::horn::HornShift;
pub use crate::horn::ModelIsInfinite;
pub use crate::horn::ModelValue;
pub use crate::level::Level;
pub use crate::level::LevelConstant;
pub use crate::level::LevelError;
pub use crate::level::LevelIsZero;
pub use crate::level::LevelOffset;
pub use crate::level::LevelValue;
pub use crate::level::LevelVar;
pub use crate::level::LevelVarIndex;
pub use crate::order::AtomBound;
pub use crate::order::ConstantBound;
pub use crate::order::EvidenceError;
pub use crate::order::LeqRefutation;
pub use crate::order::LeqWitness;
pub use crate::order::OrderComparison;
pub use crate::order::Strictness;
pub use crate::order::validate_refutation;
pub use crate::order::validate_witness;
pub use crate::poset::AdmissionOutcome;
pub use crate::poset::ConsistencyValue;
pub use crate::poset::ConsistencyWitness;
pub use crate::poset::ConstraintIndex;
pub use crate::poset::ConstraintRelation;
pub use crate::poset::Derivation;
pub use crate::poset::DerivationStep;
pub use crate::poset::EvidenceSubject;
pub use crate::poset::LandmarkConstraint;
pub use crate::poset::LandmarkPoset;
pub use crate::poset::LoopWitness;
pub use crate::poset::PosetError;
pub use crate::poset::PosetEvidenceError;
pub use crate::poset::validate_consistency;
pub use crate::poset::validate_loop_witness;
