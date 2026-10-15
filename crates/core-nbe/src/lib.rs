//! Normalization by evaluation for the core language: the **glued value
//! domain**, the per-run arena that owns it, its policy parameters, the
//! machine that evaluates a core term to weak head, the machine that reads one
//! back, and the machine that decides conversion.
//!
//! - [`DomainArena`] owns every glued node one run produces. A node carries a
//!   [`TermFace`], and a neutral carries an [`Unfolding`] beside its neutral
//!   form.
//! - [`ValueClosure`] and [`CompClosure`] suspend a body over a two-zone
//!   [`Environment`]; a quote evaluates to a code, a value closure over the
//!   quote, since a type has no weak head.
//! - [`SchedulingPolicy`], [`DuplicationPolicy`] and [`GranularityPolicy`] are
//!   the parameters the domain and its conversion machine are written against.
//! - [`eval_value`] and [`eval_computation`] evaluate to weak head;
//!   [`readback_value`] and [`readback_computation`] read back under a
//!   [`ReadbackMode`].
//! - [`convert_values`] and [`convert_computations`] run the conversion steps
//!   that need no search — identity, the [`Guard`] every node is minted with,
//!   and structural comparison — answering a [`Settlement`].
//! - [`decide`] runs step 4, the lazy concurrent search over goals and
//!   evaluation channels, answering a [`MachineVerdict`] and emitting its
//!   winning derivation through a trace sink. It re-shares the goals it starts
//!   fresh through a check memo keyed by [`GoalSupport`], [`ResharingMemo`] on
//!   the engine path, and reports the [`SupportEdges`] its entries rest on. Two
//!   codes are compared whole: α-equal or rigidly apart is answered as a shared
//!   comparison, and anything that could still unfold inside a type is declined
//!   with [`DeclineReason::UndecidedCodes`].
//! - [`Overlay`] holds sharing syntax over the core language in four flat
//!   families, minted only over children it holds and checked by
//!   [`Overlay::validate`] over a heap worklist; [`erase_value`] and its
//!   siblings erase it, with no policy, back to the unshared core term, and
//!   [`SharingMeasure::of`] measures one root of it — its shares, occurrences,
//!   share depth, node count and expansion size — in one heap walk.
//! - [`eval_overlay_value`] and [`eval_overlay_computation`] evaluate an
//!   overlay root by erasing it and running the unshared machine over the
//!   erasure: the reference every sharing stance is compared against.
//! - [`duplicate_value`] and [`duplicate_computation`] rebuild an overlay root
//!   under a [`DuplicationPolicy`] in one heap walk: copied shares are inlined,
//!   shared ones kept, and under the spinal stance an abstraction's share is
//!   distributed over its ribs; the output erases to the input's tree.
//! - [`TracedDuplication`] installs a duplication stance bound to the trace
//!   sink every conversion decided under it records into, the one route by
//!   which the spinal stance reaches evaluation; its evaluator shares each
//!   rib's evaluation across the occurrences that read it in one configuration.
//! - A hole evaluates to a neutral headed by [`NeutralHead::Hole`], suspended
//!   in its environment, and a mark to one headed by [`NeutralHead::Mark`];
//!   [`fill_and_resume`] writes a hole of a result and runs what the fill
//!   unblocked, and [`match_pattern`] and [`select_arm`] classify a match's
//!   arms in three values against a scrutinee that may hold a hole.
//! - [`identity`] is the identity recursion: what the paths of a path type are,
//!   carrier by carrier, read against evaluated endpoints, and the clause a
//!   carrier's head selects, an open carrier's being its own neutral fibre.
//!
//! What a caller must guarantee is listed in this crate's `README.md`, §
//! Expected features; each module's documentation states its mechanism and its
//! decisions.
//!
//! # Provided items
//!
//! - `eval_value` and `eval_computation`: weak-head evaluation, refusing with
//!   `EvalFault`; `eval_value_within` and `eval_comp_within` evaluate in an
//!   environment supplied by the caller and return the remaining fuel. This
//!   lets operator bodies and selected pattern arms run at retained bindings
//!   without minting an application.
//! - `readback_value` and `readback_computation` under
//!   `ReadbackMode::ZeroUnfold` or `ReadbackMode::Unfolding`, refusing with
//!   `ReadbackFault`.
//! - Native list values and pure right folds: evaluation reduces cells
//!   iteratively, while a neutral list retains its nil closure and two-binder
//!   cell closure. Readback preserves annotations and captured variables;
//!   conversion compares both branch scopes, with kernel-replayed equality and
//!   refutations. Witness:
//!   `machine::tests::neutral_list_fold_conversion_replays_both_branch_scopes`.
//! - `DomainArena` with `DomainValueId`, `DomainCompId`, `NeutralId`,
//!   `ValueClosureId` and `CompClosureId`: checked constructors and lookups,
//!   `force_neutral`, and `RunWatermark` with `DomainArena::truncate_to`.
//! - The glued vocabulary: `DomainValue`, `DomainComp`, `Neutral`,
//!   `NeutralHead`, `Elimination`, `TermFace`, `CompTermFace`, `Unfolding` and
//!   `Glued`.
//! - `ValueClosure`, `CompClosure` and the two-zone `Environment` they close
//!   over.
//! - `SchedulingPolicy` with its `Share`, and `DuplicationPolicy` with
//!   `DuplicationPolicy::copies`.
//! - `GranularityPolicy` with its `GranularityStance`: how finely the
//!   conversion machine shares evaluations, `Skeleton` by default and `Spinal`
//!   refused with `PolicyRefusal::GranularityGated`.
//! - `Definitions`: the lowered chain, the definitional environment and the
//!   scope a run reads unfoldings through, with the `Endpoints` stance a
//!   compound endpoint reads in, the `Recursion` stance a readback names a
//!   definition's own recursion by, and `Fuel`, the run's budget.
//! - `LoweredChain`: a definition chain with every body lowered into the run's
//!   core arena in one pass, so `ReadbackMode::Unfolding` forces any body the
//!   chain holds — evaluating its lowering closed and recording it with
//!   `force_neutral` — and `ReadbackFault::UnloweredBody` is reachable only for
//!   a body no entry names. `LoweredChain::define` appends one definition whose
//!   body is already lowered, in place, and equals the extended chain lowered
//!   whole.
//! - `Presented` with `LoweredChain::present`: the rules a data declaration
//!   presents its type by. The conversion machine reads a value pair's
//!   presented constructors by their normal forms before it plans the pair, the
//!   kernel's replay taking the same normal forms after weak head reduction, so
//!   the step records no decision (`presented` module docs). Witness:
//!   `presented::tests::a_circle_word_reads_as_its_reduced_word`.
//! - `convert_values` and `convert_computations`: conversion steps 1 through 3,
//!   answering a `Settlement` — `Identical` from step 1, `GuardedApart` from
//!   step 2, `StructurallyEqual`, `StructurallyApart` or `Deferred` with its
//!   `Deferral` from step 3 — projected by `Settlement::verdict` to a
//!   three-valued `Convertibility`, refusing with `ConversionFault`. Each step
//!   answers a case the previous one does not, and a pair needing an unfolding
//!   or an opened binder is deferred, never separated.
//! - `decide`: the conversion machine over a `Problem` under `MachineSettings`,
//!   generic over the check memo it re-shares goals through, answering a
//!   `MachineReport` with its `MachineVerdict`, `ProcessCount`,
//!   `DerivationCount`, `StepCount` and `SupportEdges`, and emitting the
//!   winning derivation in preorder through a `TraceSink<TraceNode>`; refusing
//!   with `ConversionFault`. Positive leaves carry explicit shared-comparison
//!   evidence so nested component proofs retain their boundaries. The
//!   search-free steps answer first with no process started; otherwise goals
//!   and evaluation channels run fairly over one run queue until the root
//!   answers or the run declines — `DeclineReason::Cycle` when a goal would
//!   unfold a definition over a spine already unfolded on its chain or the
//!   needed goals all wait on one another through a re-shared goal,
//!   `DeclineReason::Budget` when the run spends its `StepBudget`. Every rule
//!   arm is exercised, both verdicts and both declines, a refutation naming its
//!   negative premise and outranking a decline, one channel per distinct
//!   definition body, a null sink that keeps no derivation while reaching the
//!   recording sink's verdict, and a null memo that reaches the live memo's
//!   verdict. Every recorded derivation replays through `gandr-kernel-core`'s
//!   `replay` to the machine's verdict, a trace claiming the other verdict or
//!   naming the wrong side is refused, and a run an unlucky schedule declines
//!   stays declined through the kernel.
//! - The commuting conversions of `F` in `decide`: before two neutral
//!   computations over one head decompose, the machine makes the first two
//!   binds in a row on a side one (`Reassociate`), then binds a side one bind
//!   short into `return` (`ReturnEta`), each a recorded decision in the order
//!   the kernel's replay reads; the rewritten spine holds a native continuation
//!   (`CompBody::Then`, `CompBody::Returned`) rather than source syntax, and
//!   the structural steps defer such a pair rather than separate it. Witness:
//!   `machine::tests::the_laws_of_bind_convert_by_their_decisions`.
//! - `GoalSupport`, the key a goal started fresh is re-shared on — its
//!   `SupportSides` and binder level, agreeing by identity, digested from
//!   content on the one `ResharingPlane` — with `ResharingMemo` the engine
//!   path's memo over it and `ProcessId` its outcome; and `SupportEdges`, the
//!   `EdgeCount` of definitions and entries the run's memo entries rest on,
//!   acceptances on their winning derivation and refusals on the union over
//!   their branches. A decomposition whose premises name one pair starts one
//!   goal, so a family the memoless run expands exponentially runs linearly,
//!   and the edges grow with the distinct goals.
//! - `Guard`, the cached word minted with every value, computation and neutral
//!   and read through `DomainArena::value_guard`, `comp_guard` and
//!   `neutral_guard`; `Guard::settles` answers `GuardAnswer::Apart` only for
//!   two rigid words whose `ContentHash`es differ.
//! - `Overlay`, the sharing overlay: one flat family per core family behind
//!   `OverlayValueId`, `OverlayCompId`, `OverlayValueTypeId` and
//!   `OverlayCompTypeId`, each node one of the closed set opaque, bound, shared
//!   and grafted (`ValueNode`, `CompNode`, `ValueTypeNode`, `CompTypeNode` over
//!   `Bound`, `Sharing` and the four graft formers); minted only over children
//!   it holds, refusing with `OverlayFault`; released by `OverlayWatermark`
//!   with `Overlay::truncate_to`.
//! - `Overlay::validate`: a heap worklist over one root that refuses, by an
//!   `OverlayRefusal` naming the node, an open node set, an occurrence of
//!   another family than its leg, an occurrence out of preorder or past its
//!   share's arity, a share its body under-fills or that stands for nothing, a
//!   node reached twice and a root the overlay does not hold.
//! - `erase_value`, `erase_computation`, `erase_value_type` and
//!   `erase_comp_type`: total, policy-free erasure from an overlay root back to
//!   the unshared core term, refusing with `EraseFault` and leaving the core
//!   arena as it found it. The erased arena equals node for node the one a
//!   hand-built unshared term mints, and the unshared pipeline evaluates and
//!   reads back both to equal domain arenas, core arenas and results on every
//!   deep case.
//! - `SharingMeasure::of`: He's measure over one validated overlay root in one
//!   post-order walk on the heap — `ShareCount`, `OccurrenceCount`,
//!   `ShareDepth`, `NodeCount` and `ExpansionSize`, the last the size of the
//!   unshared term the root stands for — refusing with `MeasureFault`: a
//!   validation refusal unchanged, or a sum past a 64-bit counter named by its
//!   `MeasuredQuantity` and its node. The expansion size equals the erased
//!   term's size walked as a tree over every closed sketch of up to nine nodes
//!   and every deep case.
//! - `eval_overlay_value` and `eval_overlay_computation`: the overlay
//!   evaluator's reference — erase the root, then run the unshared machine over
//!   the erasure in the empty environment — minting into the core and domain
//!   arenas, node for node, what erasure followed by the unshared pipeline
//!   mints, with the same result and the same unspent fuel; refusing with
//!   `OverlayEvalFault`, erasure's refusal leaving the core arena as it found
//!   it.
//! - `duplicate_value` and `duplicate_computation`: an overlay root rebuilt
//!   under a `DuplicationPolicy` into fresh nodes of the same overlay in one
//!   heap walk — a copied leg inlined, a shared leg kept, and under the spinal
//!   stance an abstraction's share distributed over its ribs — the output
//!   validating and erasing to the input's tree, the input untouched; refusing
//!   with `DuplicationFault` and leaving the overlay at its entry watermark,
//!   the copying stance priced by the measure before it mints.
//! - `TracedDuplication`: a duplication stance installed with the trace sink
//!   its conversions record into, the only route to
//!   `DuplicationStance::Spinal`. `TracedDuplication::install` refuses the
//!   spinal stance over a sink that retains nothing with
//!   `PolicyRefusal::Untraced`, and `DuplicationPolicy::new` still refuses it
//!   with `PolicyRefusal::StanceGated`. The installation duplicates, evaluates
//!   an overlay root — the erase-and-clone stance through the reference, the
//!   spinal stance through its own duplicate with each leg's evaluation shared
//!   per configuration, refusing with `OverlayEvalFault::Duplication` — and
//!   runs `decide` into its sink. The kernel replays every spinal catalogue and
//!   ladder trace and agrees with each verdict; an unlucky spinal schedule
//!   declines and the kernel declines with it; every deep case evaluates and
//!   reads back under the spinal stance to the tree its erasure gives; and the
//!   evaluator's step count shows a rib evaluated once across the applications
//!   of its abstraction, a rib full laziness could not float out included, and
//!   an open leg evaluated per occurrence.
//! - `fill_and_resume`, `match_pattern`, `select_arm`, `Matched`, `Selection`,
//!   `ArmIndex`, `LiveFault` and `MatchFault`, with `NeutralHead::Hole`,
//!   `NeutralHead::Mark`, `Suspended` and the indeterminate deferral and
//!   decline: live evaluation, whose module documentation lists the witnesses.
//!
//! # References
//!
//! - Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility
//!   Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL),
//!   Article 53, January 2026. `doi:10.1145/3776695` — laziness recovered by
//!   scheduling rather than by representation, the non-uniform-share conjecture
//!   that motivates the scheduling parameter without fixing its default, the
//!   early-success, `var-1`, `var-2`, `var-3` and `const` rules conversion's
//!   first three steps implement, and the concurrent machine of §5 with the
//!   frozen constants and biased choice of §6.1 and the two η cases of §6.2
//!   that `decide` runs.
//! - Nathanaëlle Courant. _Towards an Efficient and Formally-Verified
//!   Convertibility Checker_. Doctoral thesis, Université Paris Cité, September
//!   2024. `hal:tel-04884688`, chapter 12 — the complexity analysis whose
//!   exponent is the size of the smallest proof, the axis a duplication stance
//!   moves.
//! - Thibaut Balabonski. "Weak Optimality, and the Meaning of Sharing."
//!   _Proceedings of the 18th ACM SIGPLAN International Conference on
//!   Functional Programming (ICFP 2013)_, pages 263–274, September 2013.
//!   `doi:10.1145/2500365.2500606` — spinal and ordinary full laziness are both
//!   β-optimal for weak reduction, so the spinal stance pays only under strong
//!   reduction and stays a measured choice.
//! - Fanny He. _The Atomic Lambda-Mu Calculus_. Doctoral thesis, University of Bath,
//!   2018. `https://researchportal.bath.ac.uk/en/studentTheses/the-atomic-lambda-mu-calculus`
//!   — the strong-normalisation measure for sharing reductions that
//!   `SharingMeasure` reads over the overlay.
//! - Paul Blain Levy. _Call-By-Push-Value: A Functional/Imperative Synthesis_.
//!   Semantics Structures in Computation 2, Kluwer Academic Publishers, 2003.
//!   `isbn:978-1-4020-1730-8`, `doi:10.1007/978-94-007-0954-6` — the polarity
//!   split the domain's value and computation halves follow.
//! - Henk P. Barendregt. _The Lambda Calculus: Its Syntax and Semantics_.
//!   Revised edition, North-Holland, 1984. `isbn:978-0-444-87508-2` —
//!   confluence of β and the normal-order and applicative-order strategies the
//!   static normalization property compares against.
//!
//! # Optional tracing
//!
//! Enable `tracing` to observe evaluation and readback boundaries. The feature
//! preserves `no_std` and activates no subscriber or output backend. Fuel
//! checks and semantic errors remain ordinary code, independent of
//! instrumentation.
//!
//! | Boundary | Level | Fields |
//! | -------- | ----- | ------ |
//! | `eval_value`, `eval_computation` | INFO | Initial `fuel` |
//! | `eval_comp_within` | DEBUG | Initial `fuel`, including evaluations driven by readback |
//! | `readback_value`, `readback_computation` | INFO | Initial `fuel` and `unfolding` mode |
//! | Evaluation or readback fuel exhaustion | WARN | A fixed message inside the active span |
//!
//! The caller owns filtering, the subscriber and the output destination.
//! `tracing::instrument` uses `skip_all`: no arguments, terms, environments,
//! arena contents or result payloads are recorded, and no argument gains a
//! `Debug` bound. The crate's `Debug` implementations stay unconditional. These
//! are diagnostic spans, not the conversion decision vocabulary or a replay
//! certificate.
//!
//! The choice is `tracing` 0.1.44 with only `attributes`, optional and off by
//! default. Its structured spans retain the relation between readback and
//! nested evaluation without an async runtime. Flat `log` events lose that
//! nesting; a custom observer would duplicate a standard diagnostics interface.
//! Revisit for a security advisory affecting the selected version, loss of
//! maintenance, or a consumer requiring a different diagnostic model. The
//! feature does not change scheduling, duplication or reduction decisions.
//!
//! # What stays in kernel-core
//!
//! `gandr-kernel-core` keeps its own conversion: identity and structural
//! equality over kernel types and the codes they carry, in the kernel's own
//! arena, two-valued, failing closed to distinct. It stays separate because it
//! is trusted and this pipeline is not. The kernel compares kernel syntax with
//! nothing to unfold and no closures, and it accepts nothing it cannot recheck.
//! This pipeline compares glued domain values, holds neutrals with bodies and
//! closures over environments, answers three ways, and carries a guard table
//! the kernel admits into nothing; its answers reach the kernel only as a
//! conversion trace, which the kernel's `replay` re-derives over kernel terms,
//! firing every reduction itself. Sharing code would put the domain inside the
//! trusted base or make the kernel depend on an untrusted engine, and the two
//! walks share no node type. What is shared is what both must agree on:
//! canonical level equality, the `Eq` of `gandr-kernel-strata`'s `Level`, and
//! the per-call discipline of a set of met pairs.
//!
//! # Specification attributes
//!
//! Each nontrivial item states its contract in `# Specification` and names its
//! valid-input domain, observable boundaries and test witnesses in `#
//! Adequacy`. Executable `#[spec(...)]` predicates cover arena membership,
//! scope and binder boundaries, scheduler transitions, result precedence,
//! sharing laws and rollback. Both ordinary and `anodized_panic` test modes
//! exercise the same witnesses; predicates complement rather than replace
//! independent structural, cost and kernel-replay observations. Entry captures
//! retain scalar metadata, not copied arenas or replayed evaluations.
//!
//! Conversion validates a domain id before taking the identity shortcut.
//! Invalid operands and exhausted binder space refuse without opening an
//! invalid environment; a spent-step overflow remains a budget backstop.
//! Completed memo premises wake later decompositions, and opaque overlay leaves
//! must resolve in the core arena at erasure entry, before any graft is minted.
//! The boundary witnesses distinguish each refusal from its neighboring
//! successful case.
//!
//! Native classifier comparison resolves both endpoint pairs before appending
//! either obligation, so a missing target refuses without a partial queue or an
//! enforcement panic. A malformed replayed transport returns `MachineInvariant`
//! instead of violating a stack precondition. Both boundaries retain their
//! regression witnesses.
//!
//! The generic hash constructor has no executable predicate: an arbitrary
//! `Hash` implementation may be effectful, so hashing it again is not an
//! independent observer. Fixed FNV vectors witness the fold instead. The
//! `SharingMeasure` declaration records its four laws in prose because the
//! facade's feature set cannot attach a data-item predicate; its constructors
//! enforce those laws.
//!
//! Readback, sharing and static-normalization witnesses use one structural tree
//! oracle. Its static-term and quoted-type boundaries are witnessed by
//! `readback_terms::readback_terms::the_comparator_reads_static_formers` and
//! `readback_terms::readback_terms::the_comparator_descends_into_quoted_type_families`;
//! the latter also refuses identical quotes with missing type children.
//! `readback_terms::readback_terms::native_tree_comparison_preserves_endpoints_maps_and_evidence`
//! separates native endpoint order, translator syntax and evidence payloads
//! across distinct arenas. The substitution oracle separately witnesses
//! outermost versus innermost redex selection and ordered-sibling preservation.

#![no_std]

extern crate alloc;

mod arena;
mod closure;
mod code;
mod conv;
mod derivation;
mod domain;
mod duplicate;
mod eval;
mod free;
mod fusion;
mod guard;
pub mod identity;
mod live;
mod machine;
mod measure;
mod overlay;
mod overlay_eval;
mod policy;
mod presented;
mod readback;
mod resharing;
mod rules;
mod spec;
pub mod stage;
mod traced;

pub use crate::arena::CompClosureId;
pub use crate::arena::DomainArena;
pub use crate::arena::DomainCompId;
pub use crate::arena::DomainFault;
pub use crate::arena::DomainValueId;
pub use crate::arena::FieldSpan;
pub use crate::arena::NeutralId;
pub use crate::arena::RunWatermark;
pub use crate::arena::ValueClosureId;
pub use crate::closure::CompBody;
pub use crate::closure::CompClosure;
pub use crate::closure::Environment;
pub use crate::closure::EnvironmentDepth;
pub use crate::closure::Mover;
pub use crate::closure::ValueBody;
pub use crate::closure::ValueClosure;
pub use crate::conv::ConversionFault;
pub use crate::conv::Convertibility;
pub use crate::conv::Deferral;
pub use crate::conv::Settlement;
pub use crate::conv::convert_computations;
pub use crate::conv::convert_values;
pub use crate::derivation::DerivationCount;
pub use crate::domain::BinderLevel;
pub use crate::domain::CompTermFace;
pub use crate::domain::DomainComp;
pub use crate::domain::DomainValue;
pub use crate::domain::Elimination;
pub use crate::domain::ForceRefusal;
pub use crate::domain::Glued;
pub use crate::domain::LevelEntry;
pub use crate::domain::LiftTarget;
pub use crate::domain::Neutral;
pub use crate::domain::NeutralHead;
pub use crate::domain::Suspended;
pub use crate::domain::TermFace;
pub use crate::domain::Unfolding;
pub use crate::duplicate::DuplicationFault;
pub use crate::duplicate::duplicate_computation;
pub use crate::duplicate::duplicate_value;
pub use crate::eval::Constants;
pub use crate::eval::Definitions;
pub use crate::eval::Endpoints;
pub use crate::eval::EvalFault;
pub use crate::eval::Fuel;
pub use crate::eval::LoweredChain;
pub use crate::eval::Recursion;
pub use crate::eval::eval_comp_within;
pub use crate::eval::eval_computation;
pub use crate::eval::eval_value;
pub use crate::eval::eval_value_within;
pub use crate::free::CoreTerm;
pub use crate::free::FreeFault;
pub use crate::free::FreeIndices;
pub use crate::guard::ContentHash;
pub use crate::guard::Guard;
pub use crate::guard::GuardAnswer;
pub use crate::live::ArmIndex;
pub use crate::live::LiveFault;
pub use crate::live::MatchFault;
pub use crate::live::Matched;
pub use crate::live::Selection;
pub use crate::live::fill_and_resume;
pub use crate::live::match_pattern;
pub use crate::live::select_arm;
pub use crate::machine::DeclineReason;
pub use crate::machine::MachineReport;
pub use crate::machine::MachineSettings;
pub use crate::machine::MachineVerdict;
pub use crate::machine::Problem;
pub use crate::machine::ProcessCount;
pub use crate::machine::ProcessId;
pub use crate::machine::StepBudget;
pub use crate::machine::StepCount;
pub use crate::machine::TraceNode;
pub use crate::machine::decide;
pub use crate::measure::ExpansionSize;
pub use crate::measure::MeasureFault;
pub use crate::measure::MeasuredQuantity;
pub use crate::measure::NodeCount;
pub use crate::measure::OccurrenceCount;
pub use crate::measure::ShareCount;
pub use crate::measure::ShareDepth;
pub use crate::measure::SharingMeasure;
pub use crate::overlay::Bound;
pub use crate::overlay::CompGraft;
pub use crate::overlay::CompNode;
pub use crate::overlay::CompTypeGraft;
pub use crate::overlay::CompTypeNode;
pub use crate::overlay::EraseFault;
pub use crate::overlay::Overlay;
pub use crate::overlay::OverlayCompId;
pub use crate::overlay::OverlayCompTypeId;
pub use crate::overlay::OverlayFamily;
pub use crate::overlay::OverlayFault;
pub use crate::overlay::OverlayId;
pub use crate::overlay::OverlayRefusal;
pub use crate::overlay::OverlayValueId;
pub use crate::overlay::OverlayValueTypeId;
pub use crate::overlay::OverlayWatermark;
pub use crate::overlay::ShareArity;
pub use crate::overlay::ShareDistance;
pub use crate::overlay::SharePosition;
pub use crate::overlay::Sharing;
pub use crate::overlay::ValueGraft;
pub use crate::overlay::ValueNode;
pub use crate::overlay::ValueTypeGraft;
pub use crate::overlay::ValueTypeNode;
pub use crate::overlay::erase_comp_type;
pub use crate::overlay::erase_computation;
pub use crate::overlay::erase_value;
pub use crate::overlay::erase_value_type;
pub use crate::overlay_eval::OverlayEvalFault;
pub use crate::overlay_eval::eval_overlay_computation;
pub use crate::overlay_eval::eval_overlay_value;
pub use crate::policy::Copied;
pub use crate::policy::DuplicationPolicy;
pub use crate::policy::DuplicationStance;
pub use crate::policy::GranularityPolicy;
pub use crate::policy::GranularityStance;
pub use crate::policy::PolicyRefusal;
pub use crate::policy::SchedulingPolicy;
pub use crate::policy::SchedulingStance;
pub use crate::policy::Share;
pub use crate::policy::SharedPart;
pub use crate::presented::Presented;
pub use crate::readback::ReadbackFault;
pub use crate::readback::ReadbackMode;
pub use crate::readback::readback_computation;
pub use crate::readback::readback_value;
pub use crate::resharing::EdgeCount;
pub use crate::resharing::GoalSupport;
pub use crate::resharing::ResharingMemo;
pub use crate::resharing::ResharingPlane;
pub use crate::resharing::SupportEdges;
pub use crate::resharing::SupportSides;
pub use crate::traced::TracedDuplication;
