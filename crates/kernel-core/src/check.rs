//! The **defunctionalized checking machine**: bidirectional type checking that
//! re-derives every obligation and grants the producer no credence.
//!
//! # Bidirectional, annotation-free
//!
//! Terms carry no type annotations, so checking is bidirectional. The
//! introductions — lambda, injection, pair, thunk, return — **check** against
//! an expected type flowing down from the declaration's declared type; the
//! eliminators and atoms — variable, constant, application, force, bind, case,
//! literal, lift — **synthesize** a type flowing up. A synthesizing term used
//! where a type is expected triggers a conversion at the mode switch. The
//! empty sum's elimination is checking-only: its value child checks at the
//! empty sum and the expected computation type supplies its result. A data
//! type with no constructor, and a path between two apart terms of a data type
//! ([`crate::presented`] § Apartness), are eliminated by a data case of no
//! branch, which synthesizes its motive at the scrutinee. Neither needs a
//! metavariable or inference.
//!
//! # Arena-native: ids, never owned types
//!
//! Every type the machine touches is a `Copy` id into the environment's arena:
//! the declared type, a context slot, a synthesized type, an expected type
//! flowing into a check. Eliminating a type former is a read of its child ids.
//! Synthesized types are minted into the arena as checker intermediates, which
//! the admission choke point truncates after the verdict. Node reads borrow
//! arena storage; frames retain the child ids and levels synthesized types
//! need, without cloning literal payloads merely to dispatch a rule.
//!
//! # Terms live in types, and four rules rest on it
//!
//! The universe-decoding former carries a value, so a type can mention a bound
//! variable. Four consequences are load-bearing here and each is one arm:
//!
//! - **A context slot is open.** A slot is recorded against the context prefix
//!   that precedes it, so a variable synthesis raises it past the binders
//!   between the slot and the use site before returning it.
//! - **An application substitutes into the codomain.** At a dependent head the
//!   codomain is instantiated at the argument rather than produced as it
//!   stands.
//! - **The formation walk carries a context.** A dependent arrow's codomain is
//!   formed under the domain's binder, so the walk pushes and pops slots
//!   exactly as the checking machine does.
//! - **The formation walk owes obligations it cannot discharge.** Deciding a
//!   code's type is the checking machine's job, and having formation call it
//!   would make the two walks mutually recursive. Formation records what it
//!   owes; [`drain_code_obligations`] drains the record through the checking
//!   machine; and a check that owes more codes appends to the same worklist.
//!   **Neither walk reaches the other**, and the drain is a loop with a ceiling
//!   rather than an open recursion.
//!
//! # Totality by defunctionalization, with no depth budget
//!
//! The checker runs as an explicit machine over a goal register, a produced
//! register, a heap frame stack, and an explicit typing-context stack — never
//! mutually recursive methods bounded by a depth budget — so it is total on
//! adversarial depth, which matters because decode can build an arbitrarily
//! deep term from bytes. Type formation is its own iterative walk the machine
//! calls directly, as it calls the already-iterative conversion.
//!
//! # Correspondence: recursive arm to machine step
//!
//! This table is the trusted-base audit artifact. Each arm of the recursive
//! presentation the machine replaces maps to exactly one goal expansion plus,
//! for a multi-child arm, one continuation frame. A reviewer confirms the
//! machine **is** the judgement by walking it.
//!
//! | recursive arm                          | goal push                    | frames                                              |
//! | -------------------------------------- | ---------------------------- | --------------------------------------------------- |
//! | `value_type_level` Base / Unit / Empty | leaf, level zero             | —                                                   |
//! | `value_type_level` Universe, any sort  | leaf, scope then successor   | —                                                   |
//! | `value_type_level` Abstract            | leaf, kind lookup            | —                                                   |
//! | `value_type_level` Element             | leaf, level read, code owed  | —                                                   |
//! | `value_type_level` Path                | `ValueLevel(domain)`, closed domain, endpoints owed | —                                  |
//! | `value_type_level` Product / Sum       | `ValueLevel(first)`          | `MaxSecondValue`, then `MaxWith`                    |
//! | `value_type_level` Thunk               | `CompLevel(body)`            | — (the level passes through)                        |
//! | `value_type_level` Lift                | `ValueLevel(inner)`          | `LiftCheck`                                         |
//! | `comp_type_level` Returner             | `ValueLevel(result)`         | — (the level passes through)                        |
//! | `comp_type_level` Arrow                | `ValueLevel(domain)`         | `MaxSecondComp`, then `MaxWith`                     |
//! | `comp_type_level` Pi                   | `ValueLevel(domain)`         | `MaxSecondCompUnder`, `ScopeExit`, then `MaxWith`   |
//! | `comp_type_level` Element              | leaf, level read, code owed  | —                                                   |
//! | `comp_type_level` With                 | `CompLevel(first)`, zero for none | `MaxSecondComp` per later component, then `MaxWith` |
//! | `synth_value` Var                      | leaf, slot lookup then shift | —                                                   |
//! | `synth_value` Const / Unit / Lit       | leaf, resolve or mint        | —                                                   |
//! | `synth_value` Pair                     | `SynthValue(first)`          | `SynthPairFirst`, then `SynthPairSecond`            |
//! | `synth_value` Thunk                    | `SynthComp(body)`            | `SynthThunk`                                        |
//! | `synth_value` Lift                     | `SynthValue(body)`           | `SynthLift`                                         |
//! | `synth_value` Injection                | leaf, not inferable          | —                                                   |
//! | `synth_value` Here                     | `SynthValue(point)`          | `SynthHere`, closed domain                          |
//! | `synth_value` Higher / `HigherEvaluation` / `QuantifiedEvaluation` | leaf, not inferable | — |
//! | `synth_value` Quote, either family     | leaf, formation then universe | —                                                  |
//! | `synth_comp` Absurd                    | leaf, not inferable          | —                                                   |
//! | `check_comp` Absurd                    | `CheckValue(body, Empty)`    | —                                                   |
//! | `check_value` Injection                | `CheckValue(body, summand)`  | —                                                   |
//! | `check_value` Pair                     | `CheckValue(first, first_t)` | `CheckPairSecond`                                   |
//! | `check_value` Thunk                    | `CheckComp(body, codomain)`  | —                                                   |
//! | `check_value` at Path, introduction    | `CheckValue(value, fibre)`   | —                                                   |
//! | `check_value` Here                     | `CheckValue(point, domain)`  | `CheckHere`                                         |
//! | `check_value` Higher                   | one `CheckValue` per guard   | `Pending`                                           |
//! | `check_value` `HigherEvaluation`       | per component, in its telescope | `Components`, then `Pending`                     |
//! | `check_value` `QuantifiedEvaluation`   | per telescope of each step tree | `Components`, then `Pending`                     |
//! | `check_value` synth fallthrough        | `SynthValue(value)`          | `ConvertValue`                                      |
//! | `synth_comp` Application, Arrow head   | `SynthComp(head)`            | `SynthApply`, then `ProduceComp`                    |
//! | `synth_comp` Application, Pi head      | `SynthComp(head)`            | `SynthApply`, then `ProduceComp` at the instance    |
//! | `synth_comp` Force                     | `SynthValue(value)`          | `SynthForce`                                        |
//! | `synth_comp` Return                    | `SynthValue(value)`          | `SynthReturn`                                       |
//! | `synth_comp` Bind                      | `SynthComp(bound)`           | `SynthBind`, `ScopeExit`, then `Strengthen`         |
//! | `synth_comp` Case                      | `SynthValue(scrutinee)`      | `SynthCaseScrutinee` / `AfterLeft` / `AfterRight`, `ScopeExit`, each branch strengthened |
//! | `synth_comp` `PathTransport`           | `SynthValue(path)`           | `ElementTransport`, then `ProduceComp` at the target |
//! | `synth_comp` `TelescopeTransport`      | `SynthValue(path)`           | `TelescopePath`, `TelescopeStart`, `TelescopeOver`, then `ProduceComp` at the target pair |
//! | `synth_comp` `RelatedApplication`      | `SynthValue(path)`           | `RelatedPath`, `Pending`, `RelatedBody`, three `ScopeExit` and `Strengthen` |
//! | `synth_comp` With                      | `SynthComp(first)`, terminal for none | `SynthWith` per component                       |
//! | `synth_comp` Project                   | `SynthComp(pair)`            | `Project`, the component read off the lazy product  |
//! | `synth_comp` Lambda                    | leaf, not inferable          | —                                                   |
//! | `check_comp` Lambda, Arrow             | `CheckComp(body, codomain↑)` | `ScopeExit`                                         |
//! | `check_comp` Lambda, Pi                | `CheckComp(body, codomain)`  | `ScopeExit`                                         |
//! | `check_comp` Return                    | `CheckValue(value, result)`  | —                                                   |
//! | `check_comp` Bind                      | `SynthComp(bound)`           | `CheckBind` against `expected↑`, `ScopeExit`        |
//! | `check_comp` With                      | `CheckComp(left, left_t)`    | `Pending` with `CheckComp(right, right_t)`          |
//! | `check_comp` Case                      | `SynthValue(scrutinee)`      | `CheckCaseScrutinee` / `AfterLeft` against `expected↑`, `ScopeExit` |
//! | `check_comp` Application, fixpoint head | `SynthValue(argument)`     | `FixpointArgument`, then `CheckComp(head, argument_t → expected)` |
//! | `check_comp` synth fallthrough         | `SynthComp(computation)`     | `ConvertComp`                                       |
//!
//! **A type keeps the scope it was written in.** A plain arrow's codomain is
//! written outside the arrow's binder — formation and the reach walk read it
//! there — so a lambda checked against it weakens it (`↑`) by the binder it
//! steps under, where a dependent arrow's codomain is already written under
//! it. A bind or a case moves its expected type under its binder the same way,
//! and a type synthesized under a binder is strengthened back out of it,
//! refused as [`KernelError::BinderEscape`] when it mentions the value bound.
//! While every type was closed each of these was the identity; a code in a
//! context of types is what makes them load-bearing.
//!
//! **The two `Element` rows are the arms that answer without descending.** Each
//! reads the level off the node and records the code obligation with the sort
//! of universe it owes; it pushes no goal and holds no frame, because the code
//! is a *term* and the formation walk decides no term. The obligation leaves
//! this table and re-enters it at [`drain_code_obligations`], which starts a
//! fresh `CheckValue` goal against the universe the node named — one loop
//! below the two machines rather than a step inside either. The `Quote` row is
//! the converse crossing: a term whose type is a formation answer, so it calls
//! the formation walk directly, as the lift's frame does.
//!
//! # The memo is the default path on **both** machines
//!
//! Admitting one declaration runs two iterative machines over the shared graph:
//! this module's goal loop over the body, and [`type_level`]'s formation walk
//! over the declared type. Both consult the memo. A memo covering only the term
//! half would ship a small constant against an exponential capability, because
//! type formation would keep expanding once per occurrence.
//!
//! The memo is reached through a statically dispatched seam whose activity is
//! an associated constant, so the memoless path is **the same function at a
//! different type parameter** rather than a second implementation — which is
//! what makes the differential a genuine one and what makes the memoless path a
//! permanent rollback target rather than dead code.
//!
//! # The dependent arrow and the drain
//!
//! The dependent arrow forms at the join of its children like the
//! non-dependent one, and a lambda checks against the domain slot its codomain
//! is written against. Universe decoding makes a type depend on a code value.
//! Native nominal applications also carry term arguments, checked against the
//! declaration's parameter telescope; these are invariant typed indices, not
//! implicitly decoded type arguments.
//!
//! **The carried level keeps the two machines apart.** The former names the
//! universe it is read out of, so type formation is a lookup rather than an
//! inference, and the obligation formation cannot discharge — that the code
//! inhabits that universe — is recorded rather than pursued. The drain carries
//! a ceiling derived from the format's subterm-table cap, because a drained
//! check can form a synthesized type and owe more codes, so the loop's bound
//! is not the artifact's own size.
//!
//! A type synthesized under the binder of a bind or a case branch is
//! strengthened by instantiating the binder's variable at the index one past
//! the outer context, which nothing outside the binder can name; the reach
//! walk refuses the result as [`KernelError::BinderEscape`] when that index
//! survives — exactly when the type mentioned the bound value. A dedicated
//! occurrence walk would answer the same question as a third machine; the
//! instantiation and the reach walk already answer it.
//!
//! # Universe families, codes and the lift
//!
//! **Two universes, one rule.** The universe of value types and the universe
//! of computation types each form one level above the level they carry, as
//! value types: a code is a value whichever family it decodes into. A sealed
//! atom's kind must be the value universe, because an atom is a value type. A
//! quote synthesizes the universe of its family at its quoted type's own
//! level, by calling the formation walk directly, as the lift's frame does;
//! the computation decode owes its code against the computation universe
//! exactly as the value decode owes its code against the value universe,
//! through the same deferred obligation.
//!
//! **No cumulativity; the lift is written.** A code inhabits exactly the
//! universe at its type's level, so a code bound for a larger universe reaches
//! the kernel as the quote of an explicit `Lift`, and the formation walk's
//! strictness check on that lift is the kernel's smallness check. The producer
//! decides smallness at the site it checks and writes the lift at
//! readmission; the kernel trusts neither the decision nor the level. The
//! alternative, a cumulative universe rule in conversion or in checking, would
//! make conversion directional and put subtyping into the trusted base; the
//! reversal condition is a measured cost of the written lifts that a
//! subsumption rule would remove.
//!
//! **Codes compare by their quoted types.** Structural conversion compares two
//! quotes by the types they quote; [`replay`](mod@crate::replay) states how a
//! replayed comparison of two codes closes. Conversion fires no reduction, so
//! a producer hands the kernel reduced codes to avoid a refusal.
//!
//! # Static operators
//!
//! **Formation.** A static Pi forms only over static classifiers — a universe
//! of either sort, or a static Pi — and refuses any other child as
//! `StaticClassifierExpected`. It forms at the join of its children's levels
//! and is a value type, so an operator is a value whatever it builds. The
//! check reads each child's head; a static Pi child is formed by the walk in
//! turn, so every leaf of a curried classifier is reached.
//!
//! **Application.** A static application synthesizes: its head synthesizes a
//! static Pi, its argument checks against the domain, and it produces the
//! codomain, which binds nothing. A head of any other type refuses as
//! `ValueShapeMismatch` expecting a static Pi. Every static application the
//! kernel admits is neutral: there is no static lambda for it to meet.
//! Structural conversion compares two static applications head to head and
//! argument to argument, and a static Pi by its two children.
//!
//! **Alternatives.** A dependent static Pi would need a substitution at every
//! synthesis; no former at this vocabulary is indexed by a static argument.
//! The static lambda's absence and its reversal are recorded in
//! `gandr-kernel-term`, and the replay's operator unfolding in
//! [`replay`](mod@crate::replay).
//!
//! # Native List
//!
//! `List A` is a built-in finite former beside nominal data and records. Its
//! introductions and pure right fold participate in ordinary declaration
//! checking, readmission, encoding, substitution and normalization. They are
//! not a Sum encoding and add no effects to the kernel.
//!
//! | Former | Typing and computation |
//! | ------ | ---------------------- |
//! | `List A` | Forms at the universe level of `A`; conversion compares element types. |
//! | `nil` | Checks at any expected `List A`; does not synthesize an element type. |
//! | `cons head tail` | Checks `head : A` and `tail : List A`; malformed tails and Sum injections refuse. |
//! | `fold[A, B] list on_nil on_cons` | Forms both annotations, checks `list : List A`, and synthesizes `F B`. The empty branch checks at `F B` in the ambient context. The cell branch checks beneath `head : A` then `folded : B`, with capture-avoiding shifts of the ambient types. Nil reduces to `on_nil`; cons folds its tail before entering `on_cons`. |
//!
//! The two cell binders are ordered: folded result is index zero, head is
//! index one. Substitution protects both binders and any outer context. A
//! neutral list retains its fold rather than fabricating a result. Checking
//! and replay use the iterative machines, not recursive host-language list
//! ownership. The fold carries its element and result annotations so the
//! eliminator synthesizes.
//!
//! **Choice.** Complete the represented List former instead of translating it
//! into sums or nominal declarations; the kernel needs no host operations or
//! effect rows for this eliminator. **Reversal.** Dependent motives or general
//! strictly positive descriptions require their own formation, binding and
//! replay rules; neither is implied by this pure fold. The
//! `native_list_introductions_and_fold_check` and
//! `native_list_fold_reduces_without_capturing_outer_variables` witnesses
//! exercise native typing, refusals and reduction; `gandr-kernel-term`'s tag
//! table assigns the persisted syntax.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_check_memo::OrderedMemo;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Declaration;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::RelatedEndpoints;
use gandr_kernel_term::TableEntryCount;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_arith::arith;
use quenchant_shape::shape::Maybe;

use crate::census::ExpansionCensus;
use crate::census::ExpansionKind;
use crate::conv::ConversionGoal;
use crate::conv::Convertibility;
use crate::conv::case_branch_mismatch;
use crate::conv::convert_comp_type;
use crate::conv::convertible_comp_types;
use crate::conv::pending_endpoints;
use crate::encoding::SupportGoal;
use crate::env::AdmittedDeclaration;
use crate::env::projected_atoms;
use crate::error::ExpectedComputationShape;
use crate::error::ExpectedValueShape;
use crate::error::KernelError;
use crate::error::NonInferableForm;
use crate::error::RegisterFault;
use crate::levels::LevelContext;
use crate::replay::EndpointReading;
use crate::replay::ReplayBudget;
use crate::replay::Unfoldable;
use crate::replay::Unfoldings;
use crate::replay::read_decode;
use crate::replay::read_endpoints;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_comp_type;
use crate::rewrite::shift_value_type;
use crate::rewrite::substitute_comp_type;
use crate::rewrite::substitute_comp_type_at_call;
use crate::rewrite::substitute_value_type;
use crate::seal;
use crate::stage_order::StageOrder;
use crate::support::LooseDepth;
use crate::support::NodeOutcome;
use crate::support::NodeSupport;
use crate::support::SupportContext;
use crate::support::SupportPlane;
use crate::witness::comp_type_witness;
use crate::witness::value_type_witness;

/// The memo an unsupplied check builds for itself: the default path.
pub type DefaultMemo = OrderedMemo<NodeSupport, NodeOutcome>;

/// Borrow a value node, or the fail-closed arena fault.
///
/// Child ids are copied; a lift frame owns the level its synthesized type
/// needs. Literal payloads stay in the arena: the lookup does not clone their
/// bytes.
///
/// # Specification
/// - requires: nothing; an id that resolves to nothing is admissible input and
///   is refused.
/// - ensures: a reference to exactly the arena node at `id`.
/// - provides: the fail-closed borrow every value rule uses; callers retain
///   only the data their later frames need before mutating the arena.
/// - fails: `KernelError::ArenaFault` for an id that resolves to no node, so a
///   resolution defect rejects the declaration rather than proceeding on a
///   fabricated node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a readable variable produces its context type; truncating
///   value and computation roots instead produces the exact arena fault without
///   fabricating a type or growing the arena.
/// - witness: `check::tests::a_variable_synthesizes_its_context_type`
/// - witness: `check::tests::unreadable_term_roots_fail_closed`
#[spec(ensures: |ret| arena.value(id).map_or_else(
    || matches!(&ret, Err(KernelError::ArenaFault)),
    |expected| ret.as_ref().is_ok_and(|found| core::ptr::eq(core::ptr::from_ref(*found), core::ptr::from_ref(expected))),
))]
#[inline]
fn read_value(
    arena: &TermArena,
    id: ValueId,
) -> Result<&Value, KernelError>
{
    arena.value(id).ok_or(KernelError::ArenaFault)
}

/// Resolve a computation id, or the fail-closed arena fault.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as `read_value`, on the computation plane.
/// - provides: the fail-closed read every computation rule goes through.
/// - fails: `KernelError::ArenaFault` for an id that resolves to no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an application produces its codomain and a return binds
///   its value; an unreadable computation root instead gives the arena fault.
/// - witness: `check::tests::an_application_produces_the_codomain`
/// - witness: `check::tests::a_bind_binds_the_returned_value`
/// - witness: `check::tests::unreadable_term_roots_fail_closed`
#[spec(ensures: |ret| arena.computation(id).map_or_else(
    || matches!(&ret, Err(KernelError::ArenaFault)),
    |expected| ret.as_ref().is_ok_and(|found| core::ptr::eq(core::ptr::from_ref(*found), core::ptr::from_ref(expected))),
))]
#[inline]
fn read_computation(
    arena: &TermArena,
    id: ComputationId,
) -> Result<&Computation, KernelError>
{
    arena.computation(id).ok_or(KernelError::ArenaFault)
}

/// A value-type shape mismatch, with a content witness of the offending type.
///
/// # Specification
/// trivial.
#[inline]
fn value_shape_mismatch(
    arena: &TermArena,
    expected: ExpectedValueShape,
    actual: ValueTypeId,
) -> KernelError
{
    KernelError::ValueShapeMismatch {
        expected,
        actual: value_type_witness(arena, actual),
    }
}

/// Pair each case branch with the summand it binds, the first branch last.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success, one `(branch, summand)` pair per branch, in reverse
///   summand order so popping yields them first to last.
/// - fails: a sum shape mismatch when `scrutinee_type` is not a sum of exactly
///   as many summands as there are branches; [`KernelError::ArenaFault`] never,
///   an unresolvable classifier being a shape mismatch too.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a three-way case checks and synthesizes; a case of two
///   branches over a sum of three, and a case over a product, refuse as a sum
///   shape mismatch.
/// - witness: `check::tests::an_n_way_case_binds_each_summand`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |pairs| pairs.len() == branches.len()
    && pairs.iter().rev().map(|&(branch, _)| branch).eq(branches.iter().copied())))]
fn case_branches(
    arena: &TermArena,
    scrutinee_type: ValueTypeId,
    branches: &[ComputationId],
) -> Result<Vec<(ComputationId, ValueTypeId)>, KernelError>
{
    match arena.value_type(scrutinee_type) {
        Some(&ValueType::Sum(ref summands)) if summands.len() == branches.len() => Ok(branches
            .iter()
            .copied()
            .zip(summands.iter().copied())
            .rev()
            .collect()),
        _ => Err(value_shape_mismatch(
            arena,
            ExpectedValueShape::Sum,
            scrutinee_type,
        )),
    }
}

/// A computation-type shape mismatch, with a content witness.
///
/// # Specification
/// trivial.
#[inline]
fn comp_shape_mismatch(
    arena: &TermArena,
    expected: ExpectedComputationShape,
    actual: CompTypeId,
) -> KernelError
{
    KernelError::ComputationShapeMismatch {
        expected,
        actual: comp_type_witness(arena, actual),
    }
}

/// What `goal` comes to once the returned endpoints its structure leaves open
/// are read: normalized with the admitted definitions in `entries` unfolding,
/// and the normal forms converted by the one conversion; and, where that
/// leaves the goal apart, what the endpoint pairs the declaration relates
/// make of it.
///
/// # Specification
/// - requires: `goal`'s roots and the judgement's related pairs live in
///   `arena`.
/// - ensures: [`EndpointReading::Converts`] when the structural walk converges
///   setting nothing aside, or [`read_endpoints`] converts the set-aside pairs
///   at the unfoldings of the judgement's entries' definitions, every other
///   entry opaque; otherwise, when the judgement relates no pair,
///   [`EndpointReading::Apart`], and when it does, what
///   [`crate::element_identity::related_endpoints`] makes of the goal at those
///   unfoldings. `arena` holds what it held on entry.
/// - provides: the one place the checker reads a returned endpoint, shared by
///   every mode switch; the unfoldings are built only when a pair is set aside
///   or a relation is read. Reflexivity relates its endpoints by the dialogue
///   it carries instead ([`crate::element_identity::reflexive_endpoints`]).
/// - fails: [`crate::element_identity::IdentityError::RelatedEndpointsDiffer`]
///   when a related pair's dialogue does not replay.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a path type whose endpoint returns its value through a
///   definition converts at a mode switch, and one returning a different value
///   does not; compound endpoints related only through a definition's body
///   convert by the definition's dialogue and are refused by name when it is
///   corrupted.
/// - witness: `element_identity::tests::a_returned_endpoint_reads_at_a_mode_switch`
/// - witness: `element_identity::tests::a_certificate_with_a_returned_endpoint_decodes_checks_and_replays`
/// - witness: `element_identity::tests::a_definition_relating_compound_endpoints_admits_274`
/// - witness: `element_identity::tests::a_corrupted_relation_is_refused_by_name`
#[spec(captures: before = arena.watermark(), ensures: arena.watermark() == before)]
fn read_returned(
    arena: &mut TermArena,
    judgement: Judgement<'_>,
    goal: ConversionGoal,
) -> Result<EndpointReading, KernelError>
{
    let mut pending = Vec::new();
    let structural = pending_endpoints(arena, judgement.presentations, goal, &mut pending);
    if structural == Convertibility::Convertible && pending.is_empty() {
        return Ok(EndpointReading::Converts);
    }
    if structural == Convertibility::Distinct && judgement.related.is_empty() {
        return Ok(EndpointReading::Apart);
    }
    let unfoldings = entry_unfoldings(judgement);
    if structural == Convertibility::Convertible
        && read_endpoints(arena, &unfoldings, &pending, ReplayBudget::DEFAULT)
            == EndpointReading::Converts
    {
        return Ok(EndpointReading::Converts);
    }
    if judgement.related.is_empty() {
        return Ok(EndpointReading::Apart);
    }
    crate::element_identity::related_endpoints(arena, &unfoldings, judgement.related, goal)
}

/// The unfoldings a judgement's readings run at: the body of every admitted
/// definition, every other entry opaque, and the judgement's presentations.
///
/// # Specification
/// - ensures: one unfolding per entry of `judgement`, in order — the body of a
///   definition, [`Unfoldable::Opaque`] for a datatype, a codata type, an axiom
///   or an abstract type — presenting the judgement's presentations.
/// - executable: none — the unfoldings expose no per-constant listing to
///   compare with the entries.
///
/// # Adequacy
/// - hypothesis: L3 — a returned endpoint read through a definition, and a
///   decode read through a call into a thunk, each read at these unfoldings.
/// - witness: `element_identity::tests::a_returned_endpoint_reads_at_a_mode_switch`
/// - witness: `check::tests::a_pair_checks_at_a_fibre_decoding_a_call_into_its_first_component_721`
fn entry_unfoldings(judgement: Judgement<'_>) -> Unfoldings
{
    Unfoldings::new(
        judgement
            .entries
            .iter()
            .map(|entry| match *entry.content() {
                DeclarationContent::Def { body, .. } => Unfoldable::Body(body),
                DeclarationContent::Data { .. }
                | DeclarationContent::Codata { .. }
                | DeclarationContent::Axiom { .. }
                | DeclarationContent::AbstractType { .. } => Unfoldable::Opaque,
            })
            .collect(),
    )
    .presenting(judgement.presentations.clone())
}

/// The shape an introduction form needs of the type it checks at, for the
/// forms whose check reads that type's head: a record, a list, an injection,
/// a tuple and a thunk. Every other value checks by synthesis or by a rule of
/// its own.
///
/// # Specification
/// - ensures: `Some` of the shape the form's arm of the check refuses with, for
///   exactly the six forms named; `None` for every other value and for an
///   absent one.
///
/// # Adequacy
/// - hypothesis: L3 — a tuple at a decode of a returned code reads the decode
///   first and checks at the type it quotes.
/// - witness: `check::tests::a_pair_checks_at_a_fibre_decoding_a_call_into_its_first_component_721`
#[spec(ensures: |ret| ret.is_some() == matches!(value, Some(Value::Record(_) | Value::ListNil | Value::ListCons(..) | Value::Injection(..) | Value::Tuple(_) | Value::Thunk(_))))]
const fn introduced_shape(value: Option<&Value>) -> Option<ExpectedValueShape>
{
    let Some(value) = value
    else {
        return None;
    };
    match *value {
        Value::Record(_) => Some(ExpectedValueShape::Record),
        Value::ListNil | Value::ListCons(..) => Some(ExpectedValueShape::List),
        Value::Injection(..) => Some(ExpectedValueShape::Sum),
        Value::Tuple(_) => Some(ExpectedValueShape::Product),
        Value::Thunk(_) => Some(ExpectedValueShape::Thunk),
        Value::Here { .. }
        | Value::Stay { .. }
        | Value::Higher { .. }
        | Value::HigherEvaluation { .. }
        | Value::QuantifiedEvaluation { .. }
        | Value::Constructor { .. }
        | Value::Returned(_)
        | Value::PathRefl(_)
        | Value::PathProduct(..)
        | Value::SessionPath { .. }
        | Value::SessionFlow { .. }
        | Value::ForwardFlow { .. }
        | Value::FunctionFlow { .. }
        | Value::Then { .. }
        | Value::FlowProduct(..)
        | Value::PathEquiv { .. }
        | Value::Univalence { .. }
        | Value::Variable(_)
        | Value::Constant(_)
        | Value::Literal(_)
        | Value::Lift { .. }
        | Value::Quote(_)
        | Value::QuoteComputation(_)
        | Value::StaticApplication(..) => None,
    }
}

/// The read-only inputs every judgement of one declaration stands on.
///
/// They are the environment's admission log, this declaration's admitted
/// level context, the atoms whose minting admission is open, and the block a
/// data declaration's own fields may name. Grouped because they travel
/// together through both machines and are constant for the whole of one
/// check, which is also why none is in a memo key.
#[derive(Clone, Copy, Debug)]
pub struct Judgement<'session>
{
    /// The environment's admitted declarations, for constant and atom
    /// resolution.
    entries: &'session [AdmittedDeclaration],
    /// This declaration's admitted level context.
    levels: &'session LevelContext,
    /// The atoms this declaration reads as their representations, because
    /// it is admitted inside the admission that minted them.
    manifest: &'session [ConstantIndex],
    /// The path endpoints the declaration's conversions relate, with the
    /// dialogue relating each pair: empty but for a relating definition.
    related: &'session [RelatedEndpoints],
    /// The laws the declaration's folds rest on, one per rule of the folded
    /// type: empty but for a lawful definition.
    laws: &'session [ConstantIndex],
    /// The block in scope beside the admitted prefix: a data or codata
    /// declaration's own signature while its fields or observations form, or a
    /// mutual block's members while its families form.
    block: Block<'session>,
    /// The presented types among the entries, whose terms conversion
    /// rewrites.
    presentations: &'session crate::presented::Presentations,
    /// The structural fixpoint a definition's body thunks: its own, whose
    /// self binder its constant reads as in a case's field types.
    own: Maybe<ComputationId, recursion::Unowned>,
    /// The structural fixpoint whose result of its recursed-on parameter's
    /// type is read at that parameter's stage.
    following: Maybe<ComputationId, recursion::Unowned>,
}

/// The block a judgement may name past the admitted prefix.
#[derive(Clone, Copy, Debug)]
enum Block<'session>
{
    /// No block: every nominal head names an admitted declaration.
    Outside,
    /// A data declaration being admitted at `position`, its signature in
    /// scope for its own fields.
    Inside
    {
        /// The position the declaration takes.
        position: ConstantIndex,
        /// The declaration's own telescope and constructor table.
        signature: former::Signature<'session>,
    },
    /// A mutual block whose families are forming: every family in scope at
    /// its signature, and every definition at its declared type.
    Mutual
    {
        /// The block's extent.
        block: occurrence::Block,
        /// Its members, in order from the block's first position.
        members: &'session [Declaration],
    },
    /// A codata declaration being admitted at `position`, its signature in
    /// scope for its own observations.
    Codata
    {
        /// The position the declaration takes.
        position: ConstantIndex,
        /// The declaration's own telescope and observations.
        signature: codata::Signature<'session>,
    },
}

impl<'session> Judgement<'session>
{
    /// Pair an admission log with a level context, outside any block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        entries: &'session [AdmittedDeclaration],
        levels: &'session LevelContext,
    ) -> Self
    {
        Self {
            entries,
            levels,
            manifest: &[],
            related: &[],
            laws: &[],
            block: Block::Outside,
            presentations: &crate::presented::FREE,
            own: Maybe::Absent(recursion::Unowned::Outside),
            following: Maybe::Absent(recursion::Unowned::Outside),
        }
    }

    /// The same judgement with `fixpoint` as the definition's own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    const fn owning(
        self,
        fixpoint: ComputationId,
    ) -> Self
    {
        Self {
            own: Maybe::Present(fixpoint),
            ..self
        }
    }

    /// The same judgement reading `fixpoint`'s result of its recursed-on
    /// parameter's type at that parameter's stage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    const fn following(
        self,
        fixpoint: ComputationId,
    ) -> Self
    {
        Self {
            following: Maybe::Present(fixpoint),
            ..self
        }
    }

    /// The same judgement rewriting the terms of the presented types in
    /// `presentations`, which are those of its entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn presenting(
        self,
        presentations: &'session crate::presented::Presentations,
    ) -> Self
    {
        Self {
            presentations,
            ..self
        }
    }

    /// The same judgement inside the minting admissions of `manifest`: every
    /// atom it names reads as its representation at a definition's declared
    /// type and at every constant's synthesized type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unsealing(
        self,
        manifest: &'session [ConstantIndex],
    ) -> Self
    {
        Self { manifest, ..self }
    }

    /// The same judgement reading `related` where a mode switch's forced
    /// reading leaves path endpoints apart.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn relating(
        self,
        related: &'session [RelatedEndpoints],
    ) -> Self
    {
        Self { related, ..self }
    }

    /// The same judgement resting a fold on `laws` where it computes a rule's
    /// sides apart.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lawful(
        self,
        laws: &'session [ConstantIndex],
    ) -> Self
    {
        Self { laws, ..self }
    }

    /// The same judgement with a data block in scope at its own position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    const fn within_block(
        self,
        position: ConstantIndex,
        signature: former::Signature<'session>,
    ) -> Self
    {
        Self {
            block: Block::Inside {
                position,
                signature,
            },
            ..self
        }
    }

    /// The same judgement with a codata declaration in scope at its own
    /// position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    const fn within_codata(
        self,
        position: ConstantIndex,
        signature: codata::Signature<'session>,
    ) -> Self
    {
        Self {
            block: Block::Codata {
                position,
                signature,
            },
            ..self
        }
    }

    /// The same judgement with the members of a mutual block in scope while
    /// its families form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn within_mutual(
        self,
        block: occurrence::Block,
        members: &'session [Declaration],
    ) -> Self
    {
        Self {
            block: Block::Mutual { block, members },
            ..self
        }
    }

    /// The same judgement with the whole of its mutual block in scope, as
    /// the block's families formed: a family's field read inside a
    /// definition may name a later definition of the block at its declared
    /// type, which the families foresaw.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: inside a mutual block, the block reaching past its last
    ///   member; every other judgement unchanged.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe whose field decodes a later definition of
    ///   its block reaches the decoder's stage check rather than an unbound
    ///   constant.
    /// - witness: `tests::recursive_data::a_mutual_block_is_refused_whole`
    #[spec(ensures: |ret| match (self.block, ret.block) {
        (Block::Mutual { members, .. }, Block::Mutual { members: kept, .. }) => members.len() == kept.len(),
        _ => true,
    })]
    #[must_use]
    fn foreseeing(self) -> Self
    {
        let Block::Mutual { block, members } = self.block
        else {
            return self;
        };
        let end = ConstantIndex::from(usize::from(block.first()).saturating_add(members.len()));
        self.within_mutual(
            occurrence::Block::new(block.first(), block.families(), end),
            members,
        )
    }

    /// The member of the mutual block in scope at `index`, with what it is in
    /// the block.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a member exactly when a mutual block is in scope and holds
    ///   `index`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe's family and its decoder each resolve in
    ///   the block, and the position past it does not.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
    #[spec(ensures: |ret| match ret {
        Maybe::Present((_, membership)) => membership != occurrence::Membership::Other,
        Maybe::Absent(_) => true,
    })]
    fn member(
        self,
        index: ConstantIndex,
    ) -> Maybe<(&'session Declaration, occurrence::Membership), constant_type::Absent>
    {
        let Block::Mutual { block, members } = self.block
        else {
            return Maybe::Absent(constant_type::Absent::Unadmitted);
        };
        let membership = block.membership(index);
        if membership == occurrence::Membership::Other {
            return Maybe::Absent(constant_type::Absent::Unadmitted);
        }
        usize::from(index)
            .checked_sub(usize::from(block.first()))
            .and_then(|offset| members.get(offset))
            .map_or(Maybe::Absent(constant_type::Absent::Unadmitted), |member| {
                Maybe::Present((member, membership))
            })
    }
}

/// The mutable state one declaration's check threads through both machines:
/// the memo, the session its keys are derived against, the expansion census,
/// and the code obligations the formation walk owes.
///
/// Grouped because the four travel together everywhere and are meaningful only
/// as a set — the memo is keyed against the session, the census counts what the
/// memo did not serve, and the obligations are what a walk could not answer on
/// its own. The read-only half of a judgement is [`Judgement`]; this is the
/// half that changes.
struct Recording<'session, M>
{
    /// The check memo, at whichever instantiation this run takes.
    memo: &'session mut M,
    /// The session the memo's keys are derived against.
    session: &'session mut SupportContext,
    /// The per-plane expansion census.
    census: &'session mut ExpansionCensus,
    /// The code obligations the formation walk deferred.
    owed: &'session mut Vec<CodeObligation>,
}

/// A pending type-formation obligation — the goal of the [`type_level`] walk.
#[derive(Clone, Copy, Debug)]
enum TypeLevelGoal
{
    /// The level of a value type.
    Value(ValueTypeId),
    /// The level of a computation type.
    Comp(CompTypeId),
}

impl TypeLevelGoal
{
    /// This goal in the memo's support vocabulary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn support(self) -> SupportGoal
    {
        match self {
            Self::Value(id) => SupportGoal::ValueTypeLevel(id),
            Self::Comp(id) => SupportGoal::CompTypeLevel(id),
        }
    }
}

/// A code obligation the formation walk deferred: this value must check against
/// the universe the type that carried it named.
///
/// **The deferral is what keeps the two machines two machines.** Deciding a
/// code's type is the checking machine's job, and having the formation walk
/// call it would make the two mutually recursive — the shape the recursion ban
/// exists to forbid. Instead formation records what it owes, the driver drains
/// the record through the checking machine, and neither walk reaches the other.
///
/// **An obligation is drained where it was owed.** It carries the typing
/// telescope it stood in and the stages the recording run had minted by the
/// time it returned, so a code a structural fixpoint's body names — a call to
/// the fixpoint's own self binder at a field a case opened, decoded in a type
/// — stands below the stage that case put its fields at, as it did where the
/// formation walk met it. Formation outside a run owes under no stage. The
/// decoder of `fixture/model/universe/inductive-recursive.gandr` in the
/// surface corpus, whose arm returns `+U ((x : elPi[<](a)) -> -F
/// elPi[<](b(x)))`, is the witness on readmission.
#[derive(Clone, Debug, Eq, PartialEq)]
enum CodeObligation
{
    /// A universe code deferred by Element formation.
    Universe
    {
        /// Value that must inhabit the universe.
        code: ValueId,
        /// Required universe family.
        sort: GroundSort,
        /// Required universe level.
        level: Level,
        /// Ambient typing telescope.
        context: Vec<ValueTypeId>,
        /// The stages the recording run had minted.
        stages: StageOrder,
        /// The mutual block it was owed inside.
        scope: Owing,
    },
    /// Declaration-directed argument checks deferred by nominal formation.
    Data
    {
        /// Nominal application whose arguments must check.
        datatype: ValueTypeId,
        /// Ambient typing telescope.
        context: Vec<ValueTypeId>,
        /// The stages the recording run had minted.
        stages: StageOrder,
        /// The mutual block it was owed inside.
        scope: Owing,
    },
    /// Argument checks deferred by codata formation.
    Codata
    {
        /// Codata application whose arguments must check.
        codata: CompTypeId,
        /// Ambient typing telescope.
        context: Vec<ValueTypeId>,
        /// The stages the recording run had minted.
        stages: StageOrder,
        /// The mutual block it was owed inside.
        scope: Owing,
    },
    /// Endpoint checks deferred by identity formation.
    Endpoints
    {
        /// The domain both endpoints inhabit.
        domain: ValueTypeId,
        /// Source endpoint.
        left: ValueId,
        /// Target endpoint.
        right: ValueId,
        /// Ambient typing telescope.
        context: Vec<ValueTypeId>,
        /// The stages the recording run had minted.
        stages: StageOrder,
        /// The mutual block it was owed inside.
        scope: Owing,
    },
}

/// The mutual block an obligation was owed inside, which its drain reads it
/// in: a field a definition reads inside its own fixpoint names the block's
/// later definitions, as its family did, and the codes it owes are checked
/// with them in scope.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the extent of the block the owing judgement held, or that it held
///   none.
/// - provides: the scope a drained obligation is judged in.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a universe whose field decodes a later definition of its
///   block reaches the decoder's stage check on the drained code.
/// - witness: `tests::recursive_data::a_mutual_block_is_refused_whole`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Owing
{
    /// Outside a mutual block.
    Alone,
    /// Inside a mutual block, to the extent the owing judgement read.
    Mutual(occurrence::Block),
}

impl Owing
{
    /// The scope `judgement` reads.
    ///
    /// # Specification
    /// trivial.
    const fn of(judgement: Judgement<'_>) -> Self
    {
        match judgement.block {
            Block::Mutual { block, .. } => Self::Mutual(block),
            Block::Outside | Block::Inside { .. } | Block::Codata { .. } => Self::Alone,
        }
    }

    /// `judgement`, reading this scope's block when it holds the members.
    ///
    /// # Specification
    /// trivial.
    const fn reading(
        self,
        judgement: Judgement<'_>,
    ) -> Judgement<'_>
    {
        match (self, judgement.block) {
            (Self::Mutual(block), Block::Mutual { members, .. }) => {
                judgement.within_mutual(block, members)
            },
            _ => judgement,
        }
    }
}

/// The ceiling on how many code obligations one declaration's check may drain.
///
/// A drained obligation runs the checking machine, which can form a synthesized
/// type over nodes it just minted and owe codes that were never table entries,
/// so **the obligation count is not bounded by the artifact's entry count** and
/// the constant is a ceiling rather than a derivation. What the format's entry
/// cap supplies is a scale that moves with the artifact sizes the kernel
/// accepts, so retuning the cap retunes this with it and no second magic number
/// enters the trusted base. Past the ceiling the declaration is refused rather
/// than pursued, which is the fail-closed posture the rest of the kernel takes
/// toward a condition it cannot bound.
const MAX_CODE_OBLIGATIONS: TableEntryCount = gandr_kernel_term::MAX_TABLE_ENTRIES;

/// A continuation of the type-formation walk.
#[derive(Debug)]
enum TypeLevelFrame
{
    /// The first operand's level is in the register; take the second value
    /// operand next — a product or a sum.
    MaxSecondValue(ValueTypeId),
    /// The first operand's level is in the register; take the second
    /// computation operand next — an arrow, whose codomain stands in the same
    /// context the arrow does.
    MaxSecondComp(CompTypeId),
    /// The domain's level is in the register; take the codomain next, **under
    /// the domain's binder** — a dependent arrow.
    MaxSecondCompUnder(ValueTypeId, CompTypeId),
    /// The first factor's level is in the register; take the second factor
    /// next, **under the first factor's binder** — a dependent pair.
    MaxSecondValueUnder(ValueTypeId, ValueTypeId),
    /// A formation binder closes: pop the innermost context slot.
    ScopeExit,
    /// Restore the surrounding telescope after closed session payload
    /// formation.
    SessionScope(Vec<ValueTypeId>),
    /// The second operand's level is in the register; join with the first.
    MaxWith(Level),
    /// The inner level is in the register; check the lift's strictness and
    /// replace it with the target.
    LiftCheck(Level),
    /// The goal this frame was pushed for is now answered; record it.
    ///
    /// Pushed **before** the goal's own continuations, so it pops after all of
    /// them — which is exactly when the register holds that goal's final
    /// answer, by the machine's own unwinding invariant.
    Memoize(NodeSupport),
}

/// The universe level of a well-formed value or computation type: the
/// well-formedness gate, computed iteratively so it is total on any depth.
///
/// # Specification
/// - requires: the judgement and context belong to this arena; the memo and
///   session hold only this call's history. An unreadable root is admissible
///   input and refuses rather than panicking.
/// - ensures: `Ok(level)` — the type's universe level — exactly when every
///   embedded level is in scope, every lift strictly raises, every sealed atom
///   resolves to an admitted abstract-type declaration, every static Pi stands
///   over static classifiers, and no successor overflows; a bare universe of
///   either sort at `l` forms at `l + 1`, a static Pi at the join of its
///   children, and a decode of either family forms at the level it carries and
///   owes its code. The walk is iterative over an explicit heap frame stack, so
///   it is total on any type depth.
/// - provides: type formation for the declared type and for the machine's lift
///   synthesis, with the memo consulted on **this** plane so the type half's
///   collapse is real rather than assumed. The predicate checks result scope
///   and the null memo's closed-leaf rule. The full formation judgement and
///   provenance still require the rule derivation, not a second formation walk.
/// - fails: [`KernelError::LevelVariableOutOfScope`],
///   [`KernelError::LevelArithmetic`], [`KernelError::UniverseViolation`],
///   [`KernelError::LevelOracleFault`], [`KernelError::NotAnAbstractType`],
///   [`KernelError::AbstractTypeKindNotUniverse`],
///   [`KernelError::StaticClassifierExpected`], [`KernelError::ArenaFault`];
///   [`KernelError::StagePresented`] for a type naming a stage.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the composite level is pinned by the join over one
///   type of every former; the L3 residues are the universe successor at both
///   sorts, the arrow join, the lift-strictness boundary, the decode obligation
///   of either family and the atom lookup, each pinned by a unit golden or its
///   negative.
/// - witness: `check::tests::a_universe_forms_one_level_up`
/// - witness: `check::tests::a_lift_requires_a_strictly_higher_target`
/// - witness: `check::tests::an_arrow_forms_at_the_join_of_its_children`
/// - witness: `check::tests::a_dependent_arrow_forms_checks_and_eliminates_like_an_arrow`
/// - witness: `check::tests::a_dependent_identity_checks_through_its_codes`
/// - witness: `check::tests::a_computation_decode_owes_its_code_to_the_computation_universe`
/// - witness: `check::tests::an_abstract_type_forms_at_its_declared_universe`
/// - witness: `check::tests::a_static_pi_forms_over_static_classifiers_only`
/// - witness: `session::tests::session_codes_are_closed_and_contractive`
/// - witness: `check::tests::a_prenex_scope_controls_universe_formation`
/// - witness: `element_identity::tests::identity_at_an_open_type_is_a_neutral_fibre`
#[spec(ensures: |ret| {
    let closed_leaf = match root {
        TypeLevelGoal::Value(id) => matches!(arena.value_type(id), Some(&ValueType::Base(_))) || matches!(arena.value_type(id), Some(&ValueType::Product(ref parts) | &ValueType::Sum(ref parts)) if parts.is_empty()),
        TypeLevelGoal::Comp(_) => false,
    };
    (ret.is_err() || ret.as_ref().is_ok_and(|level| judgement.levels.check_level_scope(level).is_ok()))
        && (matches!(M::ACTIVITY, MemoActivity::Active) || !closed_leaf
            || ret.as_ref().is_ok_and(|level| *level == Level::zero()))
        && (matches!(M::ACTIVITY, MemoActivity::Active) || match root {
            TypeLevelGoal::Value(id) if matches!(arena.value_type(id), Some(&ValueType::PathUniverse(..))) =>
                ret.as_ref().map_or(true, |level| *level == Level::zero()),
            TypeLevelGoal::Value(_) | TypeLevelGoal::Comp(_) => true,
        })
})]
fn type_level<M>(
    arena: &TermArena,
    judgement: Judgement<'_>,
    root: TypeLevelGoal,
    mut context: Vec<ValueTypeId>,
    recording: Recording<'_, M>,
) -> Result<Level, KernelError>
where
    M: CheckMemo<NodeSupport, NodeOutcome>,
{
    let Recording {
        memo,
        session,
        census,
        owed,
    } = recording;
    let mut frames: Vec<TypeLevelFrame> = Vec::new();
    let mut goal = root;
    'expand: loop {
        // A type's level depends on the type node and on the binders its codes
        // read, so the support carries the same read binders a term
        // goal's does. When the memo is inactive this whole block is a
        // constant-false branch that monomorphization removes.
        let mut recalled: Option<Level> = None;
        if matches!(M::ACTIVITY, MemoActivity::Active) {
            let support = NodeSupport::build(arena, session, goal.support(), context.as_slice());
            match memo.recall(&support) {
                Some(hit) => match *hit.outcome() {
                    NodeOutcome::Formed(ref level) => recalled = Some(level.clone()),
                    // A term-shaped answer cannot have come from this walk. The
                    // memo is shared between the two machines, and a shape
                    // disagreement means the entry was not this machine's:
                    // decline it and recompute, which costs one expansion and
                    // cannot fabricate a level.
                    NodeOutcome::Checked | NodeOutcome::ValueType(_) | NodeOutcome::CompType(_) => {
                        frames.push(TypeLevelFrame::Memoize(support));
                    },
                },
                None => frames.push(TypeLevelFrame::Memoize(support)),
            }
        }
        census.record(SupportPlane::Type, match recalled {
            Some(_) => ExpansionKind::Recalled,
            None => ExpansionKind::Expanded,
        });
        let mut produced: Level = match recalled {
            Some(level) => level,
            None => match goal {
                TypeLevelGoal::Value(id) => {
                    let value_type = arena.value_type(id).ok_or(KernelError::ArenaFault)?;
                    match *value_type {
                        ValueType::Data {
                            declaration,
                            ref arguments,
                        } => {
                            let signature = former::resolve(judgement, declaration)?;
                            if signature.arity() != former::FamilyArity(arguments.len()) {
                                return Err(KernelError::DataArgumentArity);
                            }
                            let level = former::level(arena, signature.kind)?;
                            judgement.levels.check_level_scope(&level)?;
                            if !arguments.is_empty() {
                                owed.push(CodeObligation::Data {
                                    datatype: id,
                                    context: context.clone(),
                                    stages: StageOrder::default(),
                                    scope: Owing::of(judgement),
                                });
                            }
                            level
                        },
                        ValueType::Record(ref fields) => {
                            let mut fields = fields.values().copied();
                            if let Some(first) = fields.next() {
                                frames.extend(fields.rev().map(TypeLevelFrame::MaxSecondValue));
                                goal = TypeLevelGoal::Value(first);
                                continue 'expand;
                            }
                            Level::zero()
                        },
                        ValueType::Session {
                            ref graph,
                            payloads,
                        } => {
                            crate::session::validate_graph(arena, graph, payloads)
                                .map_err(KernelError::Session)?;
                            frames
                                .push(TypeLevelFrame::SessionScope(core::mem::take(&mut context)));
                            goal = TypeLevelGoal::Value(payloads);
                            continue 'expand;
                        },
                        ValueType::PathUniverse(..) => {
                            let endpoints = crate::path_universe::endpoints(
                                arena,
                                id,
                                crate::replay::ReplayBudget::DEFAULT,
                            )
                            .map_err(KernelError::Path)?;
                            frames.push(TypeLevelFrame::MaxSecondValue(endpoints.target));
                            goal = TypeLevelGoal::Value(endpoints.source);
                            continue 'expand;
                        },
                        ValueType::FlowUniverse(..) => {
                            let endpoints = crate::flow_universe::endpoints(
                                arena,
                                id,
                                crate::replay::ReplayBudget::DEFAULT,
                            )
                            .map_err(KernelError::Flow)?;
                            frames.push(TypeLevelFrame::MaxSecondValue(endpoints.target));
                            goal = TypeLevelGoal::Value(endpoints.source);
                            continue 'expand;
                        },
                        // An identity forms at its domain's level, open or
                        // closed: at an open domain it is its own neutral
                        // fibre. Its endpoints are terms, so their checks are
                        // owed to the checking machine like a decode's code.
                        // A directed identity forms alike: direction is in
                        // its introductions and its elimination, not in its
                        // formation.
                        ValueType::Path {
                            domain,
                            left,
                            right,
                        }
                        | ValueType::Flow {
                            domain,
                            source: left,
                            target: right,
                        } => {
                            owed.push(CodeObligation::Endpoints {
                                domain,
                                left,
                                right,
                                context: context.clone(),
                                stages: StageOrder::default(),
                                scope: Owing::of(judgement),
                            });
                            goal = TypeLevelGoal::Value(domain);
                            continue 'expand;
                        },
                        // A bridge forms as an identity does, at its domain's
                        // level with its endpoints owed, unless its domain
                        // reaches a sealed atom stating no interface: the
                        // relation there is the abstraction's to choose, and is
                        // refused by name.
                        ValueType::Bridge {
                            domain,
                            left,
                            right,
                        } => {
                            crate::element_identity::require_unsealed(
                                arena,
                                crate::identity_recursion::Interfaces::of(judgement.entries),
                                domain,
                            )?;
                            owed.push(CodeObligation::Endpoints {
                                domain,
                                left,
                                right,
                                context: context.clone(),
                                stages: StageOrder::default(),
                                scope: Owing::of(judgement),
                            });
                            goal = TypeLevelGoal::Value(domain);
                            continue 'expand;
                        },
                        ValueType::Base(_) => Level::zero(),
                        // A universe of either sort forms one level above the
                        // level it carries, in the universe of value types:
                        // a code is a value whatever family it decodes into.
                        ValueType::Universe { ref level, .. } => {
                            judgement.levels.check_level_scope(level)?;
                            level.succ()?
                        },
                        // A sealed atom forms at the level its own
                        // declaration's kind fixes. The lookup is the whole
                        // rule: nothing is inferred, nothing unfolds, and a
                        // position that does not resolve to an abstract-type
                        // declaration is refused here rather than trusted.
                        ValueType::Abstract(atom) => {
                            abstract_atom_level(arena, judgement.entries, atom)?
                        },
                        // A code's type is the checking machine's question, so
                        // the level is read off the node and the obligation is
                        // recorded for the driver to drain. Reading it is not
                        // trusting it: nothing admits until the recorded
                        // obligation has been checked.
                        ValueType::Element { code, ref target } => {
                            judgement.levels.check_level_scope(target)?;
                            owed.push(CodeObligation::Universe {
                                code,
                                sort: GroundSort::Value,
                                level: target.clone(),
                                context: context.clone(),
                                stages: StageOrder::default(),
                                scope: Owing::of(judgement),
                            });
                            target.clone()
                        },
                        // A product or a sum forms at the join of its parts'
                        // levels; the unit and the empty type, with no part,
                        // form at level zero.
                        ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                            let mut parts = parts.iter().copied();
                            if let Some(first) = parts.next() {
                                frames.extend(parts.rev().map(TypeLevelFrame::MaxSecondValue));
                                goal = TypeLevelGoal::Value(first);
                                continue 'expand;
                            }
                            Level::zero()
                        },
                        // The dependent pair forms at the join of its factors'
                        // levels, as the dependent arrow does, its second
                        // factor formed under the first's binder.
                        ValueType::Sigma { first, second } => {
                            frames.push(TypeLevelFrame::MaxSecondValueUnder(first, second));
                            goal = TypeLevelGoal::Value(first);
                            continue 'expand;
                        },
                        // A static Pi classifies type operators, so both its
                        // children must classify codes: a universe, or a static
                        // Pi over universes, which the walk forms in turn. Its
                        // inhabitants are codes, so it forms at the join of its
                        // children's levels, among the value types.
                        ValueType::StaticPi { domain, codomain } => {
                            static_classifier(arena, domain)?;
                            static_classifier(arena, codomain)?;
                            frames.push(TypeLevelFrame::MaxSecondValue(codomain));
                            goal = TypeLevelGoal::Value(domain);
                            continue 'expand;
                        },
                        ValueType::Thunk(body) => {
                            goal = TypeLevelGoal::Comp(body);
                            continue 'expand;
                        },
                        ValueType::List(element) => {
                            goal = TypeLevelGoal::Value(element);
                            continue 'expand;
                        },
                        ValueType::Lift { inner, ref target } => {
                            frames.push(TypeLevelFrame::LiftCheck(target.clone()));
                            goal = TypeLevelGoal::Value(inner);
                            continue 'expand;
                        },
                        // Formation reads presented types alone, and admission
                        // alone mints a stage.
                        ValueType::Staged { .. } => return Err(KernelError::StagePresented),
                    }
                },
                TypeLevelGoal::Comp(id) => {
                    let comp_type = arena.comp_type(id).ok_or(KernelError::ArenaFault)?;
                    match *comp_type {
                        CompType::Returner(result) => {
                            goal = TypeLevelGoal::Value(result);
                            continue 'expand;
                        },
                        // Both arrows form at the join of their two children's
                        // levels, and the dependent one needs no context to do
                        // it: no type former is indexed by a value term, so a
                        // codomain's level is a function of its own node however
                        // many binders it stands under.
                        CompType::Arrow { domain, codomain } => {
                            frames.push(TypeLevelFrame::MaxSecondComp(codomain));
                            goal = TypeLevelGoal::Value(domain);
                            continue 'expand;
                        },
                        // The dependent arrow's codomain is formed under the
                        // domain's binder, so the walk carries a context of its
                        // own — the half of "types in the context stop being
                        // closed" that formation pays.
                        CompType::Pi { domain, codomain } => {
                            frames.push(TypeLevelFrame::MaxSecondCompUnder(domain, codomain));
                            goal = TypeLevelGoal::Value(domain);
                            continue 'expand;
                        },
                        // The computation decode is the value decode's twin: the
                        // level is read off the node and the code is owed
                        // against the computation universe at that level.
                        CompType::Element { code, ref target } => {
                            judgement.levels.check_level_scope(target)?;
                            owed.push(CodeObligation::Universe {
                                code,
                                sort: GroundSort::Computation,
                                level: target.clone(),
                                context: context.clone(),
                                stages: StageOrder::default(),
                                scope: Owing::of(judgement),
                            });
                            target.clone()
                        },
                        // The lazy product forms at the join of its
                        // components' levels, as the product does: no
                        // component binds anything, and the terminal type,
                        // with none, forms at level zero.
                        CompType::With(ref parts) => {
                            let mut parts = parts.iter().copied();
                            if let Some(first) = parts.next() {
                                frames.extend(parts.rev().map(TypeLevelFrame::MaxSecondComp));
                                goal = TypeLevelGoal::Comp(first);
                                continue 'expand;
                            }
                            Level::zero()
                        },
                        // A codata application forms at its declaration's
                        // computation universe; its arguments are owed against
                        // the telescope, as a data application's are.
                        CompType::Codata {
                            declaration,
                            ref arguments,
                        } => {
                            let signature = codata::resolve(judgement, declaration)?;
                            if signature.parameters.len() != arguments.len() {
                                return Err(KernelError::DataArgumentArity);
                            }
                            let level = codata::level(arena, signature.kind)?;
                            judgement.levels.check_level_scope(&level)?;
                            if !arguments.is_empty() {
                                owed.push(CodeObligation::Codata {
                                    codata: id,
                                    context: context.clone(),
                                    stages: StageOrder::default(),
                                    scope: Owing::of(judgement),
                                });
                            }
                            level
                        },
                    }
                },
            },
        };
        loop {
            let Some(frame) = frames.pop()
            else {
                return Ok(produced);
            };
            match frame {
                TypeLevelFrame::Memoize(support) => {
                    // A memo at its ceiling declines to record. The check
                    // proceeds unmemoized from there, which costs collapse and
                    // never correctness.
                    let _recorded = memo.remember(support, NodeOutcome::Formed(produced.clone()));
                },
                TypeLevelFrame::MaxSecondValue(second) => {
                    frames.push(TypeLevelFrame::MaxWith(produced));
                    goal = TypeLevelGoal::Value(second);
                    continue 'expand;
                },
                TypeLevelFrame::MaxSecondComp(second) => {
                    frames.push(TypeLevelFrame::MaxWith(produced));
                    goal = TypeLevelGoal::Comp(second);
                    continue 'expand;
                },
                TypeLevelFrame::MaxSecondCompUnder(domain, second) => {
                    frames.push(TypeLevelFrame::MaxWith(produced));
                    frames.push(TypeLevelFrame::ScopeExit);
                    context.push(domain);
                    goal = TypeLevelGoal::Comp(second);
                    continue 'expand;
                },
                TypeLevelFrame::MaxSecondValueUnder(first, second) => {
                    frames.push(TypeLevelFrame::MaxWith(produced));
                    frames.push(TypeLevelFrame::ScopeExit);
                    context.push(first);
                    goal = TypeLevelGoal::Value(second);
                    continue 'expand;
                },
                TypeLevelFrame::SessionScope(outer) => context = outer,
                TypeLevelFrame::ScopeExit => {
                    let _popped = context.pop();
                },
                TypeLevelFrame::MaxWith(first) => {
                    produced = first.max(&produced);
                },
                TypeLevelFrame::LiftCheck(target) => {
                    judgement.levels.check_level_scope(&target)?;
                    judgement.levels.check_universe_below(&produced, &target)?;
                    produced = target;
                },
            }
        }
    }
}

/// The universe level of a sealed abstract type, read off its declaration's
/// kind.
///
/// This is the **whole** formation rule for a sealed atom, and its shape is the
/// point: a lookup, not an inference. The kernel resolves the position,
/// requires the declaration it finds to be an abstract type, and reads the
/// level out of a kind that admission already pinned to a universe. No branch
/// consults the atom's representation: formation is the same inside the
/// minting admission and outside it, and only the seal rule, at a member's
/// declared type and a constant's synthesized one, ever reads it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `|ret| match
///   entries.get(usize::from(atom)).map(AdmittedDeclaration::content) {
///   Some(&DeclarationContent::AbstractType { kind, .. }) =>
///   arena.value_type(kind).map_or_else(|| ret.is_err(), |node| match *node {
///   ValueType::Universe { sort: GroundSort::Value, ref level } =>
///   ret.as_ref().is_ok_and(|actual| actual == level), _ => ret.is_err() }), _
///   => ret.is_err() }` — success carries the declared universe level exactly
///   when `atom` names an admitted abstract type whose kind resolves to a
///   universe of value types.
/// - provides: the atom's formation level.
/// - fails: [`KernelError::NotAnAbstractType`] for an out-of-range position, a
///   forward reference, or a definition or axiom at that position;
///   [`KernelError::AbstractTypeKindNotUniverse`] when the kind is not a
///   universe of value types, which admission pins and which is therefore
///   surfaced rather than trusted; [`KernelError::ArenaFault`] on an unreadable
///   kind.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L2 — an atom typed at its declared universe is pinned by the
///   admission witness; the L3 residues are the three refusal arms, each pinned
///   by its own negative witness.
/// - witness: `check::tests::an_abstract_type_forms_at_its_declared_universe`
/// - witness: `check::tests::an_atom_naming_a_definition_is_not_an_abstract_type`
/// - witness: `check::tests::a_forward_atom_reference_is_not_an_abstract_type`
#[spec(ensures: |ret| match entries.get(usize::from(atom)).map(AdmittedDeclaration::content) { Some(&DeclarationContent::AbstractType { kind, .. }) => arena.value_type(kind).map_or_else(|| ret.is_err(), |node| match *node { ValueType::Universe { sort: GroundSort::Value, ref level } => ret.as_ref().is_ok_and(|actual| actual == level), ValueType::Data { .. } | ValueType::Record(_) | ValueType::Session { .. } | ValueType::PathUniverse(..) | ValueType::FlowUniverse(..) | ValueType::Path { .. } | ValueType::Flow { .. } | ValueType::Bridge { .. } | ValueType::Base(_) | ValueType::Product(_) | ValueType::Sigma { .. } | ValueType::Sum(_) | ValueType::List(_) | ValueType::Thunk(_) | ValueType::Universe { .. } | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::Abstract(_) | ValueType::StaticPi { .. } | ValueType::Staged { .. } => ret.is_err() }), _ => ret.is_err() })]
fn abstract_atom_level(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    atom: ConstantIndex,
) -> Result<Level, KernelError>
{
    let entry = entries
        .get(usize::from(atom))
        .ok_or(KernelError::NotAnAbstractType { index: atom })?;
    let DeclarationContent::AbstractType { kind, .. } = *entry.content()
    else {
        return Err(KernelError::NotAnAbstractType { index: atom });
    };
    let kind_node = arena.value_type(kind).ok_or(KernelError::ArenaFault)?;
    match *kind_node {
        ValueType::Universe {
            sort: GroundSort::Value,
            ref level,
        } => Ok(level.clone()),
        ValueType::Universe {
            sort: GroundSort::Computation,
            ..
        }
        | ValueType::Data { .. }
        | ValueType::Record(_)
        | ValueType::PathUniverse(..)
        | ValueType::FlowUniverse(..)
        | ValueType::Base(_)
        | ValueType::Product(..)
        | ValueType::Sigma { .. }
        | ValueType::Session { .. }
        | ValueType::List(_)
        | ValueType::Sum(..)
        | ValueType::Thunk(_)
        | ValueType::Lift { .. }
        | ValueType::Element { .. }
        | ValueType::Abstract(_)
        | ValueType::Path { .. }
        | ValueType::Flow { .. }
        | ValueType::Bridge { .. }
        | ValueType::StaticPi { .. }
        | ValueType::Staged { .. } => Err(KernelError::AbstractTypeKindNotUniverse {
            actual: value_type_witness(arena, kind),
        }),
    }
}

/// Require `classifier` to classify codes: a universe of either sort, or a
/// static Pi.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when `classifier` resolves to a universe or to a
///   static Pi.
/// - provides: the head check static Pi formation runs on each child. A static
///   Pi child is formed by the walk in turn, so the check reaches every leaf of
///   a nested classifier.
/// - fails: [`KernelError::StaticClassifierExpected`] for any other type, and
///   [`KernelError::ArenaFault`] when `classifier` does not resolve.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a universe of either sort and a static Pi pass; a base
///   type at either child refuses by name.
/// - witness: `check::tests::a_static_pi_forms_over_static_classifiers_only`
#[spec(ensures: |ret| ret.is_ok() == matches!(arena.value_type(classifier), Some(&ValueType::Universe { .. } | &ValueType::StaticPi { .. })))]
fn static_classifier(
    arena: &TermArena,
    classifier: ValueTypeId,
) -> Result<(), KernelError>
{
    match *arena
        .value_type(classifier)
        .ok_or(KernelError::ArenaFault)?
    {
        ValueType::Universe { .. } | ValueType::StaticPi { .. } => Ok(()),
        ValueType::Data { .. }
        | ValueType::Record(_)
        | ValueType::PathUniverse(..)
        | ValueType::FlowUniverse(..)
        | ValueType::Base(_)
        | ValueType::Product(..)
        | ValueType::Sigma { .. }
        | ValueType::Session { .. }
        | ValueType::List(_)
        | ValueType::Sum(..)
        | ValueType::Thunk(_)
        | ValueType::Lift { .. }
        | ValueType::Element { .. }
        | ValueType::Abstract(_)
        | ValueType::Path { .. }
        | ValueType::Flow { .. }
        | ValueType::Bridge { .. }
        | ValueType::Staged { .. } => Err(KernelError::StaticClassifierExpected {
            actual: value_type_witness(arena, classifier),
        }),
    }
}

/// A result the checker machine produced into its register.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Produced
{
    /// A synthesized value type.
    ValueType(ValueTypeId),
    /// A synthesized computation type.
    CompType(CompTypeId),
    /// A check succeeded; no type is carried.
    Checked,
}

quenchant_shape::reason_enum! {
    /// Why a memo outcome cannot supply the term register.
    mod term_outcome {
        /// A result belongs to the other checking machine.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// A universe level is a formation answer, not a term answer.
            Formation,
        }
    }
}

impl Produced
{
    /// This answer in the memo's outcome vocabulary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn outcome(self) -> NodeOutcome
    {
        match self {
            Self::ValueType(id) => NodeOutcome::ValueType(id),
            Self::CompType(id) => NodeOutcome::CompType(id),
            Self::Checked => NodeOutcome::Checked,
        }
    }

    /// Read a memo outcome back as a register value.
    ///
    /// A formation level cannot be the answer to a term goal, so it is treated
    /// as a **miss** rather than trusted: declining costs one recomputation and
    /// cannot fabricate a verdict.
    ///
    /// # Specification
    /// - requires: nothing; an outcome of the formation machine is admissible
    ///   input.
    /// - ensures: the register value a term goal's answer carries, and nothing
    ///   for a formation level, which is not an answer to a term goal.
    /// - provides: the term register or [`Absent::Formation`], which declines a
    ///   formation answer and forces recomputation.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a formation answer cannot satisfy a term goal; the
    ///   mirror-plane poison witness observes recomputation and the verdict.
    /// - witness: `tests::acceptance::a_formation_shaped_answer_in_a_term_support_is_declined_and_recomputed`
    ///
    /// [`Absent::Formation`]: term_outcome::Absent::Formation
    #[spec(ensures: |ret| matches!((outcome, &ret),
        (NodeOutcome::ValueType(_), Maybe::Present(Self::ValueType(_)))
        | (NodeOutcome::CompType(_), Maybe::Present(Self::CompType(_)))
        | (NodeOutcome::Checked, Maybe::Present(Self::Checked))
        | (NodeOutcome::Formed(_), Maybe::Absent(term_outcome::Absent::Formation))))]
    #[inline]
    const fn of_outcome(outcome: &NodeOutcome) -> Maybe<Self, term_outcome::Absent>
    {
        match *outcome {
            NodeOutcome::ValueType(id) => Maybe::Present(Self::ValueType(id)),
            NodeOutcome::CompType(id) => Maybe::Present(Self::CompType(id)),
            NodeOutcome::Checked => Maybe::Present(Self::Checked),
            NodeOutcome::Formed(_) => Maybe::Absent(term_outcome::Absent::Formation),
        }
    }

    /// Project a synthesized value type out of the register.
    ///
    /// # Specification
    /// - requires: nothing; every register state is admissible input.
    /// - ensures: a value-type register projects its id; either other state
    ///   returns the precise value-polarity fault.
    /// - provides: the fail-closed projection every value-consuming frame
    ///   takes, so a wiring defect refuses instead of fabricating a type.
    /// - fails: [`KernelError::CheckerRegisterFault`] with
    ///   [`RegisterFault::ExpectedValueType`] on a non-value register.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::CheckerRegisterFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the variable fixture preserves its selected context
    ///   type; both other register states produce the exact polarity fault.
    /// - witness: `check::tests::a_variable_synthesizes_its_context_type`
    /// - witness: `check::tests::register_polarity_faults_fail_closed`
    #[spec(ensures: |ret| matches!((self, &ret),
        (Self::ValueType(_), Ok(_))
        | (Self::CompType(_) | Self::Checked,
            Err(KernelError::CheckerRegisterFault(RegisterFault::ExpectedValueType)))))]
    #[inline]
    const fn value_type(self) -> Result<ValueTypeId, KernelError>
    {
        match self {
            Self::ValueType(id) => Ok(id),
            Self::CompType(_) | Self::Checked => Err(KernelError::CheckerRegisterFault(
                RegisterFault::ExpectedValueType,
            )),
        }
    }

    /// Project a synthesized computation type out of the register.
    ///
    /// # Specification
    /// - requires: nothing; every register state is admissible input.
    /// - ensures: a computation-type register projects its id; either other
    ///   state returns the precise computation-polarity fault.
    /// - provides: the fail-closed projection every computation-consuming frame
    ///   takes, with the same refusal discipline as [`Self::value_type`].
    /// - fails: [`KernelError::CheckerRegisterFault`] with
    ///   [`RegisterFault::ExpectedCompType`] on a non-computation register.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::CheckerRegisterFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — forcing a thunk preserves its computation type; both
    ///   other register states produce the exact polarity fault.
    /// - witness: `check::tests::a_force_unwraps_a_thunk`
    /// - witness: `check::tests::register_polarity_faults_fail_closed`
    #[spec(ensures: |ret| matches!((self, &ret),
        (Self::CompType(_), Ok(_))
        | (Self::ValueType(_) | Self::Checked,
            Err(KernelError::CheckerRegisterFault(RegisterFault::ExpectedCompType)))))]
    #[inline]
    const fn comp_type(self) -> Result<CompTypeId, KernelError>
    {
        match self {
            Self::CompType(id) => Ok(id),
            Self::ValueType(_) | Self::Checked => Err(KernelError::CheckerRegisterFault(
                RegisterFault::ExpectedCompType,
            )),
        }
    }
}

/// A checking obligation over a term node — the goal of the machine.
#[derive(Clone, Copy, Debug)]
enum Goal
{
    /// Synthesize a value's type.
    SynthValue(ValueId),
    /// Check a value against an expected value type.
    CheckValue(ValueId, ValueTypeId),
    /// Synthesize a computation's type.
    SynthComp(ComputationId),
    /// Check a computation against an expected computation type.
    CheckComp(ComputationId, CompTypeId),
}

impl Goal
{
    /// This goal in the memo's support vocabulary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn support(self) -> SupportGoal
    {
        match self {
            Self::SynthValue(id) => SupportGoal::SynthValue(id),
            Self::CheckValue(id, expected) => SupportGoal::CheckValue(id, expected),
            Self::SynthComp(id) => SupportGoal::SynthComp(id),
            Self::CheckComp(id, expected) => SupportGoal::CheckComp(id, expected),
        }
    }
}

/// A continuation of the checker machine. Every held type is a `Copy` id.
#[derive(Debug)]
enum Frame
{
    /// Discharge the remaining ordered goals, then yield their promised result.
    Pending(Vec<Goal>, Produced),
    /// Accumulate inferred record field types without recursive checking.
    RecordField
    {
        /// Label for the current synthesized field.
        label: gandr_kernel_term::FieldLabel,
        /// Remaining label/value pairs, in reverse canonical order.
        remaining: Vec<(gandr_kernel_term::FieldLabel, ValueId)>,
        /// Classifiers inferred so far.
        fields: alloc::collections::BTreeMap<gandr_kernel_term::FieldLabel, ValueTypeId>,
    },
    /// Project a field once the record's classifier is known.
    RecordProjection(gandr_kernel_term::FieldLabel),
    /// Project a component once the tuple's classifier is known; the tuple
    /// itself is kept, since a dependent pair's second factor reads the first
    /// component.
    TupleProjection(ValueId, gandr_kernel_term::Component),
    /// Check a motive and constructor-specific branches after scrutinee
    /// synthesis, the branches at `motive`: the written one, or the staged
    /// result the case is checked at ([`recursion::motive_at`]).
    DataCase
    {
        /// The case.
        case: ComputationId,
        /// The motive its branches are read at.
        motive: CompTypeId,
    },
    /// Decide that a case over a presented type respects the type's rules,
    /// once its branches have checked.
    Respect(ComputationId, respect::Reading),
    /// Show a case over a sort its words loop at respects each loop, once its
    /// branches have checked.
    Loops(ComputationId, ValueTypeId),
    /// Form a dependent split's motive and check its body after scrutinee
    /// synthesis.
    SigmaSplit(ComputationId),
    /// Restore the outer context after checking closed payload paths.
    SessionPayload
    {
        /// Session-path classifier to synthesize after its obligations.
        classifier: ValueTypeId,
        /// Surrounding telescope, excluded from the closed proof tuple.
        context: Vec<ValueTypeId>,
    },
    /// Synthesize the second product-path component after the first.
    PathProductFirst(ValueId),
    /// Combine the two decoded component endpoints.
    PathProductSecond(crate::path_universe::PathType),
    /// Synthesize the second product-flow component after the first.
    FlowProductFirst(ValueId),
    /// Combine the two decoded component endpoints of a flow product.
    FlowProductSecond(crate::flow_universe::FlowType),
    /// Check the backward map after the closed forward map.
    PathForward
    {
        /// The native equivalence carrying both maps and its evidence.
        path: ValueId,
        /// Validated endpoint types.
        endpoints: crate::path_universe::PathType,
        /// The enclosing context, restored after both map checks.
        context: Vec<ValueTypeId>,
    },
    /// Replay both round trips after both translators checked.
    PathBackward
    {
        /// The native equivalence.
        path: ValueId,
        /// Validated endpoint types.
        endpoints: crate::path_universe::PathType,
        /// The enclosing context.
        context: Vec<ValueTypeId>,
    },
    /// Check a transport operand after synthesizing its path classifier.
    Transport(ValueId),
    /// A `here` synthesis: the point's type is synthesized; the identity is
    /// its diagonal.
    SynthHere(ValueId),
    /// A returned endpoint's synthesis: its computation is synthesizing, and
    /// must synthesize a returner.
    SynthReturned,
    /// A `here` or `stay` check: the point checked at the domain; it must
    /// convert with both held endpoints, by the forced conversion or the
    /// dialogue it carries for each.
    CheckHere
    {
        /// The reflexivity's point.
        point: ValueId,
        /// The source endpoint.
        left: ValueId,
        /// The target endpoint.
        right: ValueId,
        /// The dialogue relating the point to each endpoint.
        dialogues: alloc::sync::Arc<gandr_kernel_term::EndpointDialogues>,
    },
    /// A higher evaluation's component checks, each in its own pattern
    /// telescope, then the enclosing context restored.
    Components
    {
        /// The enclosing context.
        outer: Vec<ValueTypeId>,
        /// The components still to check, the next one last.
        remaining: Vec<crate::identity_recursion::ComponentObligation>,
    },
    /// An element transport: its path's classifier is synthesized.
    ElementTransport(ComputationId),
    /// A telescope transport: its path's classifier is synthesized.
    TelescopePath(ComputationId),
    /// A telescope transport: its start checked at the family's fibre over
    /// the path's source; synthesize the identity over the path.
    TelescopeStart
    {
        /// The transport.
        transport: ComputationId,
        /// The path's source and target.
        ends: (ValueId, ValueId),
    },
    /// A telescope transport: the identity over the path is synthesized.
    TelescopeOver
    {
        /// The transport.
        transport: ComputationId,
        /// The path's source and target.
        ends: (ValueId, ValueId),
    },
    /// A `stay` synthesis: the point's type is synthesized; the flow is its
    /// diagonal.
    SynthStay(ValueId),
    /// Replay a forward flow's images after its translator checked in the
    /// empty context.
    FlowForward
    {
        /// The forward flow.
        flow: ValueId,
        /// Its validated first-order endpoint types.
        endpoints: crate::flow_universe::FlowType,
        /// The enclosing context, restored after the replay.
        context: Vec<ValueTypeId>,
    },
    /// A function flow: the boundary at `position` is synthesized; orient it.
    FlowBoundary
    {
        /// The function flow.
        flow: ValueId,
        /// The boundary whose classifier is synthesized.
        position: crate::flow_universe::Boundary,
    },
    /// A composition: its first flow's classifier is synthesized.
    ThenFirst(ValueId),
    /// A composition: its second flow's classifier is synthesized; the first's
    /// is held.
    ThenSecond
    {
        /// The composition.
        then: ValueId,
        /// The first flow's classifier.
        first: ValueTypeId,
    },
    /// A ride: its flow's classifier is synthesized.
    Ride(ComputationId),
    /// A telescope ride: its flow's classifier is synthesized.
    TelescopeRideFlow(ComputationId),
    /// A telescope ride: its start checked at the family's fibre over the
    /// flow's source; synthesize the flow over the flow.
    TelescopeRideStart
    {
        /// The ride.
        ride: ComputationId,
        /// The flow's source and target.
        ends: (ValueId, ValueId),
    },
    /// A telescope ride: the flow over the flow is synthesized.
    TelescopeRideOver
    {
        /// The ride.
        ride: ComputationId,
        /// The flow's source and target.
        ends: (ValueId, ValueId),
    },
    /// A related application: its function identity's classifier is
    /// synthesized.
    RelatedPath(ComputationId),
    /// A related application: its premises checked; synthesize the body under
    /// the two results and their identity, held in binding order.
    RelatedBody
    {
        /// The body source.
        body: ComputationId,
        /// The source result's, the target result's, and their identity's
        /// types, each written in the context its binder extends.
        binders: [ValueTypeId; 3],
    },
    /// A tuple synthesis: the component in the register is synthesized; the
    /// rest are held, in reverse order, with the types synthesized so far.
    SynthTuple
    {
        /// The components still to synthesize, the next one last.
        remaining: Vec<ValueId>,
        /// The component types synthesized so far, in order.
        types: Vec<ValueTypeId>,
    },
    /// A thunk synthesis: the body computation is synthesizing.
    SynthThunk,
    /// A lift synthesis: the body is synthesizing; the target level is held.
    SynthLift(Level),
    /// A list-cell check: the head checked; check the tail against the held
    /// list type.
    CheckPairSecond(ValueId, ValueTypeId),
    /// Check the nil branch after checking the fold's list.
    FoldNil(ComputationId, CompTypeId),
    /// Check the cons branch under its head and folded-result binders.
    FoldCons(ValueTypeId, CompTypeId, ComputationId),
    /// A list case: the list is synthesizing; the branches and the case's
    /// expected type are held.
    ListCaseScrutinee
    {
        /// The empty branch source.
        on_nil: ComputationId,
        /// The cell branch source.
        on_cons: ComputationId,
        /// The case's expected type.
        expected: CompTypeId,
    },
    /// Check a list case's cell branch under a binder of the element and one
    /// of the tail, against the case's expected type: the element, the tail's
    /// type — at the stage the case opened when the list stood at one — the
    /// expected type and the branch.
    ListCaseCons(ValueTypeId, ValueTypeId, CompTypeId, ComputationId),
    /// A value mode switch: the value synthesized; convert against the held
    /// expected type.
    ConvertValue(ValueTypeId),
    /// An application: the head is synthesized; the argument source is held.
    SynthApply(ValueId),
    /// An application of a fixpoint in checking position: the argument is
    /// synthesizing; the fixpoint and the application's expected type are
    /// held, and the fixpoint checks against the arrow from the argument's
    /// type to it.
    FixpointArgument(ComputationId, CompTypeId),
    /// An application: the argument checked; produce the held codomain.
    ProduceComp(CompTypeId),
    /// A call into a definition whose result follows a parameter: the
    /// application's returner of the held staged type's base reads at it.
    Restage(ValueTypeId),
    /// A static application: the head is synthesized; the argument source is
    /// held.
    SynthStaticApply(ValueId),
    /// A static application: the argument checked; produce the held codomain.
    ProduceValue(ValueTypeId),
    /// A univalence: its record is synthesized; read the identity and the
    /// record type off that type, then check the record against it.
    UnivalenceRecord(ValueId),
    /// A force: the value is synthesized.
    SynthForce,
    /// A returner synthesis: the value is synthesized.
    SynthReturn,
    /// A lazy pairing synthesis: the component in the register is
    /// synthesized; the rest are held, in reverse order, with the types
    /// synthesized so far.
    SynthWith
    {
        /// The components still to synthesize, the next one last.
        remaining: Vec<ComputationId>,
        /// The component types synthesized so far, in order.
        types: Vec<CompTypeId>,
    },
    /// A projection: the pairing's type is synthesizing; the component is
    /// held.
    Project(gandr_kernel_term::Component),
    /// A bind synthesis: the bound computation is synthesized; the body source
    /// is held, and the body's type, strengthened past the bind's binder,
    /// becomes the bind's.
    SynthBind(ComputationId),
    /// A case synthesis: the scrutinee is synthesized; the branch sources are
    /// held, in summand order.
    SynthCaseScrutinee(alloc::boxed::Box<[ComputationId]>),
    /// A case synthesis: the branch in the register synthesized under its
    /// summand; the rest are held with their summands, and the first branch's
    /// type, once known, for the convergence check.
    SynthCaseBranch
    {
        /// The branches still to synthesize with their summands, the next one
        /// last.
        remaining: Vec<(ComputationId, ValueTypeId)>,
        /// The first branch's strengthened type, once synthesized.
        first: Option<CompTypeId>,
    },
    /// A computation mode switch: the computation synthesized; convert against
    /// the held expected type.
    ConvertComp(CompTypeId),
    /// A bind check: the bound computation synthesized; the body source and the
    /// expected type are held.
    CheckBind(ComputationId, CompTypeId),
    /// A case check: the scrutinee synthesized; the branch sources and expected
    /// type are held.
    CheckCaseScrutinee
    {
        /// The branch sources, in summand order.
        branches: alloc::boxed::Box<[ComputationId]>,
        /// The expected type every branch checks against, written outside
        /// their binders.
        expected: CompTypeId,
    },
    /// A case check: the branches still to check, each under its summand.
    CheckCaseBranch
    {
        /// The branches still to check with their summands, the next one last.
        remaining: Vec<(ComputationId, ValueTypeId)>,
        /// The expected type every branch checks against, already read from
        /// under its binder.
        expected: CompTypeId,
    },
    /// A binder scope closes: pop the innermost context slot.
    ScopeExit,
    /// A structural fixpoint's body has checked: the goals after it stand
    /// under one stage fewer.
    StageExit,
    /// A binder scope has closed: strengthen the computation type synthesized
    /// under it back out of it.
    Strengthen,
    /// The goal this frame was pushed for is now answered; record it.
    ///
    /// Pushed **before** the goal's own continuations, so it pops after all of
    /// them — which is exactly when the produced register holds that goal's
    /// final answer, by the machine's own unwinding invariant.
    Memoize(NodeSupport),
}

quenchant_shape::reason_enum! {
    /// Why a raw context slot is unavailable.
    mod context_slot {
        /// The requested de Bruijn index names no context slot.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The index is at or beyond the context length.
            OutOfScope,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no variable type can be raised into the use context.
    mod variable_type {
        /// The variable has no binding in this context.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// No raw slot exists at the variable's de Bruijn index.
            Unbound,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why the admission log supplies no constant type.
    mod constant_type {
        /// The constant has no prior admitted declaration.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The requested index is outside the admission log.
            Unadmitted,
        }
    }
}

/// The value type bound at de Bruijn `index`, if in scope. The context head is
/// index zero.
///
/// # Specification
/// - requires: `context` is the machine's typing context, outermost first, so
///   index zero names its last slot.
/// - ensures: the slot `index` names when it is in scope, and nothing when the
///   index reaches past the context.
/// - provides: the raw slot or [`Absent::OutOfScope`] when the index names no
///   slot, including an index not representable as `usize`.
/// - fails: never — an out-of-scope index is the absence, which the caller
///   refuses on.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — inner and outer slots distinguish reversal and off-by-one
///   errors; empty, exact-length and maximal indices observe absence.
/// - witness: `check::tests::a_variable_synthesizes_its_context_type`
///
/// [`Absent::OutOfScope`]: context_slot::Absent::OutOfScope
#[spec(ensures: |ret| usize::try_from(u32::from(index)).ok()
    .and_then(|steps| context.iter().rev().nth(steps))
    .map_or_else(
        || matches!(&ret, Maybe::Absent(context_slot::Absent::OutOfScope)),
        |expected| matches!(&ret, Maybe::Present(found) if found == expected),
    ))]
#[inline]
fn slot(
    context: &[ValueTypeId],
    index: DeBruijnIndex,
) -> Maybe<ValueTypeId, context_slot::Absent>
{
    let Ok(steps) = usize::try_from(u32::from(index))
    else {
        return Maybe::Absent(context_slot::Absent::OutOfScope);
    };
    if steps >= context.len() {
        return Maybe::Absent(context_slot::Absent::OutOfScope);
    }
    // The range guard establishes length > steps; both subtractions are exact.
    let remaining = arith::sub(arith::Int::from(context.len()), arith::Int::from(steps));
    let position = usize::from(arith::sub(remaining, arith::Int::from(1_usize)));
    match context.get(position) {
        Some(&found) => Maybe::Present(found),
        None => Maybe::Absent(context_slot::Absent::OutOfScope),
    }
}

/// The value type bound at de Bruijn `index`, **read into the context the
/// variable stands in**.
///
/// A slot was recorded against the context prefix that preceded it, so a slot
/// reached across `index` binders is written one context shorter for each of
/// them and has to be raised past all of them before it means anything at the
/// use site. That is the shift the dependent arrow makes necessary and the
/// reason a context of types stops being a context of closed things.
///
/// # Specification
/// - requires: `context` is the machine's typing context, outermost first.
/// - ensures: the slot raised past the binders between it and the use site
///   exactly when `index` names a slot in scope.
/// - provides: the raised type or [`Absent::Unbound`] when the variable names
///   no context slot. The context's provenance and raised-content equality
///   remain prose-only: the context carries no origin token, and checking the
///   shifted result would repeat the mutating rewrite or require an allocating
///   entry snapshot.
/// - fails: never — an out-of-scope index is non-failure absence here.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the slot lookup and the raise, separated
///   by a variable naming a closed slot (the slot itself, unshifted because
///   raising a closed type is the identity) and by the shifting machine's own
///   witnesses at a family where indices occur.
/// - witness: `check::tests::a_variable_synthesizes_its_context_type`
///
/// [`Absent::Unbound`]: variable_type::Absent::Unbound
#[spec(captures: entry_mark = arena.watermark(), ensures: |ret|
    entry_mark.clamped_into(gandr_kernel_term::ArenaWatermark::default(), arena.watermark()) == entry_mark
        && match (slot(context, index), &ret) {
            (Maybe::Present(_), &Maybe::Present(_)) => true,
            (Maybe::Absent(context_slot::Absent::OutOfScope), &Maybe::Absent(variable_type::Absent::Unbound)) => arena.watermark() == entry_mark,
            _ => false,
        })]
#[inline]
fn lookup(
    arena: &mut TermArena,
    session: &mut SupportContext,
    context: &[ValueTypeId],
    index: DeBruijnIndex,
) -> Maybe<ValueTypeId, variable_type::Absent>
{
    let found = match slot(context, index) {
        Maybe::Present(found) => found,
        Maybe::Absent(context_slot::Absent::OutOfScope) => {
            return Maybe::Absent(variable_type::Absent::Unbound);
        },
    };
    let amount = BinderDepth::past(BinderDepth::from(u32::from(index)));
    let (table, rewrites) = session.rewrite_parts();
    Maybe::Present(shift_value_type(
        arena,
        table,
        rewrites,
        found,
        BinderDepth::NONE,
        amount,
    ))
}

/// `subject`, written outside one binder, read under it.
///
/// # Specification
/// - requires: `subject` is written in the context the binder extends.
/// - ensures: every free index of `subject` raised by one, so each names the
///   slot it named from under the binder; a closed type comes back unchanged.
/// - provides: the weakening a lambda checked against a plain arrow, a bind and
///   a case each take on the type they check their body against.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a codomain naming a code bound outside the arrow, checked
///   from under the lambda and from under a bind, each separated from the
///   unweakened reading by the variable it would otherwise name.
/// - witness: `check::tests::a_plain_arrow_reads_its_codomain_outside_its_binder`
/// - witness: `check::tests::a_bind_reads_its_expected_type_outside_its_binder`
#[spec(captures: [entry_mark = arena.watermark(), entry_head = arena.comp_type(subject).map(core::mem::discriminant)],
    ensures: |ret| entry_mark.clamped_into(gandr_kernel_term::ArenaWatermark::default(), arena.watermark()) == entry_mark
        && arena.comp_type(ret).map(core::mem::discriminant) == entry_head)]
#[inline]
fn weakened(
    arena: &mut TermArena,
    session: &mut SupportContext,
    subject: CompTypeId,
) -> CompTypeId
{
    let (table, rewrites) = session.rewrite_parts();
    shift_comp_type(
        arena,
        table,
        rewrites,
        subject,
        BinderDepth::NONE,
        BinderDepth::from(1_u32),
    )
}

/// `subject`, synthesized under one binder, read outside it.
///
/// The binder's variable is replaced by the index one past the outer context —
/// a variable nothing outside the binder can name — and every other index is
/// lowered by one. The replacement survives exactly where the binder's variable
/// occurred, and the reach walk sees it as an index past the context.
///
/// # Specification
/// - requires: `outside` is the context the binder extended, its slot already
///   popped; `subject` was synthesized under that binder.
/// - ensures: `subject` with every free index lowered by one, exactly when it
///   does not mention the binder's variable; a closed type comes back
///   unchanged.
/// - provides: the strengthening a synthesized bind and each synthesized case
///   branch take.
/// - fails: [`KernelError::BinderEscape`] when `subject` mentions the binder's
///   variable or reaches past the context it was synthesized in.
/// - panics: none.
///
/// # Errors
/// [`KernelError::BinderEscape`].
///
/// # Adequacy
/// - hypothesis: L3 — a type naming a code bound outside the bind, which
///   lowers, and a type naming the bound value, which is refused.
/// - witness: `check::tests::a_bind_strengthens_its_type_past_its_binder`
#[spec(captures: [entry_mark = arena.watermark(), entry_head = arena.comp_type(subject).map(core::mem::discriminant)],
    ensures: |ret| entry_mark.clamped_into(gandr_kernel_term::ArenaWatermark::default(), arena.watermark()) == entry_mark
        && match ret {
            Ok(lowered) => arena.comp_type(lowered).map(core::mem::discriminant) == entry_head,
            Err(KernelError::BinderEscape { .. }) => true,
            Err(_) => false,
        })]
fn strengthened(
    arena: &mut TermArena,
    session: &mut SupportContext,
    outside: &[ValueTypeId],
    subject: CompTypeId,
) -> Result<CompTypeId, KernelError>
{
    let escape = |arena: &TermArena| KernelError::BinderEscape {
        actual: comp_type_witness(arena, subject),
    };
    let Ok(width) = u32::try_from(outside.len())
    else {
        return Err(escape(arena));
    };
    let fresh = arena.value_variable(DeBruijnIndex::from(width));
    let (table, rewrites) = session.rewrite_parts();
    let lowered = substitute_comp_type(arena, table, rewrites, subject, fresh);
    if session.comp_type_reach(arena, lowered) > LooseDepth::from(width) {
        return Err(escape(arena));
    }

    Ok(lowered)
}

/// The declared value type of a prior admitted declaration, or of a
/// definition of the mutual block whose families are forming.
///
/// # Specification
/// - requires: the judgement's entries are the environment's admission log, in
///   admission order.
/// - ensures: the declared value-type root of the declaration at `index` the
///   log holds; else, while a mutual block's families form, the declared type
///   of the block's definition at `index`; and nothing otherwise — which is
///   what makes any other forward reference into the append-only log a refusal
///   rather than a resolution.
/// - provides: the declared type or [`Absent::Unadmitted`] when the index names
///   no prior admitted declaration and no foreseen definition.
/// - fails: never — an unresolved position is the absence, which the caller
///   refuses on.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a prior declaration supplies its type; a forward
///   reference refuses instead of resolving an unrelated entry; a universe's
///   field names its decoder at the decoder's declared type.
/// - witness: `env::tests::a_definition_referencing_a_prior_one_checks`
/// - witness: `env::tests::a_forward_constant_reference_is_unbound`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
///
/// [`Absent::Unadmitted`]: constant_type::Absent::Unadmitted
#[spec(ensures: |ret| judgement.entries.get(usize::from(index)).is_none_or(
    |entry| matches!(&ret, Maybe::Present(found) if *found == entry.declared_id()),
))]
#[inline]
fn resolve_constant(
    judgement: Judgement<'_>,
    index: ConstantIndex,
) -> Maybe<ValueTypeId, constant_type::Absent>
{
    if let Some(entry) = judgement.entries.get(usize::from(index)) {
        return Maybe::Present(entry.declared_id());
    }
    match judgement.member(index) {
        Maybe::Present((member, occurrence::Membership::Definition)) => {
            Maybe::Present(member.declared_id())
        },
        Maybe::Present((_, occurrence::Membership::Family | occurrence::Membership::Other))
        | Maybe::Absent(_) => Maybe::Absent(constant_type::Absent::Unadmitted),
    }
}

/// The δ-rules the admission log offers a replay: each definition's body at
/// its admission position, every other declaration opaque; and the presented
/// types whose terms the replay rewrites.
///
/// # Specification
/// - requires: the judgement's entries are the environment's admission log, in
///   admission order, every body minted into the arena the replay runs in, and
///   its presentations are those of the entries.
/// - ensures: [`Unfoldable::Body`] at each definition's position and
///   [`Unfoldable::Opaque`] at every data declaration, axiom and abstract type,
///   one entry per admitted declaration, presenting the judgement's
///   presentations.
/// - provides: the unfoldings a persisted higher evaluation and a universe
///   path's round trips replay under, so a function either relates may name
///   what was admitted before it; and the bodies a respect obligation's cong
///   chains are read through.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a composition of two admitted definitions replays its
///   anchor-free δ-steps against their bodies, and so does negation named as a
///   universe path's translator.
/// - witness: `element_identity::tests::a_higher_evaluation_unfolds_what_the_environment_admitted`
/// - witness: `path_universe::tests::a_translator_may_name_an_admitted_definition`
#[spec(ensures: |ret| judgement.entries.iter().enumerate().all(|(position, entry)| {
    ret.unfolding(ConstantIndex::from(position)) == match *entry.content() {
        | DeclarationContent::Def { body, .. } => Unfoldable::Body(body),
        | DeclarationContent::Data { .. }
        | DeclarationContent::Codata { .. }
        | DeclarationContent::Axiom { .. }
        | DeclarationContent::AbstractType { .. } => Unfoldable::Opaque,
    }
}) && ret.presentations() == judgement.presentations)]
fn admitted_unfoldings(judgement: Judgement<'_>) -> Unfoldings
{
    Unfoldings::new(
        judgement
            .entries
            .iter()
            .map(|entry| match *entry.content() {
                DeclarationContent::Def { body, .. } => Unfoldable::Body(body),
                DeclarationContent::Data { .. }
                | DeclarationContent::Codata { .. }
                | DeclarationContent::Axiom { .. }
                | DeclarationContent::AbstractType { .. } => Unfoldable::Opaque,
            })
            .collect(),
    )
    .presenting(judgement.presentations.clone())
}

/// Run the checker machine from an initial goal and context to a verdict,
/// minting synthesized types into `arena`.
///
/// # Specification
/// - requires: `context` is the initial typing context, empty for a
///   declaration's body; its types and the admission log belong to this arena.
///   `stages` is the order the goal was owed under, empty unless the goal is a
///   drained obligation. The memo and session hold only this call's history.
/// - ensures: `Ok(produced)` — a synthesized type for a synthesis goal, or the
///   checked answer for a checking goal — exactly when the term checks or
///   synthesizes under this subset's rules. The walk is iterative over a heap
///   frame stack and an explicit context stack, so it is total on any term
///   depth. Synthesized types are appended to `arena` as readable intermediates
///   of the goal's family, for the caller to truncate after the verdict. A
///   successful run can defer code obligations, each carrying the stages the
///   run minted; the declaration driver drains them and can refuse at its
///   occurrence-based operational ceiling.
/// - provides: the shared checking and synthesis engine. The predicate checks
///   result polarity, readable synthesized roots and preservation of the arena
///   prefix. Typing and provenance require the rule derivation; final verdict
///   agreement across memo policies excludes operational ceiling refusals.
/// - fails: any [`KernelError`] a rule surfaces.
/// - panics: none.
///
/// # Errors
/// Any [`KernelError`].
///
/// # Adequacy
/// - hypothesis: L2/L3 — the finite corpus separates selected checking and
///   synthesis rules and their refusal arms, and compares memo policies below
///   the operational ceiling. The deep-chain witness covers its stated depth on
///   a small stack, not every possible artifact or resource bound.
/// - witness: `check::tests::a_variable_synthesizes_its_context_type`
/// - witness: `check::tests::an_injection_is_not_inferable`
/// - witness: `check::tests::an_injection_checks_against_its_sum`
/// - witness: `check::tests::a_pair_propagates_into_a_checking_component`
/// - witness: `check::tests::an_application_produces_the_codomain`
/// - witness: `check::tests::a_static_application_produces_the_codomain_of_its_head`
/// - witness: `check::tests::a_dependent_arrow_forms_checks_and_eliminates_like_an_arrow`
/// - witness: `check::tests::an_application_instantiates_a_dependent_codomain`
/// - witness: `check::tests::a_force_unwraps_a_thunk`
/// - witness: `check::tests::a_case_requires_convergent_branches`
/// - witness: `check::tests::a_case_propagates_the_expected_type`
/// - witness: `check::tests::an_n_way_case_binds_each_summand`
/// - witness: `check::tests::a_tuple_and_an_injection_read_their_positions`
/// - witness: `check::tests::a_bind_binds_the_returned_value`
/// - witness: `element_identity::tests::native_evidence_checks_against_the_fold_fibre`
/// - witness: `element_identity::tests::a_dependent_motive_instantiates_by_substitution`
/// - witness: `element_identity::tests::a_higher_evaluation_proves_function_extensionality`
#[spec(captures: entry_mark = arena.watermark(), ensures: |ret|
    entry_mark.clamped_into(gandr_kernel_term::ArenaWatermark::default(), arena.watermark()) == entry_mark
        && match (initial, &ret) {
            (Goal::SynthValue(_), &Ok(Produced::ValueType(id))) => arena.value_type(id).is_some(),
            (Goal::SynthComp(_), &Ok(Produced::CompType(id))) => arena.comp_type(id).is_some(),
            (Goal::CheckValue(_, _) | Goal::CheckComp(_, _), &Ok(Produced::Checked)) | (_, &Err(_)) => true,
            _ => false,
        })]
fn run<M>(
    arena: &mut TermArena,
    judgement: Judgement<'_>,
    mut context: Vec<ValueTypeId>,
    initial: Goal,
    mut stages: StageOrder,
    recording: Recording<'_, M>,
) -> Result<Produced, KernelError>
where
    M: CheckMemo<NodeSupport, NodeOutcome>,
{
    let Recording {
        memo,
        session,
        census,
        owed,
    } = recording;
    let first_owed = owed.len();
    let mut frames: Vec<Frame> = Vec::new();
    let mut goal = initial;
    // The case a structural fixpoint opens with, read as that fixpoint against
    // its type's rules, until the case is met. The goals between the two —
    // the fixpoint's lambda and the case itself — are neither recalled nor
    // memoized: a bare `λg. λy. case y` in a context of the same types is the
    // same goal, and it owes the case's own obligation, which the root does
    // not.
    let mut root: Maybe<(ComputationId, respect::Reading), respect::root::Absent> =
        Maybe::Absent(respect::root::Absent::Unmarked);
    // The stages this run's structural fixpoints and their cases mint, from
    // those the goal was owed under, and how many fixpoint bodies the current
    // goal stands under. A goal under one is neither recalled nor memoized:
    // whether a constructor with no recursive field stands below a stage
    // depends on every value in scope, beyond the binders its support reaches,
    // and a stage is this run's own. A goal owed under a stage stands under
    // the body that minted it.
    let mut staged_bodies = usize::from(stages != StageOrder::default());
    // The context slot and type of the self binder of the declaration's own
    // structural fixpoint, the one its body thunks, while it is in scope:
    // its constant in a case's field types reads as that binder.
    let mut own_fixpoint: Maybe<(usize, ValueTypeId), recursion::Unowned> =
        Maybe::Absent(recursion::Unowned::Outside);
    // The evidence values and evaluation components of the higher identity
    // being checked, copied out of the arena the obligations then mint into;
    // refilled per goal, so the walk allocates them once.
    let mut owed_values: Vec<ValueId> = Vec::new();
    let mut owed_components: Vec<gandr_kernel_term::EvaluationComponent> = Vec::new();
    'expand: loop {
        // Consult the memo for this goal's support before reading the node.
        // When the memo is inactive this whole block — the support
        // construction included — is a constant-false branch that
        // monomorphization removes, so the memoless path compiles to the code
        // it would have with no memo at all.
        let mut recalled: Option<Produced> = None;
        if matches!(M::ACTIVITY, MemoActivity::Active)
            && matches!(root, Maybe::Absent(_))
            && staged_bodies == 0
        {
            let support = NodeSupport::build(arena, session, goal.support(), context.as_slice());
            if let Some(hit) = memo.recall(&support) {
                recalled = match Produced::of_outcome(hit.outcome()) {
                    Maybe::Present(outcome) => Some(outcome),
                    Maybe::Absent(term_outcome::Absent::Formation) => None,
                };
            }
            if recalled.is_none() {
                frames.push(Frame::Memoize(support));
            }
        }
        census.record(SupportPlane::Term, match recalled {
            Some(_) => ExpansionKind::Recalled,
            None => ExpansionKind::Expanded,
        });
        let mut produced: Produced = match recalled {
            Some(outcome) => outcome,
            None => match goal {
                Goal::SynthValue(id) => match *read_value(arena, id)? {
                    Value::Constructor { .. } => {
                        let (datatype, mut goals) =
                            former::constructor(arena, judgement.entries, session, id)?;
                        let _level = type_level(
                            arena,
                            judgement,
                            TypeLevelGoal::Value(datatype),
                            context.clone(),
                            Recording {
                                memo,
                                session,
                                census,
                                owed,
                            },
                        )?;
                        goals.reverse();
                        if let Some(next) = goals.pop() {
                            frames.push(Frame::Pending(goals, Produced::ValueType(datatype)));
                            goal = next;
                            continue 'expand;
                        }
                        Produced::ValueType(datatype)
                    },
                    Value::Record(ref values) => {
                        let mut remaining = values
                            .iter()
                            .rev()
                            .map(|(label, value)| (label.clone(), *value))
                            .collect::<Vec<_>>();
                        let fields = alloc::collections::BTreeMap::new();
                        if let Some((label, value)) = remaining.pop() {
                            frames.push(Frame::RecordField {
                                label,
                                remaining,
                                fields,
                            });
                            goal = Goal::SynthValue(value);
                            continue 'expand;
                        }
                        Produced::ValueType(arena.value_type_record(fields))
                    },
                    Value::SessionPath {
                        path_type,
                        ref evidence,
                        payload_paths,
                    } => {
                        let evidence = alloc::sync::Arc::clone(evidence);
                        let _level = type_level(
                            arena,
                            judgement,
                            TypeLevelGoal::Value(path_type),
                            Vec::new(),
                            Recording {
                                memo,
                                session,
                                census,
                                owed,
                            },
                        )?;
                        let endpoints = crate::path_universe::endpoints(
                            arena,
                            path_type,
                            crate::ReplayBudget::DEFAULT,
                        )
                        .map_err(KernelError::Path)?;
                        let expected = crate::session::obligations(
                            arena,
                            endpoints.source,
                            endpoints.target,
                            &evidence,
                            crate::session::Relation::Bisimulation,
                        )
                        .map_err(KernelError::Session)?;
                        frames.push(Frame::SessionPayload {
                            classifier: path_type,
                            context: core::mem::take(&mut context),
                        });
                        goal = Goal::CheckValue(payload_paths, expected);
                        continue 'expand;
                    },
                    Value::SessionFlow {
                        flow_type,
                        ref evidence,
                        payload_paths,
                    } => {
                        let evidence = alloc::sync::Arc::clone(evidence);
                        let _level = type_level(
                            arena,
                            judgement,
                            TypeLevelGoal::Value(flow_type),
                            Vec::new(),
                            Recording {
                                memo,
                                session,
                                census,
                                owed,
                            },
                        )?;
                        let endpoints = crate::flow_universe::endpoints(
                            arena,
                            flow_type,
                            crate::ReplayBudget::DEFAULT,
                        )
                        .map_err(KernelError::Flow)?;
                        let expected = crate::session::obligations(
                            arena,
                            endpoints.source,
                            endpoints.target,
                            &evidence,
                            crate::session::Relation::Simulation,
                        )
                        .map_err(KernelError::Session)?;
                        frames.push(Frame::SessionPayload {
                            classifier: flow_type,
                            context: core::mem::take(&mut context),
                        });
                        goal = Goal::CheckValue(payload_paths, expected);
                        continue 'expand;
                    },
                    // `stay(c)` synthesizes the directed diagonal at the type
                    // `c` synthesizes.
                    Value::Stay { point, .. } => {
                        frames.push(Frame::SynthStay(point));
                        goal = Goal::SynthValue(point);
                        continue 'expand;
                    },
                    // A forward flow's translator checks in the empty context,
                    // as an equivalence's maps do; its images replay after.
                    Value::ForwardFlow {
                        flow_type,
                        translator,
                        ..
                    } => {
                        let _level = type_level(
                            arena,
                            judgement,
                            TypeLevelGoal::Value(flow_type),
                            Vec::new(),
                            Recording {
                                memo,
                                session,
                                census,
                                owed,
                            },
                        )?;
                        let endpoints = crate::flow_universe::forward_type(
                            arena,
                            flow_type,
                            crate::ReplayBudget::DEFAULT,
                        )
                        .map_err(KernelError::Flow)?;
                        let result = arena.comp_type_returner(endpoints.target);
                        let function = arena.comp_type_arrow(endpoints.source, result);
                        let expected = arena.value_type_thunk(function);
                        frames.push(Frame::FlowForward {
                            flow: id,
                            endpoints,
                            context: core::mem::take(&mut context),
                        });
                        goal = Goal::CheckValue(translator, expected);
                        continue 'expand;
                    },
                    // A function flow's boundaries synthesize in turn, each
                    // oriented by the variance its position fixes.
                    Value::FunctionFlow {
                        flow_type, domain, ..
                    } => {
                        let _level = type_level(
                            arena,
                            judgement,
                            TypeLevelGoal::Value(flow_type),
                            Vec::new(),
                            Recording {
                                memo,
                                session,
                                census,
                                owed,
                            },
                        )?;
                        let _arrows = crate::flow_universe::function_type(
                            arena,
                            flow_type,
                            crate::ReplayBudget::DEFAULT,
                        )
                        .map_err(KernelError::Flow)?;
                        frames.push(Frame::FlowBoundary {
                            flow: id,
                            position: crate::flow_universe::Boundary::Domain,
                        });
                        goal = Goal::SynthValue(domain);
                        continue 'expand;
                    },
                    Value::Then { first, .. } => {
                        frames.push(Frame::ThenFirst(id));
                        goal = Goal::SynthValue(first);
                        continue 'expand;
                    },
                    Value::FlowProduct(first, second) => {
                        frames.push(Frame::FlowProductFirst(second));
                        goal = Goal::SynthValue(first);
                        continue 'expand;
                    },
                    Value::PathRefl(code) => {
                        let endpoint = crate::path_universe::code(
                            arena,
                            code,
                            crate::replay::ReplayBudget::DEFAULT,
                        )
                        .map_err(KernelError::Path)?;
                        let _level = type_level(
                            arena,
                            judgement,
                            TypeLevelGoal::Value(endpoint),
                            Vec::new(),
                            Recording {
                                memo,
                                session,
                                census,
                                owed,
                            },
                        )?;
                        Produced::ValueType(arena.value_type_path_universe(code, code))
                    },
                    Value::PathProduct(first, second) => {
                        frames.push(Frame::PathProductFirst(second));
                        goal = Goal::SynthValue(first);
                        continue 'expand;
                    },
                    Value::PathEquiv {
                        path_type, forward, ..
                    } => {
                        let endpoints = crate::path_universe::endpoints(
                            arena,
                            path_type,
                            crate::replay::ReplayBudget::DEFAULT,
                        )
                        .map_err(KernelError::Path)?;
                        let result = arena.comp_type_returner(endpoints.target);
                        let function = arena.comp_type_arrow(endpoints.source, result);
                        let translator = arena.value_type_thunk(function);
                        frames.push(Frame::PathForward {
                            path: id,
                            endpoints,
                            context: core::mem::take(&mut context),
                        });
                        goal = Goal::CheckValue(forward, translator);
                        continue 'expand;
                    },
                    // Univalence synthesises the identity at the value
                    // universe between the codes its record's type names,
                    // once the record checks as the bi-invertible map between
                    // the two codes' types: the record's laws are its
                    // evidence, at any two codes.
                    Value::Univalence(equivalence) => {
                        frames.push(Frame::UnivalenceRecord(equivalence));
                        goal = Goal::SynthValue(equivalence);
                        continue 'expand;
                    },
                    Value::Variable(index) => {
                        let synthesized = match lookup(arena, session, context.as_slice(), index) {
                            Maybe::Present(synthesized) => synthesized,
                            Maybe::Absent(variable_type::Absent::Unbound) => {
                                return Err(KernelError::UnboundVariable { index });
                            },
                        };
                        Produced::ValueType(synthesized)
                    },
                    Value::Constant(index) => {
                        let declared = match resolve_constant(judgement, index) {
                            Maybe::Present(declared) => declared,
                            Maybe::Absent(constant_type::Absent::Unadmitted) => {
                                return Err(KernelError::UnboundConstant { index });
                            },
                        };
                        // Inside a minting admission an earlier member typed at
                        // one of its atoms reads at the representation, so the
                        // sealed module's members check against each other
                        // transparently.
                        let synthesized =
                            seal::unseal(arena, judgement.entries, judgement.manifest, declared)?;
                        Produced::ValueType(synthesized)
                    },
                    Value::Literal(ref literal) => {
                        Produced::ValueType(arena.value_type_base(literal.base_type()))
                    },
                    // A tuple synthesizes the product of its components'
                    // types, in order; the empty tuple synthesizes the unit.
                    Value::Tuple(ref components) => {
                        let mut remaining = components.iter().rev().copied().collect::<Vec<_>>();
                        let arity = remaining.len();
                        if let Some(first) = remaining.pop() {
                            frames.push(Frame::SynthTuple {
                                remaining,
                                types: Vec::with_capacity(arity),
                            });
                            goal = Goal::SynthValue(first);
                            continue 'expand;
                        }
                        Produced::ValueType(arena.value_type_unit())
                    },
                    Value::Thunk(body) => {
                        frames.push(Frame::SynthThunk);
                        goal = Goal::SynthComp(body);
                        continue 'expand;
                    },
                    Value::Lift { ref target, body } => {
                        frames.push(Frame::SynthLift(target.clone()));
                        goal = Goal::SynthValue(body);
                        continue 'expand;
                    },
                    Value::Injection(..) => {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::Injection,
                        });
                    },
                    Value::ListNil | Value::ListCons(..) => {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::List,
                        });
                    },
                    // A code synthesizes the universe its quoted type forms
                    // in, and of the family the type belongs to. Formation is
                    // the one question asked, so the arm calls the formation
                    // walk directly, as the lift's frame does, and descends no
                    // further itself.
                    Value::Quote(quoted) => {
                        let level = type_level(
                            arena,
                            judgement,
                            TypeLevelGoal::Value(quoted),
                            context.clone(),
                            Recording {
                                memo,
                                session,
                                census,
                                owed,
                            },
                        )?;
                        Produced::ValueType(arena.value_type_universe(GroundSort::Value, level))
                    },
                    Value::QuoteComputation(quoted) => {
                        let level = type_level(
                            arena,
                            judgement,
                            TypeLevelGoal::Comp(quoted),
                            context.clone(),
                            Recording {
                                memo,
                                session,
                                census,
                                owed,
                            },
                        )?;
                        Produced::ValueType(
                            arena.value_type_universe(GroundSort::Computation, level),
                        )
                    },
                    // A static application synthesizes from its head, as a
                    // computation application does: the head's static Pi
                    // supplies the domain the argument checks against and the
                    // codomain it produces. No static lambda exists to stand at
                    // the head, so nothing here reduces.
                    Value::StaticApplication(head, argument) => {
                        frames.push(Frame::SynthStaticApply(argument));
                        goal = Goal::SynthValue(head);
                        continue 'expand;
                    },
                    // `here(c)` synthesizes the diagonal identity at the type
                    // `c` synthesizes, a neutral fibre where that type is open.
                    Value::Here { point, .. } => {
                        frames.push(Frame::SynthHere(point));
                        goal = Goal::SynthValue(point);
                        continue 'expand;
                    },
                    // A returned endpoint synthesizes the value type its
                    // computation returns.
                    Value::Returned(computation) => {
                        frames.push(Frame::SynthReturned);
                        goal = Goal::SynthComp(computation);
                        continue 'expand;
                    },
                    Value::Higher { .. } => {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::HigherField,
                        });
                    },
                    Value::HigherEvaluation { .. } | Value::QuantifiedEvaluation { .. } => {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::HigherEvaluation,
                        });
                    },
                },
                // A univalence checked at an identity at the value universe
                // checks its record at the bi-invertible record the two codes
                // name, so a record literal checks; anywhere else it is
                // synthesised and converted.
                Goal::CheckValue(id, expected)
                    if matches!(arena.value(id), Some(&Value::Univalence(_)))
                        && crate::path_universe::identity_codes(arena, expected).is_ok() =>
                {
                    let Value::Univalence(equivalence) = *read_value(arena, id)?
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let record = crate::path_universe::univalence_record(arena, expected)
                        .map_err(KernelError::Path)?;
                    goal = Goal::CheckValue(equivalence, record);
                    continue 'expand;
                },
                // An introduction form checked at an identity checks at the
                // fibre the identity fold computes for its domain and
                // endpoints, or at a dependent pair's at a Σ domain, or at the
                // words a looped point's free cells mint; one checked at a
                // bridge checks at the bridge fold's fibre. `here`, the higher
                // forms and the neutrals take their own arms.
                Goal::CheckValue(id, expected)
                    if crate::element_identity::goal_reading(arena, id, expected)
                        == crate::element_identity::GoalReading::Fibre =>
                {
                    let (mode, domain, left, right) =
                        crate::element_identity::related_parts(arena, expected)?;
                    // The decode of a returned code is read to the type the code
                    // quotes, as an introduction form reads it: the identity at
                    // `El(⟨R a b⟩)` is the identity at the type `R a b` returns.
                    let domain = if let Some(&ValueType::Element { code, .. }) =
                        arena.value_type(domain)
                        && matches!(arena.value(code), Some(Value::Returned(_)))
                    {
                        let unfoldings = entry_unfoldings(judgement);
                        read_decode(arena, &unfoldings, code, ReplayBudget::DEFAULT)
                            .unwrap_or(domain)
                    }
                    else {
                        domain
                    };
                    if mode == crate::identity_recursion::Mode::Bridge {
                        goal = Goal::CheckValue(
                            id,
                            crate::element_identity::bridge_fibre(
                                arena,
                                crate::identity_recursion::Interfaces::of(judgement.entries),
                                domain,
                                left,
                                right,
                            )?,
                        );
                        continue 'expand;
                    }
                    // A path whose one endpoint spells a looped point and whose
                    // other converts with it is those words: the value checks at
                    // the words, and the path then converts with them. A path
                    // whose endpoints both compute the point without spelling
                    // it, `Path(Circle, mul(Base, Base), mul(Base, Base))`,
                    // checks at the words of the one type of words over its
                    // sort, and converts with the path at that point, which
                    // pairs each endpoint with the point (#485).
                    let spelled = |sides| judgement.presentations.words(arena, domain, sides);
                    if spelled((left, right)).is_none()
                        && let Some(words) =
                            spelled((right, right)).or_else(|| spelled((left, left)))
                    {
                        let words = arena.value_type_data(words, Vec::new());
                        frames.push(Frame::ConvertValue(expected));
                        frames.push(Frame::ProduceValue(words));
                        goal = Goal::CheckValue(id, words);
                        continue 'expand;
                    }
                    if spelled((left, right)).is_none()
                        && let Some(&ValueType::Data {
                            declaration: sort,
                            ref arguments,
                        }) = arena.value_type(domain)
                        && arguments.is_empty()
                        && let mut looping = judgement.presentations.looping(sort)
                        && let Some((words, _)) = looping.next()
                        && looping.next().is_none()
                        && let Some(point) =
                            crate::words::point(arena, judgement.presentations, words)
                    {
                        let at_point = arena.value_type_path(domain, point, point);
                        let words = arena.value_type_data(words, Vec::new());
                        frames.push(Frame::ConvertValue(expected));
                        frames.push(Frame::ProduceValue(at_point));
                        goal = Goal::CheckValue(id, words);
                        continue 'expand;
                    }
                    let fibre = if let Some(words) =
                        judgement.presentations.words(arena, domain, (left, right))
                    {
                        arena.value_type_data(words, Vec::new())
                    }
                    else if let Some(&ValueType::Sigma { first, second }) =
                        arena.value_type(domain)
                    {
                        crate::element_identity::sigma_fibre(
                            arena,
                            session.rewrite_parts(),
                            judgement.entries,
                            (first, second),
                            (left, right),
                        )
                    }
                    else {
                        crate::element_identity::fibre(
                            arena,
                            crate::identity_recursion::Interfaces::of(judgement.entries),
                            domain,
                            left,
                            right,
                        )?
                    };
                    goal = Goal::CheckValue(id, fibre);
                    continue 'expand;
                },
                // A constructor wanted at a stage checks its recursive fields
                // one step below it, and one with none checks only where a
                // value in scope shows the stage holds one; its annotation
                // then meets the type the stage refines.
                Goal::CheckValue(id, expected)
                    if matches!(arena.value(id), Some(Value::Constructor { .. }))
                        && matches!(arena.value_type(expected), Some(ValueType::Staged { .. })) =>
                {
                    let Some(&ValueType::Staged { base, stage }) = arena.value_type(expected)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let (datatype, mut goals) =
                        former::constructor(arena, judgement.entries, session, id)?;
                    let _level = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Value(datatype),
                        context.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    )?;
                    // A mutual block's families share the stage: a field of
                    // any of them stands one step below.
                    let block = recursion::families(arena, judgement.entries, datatype)?;
                    recursion::constructor_fields(
                        arena,
                        (&stages, context.as_slice()),
                        block,
                        stage,
                        &mut goals,
                    )?;
                    frames.push(Frame::ConvertValue(base));
                    goals.reverse();
                    if let Some(next) = goals.pop() {
                        frames.push(Frame::Pending(goals, Produced::ValueType(datatype)));
                        goal = next;
                        continue 'expand;
                    }
                    Produced::ValueType(datatype)
                },
                // An introduction form reads the head of the type it checks
                // at, so a decode of a returned code is first read to the type
                // the code quotes: the fibre a pair's second component checks
                // at, instantiated at a first component its code calls into,
                // is one (#721). A code that reads to no quote leaves the
                // decode, which no introduction form checks at.
                Goal::CheckValue(id, expected)
                    if introduced_shape(arena.value(id)).is_some()
                        && matches!(arena.value_type(expected), Some(&ValueType::Element { code, .. })
                            if matches!(arena.value(code), Some(Value::Returned(_)))) =>
                {
                    let (Some(shape), Some(&ValueType::Element { code, .. })) = (
                        introduced_shape(arena.value(id)),
                        arena.value_type(expected),
                    )
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let unfoldings = entry_unfoldings(judgement);
                    let Some(decoded) =
                        read_decode(arena, &unfoldings, code, ReplayBudget::DEFAULT)
                    else {
                        return Err(value_shape_mismatch(arena, shape, expected));
                    };
                    goal = Goal::CheckValue(id, decoded);
                    continue 'expand;
                },
                Goal::CheckValue(id, expected) => match *read_value(arena, id)? {
                    Value::Record(ref values) => {
                        let Some(matched_native_node) = arena.value_type(expected)
                        else {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Record,
                                expected,
                            ));
                        };
                        let ValueType::Record(ref fields) = *matched_native_node
                        else {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Record,
                                expected,
                            ));
                        };
                        for label in fields.keys() {
                            if !values.contains_key(label) {
                                return Err(KernelError::AbsentRecordField {
                                    label: label.clone(),
                                });
                            }
                        }
                        let mut goals = values
                            .iter()
                            .rev()
                            .map(|(label, value)| {
                                fields.get(label).map_or(Goal::SynthValue(*value), |ty| {
                                    Goal::CheckValue(*value, *ty)
                                })
                            })
                            .collect::<Vec<_>>();
                        if let Some(next) = goals.pop() {
                            frames.push(Frame::Pending(goals, Produced::Checked));
                            goal = next;
                            continue 'expand;
                        }
                        Produced::Checked
                    },
                    Value::ListNil => match arena.value_type(expected) {
                        Some(&ValueType::List(_)) => Produced::Checked,
                        _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::List,
                                expected,
                            ));
                        },
                    },
                    Value::ListCons(head, tail) => match arena.value_type(expected) {
                        Some(&ValueType::List(element)) => {
                            frames.push(Frame::CheckPairSecond(tail, expected));
                            goal = Goal::CheckValue(head, element);
                            continue 'expand;
                        },
                        _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::List,
                                expected,
                            ));
                        },
                    },
                    // An injection checks its body against the summand it
                    // names; a position past the sum's summands is a shape
                    // mismatch, as a non-sum classifier is.
                    Value::Injection(summand, body) => {
                        match arena.value_type(expected).and_then(|held| match *held {
                            ValueType::Sum(ref summands) => {
                                summands.get(usize::from(summand)).copied()
                            },
                            ValueType::Data { .. }
                            | ValueType::Record(_)
                            | ValueType::Session { .. }
                            | ValueType::PathUniverse(..)
                            | ValueType::FlowUniverse(..)
                            | ValueType::Path { .. }
                            | ValueType::Flow { .. }
                            | ValueType::Bridge { .. }
                            | ValueType::Base(_)
                            | ValueType::Product(_)
                            | ValueType::Sigma { .. }
                            | ValueType::List(_)
                            | ValueType::Thunk(_)
                            | ValueType::Universe { .. }
                            | ValueType::Lift { .. }
                            | ValueType::Element { .. }
                            | ValueType::Abstract(_)
                            | ValueType::StaticPi { .. }
                            | ValueType::Staged { .. } => None,
                        }) {
                            Some(summand_type) => {
                                goal = Goal::CheckValue(body, summand_type);
                                continue 'expand;
                            },
                            _ => {
                                return Err(value_shape_mismatch(
                                    arena,
                                    ExpectedValueShape::Sum,
                                    expected,
                                ));
                            },
                        }
                    },
                    // A tuple checks each component against the product's
                    // component at its position; a product of another arity is
                    // a shape mismatch. A pair checks against a dependent pair:
                    // its first component at the first factor, its second at
                    // the second factor instantiated at the first component.
                    Value::Tuple(ref components) => {
                        match (arena.value_type(expected), &**components) {
                            (Some(&ValueType::Product(ref parts)), _)
                                if parts.len() == components.len() =>
                            {
                                let mut goals = components
                                    .iter()
                                    .zip(parts.iter())
                                    .rev()
                                    .map(|(&component, &part)| Goal::CheckValue(component, part))
                                    .collect::<Vec<_>>();
                                if let Some(next) = goals.pop() {
                                    frames.push(Frame::Pending(goals, Produced::Checked));
                                    goal = next;
                                    continue 'expand;
                                }
                                Produced::Checked
                            },
                            (Some(&ValueType::Sigma { first, second }), &[left, right]) => {
                                let (table, rewrites) = session.rewrite_parts();
                                let fibre =
                                    substitute_value_type(arena, table, rewrites, second, left);
                                frames.push(Frame::Pending(
                                    alloc::vec![Goal::CheckValue(right, fibre)],
                                    Produced::Checked,
                                ));
                                goal = Goal::CheckValue(left, first);
                                continue 'expand;
                            },
                            _ => {
                                return Err(value_shape_mismatch(
                                    arena,
                                    ExpectedValueShape::Product,
                                    expected,
                                ));
                            },
                        }
                    },
                    Value::Thunk(body) => match arena.value_type(expected) {
                        Some(&ValueType::Thunk(codomain)) => {
                            goal = Goal::CheckComp(body, codomain);
                            continue 'expand;
                        },
                        _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Thunk,
                                expected,
                            ));
                        },
                    },
                    Value::Here {
                        point,
                        ref dialogues,
                    } => {
                        let dialogues = alloc::sync::Arc::clone(dialogues);
                        let (domain, left, right) = crate::element_identity::reflexive_parts(
                            arena,
                            crate::identity_recursion::Interfaces::of(judgement.entries),
                            expected,
                        )?;
                        frames.push(Frame::CheckHere {
                            point,
                            left,
                            right,
                            dialogues,
                        });
                        goal = Goal::CheckValue(point, domain);
                        continue 'expand;
                    },
                    // `stay(c)` checks at a flow, at either reading, by the
                    // point at the carrier and the endpoint conversions a
                    // `here` owes.
                    Value::Stay {
                        point,
                        ref dialogues,
                    } => {
                        let dialogues = alloc::sync::Arc::clone(dialogues);
                        let ends = crate::flow_universe::ends(arena, expected)
                            .map_err(KernelError::Flow)?;
                        frames.push(Frame::CheckHere {
                            point,
                            left: ends.source,
                            right: ends.target,
                            dialogues,
                        });
                        goal = Goal::CheckValue(point, ends.carrier);
                        continue 'expand;
                    },
                    // A higher field owes one check per guard, each at the
                    // fibre its walk computes; none re-enters the machine.
                    Value::Higher {
                        ref program,
                        ref evidence,
                    } => {
                        let program = alloc::sync::Arc::clone(program);
                        owed_values.clear();
                        owed_values.extend_from_slice(evidence);
                        let mut goals = crate::element_identity::higher_obligations(
                            arena,
                            crate::identity_recursion::Interfaces::of(judgement.entries),
                            expected,
                            &program,
                            &owed_values,
                        )?
                        .into_iter()
                        .rev()
                        .map(|(guard, fibre)| Goal::CheckValue(guard, fibre))
                        .collect::<Vec<_>>();
                        if let Some(next) = goals.pop() {
                            frames.push(Frame::Pending(goals, Produced::Checked));
                            goal = next;
                            continue 'expand;
                        }
                        Produced::Checked
                    },
                    // A higher evaluation replays every component's dialogues
                    // here, unfolding what the environment admitted, and owes
                    // each component's checks in that component's pattern
                    // telescope.
                    Value::HigherEvaluation {
                        ref dialogues,
                        ref components,
                    } => {
                        let dialogues = alloc::sync::Arc::clone(dialogues);
                        owed_components.clear();
                        owed_components.extend_from_slice(components);
                        let mut remaining = crate::element_identity::evaluation_obligations(
                            arena,
                            (
                                &admitted_unfoldings(judgement),
                                crate::identity_recursion::Interfaces::of(judgement.entries),
                            ),
                            expected,
                            &dialogues,
                            &owed_components,
                        )?;
                        remaining.reverse();
                        frames.push(Frame::Components {
                            outer: core::mem::take(&mut context),
                            remaining,
                        });
                        Produced::Checked
                    },
                    // A quantified evaluation replays every step's dialogues
                    // here, as a higher evaluation does, and owes each
                    // telescope's checks: the premise evidence, each applied
                    // input and each return's values and output evidence.
                    Value::QuantifiedEvaluation {
                        ref steps,
                        ref children,
                    } => {
                        let steps = alloc::sync::Arc::clone(steps);
                        owed_values.clear();
                        owed_values.extend_from_slice(children);
                        let mut remaining = crate::element_identity::quantified_obligations(
                            arena,
                            (
                                &admitted_unfoldings(judgement),
                                crate::identity_recursion::Interfaces::of(judgement.entries),
                            ),
                            expected,
                            &steps,
                            &owed_values,
                        )?;
                        remaining.reverse();
                        frames.push(Frame::Components {
                            outer: core::mem::take(&mut context),
                            remaining,
                        });
                        Produced::Checked
                    },
                    Value::Constructor { .. }
                    | Value::Returned(_)
                    | Value::PathRefl(_)
                    | Value::PathProduct(..)
                    | Value::SessionPath { .. }
                    | Value::SessionFlow { .. }
                    | Value::ForwardFlow { .. }
                    | Value::FunctionFlow { .. }
                    | Value::Then { .. }
                    | Value::FlowProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Univalence { .. }
                    | Value::Variable(_)
                    | Value::Constant(_)
                    | Value::Literal(_)
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticApplication(..) => {
                        frames.push(Frame::ConvertValue(expected));
                        goal = Goal::SynthValue(id);
                        continue 'expand;
                    },
                },
                Goal::SynthComp(id) => match *read_computation(arena, id)? {
                    Computation::DataCase {
                        scrutinee, motive, ..
                    } => {
                        frames.push(Frame::DataCase { case: id, motive });
                        goal = Goal::SynthValue(scrutinee);
                        continue 'expand;
                    },
                    Computation::SigmaSplit { scrutinee, .. } => {
                        frames.push(Frame::SigmaSplit(id));
                        goal = Goal::SynthValue(scrutinee);
                        continue 'expand;
                    },
                    Computation::RecordProjection(record, ref label) => {
                        frames.push(Frame::RecordProjection(label.clone()));
                        goal = Goal::SynthValue(record);
                        continue 'expand;
                    },
                    Computation::TupleProjection(tuple, component) => {
                        frames.push(Frame::TupleProjection(tuple, component));
                        goal = Goal::SynthValue(tuple);
                        continue 'expand;
                    },
                    Computation::ListFold {
                        element,
                        result,
                        list,
                        on_nil,
                        on_cons,
                    } => {
                        for annotation in [element, result] {
                            let _level = type_level(
                                arena,
                                judgement,
                                TypeLevelGoal::Value(annotation),
                                context.clone(),
                                Recording {
                                    memo,
                                    session,
                                    census,
                                    owed,
                                },
                            )?;
                        }
                        let result = arena.comp_type_returner(result);
                        frames.push(Frame::ProduceComp(result));
                        frames.push(Frame::FoldCons(element, result, on_cons));
                        frames.push(Frame::FoldNil(on_nil, result));
                        let list_type = arena.value_type_list(element);
                        goal = Goal::CheckValue(list, list_type);
                        continue 'expand;
                    },
                    // A list case carries no result annotation: it only
                    // checks, its branches against the expected type.
                    Computation::ListCase { .. } => {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::ListCase,
                        });
                    },
                    Computation::Transport(path, value) => {
                        frames.push(Frame::Transport(value));
                        goal = Goal::SynthValue(path);
                        continue 'expand;
                    },
                    Computation::PathTransport { path, .. } => {
                        frames.push(Frame::ElementTransport(id));
                        goal = Goal::SynthValue(path);
                        continue 'expand;
                    },
                    Computation::TelescopeTransport { path, .. } => {
                        frames.push(Frame::TelescopePath(id));
                        goal = Goal::SynthValue(path);
                        continue 'expand;
                    },
                    Computation::Ride { flow, .. } => {
                        frames.push(Frame::Ride(id));
                        goal = Goal::SynthValue(flow);
                        continue 'expand;
                    },
                    Computation::TelescopeRide { flow, .. } => {
                        frames.push(Frame::TelescopeRideFlow(id));
                        goal = Goal::SynthValue(flow);
                        continue 'expand;
                    },
                    Computation::RelatedApplication { path, .. } => {
                        frames.push(Frame::RelatedPath(id));
                        goal = Goal::SynthValue(path);
                        continue 'expand;
                    },
                    // A call into a definition whose result follows the
                    // parameter it recurses on returns at the stage of the
                    // argument there, read as the checker reads it.
                    Computation::Application(head, argument) => {
                        if let Maybe::Present(staged) = recursion::followed(
                            arena,
                            (session, judgement.entries, context.as_slice()),
                            (head, argument),
                        ) {
                            frames.push(Frame::Restage(staged));
                        }
                        frames.push(Frame::SynthApply(argument));
                        goal = Goal::SynthComp(head);
                        continue 'expand;
                    },
                    Computation::Force(value) => {
                        frames.push(Frame::SynthForce);
                        goal = Goal::SynthValue(value);
                        continue 'expand;
                    },
                    Computation::Return(value) => {
                        frames.push(Frame::SynthReturn);
                        goal = Goal::SynthValue(value);
                        continue 'expand;
                    },
                    Computation::Bind(bound, body) => {
                        frames.push(Frame::SynthBind(body));
                        goal = Goal::SynthComp(bound);
                        continue 'expand;
                    },
                    // A pairing synthesizes when every component does, as a
                    // tuple does; a component that only checks makes the
                    // pairing checking-only too. The empty pairing
                    // synthesizes the terminal type.
                    Computation::With(ref components) => {
                        let mut remaining = components.iter().rev().copied().collect::<Vec<_>>();
                        let arity = remaining.len();
                        if let Some(first) = remaining.pop() {
                            frames.push(Frame::SynthWith {
                                remaining,
                                types: Vec::with_capacity(arity),
                            });
                            goal = Goal::SynthComp(first);
                            continue 'expand;
                        }
                        Produced::CompType(arena.comp_type_with(&[]))
                    },
                    Computation::Project(component, pair) => {
                        frames.push(Frame::Project(component));
                        goal = Goal::SynthComp(pair);
                        continue 'expand;
                    },
                    // A case of no branches has none to synthesize a type
                    // from; it only checks.
                    Computation::Case {
                        scrutinee,
                        ref branches,
                    } => {
                        if branches.is_empty() {
                            return Err(KernelError::NotInferable {
                                form: NonInferableForm::EmptyCase,
                            });
                        }
                        frames.push(Frame::SynthCaseScrutinee(branches.clone()));
                        goal = Goal::SynthValue(scrutinee);
                        continue 'expand;
                    },
                    Computation::Lambda(_) => {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::Lambda,
                        });
                    },
                    Computation::Fixpoint { .. } => {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::Fixpoint,
                        });
                    },
                },
                Goal::CheckComp(id, expected) => match *read_computation(arena, id)? {
                    // A lambda pushes the arrow's domain as the innermost
                    // context slot and checks its body against the codomain
                    // read from under that slot. The dependent arrow's codomain
                    // is written under the binder already; the plain arrow's is
                    // written outside it, so it is weakened past the slot. A
                    // codata type is read through its observations first, here
                    // and at a returner and a pairing.
                    Computation::Lambda(body) => {
                        match codata::read(arena, session, judgement, expected)
                            .map(|shape| arena.comp_type(shape))?
                        {
                            Some(&CompType::Arrow { domain, codomain }) => {
                                let scoped = weakened(arena, session, codomain);
                                context.push(domain);
                                frames.push(Frame::ScopeExit);
                                goal = Goal::CheckComp(body, scoped);
                                continue 'expand;
                            },
                            Some(&CompType::Pi { domain, codomain }) => {
                                context.push(domain);
                                frames.push(Frame::ScopeExit);
                                goal = Goal::CheckComp(body, codomain);
                                continue 'expand;
                            },
                            _ => {
                                return Err(comp_shape_mismatch(
                                    arena,
                                    ExpectedComputationShape::Arrow,
                                    expected,
                                ));
                            },
                        }
                    },
                    // A fixpoint checks with the self thunk as the innermost
                    // slot, its body against the classifier weakened past that
                    // slot. A partial one checks at any computation type, and
                    // progress is the unfolding rule's gate, not a typing
                    // condition. A structural one opens its stage first
                    // (`recursion::open_fixpoint`): the self binder takes the
                    // recursed-on parameter below the stage and the body takes
                    // it at the stage.
                    Computation::Fixpoint { body, evidence } => {
                        let position = match evidence {
                            FixpointEvidence::Partial => None,
                            FixpointEvidence::StructuralDescent => {
                                Some(gandr_kernel_term::StagedPosition::default())
                            },
                            FixpointEvidence::Staged { position } => Some(position),
                        };
                        let (own, inside) = match position {
                            None => (expected, expected),
                            Some(position) => {
                                root = respect::fold_root(
                                    arena,
                                    judgement.presentations,
                                    id,
                                    (expected, position),
                                    body,
                                );
                                let result = match judgement.following {
                                    Maybe::Present(fixpoint) if fixpoint == id => {
                                        recursion::ResultStage::Following
                                    },
                                    Maybe::Present(_) | Maybe::Absent(_) => {
                                        recursion::ResultStage::Declared
                                    },
                                };
                                let opened = recursion::open_fixpoint(
                                    arena,
                                    &mut stages,
                                    (expected, position),
                                    result,
                                )?;
                                staged_bodies = staged_bodies.saturating_add(1);
                                frames.push(Frame::StageExit);
                                (opened.own, opened.inside)
                            },
                        };
                        let recursive = arena.value_type_thunk(own);
                        let scoped = weakened(arena, session, inside);
                        if position.is_some()
                            && matches!(judgement.own, Maybe::Present(root) if root == id)
                        {
                            own_fixpoint = Maybe::Present((context.len(), recursive));
                        }
                        context.push(recursive);
                        frames.push(Frame::ScopeExit);
                        goal = Goal::CheckComp(body, scoped);
                        continue 'expand;
                    },
                    Computation::Return(value) => {
                        match codata::read(arena, session, judgement, expected)
                            .map(|shape| arena.comp_type(shape))?
                        {
                            Some(&CompType::Returner(result)) => {
                                goal = Goal::CheckValue(value, result);
                                continue 'expand;
                            },
                            _ => {
                                return Err(comp_shape_mismatch(
                                    arena,
                                    ExpectedComputationShape::Returner,
                                    expected,
                                ));
                            },
                        }
                    },
                    Computation::Bind(bound, body) => {
                        frames.push(Frame::CheckBind(body, expected));
                        goal = Goal::SynthComp(bound);
                        continue 'expand;
                    },
                    // A pairing checks against a lazy product of its arity
                    // by checking each component against its own; none binds
                    // anything.
                    Computation::With(_) => {
                        let shape = codata::read(arena, session, judgement, expected)?;
                        let mut goals = match (arena.comp_type(shape), read_computation(arena, id)?)
                        {
                            (
                                Some(&CompType::With(ref types)),
                                &Computation::With(ref components),
                            ) if types.len() == components.len() => components
                                .iter()
                                .zip(types.iter())
                                .rev()
                                .map(|(&component, &ty)| Goal::CheckComp(component, ty))
                                .collect::<Vec<_>>(),
                            _ => {
                                return Err(comp_shape_mismatch(
                                    arena,
                                    ExpectedComputationShape::With,
                                    expected,
                                ));
                            },
                        };
                        if let Some(next) = goals.pop() {
                            frames.push(Frame::Pending(goals, Produced::Checked));
                            goal = next;
                            continue 'expand;
                        }
                        Produced::Checked
                    },
                    Computation::Case {
                        scrutinee,
                        ref branches,
                    } => {
                        frames.push(Frame::CheckCaseScrutinee {
                            branches: branches.clone(),
                            expected,
                        });
                        goal = Goal::SynthValue(scrutinee);
                        continue 'expand;
                    },
                    // A list case synthesizes its list, as a sum case its
                    // scrutinee, then checks each branch against the case's
                    // type: the empty branch as it stands, the cell branch under
                    // the head and the tail.
                    Computation::ListCase {
                        list,
                        on_nil,
                        on_cons,
                    } => {
                        frames.push(Frame::ListCaseScrutinee {
                            on_nil,
                            on_cons,
                            expected,
                        });
                        goal = Goal::SynthValue(list);
                        continue 'expand;
                    },
                    // An applied fixpoint synthesizes nothing, so the
                    // application reads its arrow off the argument's type and
                    // the type it is checked against: the fixpoint checks
                    // against that arrow, which is the application rule at
                    // the domain the argument has.
                    Computation::Application(head, argument)
                        if matches!(
                            read_computation(arena, head)?,
                            &Computation::Fixpoint { .. }
                        ) =>
                    {
                        frames.push(Frame::FixpointArgument(head, expected));
                        goal = Goal::SynthValue(argument);
                        continue 'expand;
                    },
                    Computation::DataCase {
                        scrutinee, motive, ..
                    } => {
                        frames.push(Frame::ConvertComp(expected));
                        // A case checked at its written motive with the
                        // result read at a stage reads its branches there.
                        match recursion::motive_at(arena, session, motive, expected)? {
                            Maybe::Present(at) => {
                                frames.push(Frame::DataCase {
                                    case: id,
                                    motive: at,
                                });
                                goal = Goal::SynthValue(scrutinee);
                            },
                            Maybe::Absent(_plain) => goal = Goal::SynthComp(id),
                        }
                        continue 'expand;
                    },
                    Computation::SigmaSplit { .. }
                    | Computation::RecordProjection(..)
                    | Computation::TupleProjection(..)
                    | Computation::Transport(..)
                    | Computation::PathTransport { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::Ride { .. }
                    | Computation::TelescopeRide { .. }
                    | Computation::RelatedApplication { .. }
                    | Computation::ListFold { .. }
                    | Computation::Application(..)
                    | Computation::Project(..)
                    | Computation::Force(_) => {
                        frames.push(Frame::ConvertComp(expected));
                        goal = Goal::SynthComp(id);
                        continue 'expand;
                    },
                },
            },
        };
        loop {
            let Some(frame) = frames.pop()
            else {
                // Every code this run owed is drained under the stages it was
                // owed below. The order only grows, so the one the run ends
                // with keeps every fit the formation walk saw.
                if stages != StageOrder::default() {
                    for obligation in owed.iter_mut().skip(first_owed) {
                        let &mut (CodeObligation::Universe {
                            stages: ref mut under,
                            ..
                        }
                        | CodeObligation::Data {
                            stages: ref mut under,
                            ..
                        }
                        | CodeObligation::Codata {
                            stages: ref mut under,
                            ..
                        }
                        | CodeObligation::Endpoints {
                            stages: ref mut under,
                            ..
                        }) = obligation;
                        under.clone_from(&stages);
                    }
                }
                return Ok(produced);
            };
            match frame {
                Frame::Pending(mut goals, result) => {
                    if let Some(next) = goals.pop() {
                        frames.push(Frame::Pending(goals, result));
                        goal = next;
                        continue 'expand;
                    }
                    produced = result;
                },
                Frame::RecordField {
                    label,
                    mut remaining,
                    mut fields,
                } => {
                    fields.insert(label, produced.value_type()?);
                    if let Some((label, value)) = remaining.pop() {
                        frames.push(Frame::RecordField {
                            label,
                            remaining,
                            fields,
                        });
                        goal = Goal::SynthValue(value);
                        continue 'expand;
                    }
                    produced = Produced::ValueType(arena.value_type_record(fields));
                },
                Frame::RecordProjection(label) => {
                    let actual = produced.value_type()?;
                    let Some(matched_native_node) = arena.value_type(actual)
                    else {
                        return Err(value_shape_mismatch(
                            arena,
                            ExpectedValueShape::Record,
                            actual,
                        ));
                    };
                    let ValueType::Record(ref fields) = *matched_native_node
                    else {
                        return Err(value_shape_mismatch(
                            arena,
                            ExpectedValueShape::Record,
                            actual,
                        ));
                    };
                    let field = *fields
                        .get(&label)
                        .ok_or(KernelError::AbsentRecordField { label })?;
                    produced = Produced::CompType(arena.comp_type_returner(field));
                },
                // A projection of a product returns the part at its position.
                // A projection of a dependent pair returns the first factor at
                // the first component and, at the second, the second factor
                // instantiated at the first component's own projection.
                Frame::TupleProjection(tuple, component) => {
                    let actual = produced.value_type()?;
                    if let Some(&ValueType::Sigma { first, second }) = arena.value_type(actual) {
                        let part = match usize::from(component) {
                            0 => first,
                            1 => {
                                let projected = arena.computation_tuple_projection(
                                    tuple,
                                    gandr_kernel_term::Component::from(0_usize),
                                );
                                let projected = arena.value_returned(projected);
                                let (table, rewrites) = session.rewrite_parts();
                                substitute_value_type(arena, table, rewrites, second, projected)
                            },
                            _ => return Err(KernelError::AbsentTupleComponent { component }),
                        };
                        produced = Produced::CompType(arena.comp_type_returner(part));
                        continue;
                    }
                    let Some(parts) = arena.value_type(actual).and_then(ValueType::product_parts)
                    else {
                        return Err(value_shape_mismatch(
                            arena,
                            ExpectedValueShape::Product,
                            actual,
                        ));
                    };
                    let part = *parts
                        .get(usize::from(component))
                        .ok_or(KernelError::AbsentTupleComponent { component })?;
                    produced = Produced::CompType(arena.comp_type_returner(part));
                },
                Frame::DataCase { case, motive: at } => {
                    // A scrutinee at a stage opens one below it, and a
                    // scrutinee at a looped point's path is split over the
                    // words its free cells mint.
                    let scrutinee = produced.value_type()?;
                    let (scrutinee_type, opened) =
                        recursion::open_case(arena, judgement.entries, &mut stages, scrutinee)?;
                    // A stratified value at no stage is read at a fresh root,
                    // this run's own: the case's arms are neither recalled nor
                    // memoized, as a fixpoint's body is not.
                    if scrutinee_type == scrutinee && matches!(opened, Maybe::Present(_)) {
                        staged_bodies = staged_bodies.saturating_add(1);
                        frames.push(Frame::StageExit);
                    }
                    let datatype = judgement.presentations.identified(arena, scrutinee_type);
                    let Some(matched_native_node) = arena.computation(case)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let Computation::DataCase { ref motive, .. } = *matched_native_node
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let motive = *motive;
                    context.push(datatype);
                    let formed = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Comp(motive),
                        context.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    );
                    let _bound = context.pop();
                    let _level = formed?;
                    let reading = match core::mem::replace(
                        &mut root,
                        Maybe::Absent(respect::root::Absent::Unmarked),
                    ) {
                        Maybe::Present((marked, reading)) if marked == case => reading,
                        Maybe::Present(_) | Maybe::Absent(_) => respect::Reading::Case { datatype },
                    };
                    // A case of no branches over a path between two apart
                    // terms of a data type owes no branch.
                    let absurd = former::absurd(
                        arena,
                        (judgement.entries, judgement.presentations),
                        session,
                        case,
                        datatype,
                    )?;
                    if let Maybe::Present(result) = absurd {
                        produced = Produced::CompType(result);
                    }
                    else {
                        // Inside the declaration's own fixpoint, its constant
                        // in a field type reads as the self binder, at the
                        // binder's index in the case's context.
                        let own_constant = match own_fixpoint {
                            Maybe::Present((slot, binder))
                                if context.get(slot) == Some(&binder) =>
                            {
                                context
                                    .len()
                                    .checked_sub(slot.saturating_add(1))
                                    .and_then(|index| u32::try_from(index).ok())
                                    .map_or(Maybe::Absent(recursion::Unowned::Outside), |index| {
                                        Maybe::Present((
                                            ConstantIndex::from(judgement.entries.len()),
                                            DeBruijnIndex::from(index),
                                        ))
                                    })
                            },
                            Maybe::Present(_) | Maybe::Absent(_) => {
                                Maybe::Absent(recursion::Unowned::Outside)
                            },
                        };
                        // A rule is owed at the written motive; only a type
                        // with none reads its branches at a staged one.
                        let obliged = respect::obliged(arena, judgement.entries, datatype, reading);
                        let branches_at = match obliged {
                            Maybe::Present(_) => motive,
                            Maybe::Absent(_) => at,
                        };
                        let (result, mut goals, looped, reads) = former::case(
                            arena,
                            (judgement.entries, judgement.presentations),
                            session,
                            (case, branches_at),
                            (datatype, opened, own_constant),
                        )?;
                        // A field domain that named the constant is formed as
                        // read, under the branch's fields before it at their
                        // stage, so a decode at a place that does not descend
                        // is refused by the stage order; the field may name a
                        // later definition of the block, as its family did.
                        for read in reads {
                            let Some(&Goal::CheckComp(_, mut telescope)) =
                                goals.get(usize::from(read.tag))
                            else {
                                return Err(KernelError::ArenaFault);
                            };
                            let mut under = context.clone();
                            for _before in 0 .. usize::from(read.field) {
                                let Some(&CompType::Pi { domain, codomain }) =
                                    arena.comp_type(telescope)
                                else {
                                    return Err(KernelError::ArenaFault);
                                };
                                under.push(domain);
                                telescope = codomain;
                            }
                            let _level = type_level(
                                arena,
                                judgement.foreseeing(),
                                TypeLevelGoal::Value(read.domain),
                                under,
                                Recording {
                                    memo,
                                    session,
                                    census,
                                    owed,
                                },
                            )?;
                        }
                        if looped == former::Looped::Owed {
                            frames.push(Frame::Loops(case, datatype));
                        }
                        if let Maybe::Present(reading) = obliged {
                            frames.push(Frame::Respect(case, reading));
                        }
                        goals.reverse();
                        if let Some(next) = goals.pop() {
                            frames.push(Frame::Pending(goals, Produced::CompType(result)));
                            goal = next;
                            continue 'expand;
                        }
                        produced = Produced::CompType(result);
                    }
                },
                Frame::Respect(case, reading) => {
                    respect::respected(
                        arena,
                        (judgement.entries, &admitted_unfoldings(judgement)),
                        case,
                        reading,
                        judgement.laws,
                    )?;
                },
                Frame::Loops(case, datatype) => {
                    loops::respected(
                        arena,
                        &admitted_unfoldings(judgement),
                        context.as_slice(),
                        (case, datatype),
                    )?;
                },
                // A dependent split forms its motive under the scrutinee's
                // binder, checks its body under the two components against the
                // motive at their pair, and returns the motive at the scrutinee.
                Frame::SigmaSplit(split) => {
                    let scrutinee_type = produced.value_type()?;
                    let Some(&Computation::SigmaSplit {
                        scrutinee,
                        motive,
                        body,
                    }) = arena.computation(split)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let Some(&ValueType::Sigma { first, second }) =
                        arena.value_type(scrutinee_type)
                    else {
                        return Err(value_shape_mismatch(
                            arena,
                            ExpectedValueShape::Sigma,
                            scrutinee_type,
                        ));
                    };
                    context.push(scrutinee_type);
                    let formed = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Comp(motive),
                        context.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    );
                    let _bound = context.pop();
                    let _level = formed?;
                    let (table, rewrites) = session.rewrite_parts();
                    let result = substitute_comp_type(arena, table, rewrites, motive, scrutinee);
                    let (table, rewrites) = session.rewrite_parts();
                    let lifted = shift_comp_type(
                        arena,
                        table,
                        rewrites,
                        motive,
                        BinderDepth::from(1_u32),
                        BinderDepth::from(2_u32),
                    );
                    let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
                    let inner = arena.value_variable(DeBruijnIndex::from(0_u32));
                    let pair = arena.value_tuple(&[outer, inner]);
                    let (table, rewrites) = session.rewrite_parts();
                    let expected = substitute_comp_type(arena, table, rewrites, lifted, pair);
                    context.push(first);
                    context.push(second);
                    frames.push(Frame::ProduceComp(result));
                    frames.push(Frame::ScopeExit);
                    frames.push(Frame::ScopeExit);
                    goal = Goal::CheckComp(body, expected);
                    continue 'expand;
                },
                Frame::FoldNil(body, result) => {
                    goal = Goal::CheckComp(body, result);
                    continue 'expand;
                },
                Frame::FoldCons(element, result, body) => {
                    let under_head = weakened(arena, session, result);
                    let Some(&CompType::Returner(folded)) = arena.comp_type(under_head)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let under_both = weakened(arena, session, under_head);
                    context.push(element);
                    context.push(folded);
                    frames.push(Frame::ScopeExit);
                    frames.push(Frame::ScopeExit);
                    goal = Goal::CheckComp(body, under_both);
                    continue 'expand;
                },
                Frame::ListCaseScrutinee {
                    on_nil,
                    on_cons,
                    expected,
                } => {
                    let list_type = produced.value_type()?;
                    // A list at a stage opens one below it, which its tail
                    // takes.
                    let (read, opened) =
                        recursion::open_case(arena, judgement.entries, &mut stages, list_type)?;
                    let Some(&ValueType::List(element)) = arena.value_type(read)
                    else {
                        return Err(value_shape_mismatch(
                            arena,
                            ExpectedValueShape::List,
                            list_type,
                        ));
                    };
                    let tail = arena.value_type_list(element);
                    let tail = match opened {
                        Maybe::Present(child) => {
                            arena.value_type_staged(tail, gandr_kernel_term::Stage::At(child))
                        },
                        Maybe::Absent(_) => tail,
                    };
                    frames.push(Frame::ListCaseCons(element, tail, expected, on_cons));
                    goal = Goal::CheckComp(on_nil, expected);
                    continue 'expand;
                },
                Frame::ListCaseCons(element, tail, expected, body) => {
                    let listed = arena.comp_type_returner(tail);
                    let listed = weakened(arena, session, listed);
                    let Some(&CompType::Returner(tail)) = arena.comp_type(listed)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let under_head = weakened(arena, session, expected);
                    let under_both = weakened(arena, session, under_head);
                    context.push(element);
                    context.push(tail);
                    frames.push(Frame::ScopeExit);
                    frames.push(Frame::ScopeExit);
                    goal = Goal::CheckComp(body, under_both);
                    continue 'expand;
                },
                Frame::Memoize(support) => {
                    // A memo at its ceiling declines to record; see the same
                    // note in `type_level`.
                    let _recorded = memo.remember(support, produced.outcome());
                },
                Frame::PathProductFirst(second) => {
                    let first_type = produced.value_type()?;
                    let endpoints = crate::path_universe::endpoints(
                        arena,
                        first_type,
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(KernelError::Path)?;
                    frames.push(Frame::PathProductSecond(endpoints));
                    goal = Goal::SynthValue(second);
                    continue 'expand;
                },
                Frame::PathProductSecond(first) => {
                    let second_type = produced.value_type()?;
                    let second = crate::path_universe::endpoints(
                        arena,
                        second_type,
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(KernelError::Path)?;
                    let source = arena.value_type_product(&[first.source, second.source]);
                    let target = arena.value_type_product(&[first.target, second.target]);
                    let source = arena.value_quote(source);
                    let target = arena.value_quote(target);
                    produced = Produced::ValueType(arena.value_type_path_universe(source, target));
                },
                // **The flow product.** Each component reads as a universe
                // flow, under either reading of the level-zero universe; the
                // product relates the pairs of their endpoints, source to
                // source and target to target, as the path product does. The
                // pairs must themselves be codes of the `Flow_U` vocabulary,
                // so a component at a function or session code is refused
                // rather than minting a classifier no other rule reads.
                Frame::FlowProductFirst(second) => {
                    let first_type = produced.value_type()?;
                    let endpoints = crate::flow_universe::universe_reading(
                        arena,
                        first_type,
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(KernelError::Flow)?;
                    frames.push(Frame::FlowProductSecond(endpoints));
                    goal = Goal::SynthValue(second);
                    continue 'expand;
                },
                Frame::FlowProductSecond(first) => {
                    let second_type = produced.value_type()?;
                    let second = crate::flow_universe::universe_reading(
                        arena,
                        second_type,
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(KernelError::Flow)?;
                    let source = arena.value_type_product(&[first.source, second.source]);
                    let target = arena.value_type_product(&[first.target, second.target]);
                    let source = arena.value_quote(source);
                    let target = arena.value_quote(target);
                    let classifier = arena.value_type_flow_universe(source, target);
                    let _decoded = crate::flow_universe::endpoints(
                        arena,
                        classifier,
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(KernelError::Flow)?;
                    produced = Produced::ValueType(classifier);
                },
                Frame::PathForward {
                    path,
                    endpoints,
                    context: outer,
                } => {
                    let Value::PathEquiv { backward, .. } = *read_value(arena, path)?
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let result = arena.comp_type_returner(endpoints.source);
                    let function = arena.comp_type_arrow(endpoints.target, result);
                    let translator = arena.value_type_thunk(function);
                    frames.push(Frame::PathBackward {
                        path,
                        endpoints,
                        context: outer,
                    });
                    goal = Goal::CheckValue(backward, translator);
                    continue 'expand;
                },
                Frame::PathBackward {
                    path,
                    endpoints,
                    context: outer,
                } => {
                    let Value::PathEquiv {
                        path_type,
                        forward,
                        backward,
                        ref evidence,
                    } = *read_value(arena, path)?
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    // Replay mutates the arena; retain only the evidence across that borrow.
                    // A translator may name what the environment admitted
                    // before it, so both round trips unfold its definitions.
                    let evidence = alloc::sync::Arc::clone(evidence);
                    let unfoldings = admitted_unfoldings(judgement);
                    let watermark = arena.watermark();
                    let source = crate::path_universe::coverage::round_trip(
                        arena,
                        &unfoldings,
                        (endpoints.source, crate::path_universe::Direction::Source),
                        (forward, backward),
                        &evidence.source,
                        crate::replay::ReplayBudget::DEFAULT,
                    );
                    let result = source.and_then(|()| {
                        crate::path_universe::coverage::round_trip(
                            arena,
                            &unfoldings,
                            (endpoints.target, crate::path_universe::Direction::Target),
                            (backward, forward),
                            &evidence.target,
                            crate::replay::ReplayBudget::DEFAULT,
                        )
                    });
                    arena.truncate_to(watermark);
                    result.map_err(KernelError::Path)?;
                    context = outer;
                    produced = Produced::ValueType(path_type);
                },
                Frame::Transport(value) => {
                    let path_type = produced.value_type()?;
                    let endpoints = crate::path_universe::endpoints(
                        arena,
                        path_type,
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(KernelError::Path)?;
                    frames.push(Frame::ProduceComp(
                        arena.comp_type_returner(endpoints.target),
                    ));
                    goal = Goal::CheckValue(value, endpoints.source);
                    continue 'expand;
                },
                Frame::SynthHere(point) => {
                    let domain = produced.value_type()?;
                    produced = Produced::ValueType(arena.value_type_path(domain, point, point));
                },
                Frame::UnivalenceRecord(equivalence) => {
                    let classifier = produced.value_type()?;
                    let (path_type, record) =
                        crate::path_universe::univalence_reading(arena, classifier)
                            .map_err(KernelError::Path)?;
                    let _level = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Value(path_type),
                        context.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    )?;
                    frames.push(Frame::ProduceValue(path_type));
                    goal = Goal::CheckValue(equivalence, record);
                    continue 'expand;
                },
                Frame::SynthReturned => {
                    let synthesized = produced.comp_type()?;
                    let Some(&CompType::Returner(result)) = arena.comp_type(synthesized)
                    else {
                        return Err(KernelError::Identity(
                            crate::element_identity::IdentityError::ReturnedNonReturner(
                                comp_type_witness(arena, synthesized),
                            ),
                        ));
                    };
                    produced = Produced::ValueType(result);
                },
                // Reflexivity is decided by the kernel's term conversion,
                // the laws of bind among its forced rules; an endpoint it
                // leaves apart is related by the dialogue the `here` carries,
                // unfolding only the admitted definitions the dialogue names.
                Frame::CheckHere {
                    point,
                    left,
                    right,
                    dialogues,
                } => {
                    crate::element_identity::reflexive_endpoints(
                        arena,
                        &admitted_unfoldings(judgement),
                        point,
                        (left, right),
                        &dialogues,
                    )?;
                    produced = Produced::Checked;
                },
                Frame::Components {
                    outer,
                    mut remaining,
                } => {
                    let Some(component) = remaining.pop()
                    else {
                        context = outer;
                        produced = Produced::Checked;
                        continue;
                    };
                    context = component.context;
                    frames.push(Frame::Components { outer, remaining });
                    let mut goals = component
                        .checks
                        .into_iter()
                        .rev()
                        .map(|(value, ty)| Goal::CheckValue(value, ty))
                        .collect::<Vec<_>>();
                    let Some(next) = goals.pop()
                    else {
                        produced = Produced::Checked;
                        continue;
                    };
                    frames.push(Frame::Pending(goals, Produced::Checked));
                    goal = next;
                    continue 'expand;
                },
                // Transport's input checks at the motive instantiated at the
                // source endpoint, and it returns at the motive instantiated
                // at the target: instantiation is the rewrite machine's
                // substitution, so the law holds of every motive. A word
                // written as the path is followed as the path it is.
                Frame::ElementTransport(transport) => {
                    let path_type = produced.value_type()?;
                    let Some(&Computation::PathTransport { motive, value, .. }) =
                        arena.computation(transport)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let (domain, left, right) =
                        crate::words::followed(arena, judgement.presentations, path_type)?;
                    let mut scoped = context.clone();
                    scoped.push(domain);
                    let _level = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Value(motive),
                        scoped,
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    )?;
                    let (table, rewrites) = session.rewrite_parts();
                    let source = substitute_value_type(arena, table, rewrites, motive, left);
                    let target = substitute_value_type(arena, table, rewrites, motive, right);
                    frames.push(Frame::ProduceComp(arena.comp_type_returner(target)));
                    goal = Goal::CheckValue(value, source);
                    continue 'expand;
                },
                // A telescope transport forms its motive, reads the path's
                // carrier as the motive's first entry, and checks the start
                // in the family's fibre over the path's source.
                Frame::TelescopePath(transport) => {
                    let path_type = produced.value_type()?;
                    let Some(&Computation::TelescopeTransport { motive, start, .. }) =
                        arena.computation(transport)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let Maybe::Present(crate::element_identity::Telescope {
                        carrier, family, ..
                    }) = crate::element_identity::telescope(arena, motive)?
                    else {
                        return Err(comp_shape_mismatch(
                            arena,
                            ExpectedComputationShape::Telescope,
                            motive,
                        ));
                    };
                    let _level = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Comp(motive),
                        context.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    )?;
                    let (domain, left, right) =
                        crate::words::followed(arena, judgement.presentations, path_type)?;
                    if let Err(mismatch) = former::assignable(arena, carrier, domain) {
                        let reading = read_returned(
                            arena,
                            judgement,
                            ConversionGoal::ValueType(carrier, domain),
                        )?;
                        if reading != EndpointReading::Converts {
                            return Err(mismatch);
                        }
                    }
                    let (table, rewrites) = session.rewrite_parts();
                    let source_fibre = substitute_value_type(arena, table, rewrites, family, left);
                    frames.push(Frame::TelescopeStart {
                        transport,
                        ends: (left, right),
                    });
                    goal = Goal::CheckValue(start, source_fibre);
                    continue 'expand;
                },
                Frame::TelescopeStart { transport, ends } => {
                    let Some(&Computation::TelescopeTransport { over, .. }) =
                        arena.computation(transport)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    frames.push(Frame::TelescopeOver { transport, ends });
                    goal = Goal::SynthValue(over);
                    continue 'expand;
                },
                // **The dependency is respected or refused by name.** The
                // second identity lies over the path: it relates, in the
                // fibre at the path's target, the start transported along the
                // path to some element. The value then checks at the body
                // instantiated at the source pair and returns at the target
                // pair, each by iterated single substitution.
                Frame::TelescopeOver {
                    transport,
                    ends: (left, right),
                } => {
                    let over_type = produced.value_type()?;
                    let Some(&Computation::TelescopeTransport {
                        motive,
                        path,
                        start,
                        value,
                        ..
                    }) = arena.computation(transport)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let Maybe::Present(crate::element_identity::Telescope { family, body, .. }) =
                        crate::element_identity::telescope(arena, motive)?
                    else {
                        return Err(comp_shape_mismatch(
                            arena,
                            ExpectedComputationShape::Telescope,
                            motive,
                        ));
                    };
                    let (_fibre, _lifted, finish) =
                        crate::element_identity::path_parts(arena, over_type)?;
                    let (table, rewrites) = session.rewrite_parts();
                    let target_fibre = substitute_value_type(arena, table, rewrites, family, right);
                    let carried = arena.computation_path_transport(family, path, start);
                    let carried = arena.value_returned(carried);
                    let lies_over = arena.value_type_path(target_fibre, carried, finish);
                    if former::assignable(arena, lies_over, over_type).is_err() {
                        let reading = read_returned(
                            arena,
                            judgement,
                            ConversionGoal::ValueType(lies_over, over_type),
                        )?;
                        if reading != EndpointReading::Converts {
                            return Err(KernelError::Identity(
                                crate::element_identity::IdentityError::NotOver {
                                    expected: value_type_witness(arena, lies_over),
                                    actual: value_type_witness(arena, over_type),
                                },
                            ));
                        }
                    }
                    let (table, rewrites) = session.rewrite_parts();
                    let source = crate::element_identity::telescope_instance(
                        arena,
                        table,
                        rewrites,
                        body,
                        (left, start),
                    );
                    let target = crate::element_identity::telescope_instance(
                        arena,
                        table,
                        rewrites,
                        body,
                        (right, finish),
                    );
                    frames.push(Frame::ProduceComp(arena.comp_type_returner(target)));
                    goal = Goal::CheckValue(value, source);
                    continue 'expand;
                },
                Frame::SynthStay(point) => {
                    let domain = produced.value_type()?;
                    produced = Produced::ValueType(arena.value_type_flow(domain, point, point));
                },
                // A forward flow's translator checked; each image opens to a
                // leaf-natural target shape and its dialogue replays, unfolding
                // only what the environment admitted before it.
                Frame::FlowForward {
                    flow,
                    endpoints,
                    context: outer,
                } => {
                    let (flow_type, translator, images, dialogues) = match *read_value(arena, flow)?
                    {
                        Value::ForwardFlow {
                            flow_type,
                            translator,
                            ref outputs,
                            ref dialogues,
                        } => (
                            flow_type,
                            translator,
                            outputs.clone(),
                            alloc::sync::Arc::clone(dialogues),
                        ),
                        Value::Constructor { .. }
                        | Value::Record(_)
                        | Value::SessionPath { .. }
                        | Value::SessionFlow { .. }
                        | Value::Stay { .. }
                        | Value::FunctionFlow { .. }
                        | Value::Then { .. }
                        | Value::FlowProduct(..)
                        | Value::PathRefl(_)
                        | Value::PathProduct(..)
                        | Value::PathEquiv { .. }
                        | Value::Univalence { .. }
                        | Value::Here { .. }
                        | Value::Returned(_)
                        | Value::Higher { .. }
                        | Value::HigherEvaluation { .. }
                        | Value::QuantifiedEvaluation { .. }
                        | Value::Variable(_)
                        | Value::Constant(_)
                        | Value::Literal(_)
                        | Value::Tuple(_)
                        | Value::Injection(..)
                        | Value::ListNil
                        | Value::ListCons(..)
                        | Value::Thunk(_)
                        | Value::Lift { .. }
                        | Value::Quote(_)
                        | Value::QuoteComputation(_)
                        | Value::StaticApplication(..) => return Err(KernelError::ArenaFault),
                    };
                    let unfoldings = admitted_unfoldings(judgement);
                    let watermark = arena.watermark();
                    let result = crate::flow_universe::forward(
                        arena,
                        &unfoldings,
                        endpoints,
                        translator,
                        (&images, &dialogues),
                        crate::replay::ReplayBudget::DEFAULT,
                    );
                    arena.truncate_to(watermark);
                    result.map_err(KernelError::Flow)?;
                    context = outer;
                    produced = Produced::ValueType(flow_type);
                },
                // A function flow's boundary must run the way the arrow's
                // variance fixes at its position: the domain from the target's
                // argument to the source's, the codomain from the source's
                // result to the target's.
                Frame::FlowBoundary { flow, position } => {
                    let classifier = produced.value_type()?;
                    let Value::FunctionFlow {
                        flow_type,
                        codomain,
                        ..
                    } = *read_value(arena, flow)?
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let arrows = crate::flow_universe::function_type(
                        arena,
                        flow_type,
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(KernelError::Flow)?;
                    crate::flow_universe::oriented(
                        arena,
                        position,
                        arrows,
                        classifier,
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(KernelError::Flow)?;
                    match position {
                        crate::flow_universe::Boundary::Domain => {
                            frames.push(Frame::FlowBoundary {
                                flow,
                                position: crate::flow_universe::Boundary::Codomain,
                            });
                            goal = Goal::SynthValue(codomain);
                            continue 'expand;
                        },
                        crate::flow_universe::Boundary::Codomain => {
                            produced = Produced::ValueType(flow_type);
                        },
                    }
                },
                Frame::ThenFirst(then) => {
                    let first = produced.value_type()?;
                    let Value::Then { second, .. } = *read_value(arena, then)?
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    frames.push(Frame::ThenSecond { then, first });
                    goal = Goal::SynthValue(second);
                    continue 'expand;
                },
                // **The seam gate.** The carriers agree and the first flow's
                // target meets the second's source; a feedback seam is a
                // cycle and is refused by name.
                Frame::ThenSecond { then, first } => {
                    let second_type = produced.value_type()?;
                    let Value::Then {
                        first: earlier,
                        second,
                        seam,
                    } = *read_value(arena, then)?
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let composite = crate::flow_universe::compose(
                        arena,
                        judgement.presentations,
                        (first, second_type),
                        seam,
                        (earlier, second),
                    )
                    .map_err(KernelError::Flow)?;
                    produced = Produced::ValueType(composite);
                },
                // A ride forms its motive over the flow's carrier, passes the
                // covariance gate, checks its value at the motive's source
                // instance and returns at its target instance.
                Frame::Ride(ride) => {
                    let flow_type = produced.value_type()?;
                    let Some(&Computation::Ride { motive, value, .. }) = arena.computation(ride)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let ends =
                        crate::flow_universe::ends(arena, flow_type).map_err(KernelError::Flow)?;
                    let mut scoped = context.clone();
                    scoped.push(ends.carrier);
                    let _level = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Value(motive),
                        scoped,
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    )?;
                    crate::flow_universe::check_motive(
                        arena,
                        motive,
                        gandr_kernel_term::DeBruijnIndex::from(0_u32),
                        crate::replay::ReplayBudget::DEFAULT,
                    )
                    .map_err(KernelError::Flow)?;
                    let (table, rewrites) = session.rewrite_parts();
                    let source = substitute_value_type(arena, table, rewrites, motive, ends.source);
                    let target = substitute_value_type(arena, table, rewrites, motive, ends.target);
                    frames.push(Frame::ProduceComp(arena.comp_type_returner(target)));
                    goal = Goal::CheckValue(value, source);
                    continue 'expand;
                },
                // A telescope ride forms its motive, reads the flow's carrier
                // as the motive's first entry, passes the gate in both entries,
                // and checks the start in the family's fibre over the flow's
                // source.
                Frame::TelescopeRideFlow(ride) => {
                    let flow_type = produced.value_type()?;
                    let Some(&Computation::TelescopeRide { motive, start, .. }) =
                        arena.computation(ride)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let Maybe::Present(crate::element_identity::Telescope {
                        carrier,
                        family,
                        body,
                    }) = crate::element_identity::telescope(arena, motive)?
                    else {
                        return Err(comp_shape_mismatch(
                            arena,
                            ExpectedComputationShape::Telescope,
                            motive,
                        ));
                    };
                    let _level = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Comp(motive),
                        context.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    )?;
                    let ends =
                        crate::flow_universe::ends(arena, flow_type).map_err(KernelError::Flow)?;
                    if let Err(mismatch) = former::assignable(arena, carrier, ends.carrier) {
                        let reading = read_returned(
                            arena,
                            judgement,
                            ConversionGoal::ValueType(carrier, ends.carrier),
                        )?;
                        if reading != EndpointReading::Converts {
                            return Err(mismatch);
                        }
                    }
                    for (entry, binder) in [(family, 0_u32), (body, 0_u32), (body, 1_u32)] {
                        crate::flow_universe::check_motive(
                            arena,
                            entry,
                            gandr_kernel_term::DeBruijnIndex::from(binder),
                            crate::replay::ReplayBudget::DEFAULT,
                        )
                        .map_err(KernelError::Flow)?;
                    }
                    let (table, rewrites) = session.rewrite_parts();
                    let source_fibre =
                        substitute_value_type(arena, table, rewrites, family, ends.source);
                    frames.push(Frame::TelescopeRideStart {
                        ride,
                        ends: (ends.source, ends.target),
                    });
                    goal = Goal::CheckValue(start, source_fibre);
                    continue 'expand;
                },
                Frame::TelescopeRideStart { ride, ends } => {
                    let Some(&Computation::TelescopeRide { over, .. }) = arena.computation(ride)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    frames.push(Frame::TelescopeRideOver { ride, ends });
                    goal = Goal::SynthValue(over);
                    continue 'expand;
                },
                // **The dependency is respected or refused by name.** The
                // second flow lies over the first: it runs, in the fibre at
                // the flow's target, from the start ridden along the flow to
                // some element. The value then checks at the body instantiated
                // at the source pair and returns at the target pair.
                Frame::TelescopeRideOver {
                    ride,
                    ends: (left, right),
                } => {
                    let over_type = produced.value_type()?;
                    let Some(&Computation::TelescopeRide {
                        motive,
                        flow,
                        start,
                        value,
                        ..
                    }) = arena.computation(ride)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let Maybe::Present(crate::element_identity::Telescope { family, body, .. }) =
                        crate::element_identity::telescope(arena, motive)?
                    else {
                        return Err(comp_shape_mismatch(
                            arena,
                            ExpectedComputationShape::Telescope,
                            motive,
                        ));
                    };
                    let finish = crate::flow_universe::ends(arena, over_type)
                        .map_err(KernelError::Flow)?
                        .target;
                    let (table, rewrites) = session.rewrite_parts();
                    let target_fibre = substitute_value_type(arena, table, rewrites, family, right);
                    let carried = arena.computation_ride(family, flow, start);
                    let carried = arena.value_returned(carried);
                    let lies_over = arena.value_type_flow(target_fibre, carried, finish);
                    if former::assignable(arena, lies_over, over_type).is_err() {
                        let reading = read_returned(
                            arena,
                            judgement,
                            ConversionGoal::ValueType(lies_over, over_type),
                        )?;
                        if reading != EndpointReading::Converts {
                            return Err(KernelError::Identity(
                                crate::element_identity::IdentityError::NotOver {
                                    expected: value_type_witness(arena, lies_over),
                                    actual: value_type_witness(arena, over_type),
                                },
                            ));
                        }
                    }
                    let (table, rewrites) = session.rewrite_parts();
                    let source = crate::element_identity::telescope_instance(
                        arena,
                        table,
                        rewrites,
                        body,
                        (left, start),
                    );
                    let target = crate::element_identity::telescope_instance(
                        arena,
                        table,
                        rewrites,
                        body,
                        (right, finish),
                    );
                    frames.push(Frame::ProduceComp(arena.comp_type_returner(target)));
                    goal = Goal::CheckValue(value, source);
                    continue 'expand;
                },
                // A related application reads its function identity's domain
                // as a pure arrow, checks both arguments and their evidence,
                // then synthesizes its body under both results and their
                // identity.
                Frame::RelatedPath(application) => {
                    let path_type = produced.value_type()?;
                    let Some(&Computation::RelatedApplication {
                        left,
                        right,
                        evidence,
                        body,
                        ..
                    }) = arena.computation(application)
                    else {
                        return Err(KernelError::ArenaFault);
                    };
                    let (functions, ..) = crate::element_identity::path_parts(arena, path_type)?;
                    let Some(&ValueType::Thunk(arrow)) = arena.value_type(functions)
                    else {
                        return Err(value_shape_mismatch(
                            arena,
                            ExpectedValueShape::Thunk,
                            functions,
                        ));
                    };
                    let (argument, result) = match arena.comp_type(arrow) {
                        Some(&CompType::Arrow { domain, codomain }) => {
                            match arena.comp_type(codomain) {
                                Some(&CompType::Returner(result)) => (domain, result),
                                _ => {
                                    return Err(comp_shape_mismatch(
                                        arena,
                                        ExpectedComputationShape::Returner,
                                        codomain,
                                    ));
                                },
                            }
                        },
                        _ => {
                            return Err(comp_shape_mismatch(
                                arena,
                                ExpectedComputationShape::Arrow,
                                arrow,
                            ));
                        },
                    };
                    let premise = arena.value_type_path(argument, left, right);
                    let (table, rewrites) = session.rewrite_parts();
                    let once = shift_value_type(
                        arena,
                        table,
                        rewrites,
                        result,
                        BinderDepth::NONE,
                        BinderDepth::from(1_u32),
                    );
                    let twice = shift_value_type(
                        arena,
                        table,
                        rewrites,
                        result,
                        BinderDepth::NONE,
                        BinderDepth::from(2_u32),
                    );
                    let source_result = arena.value_variable(DeBruijnIndex::from(1_u32));
                    let target_result = arena.value_variable(DeBruijnIndex::from(0_u32));
                    let related = arena.value_type_path(twice, source_result, target_result);
                    frames.push(Frame::RelatedBody {
                        body,
                        binders: [result, once, related],
                    });
                    frames.push(Frame::Pending(
                        Vec::from([
                            Goal::CheckValue(evidence, premise),
                            Goal::CheckValue(right, argument),
                        ]),
                        Produced::Checked,
                    ));
                    goal = Goal::CheckValue(left, argument);
                    continue 'expand;
                },
                Frame::RelatedBody { body, binders } => {
                    for binder in binders {
                        context.push(binder);
                        frames.push(Frame::Strengthen);
                        frames.push(Frame::ScopeExit);
                    }
                    goal = Goal::SynthComp(body);
                    continue 'expand;
                },
                Frame::SynthTuple {
                    mut remaining,
                    mut types,
                } => {
                    types.push(produced.value_type()?);
                    if let Some(next) = remaining.pop() {
                        frames.push(Frame::SynthTuple { remaining, types });
                        goal = Goal::SynthValue(next);
                        continue 'expand;
                    }
                    produced = Produced::ValueType(arena.value_type_product(&types));
                },
                Frame::SynthThunk => {
                    let body_type = produced.comp_type()?;
                    produced = Produced::ValueType(arena.value_type_thunk(body_type));
                },
                Frame::SynthLift(target) => {
                    let body_type = produced.value_type()?;
                    let body_level = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Value(body_type),
                        context.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed,
                        },
                    )?;
                    judgement.levels.check_level_scope(&target)?;
                    judgement
                        .levels
                        .check_universe_below(&body_level, &target)?;
                    produced = Produced::ValueType(arena.value_type_lift(body_type, target));
                },
                Frame::CheckPairSecond(second, second_type) => {
                    goal = Goal::CheckValue(second, second_type);
                    continue 'expand;
                },
                // At the level-zero universe `Flow(U₀, x, y)` and `Flow_U(x,
                // y)` are two readings of one classifier: a flow synthesizing
                // either checks at the other.
                Frame::ConvertValue(expected) => {
                    let synthesized = produced.value_type()?;
                    let (expected, synthesized) =
                        recursion::unstage(arena, &stages, expected, synthesized)?;
                    // A stage below the top — a function field's, under its
                    // thunk — is decided by the order once conversion alone
                    // separates the two.
                    if let Err(mismatch) = former::assignable(arena, expected, synthesized)
                        && let Err(unsubsumed) = recursion::subsumes(
                            arena,
                            &stages,
                            recursion::Subsumed::Values(expected, synthesized),
                        )
                    {
                        if let KernelError::StageNotBelow { found, bound } = unsubsumed {
                            return Err(KernelError::StageNotBelow { found, bound });
                        }
                        let reading = read_returned(
                            arena,
                            judgement,
                            ConversionGoal::ValueType(expected, synthesized),
                        )?;
                        if reading != EndpointReading::Converts
                            && crate::flow_universe::agree(
                                arena,
                                judgement.presentations,
                                synthesized,
                                expected,
                            ) == crate::flow_universe::Agreement::Differ
                        {
                            return Err(mismatch);
                        }
                    }
                    produced = Produced::Checked;
                },
                Frame::FixpointArgument(head, expected) => {
                    let domain = produced.value_type()?;
                    let arrow = arena.comp_type_arrow(domain, expected);
                    goal = Goal::CheckComp(head, arrow);
                    continue 'expand;
                },
                Frame::SynthApply(argument) => {
                    let head_type = produced.comp_type()?;
                    let head_shape = codata::read(arena, session, judgement, head_type)?;
                    match arena.comp_type(head_shape) {
                        // An application eliminates either arrow: check the
                        // argument against the domain and produce the codomain.
                        Some(&CompType::Arrow { domain, codomain }) => {
                            frames.push(Frame::ProduceComp(codomain));
                            goal = Goal::CheckValue(argument, domain);
                            continue 'expand;
                        },
                        // **The dependent arm instantiates the codomain at the
                        // argument**, which is the whole difference between the
                        // two eliminations: a codomain that mentions its binder
                        // through a code names the argument after this step, and
                        // a codomain that mentions nothing is handed back
                        // unchanged at no cost. A plain code a later argument of
                        // the spine holds at a stage instantiates at that staged
                        // code, re-derived as the checker read it. A returned
                        // call instantiates as the lowering writes a call a type
                        // decodes: bound ahead of each decode's returned code
                        // that reads the binder (#720), the form a type written
                        // with the call holds.
                        Some(&CompType::Pi { domain, codomain }) => {
                            let spine = frames.iter().rev().map_while(|frame| {
                                if let Frame::SynthApply(later) = *frame {
                                    Some(later)
                                }
                                else {
                                    None
                                }
                            });
                            let instance = match recursion::instantiation(
                                arena,
                                (session, context.as_slice()),
                                (argument, codomain),
                                spine,
                            ) {
                                Maybe::Present(staged) => staged,
                                Maybe::Absent(recursion::Unstaged::Plain) => argument,
                            };
                            let (table, rewrites) = session.rewrite_parts();
                            let instantiated = match arena.value(instance) {
                                Some(&Value::Returned(call)) if instance == argument => {
                                    substitute_comp_type_at_call(
                                        arena,
                                        table,
                                        rewrites,
                                        codomain,
                                        (instance, call),
                                    )
                                },
                                _ => {
                                    substitute_comp_type(arena, table, rewrites, codomain, instance)
                                },
                            };
                            frames.push(Frame::ProduceComp(instantiated));
                            goal = Goal::CheckValue(argument, domain);
                            continue 'expand;
                        },
                        _ => {
                            return Err(comp_shape_mismatch(
                                arena,
                                ExpectedComputationShape::Arrow,
                                head_type,
                            ));
                        },
                    }
                },
                Frame::ProduceComp(codomain) => {
                    produced = Produced::CompType(codomain);
                },
                Frame::Restage(staged) => {
                    let read = produced.comp_type()?;
                    produced = Produced::CompType(recursion::restaged(arena, read, staged));
                },
                Frame::SynthStaticApply(argument) => {
                    let head_type = produced.value_type()?;
                    match arena.value_type(head_type) {
                        // The static Pi binds nothing, so its codomain is the
                        // application's type as it stands.
                        Some(&ValueType::StaticPi { domain, codomain }) => {
                            frames.push(Frame::ProduceValue(codomain));
                            goal = Goal::CheckValue(argument, domain);
                            continue 'expand;
                        },
                        _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::StaticPi,
                                head_type,
                            ));
                        },
                    }
                },
                Frame::SessionPayload {
                    classifier,
                    context: outer,
                } => {
                    context = outer;
                    produced = Produced::ValueType(classifier);
                },
                Frame::ProduceValue(codomain) => {
                    produced = Produced::ValueType(codomain);
                },
                Frame::SynthForce => {
                    let value_type = produced.value_type()?;
                    match arena.value_type(value_type) {
                        Some(&ValueType::Thunk(codomain)) => {
                            produced = Produced::CompType(codomain);
                        },
                        _ => {
                            return Err(value_shape_mismatch(
                                arena,
                                ExpectedValueShape::Thunk,
                                value_type,
                            ));
                        },
                    }
                },
                Frame::SynthReturn => {
                    let result_type = produced.value_type()?;
                    produced = Produced::CompType(arena.comp_type_returner(result_type));
                },
                Frame::SynthWith {
                    mut remaining,
                    mut types,
                } => {
                    types.push(produced.comp_type()?);
                    if let Some(next) = remaining.pop() {
                        frames.push(Frame::SynthWith { remaining, types });
                        goal = Goal::SynthComp(next);
                        continue 'expand;
                    }
                    produced = Produced::CompType(arena.comp_type_with(&types));
                },
                // A projection reads its component off the pairing's
                // synthesized lazy product, a codata type read through its
                // observations; any other classifier is refused by name, and
                // so is a position past the lazy product's last.
                Frame::Project(component) => {
                    let pair_type = produced.comp_type()?;
                    let pair_shape = codata::read(arena, session, judgement, pair_type)?;
                    let Some(&CompType::With(ref parts)) = arena.comp_type(pair_shape)
                    else {
                        return Err(comp_shape_mismatch(
                            arena,
                            ExpectedComputationShape::With,
                            pair_type,
                        ));
                    };
                    let part = *parts
                        .get(usize::from(component))
                        .ok_or(KernelError::AbsentTupleComponent { component })?;
                    produced = Produced::CompType(part);
                },
                // A bind reads its bound's returner, a codata type read through
                // its observations; any other classifier is refused by name.
                Frame::SynthBind(body) => {
                    let bound_type = produced.comp_type()?;
                    let bound_shape = codata::read(arena, session, judgement, bound_type)?;
                    match arena.comp_type(bound_shape) {
                        Some(&CompType::Returner(result)) => {
                            context.push(result);
                            frames.push(Frame::Strengthen);
                            frames.push(Frame::ScopeExit);
                            goal = Goal::SynthComp(body);
                            continue 'expand;
                        },
                        _ => {
                            return Err(comp_shape_mismatch(
                                arena,
                                ExpectedComputationShape::Returner,
                                bound_type,
                            ));
                        },
                    }
                },
                Frame::SynthCaseScrutinee(branches) => {
                    let scrutinee_type = produced.value_type()?;
                    let mut remaining = case_branches(arena, scrutinee_type, &branches)?;
                    let Some((branch, summand)) = remaining.pop()
                    else {
                        return Err(KernelError::NotInferable {
                            form: NonInferableForm::EmptyCase,
                        });
                    };
                    context.push(summand);
                    frames.push(Frame::SynthCaseBranch {
                        remaining,
                        first: None,
                    });
                    frames.push(Frame::ScopeExit);
                    goal = Goal::SynthComp(branch);
                    continue 'expand;
                },
                // Every branch's type, strengthened out of its binder, must
                // convert to the first branch's, which the case then has.
                Frame::SynthCaseBranch {
                    mut remaining,
                    first,
                } => {
                    let branch_type =
                        strengthened(arena, session, &context, produced.comp_type()?)?;
                    let first_type = match first {
                        None => branch_type,
                        Some(first_type) => {
                            match convertible_comp_types(arena, first_type, branch_type) {
                                Convertibility::Convertible => first_type,
                                Convertibility::Distinct => {
                                    return Err(case_branch_mismatch(
                                        arena,
                                        first_type,
                                        branch_type,
                                    ));
                                },
                            }
                        },
                    };
                    if let Some((branch, summand)) = remaining.pop() {
                        context.push(summand);
                        frames.push(Frame::SynthCaseBranch {
                            remaining,
                            first: Some(first_type),
                        });
                        frames.push(Frame::ScopeExit);
                        goal = Goal::SynthComp(branch);
                        continue 'expand;
                    }
                    produced = Produced::CompType(first_type);
                },
                Frame::ConvertComp(expected) => {
                    let synthesized = produced.comp_type()?;
                    if let Err(mismatch) = convert_comp_type(arena, expected, synthesized)
                        && let Err(unsubsumed) = recursion::subsumes(
                            arena,
                            &stages,
                            recursion::Subsumed::Comps(expected, synthesized),
                        )
                    {
                        if let KernelError::StageNotBelow { found, bound } = unsubsumed {
                            return Err(KernelError::StageNotBelow { found, bound });
                        }
                        let reading = read_returned(
                            arena,
                            judgement,
                            ConversionGoal::CompType(expected, synthesized),
                        )?;
                        if reading != EndpointReading::Converts {
                            return Err(mismatch);
                        }
                    }
                    produced = Produced::Checked;
                },
                Frame::CheckBind(body, expected) => {
                    let bound_type = produced.comp_type()?;
                    let bound_shape = codata::read(arena, session, judgement, bound_type)?;
                    match arena.comp_type(bound_shape) {
                        Some(&CompType::Returner(result)) => {
                            let scoped = weakened(arena, session, expected);
                            context.push(result);
                            frames.push(Frame::ScopeExit);
                            goal = Goal::CheckComp(body, scoped);
                            continue 'expand;
                        },
                        _ => {
                            return Err(comp_shape_mismatch(
                                arena,
                                ExpectedComputationShape::Returner,
                                bound_type,
                            ));
                        },
                    }
                },
                // Each branch checks, under its summand's binder, against the
                // expected type read from under that binder. A case of no
                // branches over the empty sum checks at once.
                Frame::CheckCaseScrutinee { branches, expected } => {
                    let scrutinee_type = produced.value_type()?;
                    let remaining = case_branches(arena, scrutinee_type, &branches)?;
                    let scoped = weakened(arena, session, expected);
                    frames.push(Frame::CheckCaseBranch {
                        remaining,
                        expected: scoped,
                    });
                    produced = Produced::Checked;
                },
                Frame::CheckCaseBranch {
                    mut remaining,
                    expected,
                } => {
                    if let Some((branch, summand)) = remaining.pop() {
                        context.push(summand);
                        frames.push(Frame::CheckCaseBranch {
                            remaining,
                            expected,
                        });
                        frames.push(Frame::ScopeExit);
                        goal = Goal::CheckComp(branch, expected);
                        continue 'expand;
                    }
                    produced = Produced::Checked;
                },
                Frame::ScopeExit => {
                    let _popped = context.pop();
                    if let Maybe::Present((slot, _)) = own_fixpoint
                        && slot >= context.len()
                    {
                        own_fixpoint = Maybe::Absent(recursion::Unowned::Outside);
                    }
                },
                Frame::StageExit => staged_bodies = staged_bodies.saturating_sub(1),
                Frame::Strengthen => {
                    let synthesized = produced.comp_type()?;
                    produced =
                        Produced::CompType(strengthened(arena, session, &context, synthesized)?);
                },
            }
        }
    }
}

/// Check a declaration's sealing provenance against its declared type.
///
/// The slot claims which atoms a sealing projection rebound; this re-derives
/// that claim rather than accepting it. Two obligations, and both are about
/// making the slot **falsifiable**: every claimed atom occurs in the declared
/// type, so the recorded extent of the projection is observable in what the
/// projection produced; and the entries are strictly ascending, so the slot is
/// a set with one spelling and a repeat cannot inflate an extent.
///
/// What is deliberately *not* checked: that sealing happened, that a signature
/// was matched, or that the producer did anything in particular. Those are
/// claims about a history the kernel did not witness and cannot re-derive.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok(())` exactly when the provenance is strictly ascending and
///   every entry occurs as a sealed atom reachable from the declared type.
/// - provides: the choke point's sealing-provenance gate.
/// - fails: [`KernelError::SealingProvenanceNotCanonical`],
///   [`KernelError::SealingProvenanceNotProjected`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L2 — a sealed member whose provenance matches its type admits;
///   the L3 residues are the two refusal arms, each pinned by a negative
///   witness naming the exact offending atom.
/// - witness: `check::tests::sealing_provenance_must_occur_in_the_declared_type`
/// - witness: `check::tests::sealing_provenance_must_be_strictly_ascending`
// The predicate covers the ascending half, stated as a sortedness test rather
// than through the body's own previous-index loop. The occurrence half would
// mean re-deriving the projected-atom set, doubling a walk over the declared
// type at the choke point, so it stays with the witnesses.
#[spec(ensures: |ret| ret.is_err()
    || provenance.is_sorted_by(|left, right| usize::from(*left) < usize::from(*right)))]
fn check_sealing_provenance(
    arena: &TermArena,
    declared: ValueTypeId,
    provenance: &[ConstantIndex],
) -> Result<(), KernelError>
{
    if provenance.is_empty() {
        return Ok(());
    }
    let mut previous: Option<ConstantIndex> = None;
    for &atom in provenance {
        if let Some(last) = previous
            && usize::from(atom) <= usize::from(last)
        {
            return Err(KernelError::SealingProvenanceNotCanonical { atom });
        }
        previous = Some(atom);
    }
    let projected = projected_atoms(arena, declared);
    for &atom in provenance {
        if !projected.contains(&atom) {
            return Err(KernelError::SealingProvenanceNotProjected { atom });
        }
    }
    Ok(())
}

/// Check a declaration through the default path: a fresh live memo, built here
/// and dropped here.
///
/// This is the entry the admission choke point calls, and it takes **no memo
/// parameter** — which is the structural form of the lifetime rule. A caller
/// cannot hand admission a memo, so nothing an earlier call recorded can reach
/// a later one through the checked entry.
///
/// # Specification
/// - requires: `declaration`'s content roots were minted into `arena`;
///   `judgement` pairs the environment's admission log with the declaration's
///   level context and the ascending positions of the abstract types whose
///   minting admission is open, outside any block.
/// - ensures: the occurrence walk's accessibility for a data declaration, and
///   the reading of none for any other, when the declared type forms, sealing
///   provenance re-derives, a definition's body checks — at its declared type
///   with every manifest atom read as its representation, as is every constant
///   it names — and every deferred code checks within the operational ceiling.
///   An axiom checks only its type; a sealed atom checks that its kind is a
///   universe and that its representation forms below that kind's successor.
///   The original arena prefix remains, and successful content roots are
///   readable. Synthesized intermediates are appended for the caller to
///   truncate.
/// - provides: the body check the choke point runs, with a fresh live memo on
///   both machines. Full typing and admission-log provenance still require the
///   rule derivation; an operational refusal does not establish ill-typedness.
/// - fails: any [`KernelError`] the checker surfaces.
/// - panics: none.
///
/// # Errors
/// Any [`KernelError`].
///
/// # Adequacy
/// - hypothesis: L2/L3 — the selected definitions, axiom and sealed atom
///   separate the three content arms; a bad code refuses. At the finite
///   occurrence boundary, a live memo accepts the shared valid declaration that
///   the null memo refuses operationally. A member inside its atom's minting
///   admission checks at the representation and the same value outside it is
///   refused.
/// - witness: `check::tests::an_identity_thunk_checks`
/// - witness: `check::tests::a_dependent_identity_checks_through_its_codes`
/// - witness: `check::tests::a_code_that_is_not_of_its_declared_universe_refuses`
/// - witness: `check::tests::an_axiom_checks_only_its_type`
/// - witness: `check::tests::a_sealed_atom_checks_only_its_kind`
/// - witness: `check::tests::obligation_ceiling_can_separate_memoized_and_memoless_checks`
/// - witness: `env::tests::a_value_of_the_representation_does_not_inhabit_the_atom`
#[spec(captures: entry_mark = arena.watermark(), ensures: |ret|
    entry_mark.clamped_into(gandr_kernel_term::ArenaWatermark::default(), arena.watermark()) == entry_mark
        && (ret.is_err() || (arena.value_type(declaration.declared_id()).is_some()
            && match *declaration.content() {
                DeclarationContent::Def { body, .. } => arena.value(body).is_some(),
                DeclarationContent::Data { .. } | DeclarationContent::Codata { .. } | DeclarationContent::Axiom { .. } | DeclarationContent::AbstractType { .. } => true,
            })))]
#[inline]
pub fn check_declaration(
    arena: &mut TermArena,
    judgement: Judgement<'_>,
    declaration: &Declaration,
) -> Result<occurrence::Accessibility, KernelError>
{
    let mut memo: DefaultMemo = DefaultMemo::new();
    let mut session = SupportContext::new();
    let mut census = ExpansionCensus::new();
    check_declaration_with_memo(
        arena,
        judgement,
        declaration,
        &mut memo,
        &mut session,
        &mut census,
    )
}

/// Form a mutual block definition's declared type before its block's
/// families are admitted: the first step of the block's schedule.
///
/// # Specification
/// - requires: `judgement` holds the block's families in scope and none of its
///   definitions; `declared` was minted into `arena`.
/// - ensures: `Ok(())` when the type forms and every code it owes checks, as a
///   lone declaration's declared type does; intermediates are appended for the
///   caller to truncate.
/// - provides: the foresight a family's fields rest on when they name the
///   definition at this type.
/// - fails: any [`KernelError`] the formation surfaces.
/// - panics: none.
///
/// # Errors
/// Any [`KernelError`].
///
/// # Adequacy
/// - hypothesis: L3 — a decoder's type over its universe forms in the block.
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
#[spec(captures: entry_mark = arena.watermark(), ensures:
    entry_mark.clamped_into(gandr_kernel_term::ArenaWatermark::default(), arena.watermark()) == entry_mark)]
pub(crate) fn form_declared(
    arena: &mut TermArena,
    judgement: Judgement<'_>,
    declared: ValueTypeId,
) -> Result<(), KernelError>
{
    let mut memo: DefaultMemo = DefaultMemo::new();
    let mut session = SupportContext::new();
    let mut census = ExpansionCensus::new();
    let presentations = crate::presented::Presentations::of(judgement.entries);
    let judgement = judgement.presenting(&presentations);
    // As a lone declaration's, the declared type forms through the seal rule.
    let unsealed = seal::unseal(arena, judgement.entries, judgement.manifest, declared)?;
    let mut owed: Vec<CodeObligation> = Vec::new();
    let _level = type_level(
        arena,
        judgement,
        TypeLevelGoal::Value(unsealed),
        Vec::new(),
        Recording {
            memo: &mut memo,
            session: &mut session,
            census: &mut census,
            owed: &mut owed,
        },
    )?;
    drain_code_obligations(arena, judgement, &mut memo, &mut session, &mut census, owed)
}

/// Check a declaration against a caller-supplied memo — the **opt-in** entry.
///
/// # This entry admits nothing, and that is the seam
///
/// It returns a verdict and never a checked id, so a caller reaching it cannot
/// get a declaration into an environment. Admission goes through
/// [`check_declaration`], which builds its own memo; there is no admitting
/// entry that accepts one. So the memo's lifetime being a single call is a
/// property of the surface rather than a discipline a caller has to remember.
///
/// # Why the memo lives for one call
///
/// The key is content and carries no arena id, so dangling ids are not the
/// reason. The rule rests on the two-wall discipline directly: **a hit claims
/// only its own history, and no kernel-checked support discipline exists**, so
/// nothing here persists.
///
/// An *outcome* also carries arena ids even though the key does not, so an
/// entry outliving its arena would hand back a synthesized type that no longer
/// resolves.
///
/// # Specification
/// - requires: as [`check_declaration`]; additionally, `memo` holds only
///   entries recorded during this same call against this same arena.
/// - ensures: the typing verdict agrees with [`check_declaration`] and the null
///   memo when neither execution reaches
///   [`KernelError::CodeObligationCeiling`]. A live memo can avoid repeated
///   obligations that exhaust the null memo's occurrence budget. Each counter
///   is monotone, and the initial formation goal charges at least one
///   type-plane event, subject to saturation, unless a data declaration's
///   occurrence walk refuses it before formation starts. The arena's original
///   prefix remains available on either verdict.
/// - provides: both memo policies through one function. Per-goal accounting,
///   memo provenance and typing agreement still require their event history or
///   differential witnesses, not a second check inside a return predicate.
/// - fails: any [`KernelError`] the checker surfaces.
/// - panics: none.
///
/// # Errors
/// Any [`KernelError`].
///
/// # Adequacy
/// - hypothesis: L2/L3 — the finite differential corpus agrees below the
///   operational ceiling. The boundary fixture separates resource refusal from
///   typing, and poisoned histories change answers on both planes,
///   demonstrating why the per-call history requirement is part of the
///   contract.
/// - witness: `tests::acceptance::memoized_checking_agrees_with_memoless_checking`
/// - witness: `tests::acceptance::a_poisoned_term_entry_turns_a_refusal_into_an_acceptance`
/// - witness: `tests::acceptance::a_poisoned_type_entry_turns_admission_into_a_universe_refusal`
/// - witness: `check::tests::obligation_ceiling_can_separate_memoized_and_memoless_checks`
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
#[spec(captures: [entry_mark = arena.watermark(),
    entry_term_expanded = u64::from(census.plane_expansions(SupportPlane::Term)),
    entry_term_recalled = u64::from(census.plane_recalls(SupportPlane::Term)),
    entry_type_expanded = u64::from(census.plane_expansions(SupportPlane::Type)),
    entry_type_recalled = u64::from(census.plane_recalls(SupportPlane::Type))],
    ensures: |ret| entry_mark.clamped_into(gandr_kernel_term::ArenaWatermark::default(), arena.watermark()) == entry_mark && {
        let term_expanded = u64::from(census.plane_expansions(SupportPlane::Term));
        let term_recalled = u64::from(census.plane_recalls(SupportPlane::Term));
        let type_expanded = u64::from(census.plane_expansions(SupportPlane::Type));
        let type_recalled = u64::from(census.plane_recalls(SupportPlane::Type));
        term_expanded >= entry_term_expanded
            && term_recalled >= entry_term_recalled
            && type_expanded >= entry_type_expanded
            && type_recalled >= entry_type_recalled
            && (matches!(ret, Err(KernelError::CrossBlockReference { .. }
                    | KernelError::NegativeOccurrence(_)
                    | KernelError::IndexOccurrence(_)
                    | KernelError::NestedOccurrence(_)
                    | KernelError::NonUniformOccurrence(_)))
                || type_expanded.saturating_add(type_recalled)
                    >= entry_type_expanded.saturating_add(entry_type_recalled).saturating_add(1_u64))
    })]
#[inline]
pub fn check_declaration_with_memo<M>(
    arena: &mut TermArena,
    judgement: Judgement<'_>,
    declaration: &Declaration,
    memo: &mut M,
    session: &mut SupportContext,
    census: &mut ExpansionCensus,
) -> Result<occurrence::Accessibility, KernelError>
where
    M: CheckMemo<NodeSupport, NodeOutcome>,
{
    let declared = declaration.declared_id();
    // A relating definition's conversions read the pairs it relates, a lawful
    // one's folds rest on its laws, and every conversion rewrites the
    // presented types admitted before it.
    let presentations = crate::presented::Presentations::of(judgement.entries);
    let judgement = judgement
        .relating(declaration.related())
        .lawful(declaration.laws())
        .presenting(&presentations);
    // A data declaration's own position names its block while it is checked:
    // the occurrence walk refuses every occurrence of a family of the block
    // the stage order cannot place below its constructor, by name, first,
    // reading a definition of the block through its body and a family
    // admitted before through its parameters' variance, and formation then
    // reads it through the block's signatures. Alone, the block is the
    // declaration's own; in a mutual block, the block in scope already holds
    // it.
    let (judgement, accessibility) = match *declaration.content() {
        DeclarationContent::Data {
            kind,
            ref parameters,
            ref indices,
            ref constructors,
            ref results,
        } => match judgement.block {
            Block::Mutual { block, members } => {
                let first = usize::from(block.first());
                let definitions = members
                    .iter()
                    .enumerate()
                    .filter_map(|(offset, member)| match *member.content() {
                        DeclarationContent::Def { body, .. } => {
                            Some((ConstantIndex::from(first.saturating_add(offset)), body))
                        },
                        DeclarationContent::Data { .. }
                        | DeclarationContent::Codata { .. }
                        | DeclarationContent::Axiom { .. }
                        | DeclarationContent::AbstractType { .. } => None,
                    })
                    .collect::<Vec<_>>();
                let accessibility = occurrence::occurrences(
                    arena,
                    (block, &definitions, judgement.entries),
                    parameters,
                    constructors,
                )?;
                (judgement, accessibility)
            },
            Block::Outside | Block::Inside { .. } | Block::Codata { .. } => {
                let position = ConstantIndex::from(judgement.entries.len());
                let accessibility = occurrence::occurrences(
                    arena,
                    (occurrence::Block::lone(position), &[], judgement.entries),
                    parameters,
                    constructors,
                )?;
                (
                    judgement.within_block(position, former::Signature {
                        parameters,
                        indices,
                        constructors,
                        results,
                        kind,
                    }),
                    accessibility,
                )
            },
        },
        // A codata declaration's own position names it while its observations
        // form; `codata::guarded` keeps every such name at an observation's
        // result.
        DeclarationContent::Codata {
            kind,
            ref parameters,
            ref observations,
        } => {
            let position = ConstantIndex::from(judgement.entries.len());
            (
                judgement.within_codata(position, codata::Signature {
                    parameters,
                    observations,
                    kind,
                }),
                occurrence::Accessibility::unwalked(),
            )
        },
        DeclarationContent::Def { .. }
        | DeclarationContent::Axiom { .. }
        | DeclarationContent::AbstractType { .. } => {
            (judgement, occurrence::Accessibility::unwalked())
        },
    };
    // The seal rule: inside the admission that minted an atom, a declaration
    // is checked at its representation — its declared type forms there, as
    // every constant it calls is read, and a definition's body is checked at
    // it. The declaration keeps its declared type, so a member is exported at
    // the atom.
    let unsealed = seal::unseal(arena, judgement.entries, judgement.manifest, declared)?;
    let mut owed: Vec<CodeObligation> = Vec::new();
    let _level = type_level(
        arena,
        judgement,
        TypeLevelGoal::Value(unsealed),
        Vec::new(),
        Recording {
            memo,
            session,
            census,
            owed: &mut owed,
        },
    )?;
    check_sealing_provenance(arena, declared, declaration.provenance())?;
    let mut following = Maybe::Absent(recursion::Unstaged::Plain);
    let verdict: Result<(), KernelError> = match *declaration.content() {
        DeclarationContent::Data {
            kind,
            ref parameters,
            ref indices,
            ref constructors,
            ref results,
        } => {
            // An indexed family states one result index per index for each
            // constructor, and presents no rules.
            let stated = results.len() == constructors.len()
                && results.iter().all(|result| result.len() == indices.len());
            let presented = !declaration.presentation().rules().is_empty()
                || declaration.presentation().cells().is_some();
            if !indices.is_empty() && (!stated || presented) {
                return Err(KernelError::IndexedSignature);
            }
            if indices.is_empty() && !results.is_empty() {
                return Err(KernelError::IndexedSignature);
            }
            let level = former::level(arena, kind)?;
            let upper = level.succ()?;
            let mut context = Vec::new();
            for parameter in parameters {
                let _formed = type_level(
                    arena,
                    judgement,
                    TypeLevelGoal::Value(*parameter),
                    context.clone(),
                    Recording {
                        memo,
                        session,
                        census,
                        owed: &mut owed,
                    },
                )?;
                context.push(*parameter);
            }
            // An index forms under the parameters and the indices before it.
            let mut indexed = context.clone();
            for index in indices {
                let _formed = type_level(
                    arena,
                    judgement,
                    TypeLevelGoal::Value(*index),
                    indexed.clone(),
                    Recording {
                        memo,
                        session,
                        census,
                        owed: &mut owed,
                    },
                )?;
                indexed.push(*index);
            }
            // A field forms under the parameters and the fields before it in
            // its constructor, which a later field's type may name; the
            // constructor's result index checks under all of them. One scope,
            // cut back to the parameters before each constructor.
            let mut scope = context.clone();
            for (tag, fields) in constructors.iter().enumerate() {
                scope.truncate(context.len());
                for field in fields {
                    let formed = type_level(
                        arena,
                        judgement,
                        TypeLevelGoal::Value(*field),
                        scope.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed: &mut owed,
                        },
                    )?;
                    judgement.levels.check_universe_below(&formed, &upper)?;
                    scope.push(*field);
                }
                let stated = results.get(tag).map_or(&[][..], Vec::as_slice);
                for (position, (&value, &index)) in stated.iter().zip(indices).enumerate() {
                    let depth = |count: usize| {
                        u32::try_from(count)
                            .map(BinderDepth::from)
                            .map_err(|_cause| KernelError::ConstructorArity)
                    };
                    let expected = former::index_at(
                        arena,
                        session,
                        index,
                        (stated, depth(position)?),
                        depth(fields.len())?,
                    )?;
                    let _checked = run(
                        arena,
                        judgement,
                        scope.clone(),
                        Goal::CheckValue(value, expected),
                        StageOrder::default(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed: &mut owed,
                        },
                    )?;
                }
            }
            // A presented type's rules are checked against the table its
            // fields just formed: linear, constructor-headed over the own
            // type, and shrinking, so its conversion terminates. A type of
            // words is re-minted from its cells and compared.
            crate::presented::admit(
                arena,
                judgement.entries,
                (
                    ConstantIndex::from(judgement.entries.len()),
                    parameters.as_slice(),
                ),
                constructors,
                declaration.presentation(),
            )?;
            Ok(())
        },
        // A codata declaration's kind is a computation universe, and its
        // observations form under the parameters below that universe's
        // successor, each naming the declaration only at its result.
        DeclarationContent::Codata {
            kind,
            ref parameters,
            ref observations,
        } => {
            let level = codata::level(arena, kind)?;
            let upper = level.succ()?;
            if observations.is_empty() {
                return Err(KernelError::CodataWithoutObservations);
            }
            let position = ConstantIndex::from(judgement.entries.len());
            let mut context = Vec::new();
            for parameter in parameters {
                let _formed = type_level(
                    arena,
                    judgement,
                    TypeLevelGoal::Value(*parameter),
                    context.clone(),
                    Recording {
                        memo,
                        session,
                        census,
                        owed: &mut owed,
                    },
                )?;
                context.push(*parameter);
            }
            let mut search = crate::env::ConstantSearch::new(position);
            for &observation in observations {
                codata::guarded(
                    arena,
                    (position, &mut search),
                    former::FamilyArity(parameters.len()),
                    observation,
                )?;
                let formed = type_level(
                    arena,
                    judgement,
                    TypeLevelGoal::Comp(observation),
                    context.clone(),
                    Recording {
                        memo,
                        session,
                        census,
                        owed: &mut owed,
                    },
                )?;
                judgement.levels.check_universe_below(&formed, &upper)?;
            }
            Ok(())
        },
        DeclarationContent::Def { body, .. } => {
            // The body is checked at the declared type the seal rule read.
            let context: Vec<ValueTypeId> = Vec::new();
            // A block's definition whose body thunks a fixpoint is that
            // fixpoint: inside it, the definition's own constant — which only
            // the block's families name — reads as the self binder.
            let owning = match (judgement.block, arena.value(body)) {
                (Block::Mutual { .. }, Some(&Value::Thunk(root)))
                    if matches!(arena.computation(root), Some(&Computation::Fixpoint { .. })) =>
                {
                    judgement.owning(root)
                },
                (
                    Block::Outside
                    | Block::Inside { .. }
                    | Block::Mutual { .. }
                    | Block::Codata { .. },
                    _,
                ) => judgement,
            };
            let _checked = run(
                arena,
                owning,
                context,
                Goal::CheckValue(body, unsealed),
                StageOrder::default(),
                Recording {
                    memo,
                    session,
                    census,
                    owed: &mut owed,
                },
            )?;
            // A structural definition whose type returns the type it recurses
            // on is checked once more with that result read at the
            // parameter's stage; when that holds, a call reads its result at
            // its argument's stage. The second check recalls nothing the first
            // recorded, which held at the declared result, and what it owes is
            // discharged with it; a refusal leaves the result as declared.
            if let Some(&Value::Thunk(root)) = arena.value(body)
                && let Some(&Computation::Fixpoint { evidence, .. }) = arena.computation(root)
                && let Some(recursed) = match evidence {
                    FixpointEvidence::Partial => None,
                    FixpointEvidence::StructuralDescent => {
                        Some(gandr_kernel_term::StagedPosition::default())
                    },
                    FixpointEvidence::Staged { position } => Some(position),
                }
                && let Some(&ValueType::Thunk(classifier)) = arena.value_type(unsealed)
                && let Maybe::Present(position) =
                    recursion::returns_recursed_on(arena, classifier, recursed)?
            {
                let mut owed_staged: Vec<CodeObligation> = Vec::new();
                let unrecorded = &mut gandr_kernel_check_memo::NullMemo;
                let staged = run(
                    arena,
                    owning.following(root),
                    Vec::new(),
                    Goal::CheckValue(body, unsealed),
                    StageOrder::default(),
                    Recording {
                        memo: unrecorded,
                        session,
                        census,
                        owed: &mut owed_staged,
                    },
                )
                .and_then(|_checked| {
                    drain_code_obligations(
                        arena,
                        judgement,
                        &mut gandr_kernel_check_memo::NullMemo,
                        session,
                        census,
                        owed_staged,
                    )
                });
                if staged.is_ok() {
                    following = Maybe::Present(position);
                }
            }
            // An operation's rules are decided over the declarations admitted
            // before it: well formed, oriented and every critical pair joined,
            // and the body their decision tree.
            crate::ruled::admit(
                arena,
                judgement.entries,
                ConstantIndex::from(judgement.entries.len()),
                (declared, body),
                declaration.operation_rules(),
            )?;
            // A presentation's rules are decided as its value states them.
            crate::theory_rules::admit(arena, judgement.entries, (declared, body))?;
            Ok(())
        },
        DeclarationContent::Axiom { .. } => Ok(()),
        // A sealed atom's admission obligation is that its kind is a universe
        // of value types — the atom is a value type, so a computation universe
        // is no kind for it — and that its representation forms below that
        // universe's successor, the bound a data declaration's fields meet.
        // There is no body to check and no inhabitant claimed. An atom stating
        // an interface owes its relation and its reflexivity, checked here,
        // over the representation the atom reads as inside its seal.
        DeclarationContent::AbstractType {
            kind,
            representation,
            interface,
            ..
        } => {
            let kind_node = arena.value_type(kind).ok_or(KernelError::ArenaFault)?;
            let level = match *kind_node {
                ValueType::Universe {
                    sort: GroundSort::Value,
                    ref level,
                } => level.clone(),
                ValueType::Universe {
                    sort: GroundSort::Computation,
                    ..
                }
                | ValueType::Data { .. }
                | ValueType::Record(_)
                | ValueType::PathUniverse(..)
                | ValueType::FlowUniverse(..)
                | ValueType::Base(_)
                | ValueType::Product(..)
                | ValueType::Sigma { .. }
                | ValueType::Session { .. }
                | ValueType::List(_)
                | ValueType::Sum(..)
                | ValueType::Thunk(_)
                | ValueType::Lift { .. }
                | ValueType::Element { .. }
                | ValueType::Abstract(_)
                | ValueType::Path { .. }
                | ValueType::Flow { .. }
                | ValueType::Bridge { .. }
                | ValueType::StaticPi { .. }
                | ValueType::Staged { .. } => {
                    return Err(KernelError::AbstractTypeKindNotUniverse {
                        actual: value_type_witness(arena, kind),
                    });
                },
            };
            let formed = type_level(
                arena,
                judgement,
                TypeLevelGoal::Value(representation),
                Vec::new(),
                Recording {
                    memo,
                    session,
                    census,
                    owed: &mut owed,
                },
            )?;
            judgement
                .levels
                .check_universe_below(&formed, &level.succ()?)?;
            if let Maybe::Present(interface) = interface {
                let (relations, reflexive) = crate::element_identity::interface_types(
                    arena,
                    (kind, level.clone()),
                    representation,
                    interface.relation(),
                );
                let law = match interface.law() {
                    Maybe::Present(law) => Some((
                        law,
                        crate::element_identity::law_type(
                            arena,
                            &level,
                            representation,
                            (interface.relation(), interface.reflexivity()),
                        ),
                    )),
                    Maybe::Absent(_) => None,
                };
                for (value, expected) in [
                    (interface.relation(), relations),
                    (interface.reflexivity(), reflexive),
                ]
                .into_iter()
                .chain(law)
                {
                    let _checked = run(
                        arena,
                        judgement,
                        Vec::new(),
                        Goal::CheckValue(value, expected),
                        StageOrder::default(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed: &mut owed,
                        },
                    )?;
                }
            }
            Ok(())
        },
    };
    verdict?;
    drain_code_obligations(arena, judgement, memo, session, census, owed)?;
    Ok(match following {
        Maybe::Present(position) => accessibility.following(position),
        Maybe::Absent(_) => accessibility,
    })
}

/// Check every code a formation walk owed, and every code those checks owe in
/// turn.
///
/// # Specification
/// - requires: `owed` holds the obligations the declaration's own walks
///   recorded, each with the context its code stands in.
/// - ensures: `Ok(())` when every pending or generated obligation checks before
///   the operational ceiling is exhausted. An empty worklist is a no-op;
///   otherwise the first attempted check charges a term-plane event when the
///   budget is nonzero. Counters never decrease and the arena prefix remains.
/// - provides: the deferred half of formation, without recursive calls between
///   the two machines. A memo hit can suppress repeated obligations, so the
///   occurrence budget can refuse a valid declaration under one memo policy but
///   not another. Full code typing still requires the checking derivation.
/// - fails: [`KernelError::CodeObligationCeiling`] when the drain exceeds
///   [`MAX_CODE_OBLIGATIONS`]; any [`KernelError`] a code's check surfaces.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the drain is a loop over an explicit worklist, not recursion.
/// - measure: the ceiling minus the number of obligations already drained,
///   which strictly falls at every iteration and is checked before the body
///   runs.
/// - boundedness: a check that owes more obligations than the ceiling allows is
///   refused rather than pursued, so the loop cannot run more than
///   [`MAX_CODE_OBLIGATIONS`] times whatever the artifact contains.
/// - input recursion: none — a drained check appends to this worklist rather
///   than re-entering this function.
///
/// # Adequacy
/// - hypothesis: L3 — the finite witnesses separate a valid code, a code's own
///   refusal, and the drain's operational boundary. Exactly the allowed count
///   succeeds with the null memo; one more refuses at the stated ceiling. The
///   same shared above-limit declaration succeeds with a fresh live memo,
///   showing that a resource refusal is not an ill-typedness judgement.
/// - witness: `check::tests::a_dependent_identity_checks_through_its_codes`
/// - witness: `check::tests::a_code_that_is_not_of_its_declared_universe_refuses`
/// - witness: `tests::acceptance::draining_code_obligations_reaches_the_checking_machine`
/// - witness: `check::tests::obligation_ceiling_can_separate_memoized_and_memoless_checks`
/// - witness: `element_identity::tests::native_evidence_checks_against_the_fold_fibre`
#[spec(captures: [entry_mark = arena.watermark(), entry_empty = owed.is_empty(),
    entry_term_expanded = u64::from(census.plane_expansions(SupportPlane::Term)),
    entry_term_recalled = u64::from(census.plane_recalls(SupportPlane::Term)),
    entry_type_expanded = u64::from(census.plane_expansions(SupportPlane::Type)),
    entry_type_recalled = u64::from(census.plane_recalls(SupportPlane::Type))],
    ensures: |ret| entry_mark.clamped_into(gandr_kernel_term::ArenaWatermark::default(), arena.watermark()) == entry_mark && {
        let term_expanded = u64::from(census.plane_expansions(SupportPlane::Term));
        let term_recalled = u64::from(census.plane_recalls(SupportPlane::Term));
        let type_expanded = u64::from(census.plane_expansions(SupportPlane::Type));
        let type_recalled = u64::from(census.plane_recalls(SupportPlane::Type));
        term_expanded >= entry_term_expanded
            && term_recalled >= entry_term_recalled
            && type_expanded >= entry_type_expanded
            && type_recalled >= entry_type_recalled
            && if entry_empty {
                ret.is_ok() && arena.watermark() == entry_mark
                && term_expanded == entry_term_expanded
                && term_recalled == entry_term_recalled
                && type_expanded == entry_type_expanded
                && type_recalled == entry_type_recalled
            } else {
                (usize::from(MAX_CODE_OBLIGATIONS) == 0
                    || term_expanded.saturating_add(term_recalled)
                        >= entry_term_expanded.saturating_add(entry_term_recalled).saturating_add(1_u64))
                    && match ret {
                        Err(KernelError::CodeObligationCeiling { ceiling }) => ceiling == MAX_CODE_OBLIGATIONS,
                        _ => true,
                    }
            }
    })]
fn drain_code_obligations<M>(
    arena: &mut TermArena,
    judgement: Judgement<'_>,
    memo: &mut M,
    session: &mut SupportContext,
    census: &mut ExpansionCensus,
    mut owed: Vec<CodeObligation>,
) -> Result<(), KernelError>
where
    M: CheckMemo<NodeSupport, NodeOutcome>,
{
    let mut drained: usize = 0;
    while let Some(obligation) = owed.pop() {
        if drained >= usize::from(MAX_CODE_OBLIGATIONS) {
            return Err(KernelError::CodeObligationCeiling {
                ceiling: MAX_CODE_OBLIGATIONS,
            });
        }
        // The preceding ceiling guard bounds this increment.
        drained = usize::from(arith::add(
            arith::Int::from(drained),
            arith::Int::from(1_usize),
        ));
        match obligation {
            CodeObligation::Universe {
                code,
                sort,
                level,
                context,
                stages,
                scope,
            } => {
                let universe = arena.value_type_universe(sort, level);
                let _checked = run(
                    arena,
                    scope.reading(judgement),
                    context,
                    Goal::CheckValue(code, universe),
                    stages,
                    Recording {
                        memo,
                        session,
                        census,
                        owed: &mut owed,
                    },
                )?;
            },
            CodeObligation::Endpoints {
                domain,
                left,
                right,
                context,
                stages,
                scope,
            } => {
                for endpoint in [left, right] {
                    let _checked = run(
                        arena,
                        scope.reading(judgement),
                        context.clone(),
                        Goal::CheckValue(endpoint, domain),
                        stages.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed: &mut owed,
                        },
                    )?;
                }
            },
            CodeObligation::Data {
                datatype,
                context,
                stages,
                scope,
            } => {
                let Some(matched_native_node) = arena.value_type(datatype)
                else {
                    return Err(KernelError::ArenaFault);
                };
                let ValueType::Data {
                    ref declaration,
                    ref arguments,
                } = *matched_native_node
                else {
                    return Err(KernelError::ArenaFault);
                };
                let judgement = scope.reading(judgement);
                let signature = former::resolve(judgement, *declaration)?;
                if signature.arity() != former::FamilyArity(arguments.len()) {
                    return Err(KernelError::DataArgumentArity);
                }
                // Each index classifier is scoped under the parameters and the
                // indices before it, so it instantiates at every argument
                // before its own place, as a parameter does.
                let telescope = signature
                    .parameters
                    .iter()
                    .chain(signature.indices)
                    .copied();
                for (index, parameter) in telescope.enumerate() {
                    let expected = former::instantiate(
                        arena,
                        session,
                        parameter,
                        datatype,
                        former::ParameterPrefix(index),
                    )?;
                    let argument = match arena.value_type(datatype) {
                        Some(&ValueType::Data { ref arguments, .. }) => arguments
                            .get(index)
                            .copied()
                            .ok_or(KernelError::DataArgumentArity)?,
                        _ => return Err(KernelError::ArenaFault),
                    };
                    let _checked = run(
                        arena,
                        judgement,
                        context.clone(),
                        Goal::CheckValue(argument, expected),
                        stages.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed: &mut owed,
                        },
                    )?;
                }
            },
            CodeObligation::Codata {
                codata: application,
                context,
                stages,
                scope,
            } => {
                let Some(&CompType::Codata { declaration, .. }) = arena.comp_type(application)
                else {
                    return Err(KernelError::ArenaFault);
                };
                let judgement = scope.reading(judgement);
                let signature = codata::resolve(judgement, declaration)?;
                for (index, &parameter) in signature.parameters.iter().enumerate() {
                    let (argument, expected) = codata::argument(
                        arena,
                        session,
                        (application, parameter),
                        former::ParameterPrefix(index),
                    )?;
                    let _checked = run(
                        arena,
                        judgement,
                        context.clone(),
                        Goal::CheckValue(argument, expected),
                        stages.clone(),
                        Recording {
                            memo,
                            session,
                            census,
                            owed: &mut owed,
                        },
                    )?;
                }
            },
        }
    }
    Ok(())
}

/// Check a closed value without admitting a declaration or retaining a memo.
///
/// # Specification
/// - requires: both roots live in `arena`.
/// - ensures: success exactly when `expected` forms and `value` checks in the
///   empty term, declaration, and level contexts, including code obligations.
/// - provides: the closed translator check for universe paths; no receipt.
/// - fails: the formation or checking machine's `KernelError`.
/// - panics: none.
///
/// # Errors
/// Any `KernelError` from formation, checking, or code-obligation replay.
///
/// # Adequacy
/// - hypothesis: L3 — malformed translator types must refuse before their
///   round-trip dialogues can certify an equivalence.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
#[spec(requires: arena.value(value).is_some() && arena.value_type(expected).is_some())]
pub(crate) fn check_closed_value(
    arena: &mut TermArena,
    value: ValueId,
    expected: ValueTypeId,
) -> Result<(), KernelError>
{
    let levels = LevelContext::admit(gandr_kernel_term::LevelParamCount::from(0_u32), Vec::new())?;
    let judgement = Judgement::new(&[], &levels);
    let mut memo = DefaultMemo::new();
    let mut session = SupportContext::new();
    let mut census = ExpansionCensus::new();
    let mut owed = Vec::new();
    let _level = type_level(
        arena,
        judgement,
        TypeLevelGoal::Value(expected),
        Vec::new(),
        Recording {
            memo: &mut memo,
            session: &mut session,
            census: &mut census,
            owed: &mut owed,
        },
    )?;
    let _checked = run(
        arena,
        judgement,
        Vec::new(),
        Goal::CheckValue(value, expected),
        StageOrder::default(),
        Recording {
            memo: &mut memo,
            session: &mut session,
            census: &mut census,
            owed: &mut owed,
        },
    )?;
    drain_code_obligations(arena, judgement, &mut memo, &mut session, &mut census, owed)
}

/// Synthesize a closed native value and discharge every code obligation.
///
/// # Specification
/// - requires: the value belongs to the arena.
/// - ensures: the returned classifier is justified in empty contexts.
/// - provides: the typed boundary for callable native transport replay.
/// - fails: any native synthesis or code-formation error.
/// - panics: none.
///
/// # Errors
/// Any `KernelError`.
///
/// # Adequacy
/// - hypothesis: L3 — replay admits a certified path and refuses forged
///   evidence.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
#[spec(
    requires: arena.value(value).is_some(),
    ensures: |ret| ret.as_ref().map_or(true, |&classifier| match arena.value(value) {
        Some(&Value::PathRefl(code)) => matches!(arena.value_type(classifier), Some(&ValueType::PathUniverse(source, target)) if source == code && target == code),
        Some(&Value::PathEquiv { path_type, .. }) => classifier == path_type,
        Some(&Value::PathProduct(..)) => matches!(arena.value_type(classifier), Some(&ValueType::PathUniverse(..))),
        _ => arena.value_type(classifier).is_some(),
    }),
)]
pub(crate) fn synth_closed_value(
    arena: &mut TermArena,
    value: ValueId,
) -> Result<ValueTypeId, KernelError>
{
    let levels = LevelContext::admit(gandr_kernel_term::LevelParamCount::from(0_u32), Vec::new())?;
    let judgement = Judgement::new(&[], &levels);
    let mut memo = DefaultMemo::new();
    let mut session = SupportContext::new();
    let mut census = ExpansionCensus::new();
    let mut owed = Vec::new();
    let result = run(
        arena,
        judgement,
        Vec::new(),
        Goal::SynthValue(value),
        StageOrder::default(),
        Recording {
            memo: &mut memo,
            session: &mut session,
            census: &mut census,
            owed: &mut owed,
        },
    )?
    .value_type()?;
    drain_code_obligations(arena, judgement, &mut memo, &mut session, &mut census, owed)?;
    Ok(result)
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_kernel_check_memo::NullMemo;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::CompType;
    use gandr_kernel_term::CompTypeId;
    use gandr_kernel_term::ComputationId;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelParamCount;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::SealExtent;
    use gandr_kernel_term::SealScope;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Summand;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::ValueId;
    use gandr_kernel_term::ValueType;
    use gandr_kernel_term::ValueTypeId;

    use super::Goal;
    use super::Judgement;
    use super::Produced;
    use super::Recording;
    use super::TypeLevelGoal;
    use super::run;
    use super::type_level;
    use crate::census::ExpansionCensus;
    use crate::env::AdmittedDeclaration;
    use crate::env::Environment;
    use crate::error::ExpectedValueShape;
    use crate::error::KernelError;
    use crate::error::NonInferableForm;
    use crate::error::RegisterFault;
    use crate::error::ValueTypeHead;
    use crate::levels::LevelContext;
    use crate::stage_order::StageOrder;
    use crate::support::SupportContext;

    #[test]
    fn native_list_introductions_and_fold_check()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let list_type = arena.value_type_list(unit_type);
        let unit = arena.value_unit();
        let nil = arena.value_list_nil();
        let cons = arena.value_list_cons(unit, nil);
        let malformed_tail = arena.value_list_cons(unit, unit);
        let malformed_head = arena.value_list_cons(nil, nil);
        let sum_encoding = arena.value_injection(Side::Left.into(), unit);
        for valid in [nil, cons] {
            assert_eq!(
                super::check_closed_value(&mut arena, valid, list_type),
                Ok(())
            );
        }
        for invalid in [malformed_tail, malformed_head, sum_encoding] {
            assert!(super::check_closed_value(&mut arena, invalid, list_type).is_err());
        }
        let head = arena.value_variable(DeBruijnIndex::from(1_u32));
        let folded = arena.value_variable(DeBruijnIndex::from(0_u32));
        let cell = arena.value_list_cons(head, folded);
        let on_cons = arena.computation_return(cell);
        let on_nil = arena.computation_return(nil);
        let fold = arena.computation_list_fold(unit_type, list_type, cons, on_nil, on_cons);
        let result = arena.comp_type_returner(list_type);
        let suspended = arena.value_type_thunk(result);
        let body = arena.value_thunk(fold);
        assert_eq!(
            super::check_closed_value(&mut arena, body, suspended),
            Ok(())
        );
        let wrong_cell = arena.value_list_cons(folded, head);
        let wrong_branch = arena.computation_return(wrong_cell);
        let wrong_fold =
            arena.computation_list_fold(unit_type, list_type, cons, on_nil, wrong_branch);
        let wrong = arena.value_thunk(wrong_fold);
        assert!(super::check_closed_value(&mut arena, wrong, suspended).is_err());
    }

    #[test]
    fn obligation_ceiling_can_separate_memoized_and_memoless_checks()
    {
        let mut environment = Environment::new();
        let code_axiom = {
            let mut staging = environment.stage();
            let universe = staging
                .arena()
                .value_type_universe(GroundSort::Value, Level::zero());
            staging.axiom(LevelSignature::monomorphic(), universe)
        };
        let code_axiom = environment
            .add_decl(code_axiom)
            .expect("the code axiom admits");
        let mut arena = environment.arena().clone();
        let (at_limit, above_limit) = {
            let mut builder = gandr_kernel_term::DeclarationBuilder::new(&mut arena);
            let code = builder.arena().value_constant(code_axiom.position());
            let leaf = builder.arena().value_type_element(code, Level::zero());
            let mut root = builder.arena().value_type_unit();
            let mut power = leaf;
            let mut remaining = usize::from(super::MAX_CODE_OBLIGATIONS);
            while remaining != 0 {
                if remaining & 1_usize != 0 {
                    root = builder.arena().value_type_product(&[root, power]);
                }
                remaining >>= 1_u32;
                if remaining != 0 {
                    power = builder.arena().value_type_product(&[power, power]);
                }
            }
            let above = builder.arena().value_type_product(&[root, leaf]);
            (builder.axiom(LevelSignature::monomorphic(), root), above)
        };
        let above_limit = gandr_kernel_term::DeclarationBuilder::new(&mut arena)
            .axiom(LevelSignature::monomorphic(), above_limit);
        let levels = level_context(LevelParamCount::from(0_u32));
        let content_end = arena.watermark();
        let at_limit = super::check_declaration_with_memo(
            &mut arena,
            super::Judgement::new(environment.entries(), &levels),
            &at_limit,
            &mut NullMemo,
            &mut SupportContext::new(),
            &mut ExpansionCensus::new(),
        );
        assert!(
            at_limit.is_ok(),
            "the exact occurrence budget is accepted: {at_limit:?}"
        );
        arena.truncate_to(content_end);
        let memoized = super::check_declaration_with_memo(
            &mut arena,
            super::Judgement::new(environment.entries(), &levels),
            &above_limit,
            &mut super::DefaultMemo::new(),
            &mut SupportContext::new(),
            &mut ExpansionCensus::new(),
        );
        assert!(
            memoized.is_ok(),
            "the shared valid type checks with a live memo: {memoized:?}"
        );
        arena.truncate_to(content_end);
        let memoless = super::check_declaration_with_memo(
            &mut arena,
            super::Judgement::new(environment.entries(), &levels),
            &above_limit,
            &mut NullMemo,
            &mut SupportContext::new(),
            &mut ExpansionCensus::new(),
        );
        assert!(
            matches!(memoless, Err(KernelError::CodeObligationCeiling { ceiling })
            if ceiling == super::MAX_CODE_OBLIGATIONS)
        );
    }

    #[test]
    fn unreadable_term_roots_fail_closed()
    {
        let mut arena = TermArena::new();
        let before = arena.watermark();
        let value = arena.value_unit();
        let computation = arena.computation_return(value);
        arena.truncate_to(before);
        assert!(matches!(
            synth_value(&mut arena, vec![], value),
            Err(KernelError::ArenaFault)
        ));
        assert!(matches!(
            synth_comp(&mut arena, vec![], computation),
            Err(KernelError::ArenaFault)
        ));
        assert_eq!(before, arena.watermark());
    }

    /// No prior declarations.
    ///
    /// # Specification
    /// trivial.
    fn no_entries() -> Vec<AdmittedDeclaration>
    {
        Vec::new()
    }

    /// An unconstrained level context over `params` prenex parameters.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a level context over `params` prenex parameters with no
    ///   declared constraints, whose universe judgements are the free-fragment
    ///   oracle's.
    /// - provides: the level context the machine cases run under.
    /// - fails: never.
    /// - panics: when admission refuses, which an empty constraint set never
    ///   does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed universes form in the zero-parameter fixture;
    ///   the one-parameter boundary admits its last variable and refuses the
    ///   next one, separating lost or enlarged scope through formation.
    /// - witness: `check::tests::a_universe_forms_one_level_up`
    /// - witness: `check::tests::a_prenex_scope_controls_universe_formation`
    #[spec(ensures: |ret| ret.params() == params)]
    fn level_context(params: LevelParamCount) -> LevelContext
    {
        LevelContext::admit(params, Vec::new()).expect("an unconstrained context admits")
    }

    /// The constant level `value`.
    ///
    /// # Specification
    /// trivial.
    fn level(value: LevelConstant) -> Level
    {
        Level::constant(value)
    }

    /// Synthesize a value's type in a bare arena under `context`.
    ///
    /// # Specification
    /// - requires: `context` is the typing context the value stands in, and
    ///   `arena` holds it.
    /// - ensures: the machine's answer for a value-synthesis goal, run at the
    ///   null memo with a fresh session and census, so the case observes the
    ///   unmemoized path.
    /// - provides: the synthesis fixture the value rules are asserted through.
    /// - fails: whatever the machine refuses the goal with.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a readable variable synthesizes the selected context
    ///   type; an injection has no synthesized type and an unreadable root
    ///   produces the arena fault. These are finite rule and refusal cases.
    /// - witness: `check::tests::a_variable_synthesizes_its_context_type`
    /// - witness: `check::tests::an_injection_is_not_inferable`
    /// - witness: `check::tests::unreadable_term_roots_fail_closed`
    #[spec(ensures: |ret| match ret {
        Ok(Produced::ValueType(id)) => arena.value_type(id).is_some(),
        Err(_) => true,
        _ => false,
    })]
    fn synth_value(
        arena: &mut TermArena,
        context: Vec<ValueTypeId>,
        value: ValueId,
    ) -> Result<Produced, KernelError>
    {
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        run(
            arena,
            Judgement::new(&entries, &context_levels),
            context,
            Goal::SynthValue(value),
            StageOrder::default(),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        )
    }

    /// Check a value against an expected type in a bare arena.
    ///
    /// # Specification
    /// - requires: `context` is the typing context the value stands in, and
    ///   `arena` holds both the value and `expected`.
    /// - ensures: the machine's answer for a checking goal, run at the null
    ///   memo with a fresh session and census.
    /// - provides: the checking fixture the value rules are asserted through.
    /// - fails: whatever the machine refuses the goal with.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an injection is accepted against its sum, and the
    ///   expected type reaches a checking component of a pair. Success is a
    ///   checking result rather than a synthesized-type register.
    /// - witness: `check::tests::an_injection_checks_against_its_sum`
    /// - witness: `check::tests::a_pair_propagates_into_a_checking_component`
    #[spec(ensures: |ret| matches!(&ret, Ok(Produced::Checked) | Err(_)))]
    fn check_value(
        arena: &mut TermArena,
        context: Vec<ValueTypeId>,
        value: ValueId,
        expected: ValueTypeId,
    ) -> Result<Produced, KernelError>
    {
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        run(
            arena,
            Judgement::new(&entries, &context_levels),
            context,
            Goal::CheckValue(value, expected),
            StageOrder::default(),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        )
    }

    /// Synthesize a computation's type in a bare arena.
    ///
    /// # Specification
    /// - requires: `context` is the typing context the computation stands in,
    ///   and `arena` holds it.
    /// - ensures: the machine's answer for a computation-synthesis goal, run at
    ///   the null memo with a fresh session and census.
    /// - provides: the synthesis fixture the computation rules are asserted
    ///   through.
    /// - fails: whatever the machine refuses the goal with.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an application and a force synthesize their selected
    ///   computation types; an unreadable computation root produces the arena
    ///   fault without fabricating a type.
    /// - witness: `check::tests::an_application_produces_the_codomain`
    /// - witness: `check::tests::a_force_unwraps_a_thunk`
    /// - witness: `check::tests::unreadable_term_roots_fail_closed`
    #[spec(ensures: |ret| match ret {
        Ok(Produced::CompType(id)) => arena.comp_type(id).is_some(),
        Err(_) => true,
        _ => false,
    })]
    fn synth_comp(
        arena: &mut TermArena,
        context: Vec<ValueTypeId>,
        computation: ComputationId,
    ) -> Result<Produced, KernelError>
    {
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        run(
            arena,
            Judgement::new(&entries, &context_levels),
            context,
            Goal::SynthComp(computation),
            StageOrder::default(),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        )
    }

    /// The level of a value type in a bare arena.
    ///
    /// # Specification
    /// - requires: `arena` holds `root`.
    /// - ensures: the universe level the formation walk reads off `root`, run
    ///   at the null memo with a fresh session and census and with its code
    ///   obligations discarded.
    /// - provides: the formation fixture the type rules are asserted through.
    /// - fails: whatever the formation walk refuses the type with.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the closed-universe successor and lift boundary
    ///   distinguish the formation result from refusal. This fixture does not
    ///   claim to discharge the codes its formation walk defers.
    /// - witness: `check::tests::a_universe_forms_one_level_up`
    /// - witness: `check::tests::a_lift_requires_a_strictly_higher_target`
    #[spec(ensures: |ret| match arena.value_type(root) {
        None => matches!(&ret, Err(KernelError::ArenaFault)),
        Some(&ValueType::Base(_)) => ret.as_ref().is_ok_and(|level| *level == Level::zero()),
        Some(held) if held.product_parts() == Some(&[]) => ret.as_ref().is_ok_and(|level| *level == Level::zero()),
        Some(_) => ret.is_err() || ret.as_ref().is_ok_and(|level| level.atoms().next().is_none()),
    })]
    fn value_level(
        arena: &TermArena,
        root: ValueTypeId,
    ) -> Result<Level, KernelError>
    {
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        type_level(
            arena,
            Judgement::new(&entries, &context_levels),
            TypeLevelGoal::Value(root),
            Vec::new(),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        )
    }

    #[test]
    fn a_variable_synthesizes_its_context_type()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_type_unit();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let produced = synth_value(&mut arena, vec![unit, integer], variable)
            .expect("an in-scope variable synthesizes");
        assert_eq!(
            integer,
            produced.value_type().expect("a value type"),
            "index zero names the innermost slot"
        );
        let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
        let produced = synth_value(&mut arena, vec![unit, integer], outer)
            .expect("the outermost slot remains in scope");
        assert_eq!(unit, produced.value_type().expect("a value type"));
        assert_eq!(
            Err(KernelError::UnboundVariable {
                index: DeBruijnIndex::from(0_u32)
            }),
            synth_value(&mut arena, Vec::new(), variable),
            "an empty context has no innermost slot"
        );
        let maximal = arena.value_variable(DeBruijnIndex::from(u32::MAX));
        assert_eq!(
            Err(KernelError::UnboundVariable {
                index: DeBruijnIndex::from(u32::MAX)
            }),
            synth_value(&mut arena, vec![unit, integer], maximal),
            "a maximal external index is absent without arithmetic failure"
        );
        let escaping = arena.value_variable(DeBruijnIndex::from(2_u32));
        assert_eq!(
            Err(KernelError::UnboundVariable {
                index: DeBruijnIndex::from(2_u32)
            }),
            synth_value(&mut arena, vec![unit, integer], escaping),
            "and an index past the context escapes"
        );
    }

    #[test]
    fn an_injection_is_not_inferable()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let injection = arena.value_injection(Side::Left.into(), unit);
        assert_eq!(
            Err(KernelError::NotInferable {
                form: NonInferableForm::Injection
            }),
            synth_value(&mut arena, Vec::new(), injection),
            "an injection carries no record of which sum it injects into"
        );
    }

    #[test]
    fn an_injection_checks_against_its_sum()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let sum = arena.value_type_sum(&[unit_type, integer]);
        let left = arena.value_injection(Side::Left.into(), unit);
        assert!(
            check_value(&mut arena, Vec::new(), left, sum).is_ok(),
            "the left injection checks against the left summand"
        );
        let right = arena.value_injection(Side::Right.into(), unit);
        assert!(
            matches!(
                check_value(&mut arena, Vec::new(), right, sum),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Product,
                    ..
                })
            ),
            "and the right injection is checked against the right summand, which the unit tuple \
             is not"
        );
        let refused = check_value(&mut arena, Vec::new(), left, unit_type);
        assert!(
            matches!(
                refused,
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Sum,
                    ..
                })
            ),
            "and a non-sum expected type is a shape mismatch: {refused:?}"
        );
    }

    #[test]
    fn a_pair_propagates_into_a_checking_component()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let injection = arena.value_injection(Side::Left.into(), unit);
        let sum = arena.value_type_sum(&[unit_type, integer]);
        let pair = arena.value_tuple(&[unit, injection]);
        let product = arena.value_type_product(&[unit_type, sum]);
        assert!(
            check_value(&mut arena, Vec::new(), pair, product).is_ok(),
            "the expected product flows into both components, so the checking-only injection \
             reaches its sum"
        );
        assert!(
            matches!(
                synth_value(&mut arena, Vec::new(), pair),
                Err(KernelError::NotInferable {
                    form: NonInferableForm::Injection
                })
            ),
            "and the same pair does not synthesize, since nothing tells the injection its sum"
        );
    }

    #[test]
    fn an_application_produces_the_codomain()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(unit_type, returner);
        let thunk_type = arena.value_type_thunk(arrow);
        let head_variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let head = arena.computation_force(head_variable);
        let unit = arena.value_unit();
        let application = arena.computation_application(head, unit);
        let produced = synth_comp(&mut arena, vec![thunk_type], application)
            .expect("an application of a forced thunk synthesizes");
        assert_eq!(
            returner,
            produced.comp_type().expect("a computation type"),
            "an application produces its head's codomain"
        );
    }

    #[test]
    fn a_force_unwraps_a_thunk()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit_type);
        let thunk_type = arena.value_type_thunk(returner);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let force = arena.computation_force(variable);
        let produced =
            synth_comp(&mut arena, vec![thunk_type], force).expect("forcing a thunk synthesizes");
        assert_eq!(
            returner,
            produced.comp_type().expect("a computation type"),
            "a force yields the thunked computation type"
        );
        let not_a_thunk = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bad_force = arena.computation_force(not_a_thunk);
        assert!(
            matches!(
                synth_comp(&mut arena, vec![unit_type], bad_force),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Thunk,
                    ..
                })
            ),
            "and forcing a non-thunk is a shape mismatch"
        );
    }

    #[test]
    fn a_bind_binds_the_returned_value()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        let thunk_type = arena.value_type_thunk(returner);
        let held = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound = arena.computation_force(held);
        // The body reads the payload the bind introduced, at index zero.
        let payload = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(payload);
        let sequence = arena.computation_bind(bound, body);
        let produced = synth_comp(&mut arena, vec![thunk_type], sequence)
            .expect("a bind over a returner synthesizes");
        let produced_type = produced.comp_type().expect("a computation type");
        let read = arena.comp_type(produced_type).expect("the type resolves");
        assert!(
            matches!(*read, CompType::Returner(result) if result == integer),
            "the body sees the bound payload's type, so the bind returns it"
        );
    }

    #[test]
    fn a_case_requires_convergent_branches()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let sum = arena.value_type_sum(&[unit_type, unit_type]);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let left = arena.computation_return(bound);
        let right = arena.computation_return(bound);
        let case = arena.computation_case(scrutinee, &[left, right]);
        assert!(
            synth_comp(&mut arena, vec![sum], case).is_ok(),
            "two branches returning their own summand converge when the summands agree"
        );

        let mixed = arena.value_type_sum(&[unit_type, integer]);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let case = arena.computation_case(scrutinee, &[left, right]);
        assert!(
            matches!(
                synth_comp(&mut arena, vec![mixed], case),
                Err(KernelError::CaseBranchMismatch(_))
            ),
            "and they diverge when the summands do"
        );
    }

    #[test]
    fn a_case_propagates_the_expected_type()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let mixed = arena.value_type_sum(&[unit_type, integer]);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit = arena.value_unit();
        let left = arena.computation_return(unit);
        let right = arena.computation_return(unit);
        let case = arena.computation_case(scrutinee, &[left, right]);
        let expected = arena.comp_type_returner(unit_type);
        let thunk = arena.value_thunk(case);
        let thunk_type = arena.value_type_thunk(expected);
        assert!(
            check_value(&mut arena, vec![mixed], thunk, thunk_type).is_ok(),
            "checking pushes one expected type into both branches, where synthesis would have \
             required them to agree on their own"
        );
    }

    /// A case binds each branch to the summand at its position, takes exactly
    /// one branch per summand, and at no branches eliminates the empty sum,
    /// which checks but cannot be synthesized.
    #[test]
    fn an_n_way_case_binds_each_summand()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(bound);
        let three_way = arena.computation_case(scrutinee, &[returned, returned, returned]);

        let uniform = arena.value_type_sum(&[integer, integer, integer]);
        let produced = synth_comp(&mut arena, vec![uniform], three_way)
            .expect("three branches returning agreeing summands converge");
        assert!(
            matches!(
                arena.comp_type(produced.comp_type().expect("a computation type")),
                Some(&CompType::Returner(result)) if result == integer
            ),
            "and the case returns the summands' common type"
        );
        let middle_differs = arena.value_type_sum(&[integer, unit_type, integer]);
        assert!(
            matches!(
                synth_comp(&mut arena, vec![middle_differs], three_way),
                Err(KernelError::CaseBranchMismatch(_))
            ),
            "the middle branch binds the middle summand"
        );
        let two_way = arena.value_type_sum(&[integer, integer]);
        assert!(
            matches!(
                synth_comp(&mut arena, vec![two_way], three_way),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Sum,
                    ..
                })
            ),
            "three branches do not eliminate a sum of two"
        );

        let empty = arena.value_type_empty();
        let no_branches = arena.computation_case(scrutinee, &[]);
        let returner = arena.comp_type_returner(integer);
        let thunk_type = arena.value_type_thunk(returner);
        let thunk = arena.value_thunk(no_branches);
        assert!(
            check_value(&mut arena, vec![empty], thunk, thunk_type).is_ok(),
            "a case of no branches over the empty sum checks at any type"
        );
        assert_eq!(
            Err(KernelError::NotInferable {
                form: NonInferableForm::EmptyCase
            }),
            synth_comp(&mut arena, vec![empty], no_branches),
            "and has no branch to synthesize a type from"
        );
        assert!(
            matches!(
                check_value(&mut arena, vec![unit_type], thunk, thunk_type),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Sum,
                    ..
                })
            ),
            "but eliminates nothing that is not the empty sum"
        );
    }

    /// A tuple checks component by component against a product of its own
    /// arity and synthesizes the product of its components' types; an
    /// injection checks against the summand its position names.
    #[test]
    fn a_tuple_and_an_injection_read_their_positions()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_unit();
        let triple = arena.value_tuple(&[unit, unit, unit]);
        let three = arena.value_type_product(&[unit_type, unit_type, unit_type]);
        assert!(check_value(&mut arena, Vec::new(), triple, three).is_ok());
        let produced = synth_value(&mut arena, Vec::new(), triple)
            .expect("a tuple synthesizes")
            .value_type()
            .expect("a value type");
        assert_eq!(
            crate::conv::Convertibility::Convertible,
            crate::conv::convertible_value_types(&arena, produced, three),
            "the product of its components' types"
        );
        let two = arena.value_type_product(&[unit_type, unit_type]);
        assert!(
            matches!(
                check_value(&mut arena, Vec::new(), triple, two),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Product,
                    ..
                })
            ),
            "a product of another arity is a shape mismatch"
        );

        let sum = arena.value_type_sum(&[integer, integer, unit_type]);
        let last = arena.value_injection(Summand::from(2_usize), unit);
        assert!(
            check_value(&mut arena, Vec::new(), last, sum).is_ok(),
            "the third summand is the unit type"
        );
        let past = arena.value_injection(Summand::from(3_usize), unit);
        assert!(
            matches!(
                check_value(&mut arena, Vec::new(), past, sum),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Sum,
                    ..
                })
            ),
            "a position past the summands is a shape mismatch"
        );
    }

    #[test]
    fn a_prenex_scope_controls_universe_formation()
    {
        let mut arena = TermArena::new();
        let variable = Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(0_u32),
        ));
        let expected = variable.succ().expect("a variable's successor fits");
        let in_scope = arena.value_type_universe(GroundSort::Value, variable);
        let out_of_scope = arena.value_type_universe(
            GroundSort::Value,
            Level::var(gandr_kernel_strata::LevelVar::new(
                gandr_kernel_strata::LevelVarIndex::from(1_u32),
            )),
        );
        let levels = level_context(LevelParamCount::from(1_u32));
        let entries = no_entries();
        let formed = type_level(
            &arena,
            Judgement::new(&entries, &levels),
            TypeLevelGoal::Value(in_scope),
            Vec::new(),
            Recording {
                memo: &mut NullMemo,
                session: &mut SupportContext::new(),
                census: &mut ExpansionCensus::new(),
                owed: &mut Vec::new(),
            },
        );
        assert_eq!(formed, Ok(expected));
        let refused = type_level(
            &arena,
            Judgement::new(&entries, &levels),
            TypeLevelGoal::Value(out_of_scope),
            Vec::new(),
            Recording {
                memo: &mut NullMemo,
                session: &mut SupportContext::new(),
                census: &mut ExpansionCensus::new(),
                owed: &mut Vec::new(),
            },
        );
        assert_eq!(
            refused,
            Err(KernelError::LevelVariableOutOfScope {
                variable: gandr_kernel_strata::LevelVar::new(
                    gandr_kernel_strata::LevelVarIndex::from(1_u32),
                ),
            })
        );
    }

    #[test]
    fn a_universe_forms_one_level_up()
    {
        let mut arena = TermArena::new();
        let universe = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(3)));
        assert_eq!(
            Ok(level(LevelConstant::from(4))),
            value_level(&arena, universe),
            "the universe at l forms at l + 1"
        );
        let computation =
            arena.value_type_universe(GroundSort::Computation, level(LevelConstant::from(3)));
        assert_eq!(
            Ok(level(LevelConstant::from(4))),
            value_level(&arena, computation),
            "and so does the computation universe, itself a value type"
        );
        let unit = arena.value_type_unit();
        assert_eq!(
            Ok(level(LevelConstant::from(0))),
            value_level(&arena, unit),
            "and a small type forms at zero"
        );
    }

    #[test]
    fn a_lift_requires_a_strictly_higher_target()
    {
        let mut arena = TermArena::new();
        let universe = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(1)));
        let raised = arena.value_type_lift(universe, level(LevelConstant::from(5)));
        assert_eq!(
            Ok(level(LevelConstant::from(5))),
            value_level(&arena, raised),
            "a lift forms at its target"
        );
        // `Universe(1)` itself forms at level 2, so 3 is the first admissible
        // target and 2 is the boundary that does not strictly raise.
        let boundary = arena.value_type_lift(universe, level(LevelConstant::from(3)));
        assert_eq!(
            Ok(level(LevelConstant::from(3))),
            value_level(&arena, boundary),
            "one above the inner type's own level is admissible"
        );
        let sunk = arena.value_type_lift(universe, level(LevelConstant::from(2)));
        assert!(
            matches!(
                value_level(&arena, sunk),
                Err(KernelError::UniverseViolation(_))
            ),
            "and a target at the inner type's own level does not strictly raise"
        );
    }

    #[test]
    fn an_arrow_forms_at_the_join_of_its_children()
    {
        let mut arena = TermArena::new();
        let low = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(1)));
        let high = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(4)));
        let returner = arena.comp_type_returner(high);
        let arrow = arena.comp_type_arrow(low, returner);
        let thunk = arena.value_type_thunk(arrow);
        assert_eq!(
            Ok(level(LevelConstant::from(5))),
            value_level(&arena, thunk),
            "the arrow takes the maximum of its domain's and codomain's levels"
        );
    }

    #[test]
    fn a_static_pi_forms_over_static_classifiers_only()
    {
        let mut arena = TermArena::new();
        let low = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(1)));
        let high =
            arena.value_type_universe(GroundSort::Computation, level(LevelConstant::from(3)));
        let operator = arena.value_type_static_pi(low, high);
        assert_eq!(
            Ok(level(LevelConstant::from(4))),
            value_level(&arena, operator),
            "a static Pi forms at the join of its children's levels"
        );
        let curried = arena.value_type_static_pi(low, operator);
        assert_eq!(
            Ok(level(LevelConstant::from(4))),
            value_level(&arena, curried),
            "and a static Pi is itself a static classifier"
        );
        let integer = arena.value_type_base(BaseType::Integer);
        for ill in [
            arena.value_type_static_pi(integer, low),
            arena.value_type_static_pi(low, integer),
        ] {
            assert!(
                matches!(
                    value_level(&arena, ill),
                    Err(KernelError::StaticClassifierExpected { actual })
                        if actual.head() == ValueTypeHead::Base
                ),
                "a type that classifies no codes stands at neither child"
            );
        }
    }

    #[test]
    fn a_static_application_produces_the_codomain_of_its_head()
    {
        let mut arena = TermArena::new();
        let small = arena.value_type_universe(GroundSort::Value, Level::zero());
        let computations = arena.value_type_universe(GroundSort::Computation, Level::zero());
        let operator = arena.value_type_static_pi(small, computations);
        let integer = arena.value_type_base(BaseType::Integer);
        let code = arena.value_quote(integer);
        let head = arena.value_variable(DeBruijnIndex::from(0_u32));
        let instance = arena.value_static_application(head, code);
        let produced = synth_value(&mut arena, vec![operator], instance)
            .expect("an operator applied to a code of its domain synthesizes");
        assert_eq!(
            computations,
            produced.value_type().expect("a value type"),
            "a static application produces its head's codomain"
        );

        let unit = arena.value_unit();
        let ill_argument = arena.value_static_application(head, unit);
        assert!(
            matches!(
                synth_value(&mut arena, vec![operator], ill_argument),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Product,
                    ..
                })
            ),
            "the argument is checked against the domain"
        );
        assert!(
            matches!(
                synth_value(&mut arena, vec![small], instance),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::StaticPi,
                    ..
                })
            ),
            "and only a static Pi's inhabitant is applied"
        );
    }

    /// The dependent arrow forms like the arrow, checks a lambda like the
    /// arrow, and eliminates like the arrow. Three assertions in one case
    /// because they are one claim: at a type vocabulary with no former indexed
    /// by a value term, the binder the dependent arrow scopes its codomain
    /// under is the context slot a lambda's check already pushes, and
    /// instantiating the codomain at the argument moves nothing.
    #[test]
    fn a_dependent_arrow_forms_checks_and_eliminates_like_an_arrow()
    {
        let mut arena = TermArena::new();
        let low = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(1)));
        let high = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(4)));
        let returner = arena.comp_type_returner(high);
        let dependent = arena.comp_type_pi(low, returner);
        let thunk = arena.value_type_thunk(dependent);
        assert_eq!(
            Ok(level(LevelConstant::from(5))),
            value_level(&arena, thunk),
            "the dependent arrow forms at the join of its domain's and codomain's levels"
        );

        let unit_type = arena.value_type_unit();
        let unit_returner = arena.comp_type_returner(unit_type);
        let identity = arena.comp_type_pi(unit_type, unit_returner);
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(bound);
        let lambda = arena.computation_lambda(body);
        let mut memo = NullMemo;
        let mut session = SupportContext::new();
        let mut census = ExpansionCensus::new();
        let entries = no_entries();
        let context_levels = level_context(LevelParamCount::from(0_u32));
        let checked = run(
            &mut arena,
            Judgement::new(&entries, &context_levels),
            Vec::new(),
            Goal::CheckComp(lambda, identity),
            StageOrder::default(),
            Recording {
                memo: &mut memo,
                session: &mut session,
                census: &mut census,
                owed: &mut Vec::new(),
            },
        );
        assert_eq!(
            Ok(Produced::Checked),
            checked,
            "a lambda checks against a dependent arrow through the domain it pushes"
        );

        let head_thunk = arena.value_type_thunk(identity);
        let head_variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let head = arena.computation_force(head_variable);
        let unit = arena.value_unit();
        let application = arena.computation_application(head, unit);
        let produced = synth_comp(&mut arena, vec![head_thunk], application)
            .expect("an application at a dependent head synthesizes");
        assert_eq!(
            unit_returner,
            produced.comp_type().expect("a computation type"),
            "and the elimination produces the codomain, which no term occurs in to substitute for"
        );
    }

    #[test]
    fn an_abstract_type_forms_at_its_declared_universe()
    {
        let mut environment = Environment::new();
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(GroundSort::Value, level(LevelConstant::from(2)));
            let integer = staging.arena().value_type_base(BaseType::Integer);
            staging.abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                SealScope::Closed(SealExtent::from(0_usize)),
            )
        };
        let _admitted = environment
            .add_decl(atom)
            .expect("an abstract type at a universe kind admits");
        let definition = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_universe(GroundSort::Value, level(LevelConstant::from(9)));
            let _inner = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let _second = environment
            .add_decl(definition)
            .expect("an axiom at a universe admits");

        // The atom's own formation level is read off the kind its declaration
        // fixed, which is the whole rule.
        let referencing = {
            let mut staging = environment.stage();
            let atom_type = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            let raised = staging
                .arena()
                .value_type_lift(atom_type, level(LevelConstant::from(3)));
            staging.axiom(LevelSignature::monomorphic(), raised)
        };
        assert!(
            environment.add_decl(referencing).is_ok(),
            "a lift of the atom to one level above its declared kind admits"
        );
        let too_low = {
            let mut staging = environment.stage();
            let atom_type = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            let raised = staging
                .arena()
                .value_type_lift(atom_type, level(LevelConstant::from(2)));
            staging.axiom(LevelSignature::monomorphic(), raised)
        };
        assert!(
            matches!(
                environment.add_decl(too_low),
                Err(KernelError::UniverseViolation(_))
            ),
            "and a lift to the atom's own level does not, so the level came from the kind"
        );
    }

    #[test]
    fn an_atom_naming_a_definition_is_not_an_abstract_type()
    {
        let mut environment = Environment::new();
        let definition = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let _admitted = environment
            .add_decl(definition)
            .expect("a unit definition admits");
        let forged = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert_eq!(
            Err(KernelError::NotAnAbstractType {
                index: ConstantIndex::from(0_usize)
            }),
            environment.add_decl(forged).map(|_admitted| ()),
            "nothing in an artifact says 'I am an atom'; the kernel resolves the position"
        );
    }

    #[test]
    fn a_forward_atom_reference_is_not_an_abstract_type()
    {
        let mut environment = Environment::new();
        let forward = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(7_usize));
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert_eq!(
            Err(KernelError::NotAnAbstractType {
                index: ConstantIndex::from(7_usize)
            }),
            environment.add_decl(forward).map(|_admitted| ()),
            "an out-of-range position resolves to nothing and is refused"
        );
    }

    #[test]
    fn an_identity_thunk_checks()
    {
        let mut environment = Environment::new();
        let definition = {
            let mut staging = environment.stage();
            let integer = staging.arena().value_type_base(BaseType::Integer);
            let returner = staging.arena().comp_type_returner(integer);
            let arrow = staging.arena().comp_type_arrow(integer, returner);
            let declared = staging.arena().value_type_thunk(arrow);
            let variable = staging.arena().value_variable(DeBruijnIndex::from(0_u32));
            let body = staging.arena().computation_return(variable);
            let lambda = staging.arena().computation_lambda(body);
            let thunk = staging.arena().value_thunk(lambda);
            staging.def(LevelSignature::monomorphic(), declared, thunk)
        };
        assert!(
            environment.add_decl(definition).is_ok(),
            "the identity on integers admits through the checked choke point"
        );
    }

    /// The polymorphic identity, admitted through the public choke point.
    ///
    /// `Π (A : U 0). Π (_ : El A). F (El A)` is the smallest declaration that
    /// makes every part of the dependent machinery load-bearing at once: the
    /// codomain mentions the binder through a code, so the context stops
    /// holding closed types and a variable synthesis has to shift its slot;
    /// the formation walk owes two code obligations and the driver drains
    /// both through the checking machine; and the mode switch at the
    /// returned variable converts two codes rather than two closed types.
    #[test]
    fn a_dependent_identity_checks_through_its_codes()
    {
        let mut environment = Environment::new();
        let definition = {
            let mut staging = environment.stage();
            let zero = level(LevelConstant::from(0));
            let mint = staging.arena();
            let universe = mint.value_type_universe(GroundSort::Value, zero.clone());
            let outer_code = mint.value_variable(DeBruijnIndex::from(0_u32));
            let domain = mint.value_type_element(outer_code, zero.clone());
            let inner_code = mint.value_variable(DeBruijnIndex::from(1_u32));
            let result = mint.value_type_element(inner_code, zero);
            let returner = mint.comp_type_returner(result);
            let inner = mint.comp_type_pi(domain, returner);
            let outer = mint.comp_type_pi(universe, inner);
            let declared = mint.value_type_thunk(outer);

            let returned = mint.value_variable(DeBruijnIndex::from(0_u32));
            let body = mint.computation_return(returned);
            let inner_lambda = mint.computation_lambda(body);
            let outer_lambda = mint.computation_lambda(inner_lambda);
            let thunk = mint.value_thunk(outer_lambda);
            staging.def(LevelSignature::monomorphic(), declared, thunk)
        };
        assert_eq!(
            Ok(()),
            environment.add_decl(definition).map(|_admitted| ()),
            "the dependent identity admits through the checked choke point"
        );
    }

    /// Admit `Σ (t : U (Unit → F Type)). U (Unit → F El(⟨force t ()⟩))` at
    /// the pair `(thunk λ_. return ⌜quoted⌝, thunk λ_. return ())`, with
    /// `quoted` minted by `quote`.
    ///
    /// # Specification
    /// trivial.
    fn admit_family_pair(
        quote: impl FnOnce(&mut TermArena) -> ValueTypeId
    ) -> Result<(), KernelError>
    {
        let mut environment = Environment::new();
        let definition = {
            let mut staging = environment.stage();
            let zero = level(LevelConstant::from(0));
            let mint = staging.arena();
            let unit = mint.value_type_unit();
            let universe = mint.value_type_universe(GroundSort::Value, zero.clone());
            let returns_code = mint.comp_type_returner(universe);
            let code_arrow = mint.comp_type_arrow(unit, returns_code);
            let first = mint.value_type_thunk(code_arrow);
            let family = mint.value_variable(DeBruijnIndex::from(0_u32));
            let forced = mint.computation_force(family);
            let argument = mint.value_unit();
            let call = mint.computation_application(forced, argument);
            let code = mint.value_returned(call);
            let decoded = mint.value_type_element(code, zero);
            let returns_element = mint.comp_type_returner(decoded);
            let element_arrow = mint.comp_type_arrow(unit, returns_element);
            let second = mint.value_type_thunk(element_arrow);
            let declared = mint.value_type_sigma(first, second);

            let quoted = quote(mint);
            let quoted = mint.value_quote(quoted);
            let returns_quote = mint.computation_return(quoted);
            let code_arm = mint.computation_lambda(returns_quote);
            let code_thunk = mint.value_thunk(code_arm);
            let unit_value = mint.value_unit();
            let returns_unit = mint.computation_return(unit_value);
            let element_arm = mint.computation_lambda(returns_unit);
            let element_thunk = mint.value_thunk(element_arm);
            let pair = mint.value_tuple(&[code_thunk, element_thunk]);
            staging.def(LevelSignature::monomorphic(), declared, pair)
        };
        environment.add_decl(definition).map(|_admitted| ())
    }

    /// A pair's second component checks at the fibre instantiated at its
    /// first, whose decode reads a call into that first component: the check
    /// reads the code to the quote it returns before it reads the shape the
    /// component needs (#721). A first component returning `⌜Integer⌝` keeps
    /// `()` apart, so the reading is the one that separates the two.
    #[test]
    fn a_pair_checks_at_a_fibre_decoding_a_call_into_its_first_component_721()
    {
        assert_eq!(
            Ok(()),
            admit_family_pair(TermArena::value_type_unit),
            "the fibre decodes to the unit type its first component returns"
        );
        assert!(
            matches!(
                admit_family_pair(|mint| mint.value_type_base(BaseType::Integer)),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Product,
                    ..
                })
            ),
            "a fibre decoding to the integers refuses the empty tuple"
        );
    }

    /// Admit `Π (A : U 0). inner` with the body `thunk body`, both built by
    /// `build` against the universe and the fuss-free level; the body carries
    /// every lambda, the outer binder's included.
    ///
    /// # Specification
    /// trivial.
    fn admit_polymorphic(
        build: impl FnOnce(&mut TermArena, ValueTypeId, Level) -> (CompTypeId, ComputationId)
    ) -> Result<(), KernelError>
    {
        let mut environment = Environment::new();
        let definition = {
            let mut staging = environment.stage();
            let mint = staging.arena();
            let zero = level(LevelConstant::from(0));
            let universe = mint.value_type_universe(GroundSort::Value, zero.clone());
            let (inner, body) = build(mint, universe, zero);
            let outer = mint.comp_type_pi(universe, inner);
            let declared = mint.value_type_thunk(outer);
            let thunk = mint.value_thunk(body);
            staging.def(LevelSignature::monomorphic(), declared, thunk)
        };
        environment.add_decl(definition).map(|_admitted| ())
    }

    /// `λ λ. body`.
    ///
    /// # Specification
    /// trivial.
    fn under_two(
        mint: &mut TermArena,
        body: ComputationId,
    ) -> ComputationId
    {
        let inner = mint.computation_lambda(body);
        mint.computation_lambda(inner)
    }

    /// `Π (A : U 0). El A → F (El A)`: the plain arrow's codomain names `A`
    /// at index zero, outside the arrow's own binder, so the lambda reads it
    /// one binder further out; and the same arrow returning at a second code
    /// is refused, so the reading is the one that separates the two.
    #[test]
    fn a_plain_arrow_reads_its_codomain_outside_its_binder()
    {
        let identity = admit_polymorphic(|mint, _universe, zero| {
            let code = mint.value_variable(DeBruijnIndex::from(0_u32));
            let element = mint.value_type_element(code, zero);
            let returner = mint.comp_type_returner(element);
            let inner = mint.comp_type_arrow(element, returner);
            let returned = mint.value_variable(DeBruijnIndex::from(0_u32));
            let body = mint.computation_return(returned);
            (inner, under_two(mint, body))
        });
        assert_eq!(
            Ok(()),
            identity,
            "the identity over a plain inner arrow admits"
        );

        let crossed = admit_polymorphic(|mint, universe, zero| {
            let first = mint.value_variable(DeBruijnIndex::from(1_u32));
            let domain = mint.value_type_element(first, zero.clone());
            let second = mint.value_variable(DeBruijnIndex::from(0_u32));
            let result = mint.value_type_element(second, zero);
            let returner = mint.comp_type_returner(result);
            let arrow = mint.comp_type_arrow(domain, returner);
            let inner = mint.comp_type_pi(universe, arrow);
            let returned = mint.value_variable(DeBruijnIndex::from(0_u32));
            let body = mint.computation_return(returned);
            let innermost = mint.computation_lambda(body);
            (inner, under_two(mint, innermost))
        });
        assert!(
            matches!(crossed, Err(KernelError::ValueTypeMismatch(_))),
            "a value of the first code returned at the second is refused: {crossed:?}"
        );
    }

    /// `Π (A : U 0). El A → F (El A)` with the body `y ← return x; return y`:
    /// the bind checks its body against the expected type read from under its
    /// own binder, so `A` is found two binders further out, not one.
    #[test]
    fn a_bind_reads_its_expected_type_outside_its_binder()
    {
        let admitted = admit_polymorphic(|mint, _universe, zero| {
            let code = mint.value_variable(DeBruijnIndex::from(0_u32));
            let element = mint.value_type_element(code, zero);
            let returner = mint.comp_type_returner(element);
            let inner = mint.comp_type_arrow(element, returner);
            let argument = mint.value_variable(DeBruijnIndex::from(0_u32));
            let bound = mint.computation_return(argument);
            let payload = mint.value_variable(DeBruijnIndex::from(0_u32));
            let body = mint.computation_return(payload);
            let sequence = mint.computation_bind(bound, body);
            (inner, under_two(mint, sequence))
        });
        assert_eq!(
            Ok(()),
            admitted,
            "a bind under the polymorphic identity admits"
        );
    }

    /// A bind synthesizes its body's type strengthened past its binder: a type
    /// naming a code bound outside lowers by one, and a type naming the bound
    /// value itself is refused, since no type outside the binder states it.
    #[test]
    fn a_bind_strengthens_its_type_past_its_binder()
    {
        let mut arena = TermArena::new();
        let zero = level(LevelConstant::from(0));
        let universe = arena.value_type_universe(GroundSort::Value, zero.clone());
        let code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(code, zero.clone());
        let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound = arena.computation_return(argument);
        let payload = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(payload);
        let sequence = arena.computation_bind(bound, body);
        let produced = synth_comp(&mut arena, vec![universe, element], sequence)
            .expect("a bind returning its payload synthesizes");
        let produced_type = produced.comp_type().expect("a computation type");
        let Some(&CompType::Returner(result)) = arena.comp_type(produced_type)
        else {
            panic!("a bind over a return synthesizes a returner");
        };
        let Some(&ValueType::Element { code: named, .. }) = arena.value_type(result)
        else {
            panic!("the payload's type is read off its code");
        };
        assert_eq!(
            Some(&Value::Variable(DeBruijnIndex::from(1_u32))),
            arena.value(named),
            "the payload's type names the code one binder out from the bind"
        );

        let returns_universe = arena.comp_type_returner(universe);
        let made = arena.value_type_thunk(returns_universe);
        let decoded = arena.value_variable(DeBruijnIndex::from(0_u32));
        let decoded_element = arena.value_type_element(decoded, zero);
        let picked = arena.comp_type_returner(decoded_element);
        let pick_type = arena.comp_type_pi(universe, picked);
        let pick = arena.value_type_thunk(pick_type);
        let make = arena.value_variable(DeBruijnIndex::from(1_u32));
        let bound = arena.computation_force(make);
        let picker = arena.value_variable(DeBruijnIndex::from(1_u32));
        let head = arena.computation_force(picker);
        let chosen = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_application(head, chosen);
        let dependent = arena.computation_bind(bound, body);
        let escaped = synth_comp(&mut arena, vec![made, pick], dependent);
        assert!(
            matches!(escaped, Err(KernelError::BinderEscape { .. })),
            "a type naming the bound code is refused: {escaped:?}"
        );
    }

    /// A code whose type is not the universe its own node claimed is refused,
    /// and the refusal is the ordinary checking mismatch rather than a special
    /// one — the carried level is checked exactly like every other obligation
    /// the kernel re-derives.
    #[test]
    fn a_code_that_is_not_of_its_declared_universe_refuses()
    {
        let mut environment = Environment::new();
        let axiom = {
            let mut staging = environment.stage();
            let mint = staging.arena();
            // The unit *value* is not a code: it is the empty tuple, which
            // checks only against a product, so the type read off it does not
            // form.
            let not_a_code = mint.value_unit();
            let declared = mint.value_type_element(not_a_code, level(LevelConstant::from(0)));
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert!(
            matches!(
                environment.add_decl(axiom),
                Err(KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Product,
                    ..
                })
            ),
            "a code that does not inhabit the universe its type named is refused"
        );
    }

    /// A computation decode owes its code to the computation universe, so the
    /// same telescope over the value universe is refused, and a value quote
    /// read as a computation type is minted as written and refused there.
    #[test]
    fn a_computation_decode_owes_its_code_to_the_computation_universe()
    {
        let decode_over = |environment: &mut Environment, sort: GroundSort| {
            let mut staging = environment.stage();
            let zero = level(LevelConstant::from(0));
            let mint = staging.arena();
            let universe = mint.value_type_universe(sort, zero.clone());
            let code = mint.value_variable(DeBruijnIndex::from(0_u32));
            let decoded = mint.comp_type_element(code, zero);
            let dependent = mint.comp_type_pi(universe, decoded);
            let declared = mint.value_type_thunk(dependent);
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let mut environment = Environment::new();
        let admitted = decode_over(&mut environment, GroundSort::Computation);
        assert_eq!(
            Ok(()),
            environment.add_decl(admitted).map(|_admitted| ()),
            "a binder of the computation universe decodes to a computation type"
        );
        let refused = decode_over(&mut environment, GroundSort::Value);
        assert!(
            matches!(
                environment.add_decl(refused),
                Err(KernelError::ValueTypeMismatch(_))
            ),
            "while a binder of the value universe is a code of the other family"
        );
        let crossed = {
            let mut staging = environment.stage();
            let mint = staging.arena();
            let unit = mint.value_type_unit();
            let quote = mint.value_quote(unit);
            let decoded = mint.comp_type_element(quote, level(LevelConstant::from(0)));
            let declared = mint.value_type_thunk(decoded);
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert!(
            matches!(
                environment.add_decl(crossed),
                Err(KernelError::ValueTypeMismatch(_))
            ),
            "and a value quote decoded as a computation type is not decoded on mint but refused"
        );
    }

    #[test]
    fn a_quote_synthesizes_the_universe_of_its_family()
    {
        let mut arena = TermArena::new();
        let zero = level(LevelConstant::from(0));
        let unit = arena.value_type_unit();
        let quote = arena.value_quote(unit);
        let produced = synth_value(&mut arena, Vec::new(), quote).expect("a quote synthesizes");
        assert_eq!(
            Some(&ValueType::Universe {
                sort: GroundSort::Value,
                level: zero.clone(),
            }),
            arena.value_type(produced.value_type().expect("a value type")),
            "a value type's code inhabits the value universe at the type's own level"
        );
        let returner = arena.comp_type_returner(unit);
        let quoted = arena.value_quote_computation(returner);
        let produced = synth_value(&mut arena, Vec::new(), quoted).expect("a quote synthesizes");
        assert_eq!(
            Some(&ValueType::Universe {
                sort: GroundSort::Computation,
                level: zero.clone(),
            }),
            arena.value_type(produced.value_type().expect("a value type")),
            "a computation type's code inhabits the computation universe"
        );
        let universe = arena.value_type_universe(GroundSort::Computation, zero);
        let quoted_universe = arena.value_quote(universe);
        let produced =
            synth_value(&mut arena, Vec::new(), quoted_universe).expect("a quote synthesizes");
        assert_eq!(
            Some(&ValueType::Universe {
                sort: GroundSort::Value,
                level: level(LevelConstant::from(1)),
            }),
            arena.value_type(produced.value_type().expect("a value type")),
            "and a universe of either sort is a value type one level up"
        );
    }

    /// The kernel half of smallness: a code inhabits exactly the universe at
    /// its type's level, so a code bound for a larger universe arrives as the
    /// quote of an explicit lift, and the lift's strictness is the kernel's
    /// own check.
    #[test]
    fn a_smaller_code_checks_at_a_larger_universe_only_through_a_lift()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let quote = arena.value_quote(unit);
        let one = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(1)));
        assert!(
            matches!(
                check_value(&mut arena, Vec::new(), quote, one),
                Err(KernelError::ValueTypeMismatch(_))
            ),
            "the kernel has no cumulativity, so a bare code does not check one level up"
        );
        let lifted = arena.value_type_lift(unit, level(LevelConstant::from(1)));
        let lifted_quote = arena.value_quote(lifted);
        assert_eq!(
            Ok(Produced::Checked),
            check_value(&mut arena, Vec::new(), lifted_quote, one),
            "while the code of its lift does"
        );
        let zero = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
        let sunk = arena.value_type_lift(unit, level(LevelConstant::from(0)));
        let sunk_quote = arena.value_quote(sunk);
        assert!(
            matches!(
                check_value(&mut arena, Vec::new(), sunk_quote, zero),
                Err(KernelError::UniverseViolation(_))
            ),
            "and a lift that does not strictly raise is refused inside the quote"
        );
    }

    #[test]
    fn a_computation_universe_is_no_kind_for_an_abstract_type()
    {
        let mut environment = Environment::new();
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(GroundSort::Computation, level(LevelConstant::from(0)));
            let integer = staging.arena().value_type_base(BaseType::Integer);
            staging.abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                SealScope::Closed(SealExtent::from(0_usize)),
            )
        };
        assert!(
            matches!(
                environment.add_decl(atom),
                Err(KernelError::AbstractTypeKindNotUniverse { .. })
            ),
            "a sealed atom is a value type, so only the value universe classifies it"
        );
    }

    /// Instantiating a dependent codomain at an argument is observable because
    /// a codomain can mention its binder: applying the polymorphic identity's
    /// type to a code produces the arrow over *that* code.
    #[test]
    fn an_application_instantiates_a_dependent_codomain()
    {
        let mut arena = TermArena::new();
        let zero = level(LevelConstant::from(0));
        let universe = arena.value_type_universe(GroundSort::Value, zero.clone());
        let bound_code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound_element = arena.value_type_element(bound_code, zero.clone());
        let returner = arena.comp_type_returner(bound_element);
        let dependent = arena.comp_type_pi(universe, returner);
        let head_thunk = arena.value_type_thunk(dependent);

        // The argument is an outer variable naming a code, so the instantiated
        // codomain has to name *it* rather than the vanished binder.
        let argument = arena.value_variable(DeBruijnIndex::from(1_u32));
        let head_variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let head = arena.computation_force(head_variable);
        let application = arena.computation_application(head, argument);
        let outer_universe = arena.value_type_universe(GroundSort::Value, zero);
        let produced = synth_comp(&mut arena, vec![outer_universe, head_thunk], application)
            .expect("the dependent application synthesizes");
        let synthesized = produced.comp_type().expect("a computation type");
        let Some(&CompType::Returner(result)) = arena.comp_type(synthesized)
        else {
            panic!("the instantiated codomain is a returner");
        };
        let Some(&ValueType::Element { code, .. }) = arena.value_type(result)
        else {
            panic!("over a type read off a code");
        };
        assert_eq!(
            Some(&Value::Variable(DeBruijnIndex::from(1_u32))),
            arena.value(code),
            "the codomain names the argument rather than the binder that vanished"
        );
    }

    #[test]
    fn an_axiom_checks_only_its_type()
    {
        let mut environment = Environment::new();
        let axiom = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert!(
            environment.add_decl(axiom).is_ok(),
            "an axiom claims an inhabitant and offers no body, so only its type is checked"
        );
    }

    #[test]
    fn a_sealed_atom_checks_only_its_kind()
    {
        let mut environment = Environment::new();
        let bad = {
            let mut staging = environment.stage();
            let kind = staging.arena().value_type_unit();
            staging.abstract_type(
                LevelSignature::monomorphic(),
                kind,
                kind,
                SealScope::Closed(SealExtent::from(0_usize)),
            )
        };
        assert!(
            matches!(
                environment.add_decl(bad),
                Err(KernelError::AbstractTypeKindNotUniverse { .. })
            ),
            "an atom whose kind is not a universe would leave formation with a level to infer"
        );
    }

    #[test]
    fn sealing_provenance_must_occur_in_the_declared_type()
    {
        let mut environment = Environment::new();
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
            let integer = staging.arena().value_type_base(BaseType::Integer);
            staging.abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                SealScope::Closed(SealExtent::from(0_usize)),
            )
        };
        let _admitted = environment.add_decl(atom).expect("an atom admits");
        let claiming = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.sealed_def(LevelSignature::monomorphic(), declared, body, vec![
                ConstantIndex::from(0_usize),
            ])
        };
        assert_eq!(
            Err(KernelError::SealingProvenanceNotProjected {
                atom: ConstantIndex::from(0_usize)
            }),
            environment.add_decl(claiming).map(|_admitted| ()),
            "a provenance entry with no occurrence is an unfalsifiable claim"
        );
    }

    #[test]
    fn sealing_provenance_must_be_strictly_ascending()
    {
        let mut environment = Environment::new();
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
            let integer = staging.arena().value_type_base(BaseType::Integer);
            staging.abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                SealScope::Closed(SealExtent::from(0_usize)),
            )
        };
        let _admitted = environment.add_decl(atom).expect("an atom admits");
        let repeated = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            let body = staging.arena().value_unit();
            staging.sealed_def(LevelSignature::monomorphic(), declared, body, vec![
                ConstantIndex::from(0_usize),
                ConstantIndex::from(0_usize),
            ])
        };
        assert_eq!(
            Err(KernelError::SealingProvenanceNotCanonical {
                atom: ConstantIndex::from(0_usize)
            }),
            environment.add_decl(repeated).map(|_admitted| ()),
            "canonical order is what makes the slot a set with one spelling"
        );
    }

    #[test]
    fn register_polarity_faults_fail_closed()
    {
        assert_eq!(
            Err(KernelError::CheckerRegisterFault(
                RegisterFault::ExpectedValueType
            )),
            Produced::Checked.value_type(),
            "a wiring defect refuses rather than fabricating a type"
        );
        assert_eq!(
            Err(KernelError::CheckerRegisterFault(
                RegisterFault::ExpectedCompType
            )),
            Produced::Checked.comp_type(),
            "on both polarities"
        );
    }
}

mod codata;

mod former;

mod loops;

mod recursion;

mod respect;

pub(crate) mod occurrence;

pub use occurrence::Accessibility;
pub use occurrence::Stratification;
pub use occurrence::Variance;
