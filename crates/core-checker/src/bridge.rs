//! The kernel bridge: every declaration the judgement accepts, re-derived by
//! the certified kernel.
//!
//! # The kernel is the oracle, and the bridge is untrusted
//!
//! [`readmit`] erases each accepted declaration of a [`ModuleReport`] into a
//! fresh kernel [`Environment`] and offers it through
//! [`Environment::add_decl`], the kernel's one checked entry, which re-derives
//! every typing obligation and grants the bridge no credence. A judgement that
//! agrees only with itself is blind to a fault it shares with its own oracle;
//! the kernel's checker is a separate machine over a separate vocabulary, so an
//! acceptance the kernel does not repeat is reported as [`Outcome::Rejected`]
//! rather than trusted.
//!
//! The judgement and the bridge both sit outside the trusted base. The property
//! `every_fixture_the_checker_accepts_is_readmitted` asks the kernel to repeat
//! every acceptance over the checker's own fixture set, and
//! `every_checked_function_definition_is_readmitted` over generated function
//! definitions in the shape a lowered function tail takes: a thunked chain of
//! lambdas over a chain of binds, declared at `U` over the arrows into a
//! returner. The verdict carries the body it judged, so the bridge reads the
//! report alone and never pairs a verdict with a declaration it could disagree
//! with. The alternative was a second checker over the core vocabulary, which
//! doubles what must be trusted instead of reducing it to the kernel. The
//! choice reverses only in scope: a former whose erasure needs machinery the
//! bridge lacks — a level parameter — lands as its own change with its own
//! witnesses, and the oracle stays.
//!
//! # Erasure is an id remapping
//!
//! The core vocabulary reuses the kernel's leaves — literals, base types, de
//! Bruijn indices, admission positions, levels and sorts — so erasing a node
//! mints the kernel node of the same former over its children's images. Two
//! things are remapped: a node to the node its image is in the kernel arena,
//! and a module's admission position to the position its declaration took in
//! the kernel environment, which differs once an earlier declaration did not
//! cross. Erasure covers the fragment the judgement has rules for — universes,
//! quotes, lifts, decodes and the dependent arrow among them — reads types
//! through the same views the judgement does, and refuses every other former
//! by name. Each distinct node is erased once per declaration, so the kernel
//! sees the sharing the producer built and no more.
//!
//! Element identity erases one for one: the core's path type, reflexivity,
//! returned endpoint and element transport mirror the kernel's identity
//! nodes, so each mints the kernel node of the same former over its
//! children's images, and the kernel re-derives formation at a closed
//! carrier, endpoint conversion — reading a returned endpoint by its own
//! reduction — and transport in its motive itself. The alternative, erasing
//! reflexivity to its point and a path type to the fibre the recursion
//! classifies, has the kernel re-derive a program other than the one the
//! judgement accepted; erasing a returned endpoint to the value the
//! normaliser computed for it makes that normaliser trusted.
//!
//! A function extensionality erases to the kernel's higher evaluation, which
//! has no core counterpart: per input of the coverage the judgement recorded,
//! the values the two functions return, the diagonal evidence that they
//! agree, and the machine's two traces with their anchors forgotten. The
//! functions themselves do not cross in it; the kernel regenerates the
//! coverage from the path type and replays every trace with the admitted
//! definitions unfoldable, so a recorded component the kernel would not
//! derive is refused there. The alternative, a kernel `funext` node over the
//! two functions, would have the kernel search the domain itself, which its
//! identity at a function type does not ask of it.
//!
//! The bridge builds the position map from the admissions themselves, the only
//! map that cannot disagree with the environment it indexes. The alternative to
//! remapping was keeping module positions verbatim and admitting a placeholder
//! axiom for each declaration that did not cross, which puts assumptions in the
//! audit that the ledger never owed. The choice reverses when declarations are
//! admitted into an environment shared across modules, where the environment
//! assigns positions and the map becomes its own.
//!
//! # A sealed atom binds to its kernel admission
//!
//! An abstract type crosses as the kernel's abstract-type declaration, staged
//! with its seal open, and answers [`Outcome::Data`]: it is nominal, and no
//! axiom stands at its position. Its atom then erases to the kernel atom at
//! the position the declaration took, through the same position map as a
//! constant. Once the module position its extent reaches has been processed,
//! the bridge closes the seal in the kernel, so the kernel reads the atom
//! through to its representation for exactly the declarations the judgement
//! did, and the export records the extent the kernel drew. An atom whose
//! abstract type did not cross has no kernel position and is refused by name,
//! never minted at a guessed one. The alternatives were an axiom per atom,
//! which puts an assumption in the audit for every sealed component, and a
//! sealed outcome of its own, which every consumer of the outcome would have
//! to learn while carrying the same receipt and audit; the choice reverses if
//! an atom ever needs a receipt a data declaration does not have.
//!
//! # A lift the judgement recorded is written where it stands
//!
//! A code the judgement checked at a universe above its own carries a
//! recorded lift. Its image is the kernel's explicit lift, quoted: the code
//! decoded at its own level, lifted to the universe it was checked at. The
//! kernel has no cumulativity of its own to rediscover the crossing with.
//!
//! # A code constant is unfolded at export, and every unfolding replays
//!
//! The kernel's types hold no reducible decode: a decode of a code constant
//! that crossed with a body is erased as the type its body denotes. A code
//! constant standing as a term — the argument a polymorphic function is
//! instantiated at — is erased as the quote it unfolds to, because the
//! kernel's instantiation would otherwise mint the decode of a constant that
//! no export could reach. Each unfolding is a [`Certificate`] from the
//! normaliser's conversion machine that the constant converts to its body;
//! before the declaration is staged for admission, the kernel replays every
//! certificate's trace against its own image of the constant and of the body,
//! unfolding only what the kernel itself admitted. A trace that does not
//! replay to convertible refuses the declaration as
//! [`Refusal::CertificateDeclined`], and the environment is left as it was.
//! The replayed verdicts travel on each [`Readmitted`].
//!
//! Only the argument position unfolds: a constant elsewhere in a term, a code
//! alias's own body among them, crosses as the constant, so the certificate for
//! an alias of an alias still compares the constant it names. A declined
//! certificate is `Refusal::CertificateDeclined { unfolded, reason }`, which
//! keeps the kernel's `ReplayDecline` and stays an engine fault; a
//! certification that produces no dialogue records
//! `ReplayDecline::EngineDeclined`. The kernel admits a code constant's lifted,
//! elaborated body, read back to normal form, so the constant it unfolds is the
//! constant the judgement unfolded.
//! `every_checked_universe_declaration_is_readmitted` and
//! `every_readmission_certificate_replays` ask this of generated modules of
//! universe declarations, codes, aliases and lifts;
//! `a_code_constant_argument_unfolds_at_export` asks it of a polymorphic
//! identity instantiated at a code alias.
//!
//! The alternatives were giving the kernel cumulativity and static δ-reduction
//! in its own conversion, which widens the trusted base for what a replayed
//! trace already certifies; trusting the normaliser's readback unreplayed,
//! which leaves the exported declaration related to its source by an unchecked
//! step; and unfolding every constant in term position, which rewrites a code
//! alias's body to its target so that the alias's certificate compares the
//! wrong pair. The certificate records one step for the reason the judgement's
//! does; one trace per code replaces the steps when the machine decides codes
//! under quotes, and the argument unfolding goes when the kernel's conversion
//! unfolds what it admitted.
//!
//! # A static operator crosses as its static normal form
//!
//! The kernel has no static lambda and reduces no static application, so the
//! bridge hands it neither. A definition whose type is a static Pi is
//! [`Outcome::Static`]: the kernel is offered nothing, and its body stays for
//! the instances that name it. Every static application the bridge erases is
//! reduced — a saturated instance of a static definition by δ then β, a
//! static lambda's redex by β — and the reduct, minted into the core arena,
//! is erased in its place, until the term is a static normal form: a rigid
//! head, an operator a hole owes or a variable, applied to normal arguments,
//! which is the kernel's neutral static application. Each step is a
//! [`Certificate`] the kernel replays, one per distinct instance a declaration
//! meets, naming what it unfolded ([`Replayed::unfolded`]) and the content
//! digest of the instance it reduced ([`Replayed::redex`]). A static step
//! names operators the kernel's terms cannot hold, so each is numbered as a
//! constant above the module's positions and given its body, verbatim, for
//! that replay alone; a static lambda that reaches a binder outside itself
//! stands for no closed constant and is refused as
//! [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::StaticLambda`]. The
//! unfolding of a definition that crossed replays as the kernel's own δ-step
//! at the constant it admitted, closed on the two normal forms, because the
//! body it admitted is already normal.
//!
//! A hole of static Pi type is an opaque operator and crosses as an axiom. One
//! certificate is kept per distinct instance a declaration meets, keyed by what
//! the step unfolded and the content digest of the kernel's image of its redex:
//! the same instance written twice is replayed once, and one definition at two
//! instances is replayed twice.
//! `one_static_definition_at_two_instances_records_two_certificates` and
//! `every_checked_static_declaration_is_readmitted` assert it, the second over
//! the relative monad's operators written with and without the static spelling;
//! `a_static_lambda_crosses_only_as_a_closed_operator` asserts both arms of the
//! open-lambda refusal. The definition's normal body and the normaliser's trace
//! differ because the trace walks the unnormalized body and names operators the
//! normal form no longer holds.
//!
//! Each step is certified and replayed on its own, by rules the kernel already
//! has, because the machine produces no trace under a quote. The alternatives
//! were static reduction in the kernel's conversion, which widens the trusted
//! base for what a replayed step certifies; a certificate per occurrence rather
//! than per instance, which replays one derivation once per mention; and
//! refusing static definitions at the bridge, which leaves every declaration
//! that names one uncrossed. The per-step certificates give way to one trace
//! per code when the machine decides codes under quotes; the open-lambda
//! refusal lifts with lambda lifting over the binders the lambda reaches, which
//! numbers it as an operator closed over them.
//!
//! # An uncompleted signature enters as an axiom
//!
//! An owed hole is a declaration with a type and no body, which is exactly the
//! kernel's bodiless declaration: it is staged through [`Staging::axiom`], and
//! the hole never becomes a term. A hole the judgement refused — in synthesis
//! position, where its refusal names the hole, or under a signature that did
//! not form — crosses as nothing. An axiom's constant is rigid: no decode of
//! it unfolds.
//!
//! The kernel reports the assumption in the audit of the hole and of every
//! declaration that reads it. A hole here owes a formed type, so the kernel can
//! assume it; a hole in synthesis position has no type to assume, and the
//! judgement has refused it already. The alternatives were refusing a module
//! until its ledger is empty, which withholds the kernel's verdict on every
//! complete declaration until the last hole is filled, and a placeholder term
//! in the hole, which the kernel would check as if the author had written it.
//!
//! # A mark crosses as nothing
//!
//! A refused declaration carries its refusal as its mark, and the bridge offers
//! the kernel nothing for it: not its body, which the kernel may accept where
//! the judgement did not, and not its signature as an axiom, which would put an
//! assumption in the artifact's audit that the ledger never owed. A later
//! declaration reading it is [`Refusal::Withheld`], located at the reference.
//!
//! A reader of a marked declaration is withheld even when it checked against
//! that declaration's stated contract. The alternative was offering a marked
//! declaration's signature as an axiom so its dependents cross, which makes the
//! audit disagree with the ledger; the choice reverses only together with the
//! audit's.
//!
//! # A term hole is refused where it stands, and a mark is erased
//!
//! The kernel admits no incomplete term. A term hole the judgement accepted
//! is [`Refusal::Hole`], located at the hole's node and, through the
//! [`Readmitted`] row it stands on, at the declaration's origin; the unknown
//! type, which only an incomplete elaboration mints, is [`Refusal::Unknown`].
//! Both are user absences: the author has a hole left to fill, and filling it
//! is what lets the declaration cross. A mark is erased to the term it marks,
//! as Hazelnut's mark erasure recovers the unmarked program (Omar et al.,
//! POPL 2017, doi:10.1145/3009837.3009900): the kernel re-derives what was
//! marked, so a mark can never make it accept what it would refuse. The
//! kernel's own input invariant is unchanged; it never sees a hole, a mark or
//! the unknown type.
//!
//! The differential witness
//! `a_hole_is_refused_where_it_stands_and_its_filling_is_admitted` shows, in
//! one artifact, the refusal, the same declaration with its hole filled
//! admitted as a definition, a mark around a good body admitted, and a mark
//! around a bad one rejected by the kernel. The alternative was an axiom per
//! term hole, abstracted over the hole's context, so a declaration with a hole
//! would cross and its audit would name the assumption; it is chosen when an
//! artifact must cross before its holes are filled. A term mark is not a
//! refused declaration, whose outcome is [`Outcome::Marked`] and which crosses
//! as nothing.
//!
//! # The audit exposes source and runtime assumptions
//!
//! The kernel's audit names every axiom a declaration transitively rests on.
//! The artifact unions those reports. Without native operations, these are
//! exactly the owed source holes. Native rows additionally cross as named,
//! typed opaque axioms; their dependents retain those assumptions in the audit.
//! The kernel checks the native signatures but executes no host arithmetic.
//!
//! [`ArtifactAudit`] unions the kernel's reports over the source module, an
//! axiom's own position included. Without native operations its axioms are
//! exactly the positions the owed holes took, and it is empty exactly when the
//! ledger is; with native operations it also records their typed runtime
//! assumptions, even when no source hole is owed. The union adds no kernel-side
//! audit mechanism and never hides a native assumption, so sealedness and
//! runtime trust are separate observations. The alternatives were gating
//! readmission on an empty ledger, which hides the kernel's verdict on complete
//! declarations behind incomplete ones, and an artifact audit inside the
//! kernel, which widens the trusted surface for a fold any caller can compute.
//! The choice reverses when a publishing or dependency boundary arrives: a
//! module offered to another then needs its audit empty, and that boundary
//! gates on this report.
//!
//! # The bridge owns its staging, so it owns the rollback
//!
//! Each declaration is erased into a staging session the bridge opened, and a
//! refused erasure or a declined certificate discards it; a rejected admission
//! is truncated by the kernel's choke point. A declaration that does not cross
//! leaves the environment as it found it.
//!
//! `a_refused_declaration_leaves_the_environment_unchanged` asserts it by the
//! kernel arena's watermark against the same module without the refused
//! declaration. The alternative was leaving partially erased content in the
//! arena as unreachable nodes, which every later reader of the arena would have
//! to step over; there is no reversal while staging has an explicit discard.
//!
//! # One machine, no recursion
//!
//! Erasure is a machine of goals and frames over an explicit stack. A node is
//! open while its frame waits, so a node that is its own descendant —
//! constructible only from ids of another arena — is refused instead of erased
//! forever.
//!
//! Erasure charges no allowance: each distinct node is erased once and refused
//! if revisited while open, so a run is bounded by the arena it reads. The
//! alternative was charging the judgement's `CheckBudget`, which bounds work
//! the memo bounds already; the choice reverses if erasure ever erases one node
//! under two contexts, as a level instantiation would.
//!
//! # A split crosses as its projection binds
//!
//! The kernel has no split. Erasure mints the split's reduct into the core
//! arena and erases it in the split's place: one bind per component, component
//! zero outermost, each of the projection of the scrutinee shifted past the
//! binds before it, ending in the body, so the body reads the components at the
//! indices the split gave them and a split of no components crosses as its
//! body. The kernel then judges the projections and binds by its own rules.
//! `tests::native_formers::a_split_crosses_as_its_projection_binds`
//! crosses a split of a variable pair, which a wrong shift would project from
//! its first component, a split of a closed triple and a split of the unit.
//!
//! The alternatives were a kernel split, which widens the trusted base by a
//! binder former the projection already expresses, and refusing the split at
//! the bridge, which leaves every program that discards a unit uncrossed. A
//! split of a neutral compares in the normaliser by its arity and bodies, and
//! those verdicts are not replayed: the kernel never sees a split, only the
//! binds it judges itself. The choice reverses if the kernel gains a split of
//! its own.
//!
//! A split under a motive does not cross as binds: the binds' body would
//! answer the motive at the scrutinee, not at the pair of its components, so
//! the projections would not type it. It crosses as the kernel's dependent
//! split (`SigmaSplit`, tag `0x6B`), scrutinee, motive and body each erased in
//! turn, and the kernel judges the motive at the scrutinee itself.
//! `bridge::tests::a_dependent_pair_and_its_identity_are_readmitted` crosses
//! one under a motive that reads its scrutinee's first projection.
//!
//! # The export carries the producer's names
//!
//! [`Readmission::export`] encodes the environment the kernel built: each
//! declaration that crossed, in kernel admission order, marked checked and
//! carrying the `StructuredName` the producer gives its module position. The
//! bridge keeps each declaration as it staged it, because the kernel's
//! environment exposes an admitted declaration's audit and not its content, and
//! names it only when it is written out. A flattened structure member is
//! therefore exported as one declaration named by its segments, a declaration
//! that did not cross is not in the artifact, and every reference in it is
//! still the kernel position its target took; the name is never read.
//!
//! The alternatives were names on the checker's `Declaration`, which makes the
//! judgement carry a surface fact it never reads, and a name table beside the
//! artifact, which leaves the exported members nameless to anything reading the
//! artifact alone. The choice reverses if a renamed module must export a
//! byte-identical artifact; the names then move to that side table and the
//! export writes none.
//!
//! [`Staging::axiom`]: gandr_kernel_core::Staging::axiom

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::TraceNode;
use gandr_core_term::BinderDepth;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::SplitMotive;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_core::AxiomReport;
use gandr_kernel_core::CheckedId;
use gandr_kernel_core::EngineClaim;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_core::KernelVerdict;
use gandr_kernel_core::ParameterCount;
use gandr_kernel_core::Presentations;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_core::ReplayDecline;
use gandr_kernel_core::ReplayNode;
use gandr_kernel_core::ReplaySides;
use gandr_kernel_core::Unfoldable;
use gandr_kernel_core::Unfoldings;
use gandr_kernel_core::content_digest;
use gandr_kernel_core::read_step;
use gandr_kernel_core::replay;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Declaration as KernelDeclaration;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::EndpointDialogues;
use gandr_kernel_term::EvaluationComponent;
use gandr_kernel_term::EvaluationDialogues;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::QuantifiedStep;
use gandr_kernel_term::RelatedEndpoints;
use gandr_kernel_term::SealScope;
use gandr_kernel_term::Seam;
use gandr_kernel_term::StructuredName;
use gandr_kernel_term::Summand;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::encode;
use quenchant_shape::shape::Maybe;

use crate::code::Certificate;
use crate::code::CodeDefinitions;
use crate::code::Derivation;
use crate::code::EndpointRelation;
use crate::code::Lift;
use crate::code::Reflexivity;
use crate::code::Unfolded;
use crate::code::loose_reach;
use crate::code::unfolding;
use crate::declaration::AbstractType;
use crate::declaration::OriginToken;
use crate::funext::Funext;
use crate::funext::Step as FunextStep;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;
use crate::view::CompTypeView;

mod native;

use crate::view::FragmentRefusal;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

quenchant_shape::reason_enum! {
    /// Why a certificate was not replayed again.
    mod replay_entry {
        /// The reason no verdict was recorded.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// An earlier certificate of the declaration unfolded the same
            /// step at an instance of the same content.
            Met,
        }
    }
}

/// The bridge's refusal for a fault the judgement's step machinery reported.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a dangling node stays a dangling node, naming the same node;
///   every other refusal is a machine invariant, since a step over a judged
///   arena meets nothing else.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two arms, separated by a dangling node and a refusal of
///   another variant, each asserted exactly.
/// - witness: `bridge::tests::a_step_fault_keeps_only_a_dangling_node`
#[spec(ensures: |ret| match refusal {
    | CheckRefusal::DanglingNode { node } => ret == Refusal::DanglingNode { node },
    | _ => ret == Refusal::MachineInvariant,
})]
fn fault(refusal: CheckRefusal) -> Refusal
{
    match refusal {
        CheckRefusal::DanglingNode { node } => Refusal::DanglingNode { node },
        CheckRefusal::NotADataType(_)
        | CheckRefusal::DataKindNotUniverse(_)
        | CheckRefusal::DataFieldLevel { .. }
        | CheckRefusal::RuleNotPresentable { .. }
        | CheckRefusal::RuleNotRespected { .. }
        | CheckRefusal::NotApart { .. }
        | CheckRefusal::LoopNotRespected { .. }
        | CheckRefusal::LoopUndecided { .. }
        | CheckRefusal::AbstractKindNotUniverse(_)
        | CheckRefusal::RepresentationAboveKind { .. }
        | CheckRefusal::NotAnAbstractType(_)
        | CheckRefusal::SealSiteRepeated(_)
        | CheckRefusal::DataArgumentArity(_)
        | CheckRefusal::UnknownConstructor { .. }
        | CheckRefusal::ConstructorArity(_)
        | CheckRefusal::NonExhaustiveDataCase(_)
        | CheckRefusal::AbsentRecordField(_)
        | CheckRefusal::AbsentTupleComponent(_)
        | CheckRefusal::MissingRecordField { .. }
        | CheckRefusal::UnknownOperation { .. }
        | CheckRefusal::HandlerCoverage { .. }
        | CheckRefusal::ShiftWithoutReset { .. }
        | CheckRefusal::DependentStack { .. }
        | CheckRefusal::PathCode(_)
        | CheckRefusal::EndpointMismatch { .. }
        | CheckRefusal::CompoundEndpoint { .. }
        | CheckRefusal::FunextUnsupported { .. }
        | CheckRefusal::PointwiseDistinct { .. }
        | CheckRefusal::EquivUnsupported { .. }
        | CheckRefusal::UncertifiedStratum { .. }
        | CheckRefusal::RoundTripDistinct { .. }
        | CheckRefusal::NotOver { .. }
        | CheckRefusal::UaUncertified { .. }
        | CheckRefusal::UaInequivalent { .. }
        | CheckRefusal::TypeMismatch(_)
        | CheckRefusal::EffectSignatureConflict { .. }
        | CheckRefusal::ShapeMismatch { .. }
        | CheckRefusal::NotSynthesisable { .. }
        | CheckRefusal::UnknownConstant { .. }
        | CheckRefusal::OutOfFragment { .. }
        | CheckRefusal::UnboundIndex { .. }
        | CheckRefusal::BudgetExceeded { .. }
        | CheckRefusal::AdmissionOrder { .. }
        | CheckRefusal::MachineInvariant
        | CheckRefusal::SortMismatch { .. }
        | CheckRefusal::LevelMismatch { .. }
        | CheckRefusal::DependentBind { .. }
        | CheckRefusal::Undecided { .. }
        | CheckRefusal::FamilyArity { .. }
        | CheckRefusal::FamilyArgumentClassifier { .. }
        | CheckRefusal::StaticLambdaArgument { .. }
        | CheckRefusal::StaticClassifierExpected { .. }
        | CheckRefusal::NegativeOccurrence(_)
        | CheckRefusal::NestedOccurrence(_)
        | CheckRefusal::IndexOccurrence(_)
        | CheckRefusal::NonUniformOccurrence(_)
        | CheckRefusal::CrossBlockReference { .. }
        | CheckRefusal::StageNotBelow { .. }
        | CheckRefusal::SessionMismatch { .. }
        | CheckRefusal::Linearity { .. }
        | CheckRefusal::UnenclosedRun { .. }
        | CheckRefusal::CapabilityForged { .. }
        | CheckRefusal::CapabilityAmplified(_)
        | CheckRefusal::CapabilityOutsideAuthority { .. }
        | CheckRefusal::CapabilityEscaped { .. }
        | CheckRefusal::CapabilityConsumable(_)
        | CheckRefusal::CapabilityUngranted { .. }
        | CheckRefusal::SessionNotEquivalent { .. }
        | CheckRefusal::SessionNotSubtype { .. }
        | CheckRefusal::SessionCodeExpected { .. }
        | CheckRefusal::NonCovariantMotive { .. }
        | CheckRefusal::RideUnsupported { .. }
        | CheckRefusal::RunNotAdmitted { .. }
        | CheckRefusal::ForwardUnsupported { .. }
        | CheckRefusal::Boundary { .. }
        | CheckRefusal::Access { .. }
        | CheckRefusal::Located { .. } => Refusal::MachineInvariant,
    }
}

/// Why the bridge offered the kernel nothing for a declaration the judgement
/// accepted.
///
/// # Specification
/// - provides: a located reason the declaration cannot cross. A declined
///   certificate retains both its unfolded step and the kernel's exact
///   [`ReplayDecline`]; certification without a dialogue records
///   [`ReplayDecline::EngineDeclined`]. Its [`Self::classify`] result is
///   [`FailureClass::EngineFault`] for every decline reason.
///
/// # Adequacy
/// - hypothesis: L3 — corrupted certificates retain their replay refusal on the
///   declaration instead of becoming an accepted definition.
/// - witness: `bridge::tests::a_declining_certificate_faults_the_declaration`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Refusal
{
    /// A nominal head names a declaration that did not cross.
    WithheldData
    {
        /// The source nominal type.
        at: ValueTypeId,
        /// Its source declaration identity.
        constant: ConstantIndex,
    },
    /// A constant names a declaration of the module that did not cross into
    /// the kernel: one the judgement refused, or one the bridge or the kernel
    /// turned away. The declaration it names carries its own reason.
    Withheld
    {
        /// The constant value.
        at: ValueId,
        /// The module position it names.
        constant: ConstantIndex,
    },
    /// A former the fragment has no rule for.
    OutOfFragment
    {
        /// The node carrying the former.
        at: CoreNode,
        /// The former.
        former: UnadmittedFormer,
    },
    /// A session type, a session action or an endpoint: the kernel has no
    /// channels, so a declaration that names one stays on the checker's side,
    /// as a declaration whose former the kernel lacks does.
    Session
    {
        /// The node.
        at: CoreNode,
    },
    /// A located form, a handle or capability type, or a world: the kernel has
    /// no worlds, so a declaration that names one stays on the checker's side,
    /// as one naming a session does.
    Located
    {
        /// The node.
        at: CoreNode,
    },
    /// An id names no node of the arena: the caller paired the report with
    /// another arena.
    DanglingNode
    {
        /// The id.
        node: CoreNode,
    },
    /// A node is its own descendant, which only ids taken from another arena
    /// can build.
    Cyclic
    {
        /// The node met again while its own erasure waited.
        node: CoreNode,
    },
    /// A step of static reduction was not certified: the normaliser's
    /// conversion did not answer convertible, or the kernel's replay of its
    /// trace did not re-derive it.
    CertificateDeclined
    {
        /// What the step unfolded.
        unfolded: Unfolded,
        /// The replay's reason, or no dialogue when certification produced
        /// none.
        reason: ReplayDecline,
    },
    /// The machine's own bookkeeping disagreed with itself: a frame received
    /// an image of another family than it awaits. Unreachable while the
    /// machine's own pushes are the only source of frames; reported rather
    /// than asserted.
    MachineInvariant,
    /// A term hole: the kernel admits no incomplete term.
    Hole
    {
        /// The hole's node.
        at: CoreNode,
        /// The hole.
        hole: HoleId,
    },
    /// The unknown type, which only an incomplete elaboration mints.
    Unknown
    {
        /// The type's node.
        at: CoreNode,
    },
}

impl Refusal
{
    /// Whose fact this refusal records.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: the class is a function of the variant alone. A withheld
    ///   constant is malformed source, since the declaration it names was
    ///   turned away for a reason its own entry reports; a former outside the
    ///   fragment and a session are unrepresentable; a dangling id, a cyclic
    ///   node, a declined certificate and a machine invariant are engine
    ///   faults, because a judged term from the judged arena holds none of them
    ///   and an unfolding holds by definition; a term hole and the unknown type
    ///   are user absences.
    /// - provides: the fact a report groups by, in the same four classes the
    ///   judgement's refusals answer to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a withheld definition, an unsupported former and a
    ///   machine fault remain distinct at readmission rather than acquiring a
    ///   kernel receipt or becoming an obligation.
    /// - witness: `bridge::tests::a_body_naming_a_withheld_declaration_is_refused`
    /// - witness: `bridge::tests::the_machine_faults_are_refused_exactly`
    /// - witness: `bridge::tests::a_hole_is_refused_where_it_stands_and_its_filling_is_admitted`
    #[spec(ensures: |ret| match *self {
        | Self::Withheld { .. } | Self::WithheldData { .. } => matches!(ret, FailureClass::MalformedSource),
        | Self::OutOfFragment { .. } | Self::Session { .. } | Self::Located { .. } => matches!(ret, FailureClass::Unrepresentable),
        | Self::DanglingNode { .. } | Self::Cyclic { .. }
            | Self::CertificateDeclined { .. } | Self::MachineInvariant => matches!(ret, FailureClass::EngineFault),
        | Self::Hole { .. } | Self::Unknown { .. } => matches!(ret, FailureClass::UserAbsence),
    })]
    #[inline]
    #[must_use]
    pub const fn classify(&self) -> FailureClass
    {
        match *self {
            Self::Withheld { .. } | Self::WithheldData { .. } => FailureClass::MalformedSource,
            Self::OutOfFragment { .. } | Self::Session { .. } | Self::Located { .. } => {
                FailureClass::Unrepresentable
            },
            Self::DanglingNode { .. }
            | Self::Cyclic { .. }
            | Self::CertificateDeclined { .. }
            | Self::MachineInvariant => FailureClass::EngineFault,
            Self::Hole { .. } | Self::Unknown { .. } => FailureClass::UserAbsence,
        }
    }
}

impl From<FragmentRefusal> for Refusal
{
    /// The bridge's refusal for a type node the fragment's views cannot read.
    ///
    /// # Specification
    /// - ensures: each variant becomes the [`Refusal`] variant of the same
    ///   name, with the same payload.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unsupported type formers and a missing type id expose
    ///   the exact refusal and payload; wrong family or diagnostic substitution
    ///   changes the observed erasure, within those fragment boundaries.
    /// - witness: `bridge::tests::every_former_outside_the_fragment_is_refused_by_name`
    /// - witness: `bridge::tests::the_machine_faults_are_refused_exactly`
    #[spec(ensures: |ret| match refusal {
        | FragmentRefusal::DanglingNode { node } => ret == Self::DanglingNode { node },
        | FragmentRefusal::OutOfFragment { at, former } => ret == Self::OutOfFragment { at, former },
    })]
    #[inline]
    fn from(refusal: FragmentRefusal) -> Self
    {
        match refusal {
            FragmentRefusal::DanglingNode { node } => Self::DanglingNode { node },
            FragmentRefusal::OutOfFragment { at, former } => Self::OutOfFragment { at, former },
        }
    }
}

/// What became of one declaration at the kernel boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome
{
    /// The kernel admitted a nominal declaration, not an axiom: a native data
    /// declaration, or a sealed abstract type — its atom — at the kernel
    /// position every later reference to the atom erases to.
    Data
    {
        /// The declaration's kernel identity.
        admitted: CheckedId,
        /// Dependencies of its parameter and constructor signatures, or of its
        /// kind and representation.
        audit: AxiomReport,
    },
    /// The kernel admitted the declaration as a definition.
    Defined
    {
        /// The kernel's receipt, naming the position the declaration took.
        admitted: CheckedId,
        /// The axioms the definition transitively rests on.
        audit: AxiomReport,
    },
    /// The kernel admitted the uncompleted signature as an axiom.
    Assumed
    {
        /// The kernel's receipt, naming the position the axiom took.
        admitted: CheckedId,
        /// The audit of the axiom, which names the axiom itself.
        audit: AxiomReport,
    },
    /// The judgement refused the declaration: the refusal is its mark, and the
    /// kernel was offered nothing.
    Marked(CheckRefusal),
    /// The judgement suspended the declaration on owed holes: nothing is
    /// offered until a fill resumes it, and a reader of it is withheld.
    Suspended,
    /// The declaration is static: a type operator, classified by a static
    /// Pi, whose body normalizes away at every use, or a world, whose
    /// identity no kernel term carries. The kernel was offered nothing; each
    /// instance of an operator a later declaration reaches is reduced, and its
    /// certificate replayed, there.
    Static,
    /// The bridge refused to offer the declaration.
    Refused(Refusal),
    /// The kernel rejected the erased declaration: the judgement accepted what
    /// the kernel does not, the disagreement the oracle exists to report.
    Rejected(KernelError),
}

/// One certificate the kernel replayed for a declaration: what its step
/// unfolded, the content of the instance it fired at, and the kernel's
/// verdict on its trace.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Replayed
{
    /// What the step unfolded: a definition by its module position, or a
    /// static lambda by its node.
    unfolded: Unfolded,
    /// The kernel content digest of the instance's image, read as it stands.
    redex: ContentDigest,
    /// The kernel's verdict on the certificate's trace.
    verdict: KernelVerdict,
}

impl Replayed
{
    /// What the step unfolded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unfolded(&self) -> Unfolded
    {
        self.unfolded
    }

    /// The kernel content digest of the instance the step fired at: with
    /// [`Self::unfolded`], the certificate's address within its declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn redex(&self) -> ContentDigest
    {
        self.redex
    }

    /// The kernel's verdict on the certificate's trace.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn verdict(&self) -> KernelVerdict
    {
        self.verdict
    }
}

/// One declaration's outcome, beside the position and origin the judgement
/// echoed and the certificates its erasure replayed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Readmitted
{
    /// The declaration's module position.
    constant: ConstantIndex,
    /// The declaration's origin, echoed back.
    origin: OriginToken,
    /// What became of it.
    outcome: Outcome,
    /// The certificates the kernel replayed before the declaration was
    /// offered, in the order the erasure met the unfoldings.
    certificates: Vec<Replayed>,
}

impl Readmitted
{
    /// The declaration's module position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The declaration's origin: the location a driver resolves a refusal to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(&self) -> OriginToken
    {
        self.origin
    }

    /// What became of the declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outcome(&self) -> &Outcome
    {
        &self.outcome
    }

    /// The certificates the kernel replayed for the declaration, each
    /// convertible unless the outcome is [`Refusal::CertificateDeclined`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn certificates(&self) -> &[Replayed]
    {
        &self.certificates
    }
}

/// What a readmitted artifact rests on: the union of its declarations'
/// audits.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ArtifactAudit
{
    /// The kernel positions of the axioms any declaration rests on, ascending.
    axioms: Vec<ConstantIndex>,
    /// The kernel positions of the unchecked admissions any declaration rests
    /// on, ascending.
    unchecked: Vec<ConstantIndex>,
}

impl ArtifactAudit
{
    /// The union of the audits of every declaration the kernel admitted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the axioms and the unchecked admissions named by the audit of
    ///   any [`Outcome::Defined`] or [`Outcome::Assumed`] entry, each ascending
    ///   and without repetition; entries that did not cross contribute nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty ledgers, repeated uses of axioms and refused
    ///   entries expose the exact sorted dependency union; missing, duplicated
    ///   or spurious axioms change that audit. No unchecked admission is
    ///   introduced.
    /// - witness: `bridge::tests::an_empty_ledger_readmits_an_artifact_resting_on_no_axiom`
    /// - witness: `bridge::tests::each_owed_hole_is_an_axiom_of_the_artifact`
    #[spec(ensures: |ret| ret.axioms.iter().zip(ret.axioms.iter().skip(1)).all(|(a,b)| a < b)
        && ret.unchecked.iter().zip(ret.unchecked.iter().skip(1)).all(|(a,b)| a < b)
        && readmitted.iter().all(|entry| match entry.outcome {
            | Outcome::Defined { ref audit, .. } | Outcome::Data { ref audit, .. } | Outcome::Assumed { ref audit, .. } =>
                audit.axioms().iter().all(|at| ret.axioms.binary_search(at).is_ok())
                && audit.unchecked_admissions().iter().all(|at| ret.unchecked.binary_search(at).is_ok()),
            | _ => true,
        })
        && ret.axioms.len() <= readmitted.iter().map(|entry| match entry.outcome {
            | Outcome::Defined { ref audit, .. } | Outcome::Data { ref audit, .. } | Outcome::Assumed { ref audit, .. } => audit.axioms().len(),
            | _ => 0,
        }).sum::<usize>()
        && ret.unchecked.len() <= readmitted.iter().map(|entry| match entry.outcome {
            | Outcome::Defined { ref audit, .. } | Outcome::Data { ref audit, .. } | Outcome::Assumed { ref audit, .. } => audit.unchecked_admissions().len(),
            | _ => 0,
        }).sum::<usize>())]
    fn of(readmitted: &[Readmitted]) -> Self
    {
        let mut axioms = BTreeSet::new();
        let mut unchecked = BTreeSet::new();
        for entry in readmitted {
            if let Outcome::Defined { ref audit, .. }
            | Outcome::Data { ref audit, .. }
            | Outcome::Assumed { ref audit, .. } = entry.outcome
            {
                axioms.extend(audit.axioms().iter().copied());
                unchecked.extend(audit.unchecked_admissions().iter().copied());
            }
        }
        Self {
            axioms: axioms.into_iter().collect(),
            unchecked: unchecked.into_iter().collect(),
        }
    }

    /// The kernel positions of the axioms the artifact rests on, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn axioms(&self) -> &[ConstantIndex]
    {
        &self.axioms
    }

    /// The kernel positions of the unchecked admissions the artifact rests on,
    /// ascending. The bridge admits nothing unchecked.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unchecked_admissions(&self) -> &[ConstantIndex]
    {
        &self.unchecked
    }
}

/// A module's readmission: the kernel environment it built, one outcome per
/// declaration, the artifact's audit, and the declarations the kernel admitted.
#[derive(Clone, Debug)]
pub struct Readmission
{
    /// The environment every crossing declaration was admitted into.
    environment: Environment,
    /// One entry per judged declaration, in the report's order.
    readmitted: Vec<Readmitted>,
    /// The union of the admitted declarations' audits.
    audit: ArtifactAudit,
    /// The declarations the kernel admitted, as they were staged, in kernel
    /// admission order.
    admitted: Vec<KernelDeclaration>,
}

impl Readmission
{
    /// The environment every crossing declaration was admitted into, and
    /// nothing else.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn environment(&self) -> &Environment
    {
        &self.environment
    }

    /// One entry per judged declaration, in the report's order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn readmitted(&self) -> &[Readmitted]
    {
        &self.readmitted
    }

    /// What the artifact rests on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn audit(&self) -> &ArtifactAudit
    {
        &self.audit
    }

    /// The artifact of every declaration that crossed, each under the
    /// structured name `names` gives its module position.
    ///
    /// # Specification
    /// - requires: `names` is keyed by module position, the positions the
    ///   judged declarations carry; each crossed position indexes `admitted`.
    /// - ensures: the canonical encoding of the environment's arena and the
    ///   admitted declarations, in kernel admission order, each marked checked
    ///   and carrying the name `names` holds at its module position, or no name
    ///   where it holds none. A declaration that did not cross is not in the
    ///   artifact, and a reference in it reads the kernel position its target
    ///   took, never a name.
    /// - provides: the export a reader decodes: a flattened member is named by
    ///   its segments, and is still referred to by position.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module whose first declaration is marked, whose
    ///   later ones read earlier ones, and whose last has no name, decoded and
    ///   asserted at each declaration's exact name and the kernel position each
    ///   reference reads; a nominal declaration decoded under its own name.
    /// - witness: `bridge::tests::an_export_names_each_crossed_declaration_at_its_position`
    /// - witness: `tests::native_formers::data_declarations_and_refusals_agree_with_kernel`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every readmitted entry and every admitted declaration once; the check walks the readmitted entries three times"
        )
    )]
    #[spec(
        requires: self.readmitted.iter().all(|entry| match entry.outcome {
            | Outcome::Defined { admitted, .. } | Outcome::Assumed { admitted, .. } | Outcome::Data { admitted, .. } => self.admitted.get(usize::from(admitted.position())).is_some(),
            | _ => true,
        }),
        captures: [before = names.len(), named = self.readmitted.iter().filter(|entry|
            matches!(entry.outcome, Outcome::Defined { .. } | Outcome::Assumed { .. } | Outcome::Data { .. }) && names.contains_key(&entry.constant)).count()],
        ensures: before.checked_sub(names.len()) == Some(named) && self.readmitted.iter().all(|entry|
            !matches!(entry.outcome, Outcome::Defined { .. } | Outcome::Assumed { .. } | Outcome::Data { .. }) || !names.contains_key(&entry.constant)),
    )]
    #[inline]
    #[must_use]
    pub fn export(
        &self,
        mut names: BTreeMap<ConstantIndex, StructuredName>,
    ) -> EncodedArtifact
    {
        let mut kernel_names = BTreeMap::new();
        for entry in &self.readmitted {
            if let Outcome::Defined { admitted, .. }
            | Outcome::Assumed { admitted, .. }
            | Outcome::Data { admitted, .. } = entry.outcome
            {
                kernel_names.insert(
                    admitted.position(),
                    names.remove(&entry.constant).unwrap_or_default(),
                );
            }
        }
        let marked: Vec<_> = self
            .admitted
            .iter()
            .enumerate()
            .map(|(position, declaration)| {
                let mut declaration = declaration.clone();
                if let Some(name) = kernel_names.remove(&ConstantIndex::from(position)) {
                    declaration = declaration.named(name);
                }
                MarkedDeclaration::new(AdmissionMark::Checked, declaration)
            })
            .collect();

        encode(self.environment.arena(), &marked)
    }
}

/// Re-derive every declaration `report` accepted in a fresh kernel
/// environment.
///
/// # Specification
/// - requires: `report` was judged over `arena`; a report paired with another
///   arena is admissible input, its unresolvable ids refused rather than read.
/// - ensures: one [`Readmitted`] per judged declaration, in order, echoing its
///   position and origin. A checked declaration is offered as a definition at
///   its declared type, an unsigned one at its synthesised type, and an owed
///   hole as an axiom at the type it owes; each crosses as [`Outcome::Defined`]
///   or [`Outcome::Assumed`] when the kernel admits it. A definition whose type
///   is a static Pi is [`Outcome::Static`]: the kernel is offered nothing, and
///   its body stays for later instances to reduce. A refused declaration is
///   [`Outcome::Marked`] with its refusal, and the kernel is offered nothing
///   for it. An offer whose erasure refuses, or one of whose certificates the
///   kernel does not replay to convertible, is [`Outcome::Refused`], one the
///   kernel rejects [`Outcome::Rejected`], and each leaves the environment as
///   it was. A constant naming a declaration that crossed is erased to the
///   kernel position that declaration took; a code recorded with a lift is
///   erased to the kernel's lift of its decode; a decode of a constant that
///   crossed as a definition is erased as the decode of its body; a static
///   application at a saturated instance of a static definition or at a static
///   lambda is erased as its reduct, minted into `arena`, until none remains —
///   each step certified and replayed once per distinct instance.
/// - provides: the declarations that crossed, the native signatures present in
///   the arena, and an audit exposing every source-hole or native assumption on
///   which an admitted source declaration depends.
/// - fails: never; every declaration gets an outcome.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the kernel is the external oracle: every declaration
///   the judgement accepts over the generated well-typed and free fixture sets
///   and over generated universe and static declarations crosses, every
///   certificate a generated code constant's readmission records replays, and
///   the artifact's axioms agree with the ledger in the pure fragment. Native
///   signatures additionally expose named runtime assumptions. The L3 residues
///   are one artifact holding a marked body and a marked signed hole the kernel
///   alone admits, a hole in synthesis position and a reference to a marked
///   declaration, beside a checked and an owed positive control; the position
///   remapping, separated by a module whose later references would misresolve
///   under any other map; the rollback, separated by a refusal met after part
///   of a body was minted; a sorted universe, a lifted code and a code
///   constant's unfolding, each readmitted; one static definition at two
///   instances, two certificates; and a certificate whose trace was emptied,
///   refused.
/// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `bridge::tests::every_checked_function_definition_is_readmitted`
/// - witness: `bridge::tests::every_checked_universe_declaration_is_readmitted`
/// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
/// - witness: `bridge::tests::every_readmission_certificate_replays`
/// - witness: `bridge::tests::marks_and_holes_are_refused_beside_their_positive_controls`
/// - witness: `bridge::tests::an_empty_ledger_readmits_an_artifact_resting_on_no_axiom`
/// - witness: `bridge::tests::native_operations_cross_as_audited_assumptions`
/// - witness: `bridge::tests::each_owed_hole_is_an_axiom_of_the_artifact`
/// - witness: `bridge::tests::a_constant_resolves_to_its_readmitted_position`
/// - witness: `bridge::tests::a_refused_declaration_leaves_the_environment_unchanged`
/// - witness: `bridge::tests::a_lowered_value_definition_admits`
/// - witness: `bridge::tests::a_lowered_computation_definition_admits`
/// - witness: `bridge::tests::a_constant_reference_across_declarations_admits`
/// - witness: `bridge::tests::a_sorted_universe_readmits_at_its_level`
/// - witness: `bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
/// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
/// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
/// - witness: `bridge::tests::a_declining_certificate_faults_the_declaration`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.readmitted().len() == report.judged().len())]
pub fn readmit(
    arena: &mut CoreArena,
    report: &ModuleReport,
) -> Readmission
{
    readmit_with(arena, report, |certificate| certificate)
}

/// [`readmit`], with every certificate passed through `vouch` before the
/// kernel replays it.
///
/// # Specification
/// - requires: as [`readmit`].
/// - ensures: as [`readmit`], with each certificate replaced by what `vouch`
///   returns for it; the identity gives [`readmit`] exactly.
/// - provides: the seam a test corrupts a certificate through, to observe the
///   kernel decline it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`readmit`], with the seam separated by the identity
///   and by a certificate whose trace was emptied, refused.
/// - witness: `bridge::tests::every_readmission_certificate_replays`
/// - witness: `bridge::tests::a_declining_certificate_faults_the_declaration`
#[spec(ensures: |ret| ret.readmitted().len() == report.judged().len())]
fn readmit_with<Vouch>(
    arena: &mut CoreArena,
    report: &ModuleReport,
    vouch: Vouch,
) -> Readmission
where
    Vouch: Fn(Certificate) -> Certificate,
{
    let mut environment = Environment::new();
    let mut positions = Positions::default();
    let seeded = positions.seed_native(&mut environment, arena);
    let mut readmitted = Vec::with_capacity(report.judged().len());
    let source = Source {
        lifts: report.lifts(),
        funexts: report.funexts(),
        equivalences: report.equivalences(),
        flows: report.flows(),
        directed: report.directed(),
        reflexivities: report.reflexivities(),
        relations: report.relations(),
        laws: report.laws(),
        natives: report.natives(),
        definitions: report.definitions(),
    };
    let judged_all = report.judged();
    let mut index = 0_usize;
    while let Some(judged) = judged_all.get(index) {
        index = index.saturating_add(1);
        if let Err(ref error) = seeded {
            readmitted.push(Readmitted {
                constant: judged.constant(),
                origin: judged.origin(),
                outcome: Outcome::Rejected(error.clone()),
                certificates: Vec::new(),
            });
            continue;
        }
        let constant = judged.constant();
        // A data declaration whose fields name later declarations leads the
        // mutual block they reach, which crosses whole.
        let block = block_offers(
            arena,
            report,
            source,
            judged_all
                .get(index.saturating_sub(1) ..)
                .unwrap_or_default(),
        );
        if !block.is_empty() {
            let crossed = cross_block(
                &mut environment,
                arena,
                source,
                &mut positions,
                &block,
                &vouch,
            );
            for (member, (outcome, certificates)) in judged_all
                .get(index.saturating_sub(1) ..)
                .unwrap_or_default()
                .iter()
                .zip(crossed)
            {
                readmitted.push(Readmitted {
                    constant: member.constant(),
                    origin: member.origin(),
                    outcome,
                    certificates,
                });
            }
            index = index.saturating_sub(1).saturating_add(block.len());
            if let Some(last) = judged_all.get(index.saturating_sub(1)) {
                close_seals(
                    &mut environment,
                    &mut positions,
                    &mut readmitted,
                    last.constant(),
                );
            }
            continue;
        }
        let definition = match judged.verdict() {
            Verdict::Checked { declared, body, .. } => Some((declared.id(), body)),
            Verdict::Synthesised { body, synthesised } => Some((synthesised.produced().id(), body)),
            Verdict::Data | Verdict::Owed(_) | Verdict::Suspended(_) | Verdict::Refused(_) => None,
        };
        // A type operator — a definition whose type views as a static Pi — stays
        // on the checker's side; a type the view refuses is not one, and its
        // own erasure refuses it.
        let (outcome, certificates) = match (definition, judged.verdict()) {
            (None, Verdict::Data) => {
                let offer = match (
                    report.data_signatures().get(&constant),
                    report.abstract_types().get(&constant),
                ) {
                    (Some(signature), _) => Offer::Data(signature),
                    (None, Some(&declared)) => Offer::Abstract(declared),
                    (None, None) if report.worlds().contains(&constant) => {
                        readmitted.push(Readmitted {
                            constant,
                            origin: judged.origin(),
                            outcome: Outcome::Static,
                            certificates: Vec::new(),
                        });
                        continue;
                    },
                    (None, None) => {
                        readmitted.push(Readmitted {
                            constant,
                            origin: judged.origin(),
                            outcome: Outcome::Refused(Refusal::MachineInvariant),
                            certificates: Vec::new(),
                        });
                        continue;
                    },
                };
                cross(
                    &mut environment,
                    arena,
                    source,
                    &mut positions,
                    constant,
                    offer,
                    &vouch,
                )
            },
            (Some((declared, body)), _)
                if matches!(
                    value_type_view(arena, declared),
                    Ok(ValueTypeView::StaticPi { .. })
                ) =>
            {
                let defined = source.definitions.get(&constant).copied().unwrap_or(body);
                positions.definitions.define(constant, defined);
                (Outcome::Static, Vec::new())
            },
            (Some((declared, body)), _) => cross(
                &mut environment,
                arena,
                source,
                &mut positions,
                constant,
                Offer::Definition {
                    declared,
                    body,
                    relations: source.relations.get(&constant).map_or(&[], Vec::as_slice),
                    laws: source.laws.get(&constant).map_or(&[], Vec::as_slice),
                },
                &vouch,
            ),
            (None, Verdict::Owed(entry)) => cross(
                &mut environment,
                arena,
                source,
                &mut positions,
                constant,
                Offer::Axiom {
                    declared: entry.absence().declared().id(),
                },
                &vouch,
            ),
            (None, Verdict::Refused(refusal)) => (Outcome::Marked(refusal), Vec::new()),
            (None, Verdict::Suspended(_)) => (Outcome::Suspended, Vec::new()),
            (None, Verdict::Checked { .. } | Verdict::Synthesised { .. }) => {
                (Outcome::Refused(Refusal::MachineInvariant), Vec::new())
            },
        };
        if let (&Outcome::Data { admitted, .. }, Some(declared)) =
            (&outcome, report.abstract_types().get(&constant))
        {
            positions.open.push(OpenSeal {
                end: ConstantIndex::from(
                    usize::from(constant).saturating_add(usize::from(declared.extent())),
                ),
                atom: admitted,
                readmitted: readmitted.len(),
            });
        }
        readmitted.push(Readmitted {
            constant,
            origin: judged.origin(),
            outcome,
            certificates,
        });
        close_seals(&mut environment, &mut positions, &mut readmitted, constant);
    }
    close_seals(
        &mut environment,
        &mut positions,
        &mut readmitted,
        ConstantIndex::from(usize::MAX),
    );
    let audit = ArtifactAudit::of(&readmitted);
    Readmission {
        environment,
        readmitted,
        audit,
        admitted: positions.exports,
    }
}

/// The offers of the mutual block the first of `run`, the judged declarations
/// from it on, leads: its run of data declarations and the definitions after
/// them, up to the furthest position the run's fields reach, when that is past
/// the leader and every member crosses; nothing otherwise.
///
/// # Specification
/// - requires: `run` is a suffix of `report`'s judged declarations, which are
///   in module order.
/// - ensures: empty unless the first of `run` is data whose fields reach a
///   later position; then one offer per position from it to the reached end,
///   each data declaration of the leading run offered at its signature and each
///   later member a crossing definition — and empty when any member is not one,
///   so the declarations cross one by one and the kernel withholds what names a
///   later one.
/// - provides: the measurement the bridge crosses a block by, the checker's
///   schedule's and the kernel replay's.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a lone family offers nothing, and a universe naming its
///   decoder offers the two.
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
#[spec(ensures: |ret| ret.is_empty() || ret.len() >= 2)]
fn block_offers<'report>(
    arena: &CoreArena,
    report: &'report ModuleReport,
    source: Source<'report>,
    run: &'report [crate::module::Judged],
) -> Vec<(ConstantIndex, Offer<'report>)>
{
    let Some(leader) = run.first()
    else {
        return Vec::new();
    };
    let first = usize::from(leader.constant());
    let mut end = first.saturating_add(1);
    let mut families = true;
    let mut members = Vec::new();
    for member in run {
        let constant = member.constant();
        if usize::from(constant) >= end {
            break;
        }
        let offer = match (member.verdict(), report.data_signatures().get(&constant)) {
            (Verdict::Data, Some(signature)) if families => {
                end = end.max(usize::from(crate::occurrence::reach(
                    arena, constant, signature,
                )));
                Offer::Data(signature)
            },
            (Verdict::Checked { declared, body, .. }, _)
                if !matches!(
                    value_type_view(arena, declared.id()),
                    Ok(ValueTypeView::StaticPi { .. })
                ) =>
            {
                families = false;
                Offer::Definition {
                    declared: declared.id(),
                    body,
                    relations: source.relations.get(&constant).map_or(&[], Vec::as_slice),
                    laws: source.laws.get(&constant).map_or(&[], Vec::as_slice),
                }
            },
            (Verdict::Synthesised { body, synthesised }, _)
                if !matches!(
                    value_type_view(arena, synthesised.produced().id()),
                    Ok(ValueTypeView::StaticPi { .. })
                ) =>
            {
                families = false;
                Offer::Definition {
                    declared: synthesised.produced().id(),
                    body,
                    relations: source.relations.get(&constant).map_or(&[], Vec::as_slice),
                    laws: source.laws.get(&constant).map_or(&[], Vec::as_slice),
                }
            },
            (
                Verdict::Data
                | Verdict::Checked { .. }
                | Verdict::Synthesised { .. }
                | Verdict::Owed(_)
                | Verdict::Suspended(_)
                | Verdict::Refused(_),
                _,
            ) => return Vec::new(),
        };
        if usize::from(constant) != first.saturating_add(members.len()) {
            return Vec::new();
        }
        members.push((constant, offer));
    }
    if members.len() < 2 || members.len() != end.saturating_sub(first) {
        return Vec::new();
    }
    members
}

/// An atom the kernel admitted with its seal open, and where the seal ends.
#[derive(Clone, Copy, Debug)]
struct OpenSeal
{
    /// The last module position the seal reaches.
    end: ConstantIndex,
    /// The atom's kernel admission.
    atom: CheckedId,
    /// Its index among the readmitted declarations.
    readmitted: usize,
}

/// Close, in minting order, every open seal that ends at or before the module
/// position `reached`.
///
/// # Specification
/// - requires: every open seal names an atom the kernel admitted
///   [`SealScope::Open`] and has not closed, with its readmitted index; the
///   exports are indexed by kernel position.
/// - ensures: no open seal ends at or before `reached`; each one closed is
///   closed in the kernel, so later admissions read its atom as rigid, and its
///   export carries the extent the kernel drew, so a replay of the artifact
///   seals it at the same place. A seal the kernel refuses to close turns its
///   atom's outcome into the rejection.
/// - fails: never; a refusal is recorded, as above.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a sealed module's export replays with the atom closed
///   over its members, and a client past the seal reads the atom rigid.
/// - witness: `bridge::tests::a_bound_sealed_atom_lowers_to_the_kernel_atom`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the body partitions every open seal once; the check reads each it kept once"
    )
)]
#[spec(ensures: positions.open.iter().all(|seal| seal.end > reached))]
fn close_seals(
    environment: &mut Environment,
    positions: &mut Positions,
    readmitted: &mut [Readmitted],
    reached: ConstantIndex,
)
{
    let (closing, open): (Vec<OpenSeal>, Vec<OpenSeal>) = core::mem::take(&mut positions.open)
        .into_iter()
        .partition(|seal| seal.end <= reached);
    positions.open = open;
    for seal in closing {
        match environment.seal(seal.atom) {
            Ok(extent) => {
                if let Some(export) = positions.exports.get_mut(usize::from(seal.atom.position())) {
                    *export = export.clone().closed(extent);
                }
            },
            Err(error) => {
                if let Some(entry) = readmitted.get_mut(seal.readmitted) {
                    entry.outcome = Outcome::Rejected(error);
                }
            },
        }
    }
}

/// What every erasure reads besides the arena and the positions: the lifts,
/// function extensionalities, universe equivalences, reflexivities and endpoint
/// relations the judgement recorded and the bodies it defined its constants
/// as.
#[derive(Clone, Copy, Debug)]
struct Source<'source>
{
    /// The codes the judgement checked above their own universe, by node.
    lifts: &'source BTreeMap<ValueId, Lift>,
    /// The function extensionalities the judgement decided, by node.
    funexts: &'source BTreeMap<ValueId, Funext>,
    /// The universe equivalences the judgement decided, by node.
    equivalences: &'source BTreeMap<ValueId, crate::equiv::Equivalence>,
    /// The session statements the judgement decided, by node.
    flows: &'source BTreeMap<ValueId, crate::flow::Statement>,
    /// The forward and function flows the judgement decided, by node.
    directed: &'source BTreeMap<ValueId, crate::forward::Directed>,
    /// The reflexivities the judgement checked against a path type, by node.
    reflexivities: &'source BTreeMap<ValueId, Reflexivity>,
    /// The path endpoint pairs each accepted declaration's conversions
    /// related, by position.
    relations: &'source BTreeMap<ConstantIndex, Vec<EndpointRelation>>,
    /// The laws each lawful declaration's folds rest on, by position.
    laws: &'source BTreeMap<ConstantIndex, Vec<ConstantIndex>>,
    /// The native path each univalence statement the judgement decided
    /// derives, and each path product it judged elaborates to, by node.
    natives: &'source BTreeMap<ValueId, ValueId>,
    /// The body each accepted declaration defines its constant as, elaborated
    /// to the universe it was declared at.
    definitions: &'source BTreeMap<ConstantIndex, ValueId>,
}

/// What an accepted declaration offers the kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Offer<'signature>
{
    /// A native nominal declaration's checked signature.
    Data(&'signature gandr_core_term::DataSignature),
    /// A sealed abstract type: its kind and its representation.
    Abstract(AbstractType),
    /// A definition: a body at the type it was judged at.
    Definition
    {
        /// The type the body was judged at.
        declared: ValueTypeId,
        /// The body.
        body: ValueId,
        /// The path endpoint pairs its conversions related.
        relations: &'signature [EndpointRelation],
        /// The laws its folds rest on, by module position.
        laws: &'signature [ConstantIndex],
    },
    /// An axiom: the type an owed hole owes.
    Axiom
    {
        /// The type owed.
        declared: ValueTypeId,
    },
}

/// An offer's image in the kernel arena.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Erased
{
    /// A native signature's images, owned once by the staging declaration.
    Data
    {
        /// The parameter telescope.
        parameters: Vec<gandr_kernel_term::ValueTypeId>,
        /// Constructor fields under the parameter telescope.
        constructors: Vec<Vec<gandr_kernel_term::ValueTypeId>>,
        /// The positive universe.
        kind: gandr_kernel_term::ValueTypeId,
    },
    /// A definition's declared type and body.
    Definition
    {
        /// The declared type's image.
        declared: gandr_kernel_term::ValueTypeId,
        /// The body's image.
        body: gandr_kernel_term::ValueId,
        /// The related endpoint pairs' images, each with its dialogue.
        related: Vec<RelatedEndpoints>,
        /// The kernel positions of the laws its folds rest on.
        laws: Vec<ConstantIndex>,
    },
    /// An axiom's declared type.
    Axiom
    {
        /// The declared type's image.
        declared: gandr_kernel_term::ValueTypeId,
    },
    /// A sealed abstract type's kind and representation.
    Abstract
    {
        /// The kind's image.
        kind: gandr_kernel_term::ValueTypeId,
        /// The representation's image.
        representation: gandr_kernel_term::ValueTypeId,
    },
}

/// Erase `offer`, the declaration at `constant`, into a staging session of
/// `environment`, replay its certificates, and admit it.
///
/// # Specification
/// - requires: `positions` holds the kernel position, and for a definition the
///   bodies, of every module declaration that crossed so far, the bodies of the
///   static definitions before it, and the declarations they crossed as, in
///   kernel admission order.
/// - ensures: the offer erased into one staging session, every reduct its
///   static normal form needed minted into `arena`; every distinct certificate
///   the erasure collected, passed through `vouch`, replayed by the kernel in
///   that session against its static operators, numbered from past the
///   environment's last position; and, when each replays to convertible, the
///   offer admitted: [`Outcome::Defined`] for a definition,
///   [`Outcome::Assumed`] for an axiom and [`Outcome::Data`] for a nominal
///   declaration — an abstract type staged with its seal open — each with the
///   kernel's receipt and audit, when the kernel admits it, recorded in
///   `positions` with its staged declaration appended to the exports. A refused
///   erasure or a declined certificate discards the session and a rejection is
///   truncated by the kernel, so the environment is as it was on every outcome
///   but an admission. The replayed verdicts are returned beside the outcome.
/// - fails: never; a refusal is [`Outcome::Refused`] and a rejection
///   [`Outcome::Rejected`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — definitions, owed axioms, refused erasures and declined
///   certificates expose exact outcomes, receipts and environment contents;
///   partial publication or confusing an axiom with a definition changes them.
/// - witness: `bridge::tests::a_lowered_value_definition_admits`
/// - witness: `bridge::tests::each_owed_hole_is_an_axiom_of_the_artifact`
/// - witness: `bridge::tests::a_declining_certificate_faults_the_declaration`
/// - witness: `bridge::tests::a_refused_declaration_leaves_the_environment_unchanged`
#[spec(
    captures: [entries = environment.entries().len(), exports = positions.exports.len(), crossed = positions.admitted.len()],
    ensures: |ret| match ret.0 {
        | Outcome::Defined { admitted, .. } | Outcome::Data { admitted, .. } | Outcome::Assumed { admitted, .. } =>
            environment.entries().len().checked_sub(entries) == Some(1)
            && positions.exports.len().checked_sub(exports) == Some(1)
            && positions.admitted.len().checked_sub(crossed) == Some(1)
            && positions.admitted.get(&constant) == Some(&admitted.position())
            && matches!((offer, &ret.0), (Offer::Definition { .. }, &Outcome::Defined { .. }) | (Offer::Data(_) | Offer::Abstract(_), &Outcome::Data { .. }) | (Offer::Axiom { .. }, &Outcome::Assumed { .. }))
            && ret.1.iter().all(|replay| replay.verdict() == KernelVerdict::Convertible),
        | Outcome::Refused(_) | Outcome::Rejected(_) =>
            environment.entries().len() == entries
            && positions.exports.len() == exports && positions.admitted.len() == crossed,
        | Outcome::Marked(_) | Outcome::Suspended | Outcome::Static => false,
    },
)]
fn cross<Vouch>(
    environment: &mut Environment,
    arena: &mut CoreArena,
    source: Source<'_>,
    positions: &mut Positions,
    constant: ConstantIndex,
    offer: Offer<'_>,
    vouch: &Vouch,
) -> (Outcome, Vec<Replayed>)
where
    Vouch: Fn(Certificate) -> Certificate,
{
    let next = ConstantIndex::from(environment.entries().len());
    let base = ConstantIndex::from(usize::from(next).saturating_add(1));
    let own = [(constant, next)];
    let crossing: &[(ConstantIndex, ConstantIndex)] = match offer {
        Offer::Data(_) => &own,
        Offer::Abstract(_) | Offer::Definition { .. } | Offer::Axiom { .. } => &[],
    };
    let staged = match stage(
        environment,
        arena,
        (source, &*positions),
        offer,
        vouch,
        (crossing, base),
    ) {
        Ok(staged) => staged,
        Err(refused) => return refused,
    };
    let staged_as = staged.declaration.declaration().clone();
    let admitted = match environment.add_decl(staged.declaration) {
        Ok(admitted) => admitted,
        Err(error) => return (Outcome::Rejected(error), staged.replayed),
    };
    let outcome = settle(
        environment,
        source,
        positions,
        (constant, offer, staged.image),
        (staged_as, admitted),
    );
    (outcome, staged.replayed)
}

/// One offer erased and staged, not yet admitted.
struct Staged
{
    /// The staged declaration.
    declaration: gandr_kernel_core::StagedDeclaration,
    /// A definition's body image.
    image: Maybe<gandr_kernel_term::ValueId, staged::Absent>,
    /// The replayed verdicts of its certificates.
    replayed: Vec<Replayed>,
}

quenchant_shape::reason_enum! {
    /// Why a staged offer carries no body image.
    mod staged {
        /// The offer is no definition.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// A nominal declaration or an axiom has no body.
            Bodiless,
        }
    }
}

/// Erase `offer`, the declaration at `constant`, into a staging session of
/// `environment` and replay its certificates, beside the members of
/// `crossing`, numbering static operators from `base`.
///
/// # Specification
/// - requires: as [`cross`]; `crossing` names each member crossing with this
///   one at the kernel position it is about to take, and `base` is past all of
///   them.
/// - ensures: the staged declaration, its body's image and the replayed
///   verdicts when the erasure and every certificate succeed; otherwise the
///   session discarded and the refusal with the verdicts replayed so far.
/// - fails: never; a refusal is returned as its outcome.
/// - panics: none.
///
/// # Errors
/// The refused outcome, with the verdicts replayed before it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`cross`] and [`cross_block`].
/// - witness: `bridge::tests::a_lowered_value_definition_admits`
/// - witness: `bridge::tests::a_declining_certificate_faults_the_declaration`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|refused| matches!(refused.0, Outcome::Refused(_))))]
fn stage<Vouch>(
    environment: &mut Environment,
    arena: &mut CoreArena,
    (source, positions): (Source<'_>, &Positions),
    offer: Offer<'_>,
    vouch: &Vouch,
    (crossing, base): (&[(ConstantIndex, ConstantIndex)], ConstantIndex),
) -> Result<Staged, (Outcome, Vec<Replayed>)>
where
    Vouch: Fn(Certificate) -> Certificate,
{
    let next = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let erased = {
        let mut erasure = Erasure::new(arena, source, positions, base).crossing_block(crossing);
        erasure
            .offer(staging.arena(), offer)
            .map_err(|refusal| (refusal, Vec::new()))
            .and_then(|erased| {
                erasure
                    .replay_certificates(staging.arena(), vouch)
                    .map(|replayed| (erased, replayed))
            })
    };
    let (erased, replayed) = match erased {
        Ok(crossing) => crossing,
        Err((refusal, replayed)) => {
            staging.discard();
            return Err((Outcome::Refused(refusal), replayed));
        },
    };
    let image = match erased {
        Erased::Definition { ref body, .. } => Maybe::Present(*body),
        Erased::Data { .. } | Erased::Axiom { .. } | Erased::Abstract { .. } => {
            Maybe::Absent(staged::Absent::Bodiless)
        },
    };
    let declaration = match erased {
        Erased::Data {
            parameters,
            constructors,
            kind,
        } => {
            let staged = staging.data(
                LevelSignature::monomorphic(),
                parameters,
                constructors,
                kind,
            );
            // The rules name constructor tags and pattern variables only, so
            // they cross unchanged. A type of words names its sort by
            // position, so the sort crosses at its kernel position; a sort
            // that did not cross is named by the words' own position, which
            // the kernel refuses as no earlier sort.
            match offer {
                Offer::Data(signature) => {
                    let presentation = signature.presentation();
                    staged.presented(presentation.cells().map_or_else(
                        || presentation.clone(),
                        |cells| {
                            let sort = positions
                                .admitted
                                .get(&cells.sort())
                                .copied()
                                .unwrap_or(next);
                            gandr_kernel_term::Presentation::new(presentation.rules().to_vec())
                                .carrying(gandr_kernel_term::FreeCells::new(
                                    sort,
                                    cells.cells().to_vec(),
                                ))
                        },
                    ))
                },
                Offer::Abstract(_) | Offer::Definition { .. } | Offer::Axiom { .. } => staged,
            }
        },
        Erased::Definition {
            declared,
            body,
            related,
            laws,
        } => staging
            .def(LevelSignature::monomorphic(), declared, body)
            .relating(related)
            .lawful(laws),
        Erased::Axiom { declared } => staging.axiom(LevelSignature::monomorphic(), declared),
        Erased::Abstract {
            kind,
            representation,
        } => staging.abstract_type(
            LevelSignature::monomorphic(),
            kind,
            representation,
            SealScope::Open,
        ),
    };
    Ok(Staged {
        declaration,
        image,
        replayed,
    })
}

/// Record an offer the kernel admitted: its export, its position and, for a
/// definition, its bodies on either side.
///
/// # Specification
/// - requires: `admitted` is the kernel's receipt for `staged_as`, the
///   declaration `offer` staged at `constant`.
/// - ensures: the export appended, the position declared or defined, and the
///   outcome naming the receipt and its audit: [`Outcome::Defined`] for a
///   definition, [`Outcome::Data`] for a nominal declaration and
///   [`Outcome::Assumed`] otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`cross`].
/// - witness: `bridge::tests::a_lowered_value_definition_admits`
/// - witness: `bridge::tests::each_owed_hole_is_an_axiom_of_the_artifact`
#[spec(ensures: |ret| matches!(ret, Outcome::Defined { .. } | Outcome::Data { .. } | Outcome::Assumed { .. }))]
fn settle(
    environment: &Environment,
    source: Source<'_>,
    positions: &mut Positions,
    (constant, offer, image): (
        ConstantIndex,
        Offer<'_>,
        Maybe<gandr_kernel_term::ValueId, staged::Absent>,
    ),
    (staged_as, admitted): (KernelDeclaration, CheckedId),
) -> Outcome
{
    positions.exports.push(staged_as);
    let audit = environment.audit(admitted);
    match (offer, image) {
        (Offer::Definition { body, .. }, Maybe::Present(image)) => {
            let defined = source.definitions.get(&constant).copied().unwrap_or(body);
            positions.define(constant, admitted, defined, image);
            Outcome::Defined { admitted, audit }
        },
        (Offer::Data(signature), _) => {
            positions.declare(constant, admitted);
            positions.definitions.present(constant, signature);
            if !signature.presentation().rules().is_empty() {
                positions.presentations = Presentations::of(environment.entries());
            }
            Outcome::Data { admitted, audit }
        },
        (Offer::Abstract(_), _) => {
            positions.declare(constant, admitted);
            Outcome::Data { admitted, audit }
        },
        (Offer::Axiom { .. } | Offer::Definition { .. }, _) => {
            positions.declare(constant, admitted);
            Outcome::Assumed { admitted, audit }
        },
    }
}

/// Erase the members of a mutual block, each at the kernel position it is
/// about to take, replay their certificates, and admit them as one block.
///
/// # Specification
/// - requires: as [`cross`]; `members` are the block's offers in order, every
///   one crossing.
/// - ensures: one outcome per member, in order: each admitted as [`cross`]
///   records an admission when the kernel admits the block, and otherwise every
///   member sharing the refusal or rejection of the member that failed, the
///   environment as it was.
/// - fails: never; a refusal is [`Outcome::Refused`] and a rejection
///   [`Outcome::Rejected`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a universe and its decoder cross and are admitted
///   together; a block one member of which is refused crosses nothing.
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
#[spec(captures: entries = environment.entries().len(), ensures: |ret| ret.len() == members.len()
    && (ret.iter().all(|crossed| matches!(crossed.0, Outcome::Defined { .. } | Outcome::Data { .. } | Outcome::Assumed { .. }))
        || environment.entries().len() == entries))]
fn cross_block<Vouch>(
    environment: &mut Environment,
    arena: &mut CoreArena,
    source: Source<'_>,
    positions: &mut Positions,
    members: &[(ConstantIndex, Offer<'_>)],
    vouch: &Vouch,
) -> Vec<(Outcome, Vec<Replayed>)>
where
    Vouch: Fn(Certificate) -> Certificate,
{
    let next = environment.entries().len();
    let crossing = members
        .iter()
        .enumerate()
        .map(|(offset, &(constant, _))| {
            (constant, ConstantIndex::from(next.saturating_add(offset)))
        })
        .collect::<Vec<_>>();
    let base = ConstantIndex::from(next.saturating_add(members.len()));
    let mut staged: Vec<Staged> = Vec::with_capacity(members.len());
    for &(constant, offer) in members {
        match stage(
            environment,
            arena,
            (source, &*positions),
            offer,
            vouch,
            (&crossing, base),
        ) {
            Ok(member) => staged.push(member),
            Err((outcome, replayed)) => {
                // The block crosses whole or not at all: what staged is
                // abandoned, latest first, and every member shares the
                // refusal.
                for member in staged.into_iter().rev() {
                    environment.abandon(member.declaration);
                }
                return members
                    .iter()
                    .map(|&(member, _)| {
                        if member == constant {
                            (outcome.clone(), replayed.clone())
                        }
                        else {
                            (outcome.clone(), Vec::new())
                        }
                    })
                    .collect();
            },
        }
    }
    let exported = staged
        .iter()
        .map(|member| member.declaration.declaration().clone())
        .collect::<Vec<_>>();
    let mut images = Vec::with_capacity(staged.len());
    let mut declarations = Vec::with_capacity(staged.len());
    for member in staged {
        images.push((member.image, member.replayed));
        declarations.push(member.declaration);
    }
    match environment.add_block(declarations) {
        Ok(admitted) => members
            .iter()
            .zip(exported)
            .zip(admitted)
            .zip(images)
            .map(
                |(((&(constant, offer), staged_as), admitted), (image, replayed))| {
                    let outcome = settle(
                        environment,
                        source,
                        positions,
                        (constant, offer, image),
                        (staged_as, admitted),
                    );
                    (outcome, replayed)
                },
            )
            .collect(),
        Err(error) => images
            .into_iter()
            .map(|(_, replayed)| (Outcome::Rejected(error.clone()), replayed))
            .collect(),
    }
}

/// The kernel position each module declaration that crossed took, and the
/// bodies the crossed and the static definitions unfold to on either side.
#[derive(Clone, Debug, Default)]
struct Positions
{
    /// Native rows cross as explicitly audited, typed opaque constants.
    native: BTreeMap<gandr_core_term::primitive::Primitive, ConstantIndex>,
    /// Module position to kernel position.
    admitted: BTreeMap<ConstantIndex, ConstantIndex>,
    /// The crossed and the static definitions' core bodies, by module
    /// position: what a decode of a code naming one, or an instance of one,
    /// reduces to, and what its certificate is asked over.
    definitions: CodeDefinitions,
    /// The crossed definitions' kernel bodies, by kernel position: what the
    /// kernel's replay may unfold.
    unfoldings: BTreeMap<ConstantIndex, gandr_kernel_term::ValueId>,
    /// The declarations the kernel admitted, as they were staged — an
    /// abstract type's scope closed once its seal ends — in kernel admission
    /// order.
    exports: Vec<KernelDeclaration>,
    /// The atoms admitted whose seals have not ended, in minting order.
    open: Vec<OpenSeal>,
    /// The presented types the kernel admitted, whose terms its replay reads
    /// by their normal forms.
    presentations: Presentations,
}

impl Positions
{
    /// Admit the used native signatures without adding an evaluator to the
    /// kernel.
    ///
    /// # Specification
    /// - ensures: each distinct row has one checked axiom of its table
    ///   signature.
    /// - fails: propagates a kernel rejection; no unchecked admission is used.
    /// - panics: none.
    ///
    /// # Errors
    /// A kernel rejection of a native signature.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — native operations cross and retain their named
    ///   assumptions in a decoded artifact.
    /// - witness: `bridge::tests::native_operations_cross_as_audited_assumptions`
    #[spec(ensures: |ret| ret.is_err() || core.native_primitives().all(|primitive| self.native.contains_key(&primitive)))]
    fn seed_native(
        &mut self,
        environment: &mut Environment,
        core: &CoreArena,
    ) -> Result<(), KernelError>
    {
        use gandr_core_term::primitive::PrimitiveType;
        let primitives: BTreeSet<_> = core.native_primitives().collect();
        for primitive in primitives {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let classifier = |arena: &mut TermArena, ty: PrimitiveType| match ty {
                PrimitiveType::Integer => arena.value_type_base(BaseType::Integer),
                PrimitiveType::Boolean => {
                    let unit = arena.value_type_unit();
                    arena.value_type_sum(&[unit, unit])
                },
            };
            let result = classifier(arena, primitive.result());
            let mut computation = arena.comp_type_returner(result);
            for &argument in primitive.arguments().iter().rev() {
                let domain = classifier(arena, argument);
                computation = arena.comp_type_arrow(domain, computation);
            }
            let declared = arena.value_type_thunk(computation);
            let staged = staging.axiom(LevelSignature::monomorphic(), declared);
            let name = StructuredName::from(
                primitive
                    .name()
                    .as_ref()
                    .split('.')
                    .filter_map(|segment| gandr_kernel_term::NameSegment::from_text(segment.into()))
                    .collect::<Vec<_>>(),
            );
            let declaration = staged.declaration().clone().named(name);
            let admitted = environment.add_decl(staged)?;
            self.native.insert(primitive, admitted.position());
            self.exports.push(declaration);
        }
        Ok(())
    }
    /// Record that the module definition at `constant`, of core body `body`,
    /// crossed as `admitted` with kernel body `image`.
    ///
    /// # Specification
    /// - requires: `constant` follows every prior crossed or static definition;
    ///   `admitted` is a fresh kernel position.
    /// - ensures: the crossed table answers `admitted`'s position for
    ///   `constant`; a decode of a code naming `constant` unfolds to `body`;
    ///   the kernel's replay may unfold `admitted` to `image`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — references to prior definitions and a defined code
    ///   expose the remapped position and replayed unfolding; wrong-side bodies
    ///   or retaining module positions change admission and certificate replay.
    /// - witness: `bridge::tests::a_constant_resolves_to_its_readmitted_position`
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    #[spec(
        requires: self.admitted.last_key_value().is_none_or(|(&last, _)| last < constant)
            && !self.unfoldings.contains_key(&admitted.position()),
        ensures: self.admitted.get(&constant) == Some(&admitted.position())
            && self.unfoldings.get(&admitted.position()) == Some(&image),
    )]
    fn define(
        &mut self,
        constant: ConstantIndex,
        admitted: CheckedId,
        body: ValueId,
        image: gandr_kernel_term::ValueId,
    )
    {
        self.admitted.insert(constant, admitted.position());
        self.definitions.define(constant, body);
        self.unfoldings.insert(admitted.position(), image);
    }

    /// Record a bodiless kernel admission: an owed axiom or native data
    /// signature, without inventing a value unfolding.
    ///
    /// # Specification
    /// - requires: `constant` follows every prior crossed or static definition;
    ///   `admitted` is a fresh kernel position.
    /// - ensures: the crossed table answers `admitted`'s position for
    ///   `constant`, which stays rigid on both sides.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — owed declarations and their dependent uses expose
    ///   axiom receipts and an exact artifact audit; inventing a definition for
    ///   an axiom or failing to remap its position changes those observations.
    /// - witness: `bridge::tests::each_owed_hole_is_an_axiom_of_the_artifact`
    /// - witness: `bridge::tests::a_body_naming_a_withheld_declaration_is_refused`
    /// - witness: `tests::native_formers::data_declarations_and_refusals_agree_with_kernel`
    #[spec(
        requires: self.admitted.last_key_value().is_none_or(|(&last, _)| last < constant)
            && !self.unfoldings.contains_key(&admitted.position()),
        captures: unfolded = self.unfoldings.len(),
        ensures: self.admitted.get(&constant) == Some(&admitted.position())
            && !self.unfoldings.contains_key(&admitted.position()) && self.unfoldings.len() == unfolded,
    )]
    fn declare(
        &mut self,
        constant: ConstantIndex,
        admitted: CheckedId,
    )
    {
        self.admitted.insert(constant, admitted.position());
    }

    /// The definitions the kernel's replay may unfold, by kernel position:
    /// the crossed definitions' bodies, and the static operators one crossing
    /// numbered past them.
    ///
    /// # Specification
    /// - requires: no position of `operators` is a crossed definition's.
    /// - ensures: [`Unfoldable::Body`] at each crossed definition's kernel
    ///   position, the entry `operators` holds at each of its positions, and
    ///   [`Unfoldable::Opaque`] at every other position below the highest.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `for` loop over the merged entries, and the `while` loop
    ///   padding up to each, not recursion.
    /// - measure: the entries left, then the gap below the next.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a crossed definition alone and beside
    ///   the static operators of one crossing.
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body merges every crossed definition and operator once; the check reads each once more"
        )
    )]
    #[spec(ensures: |ret| operators.iter().all(|(&position, &entry)| {
        self.unfoldings.contains_key(&position) || ret.unfolding(position) == entry
    }) && self.unfoldings.iter().all(|(&position, &body)| {
        ret.unfolding(position) == Unfoldable::Body(body)
    }))]
    fn unfoldings(
        &self,
        operators: &BTreeMap<ConstantIndex, Unfoldable>,
    ) -> Unfoldings
    {
        let mut entries: BTreeMap<ConstantIndex, Unfoldable> = operators.clone();
        for (&position, &body) in &self.unfoldings {
            entries.insert(position, Unfoldable::Body(body));
        }
        let mut bodies = Vec::new();
        for (position, entry) in entries {
            while bodies.len() < usize::from(position) {
                bodies.push(Unfoldable::Opaque);
            }
            bodies.push(entry);
        }
        Unfoldings::new(bodies).presenting(self.presentations.clone())
    }

    /// The decision the kernel's replay reads for the normaliser's `decision`:
    /// a constant that crossed at its kernel position, a static definition at
    /// the position `operators` numbered it at, and every other node opaque to
    /// the replay.
    ///
    /// # Specification
    /// - requires: nothing; unavailable constants become opaque replay nodes.
    /// - ensures: the decision's kind, side and position survive; each constant
    ///   uses its admitted position before its operator position, and every
    ///   other trace node becomes opaque.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all decision variants over admitted, operator and
    ///   unavailable nodes expose exact replay decisions; overlapping mappings
    ///   separate admitted-position precedence, and side or position loss
    ///   differs.
    /// - witness: `bridge::tests::replay_decisions_preserve_shape_and_position_precedence`
    #[spec(ensures: |ret| {
        let mapped = |source: TraceNode, target: ReplayNode| match source {
            | TraceNode::Constant(constant) => match self.admitted.get(&constant).copied()
                .or_else(|| operators.get(&Unfolded::Definition(constant)).copied()) {
                | Some(position) => target == ReplayNode::Constant(position),
                | None => target == ReplayNode::Other,
            },
            | TraceNode::Value(_) | TraceNode::Computation(_) => target == ReplayNode::Other,
        };
        match (decision, ret) {
            | (ConversionDecision::ReduceLeft { redex: a }, ConversionDecision::ReduceLeft { redex: b })
            | (ConversionDecision::ReduceRight { redex: a }, ConversionDecision::ReduceRight { redex: b })
            | (ConversionDecision::ConstShortcut { constant: a }, ConversionDecision::ConstShortcut { constant: b })
            | (ConversionDecision::Unfold { constant: a }, ConversionDecision::Unfold { constant: b })
            | (ConversionDecision::Postpone { constant: a }, ConversionDecision::Postpone { constant: b })
            | (ConversionDecision::Force { thunk: a }, ConversionDecision::Force { thunk: b }) => mapped(a,b),
            | (ConversionDecision::Freeze { constant: a, side: x }, ConversionDecision::Freeze { constant: b, side: y })
            | (ConversionDecision::EtaExpand { side: x, variable: a }, ConversionDecision::EtaExpand { side: y, variable: b }) => x == y && mapped(a,b),
            | (ConversionDecision::ReturnEta { side: x }, ConversionDecision::ReturnEta { side: y })
            | (ConversionDecision::Reassociate { side: x }, ConversionDecision::Reassociate { side: y }) => x == y,
            | (ConversionDecision::ComparedShared { left: a, right: b }, ConversionDecision::ComparedShared { left: c, right: d }) => mapped(a,c) && mapped(b,d),
            | (ConversionDecision::NegativeSubgoal { position: a }, ConversionDecision::NegativeSubgoal { position: b }) => a == b,
            | (ConversionDecision::Decompose, ConversionDecision::Decompose) => true,
            | _ => false,
        }
    })]
    fn kernel_decision(
        &self,
        operators: &BTreeMap<Unfolded, ConstantIndex>,
        decision: ConversionDecision<TraceNode>,
    ) -> ConversionDecision<ReplayNode>
    {
        decision.map(|node: TraceNode| match node {
            TraceNode::Constant(constant) => match self.admitted.get(&constant) {
                Some(&position) => ReplayNode::Constant(position),
                None => match operators.get(&Unfolded::Definition(constant)) {
                    Some(&position) => ReplayNode::Constant(position),
                    None => ReplayNode::Other,
                },
            },
            TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
        })
    }
}

/// A node's image in the kernel arena while one declaration is erased.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Image<Erased>
{
    /// The node's frame waits on its children.
    Open,
    /// The node is erased, to this kernel node.
    Erased(Erased),
}

/// Which identity an identity frame erases: the symmetric path or the
/// directed flow, whose kernel formers share their shape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Family
{
    /// `Path`, `here`, transport.
    Path,
    /// `Flow`, `stay`, `ride`.
    Flow,
}

/// A forward flow part-way through erasure: its flow type and translator
/// crossed, its images crossing in coverage order.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ForwardErasure
{
    /// The forward flow.
    at: ValueId,
    /// The flow type's image.
    flow_type: gandr_kernel_term::ValueTypeId,
    /// The translator's image.
    translator: gandr_kernel_term::ValueId,
    /// The decided images, in coverage order.
    images: alloc::sync::Arc<[ValueId]>,
    /// The images crossed so far.
    erased: Vec<gandr_kernel_term::ValueId>,
    /// The decided dialogues, in coverage order.
    dialogues: alloc::sync::Arc<[gandr_kernel_term::Dialogue]>,
}

/// A rule waiting on the image of a child.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Frame
{
    /// Visit the next native child, retaining its image in the memo.
    NativeNext(CoreNode),
    /// Assemble a native former once every child has crossed.
    NativeBuild(CoreNode),
    /// Await a native cell's head.
    ListHead
    {
        /// Source cell.
        at: ValueId,
        /// Source tail.
        tail: ValueId,
    },
    /// Await a native cell's tail.
    ListTail
    {
        /// Source cell.
        at: ValueId,
        /// Lowered head.
        head: gandr_kernel_term::ValueId,
    },
    /// Await a fold's element annotation.
    ListElement
    {
        /// Source fold.
        at: ComputationId,
    },
    /// Await a fold's result annotation.
    ListResult
    {
        /// Source fold.
        at: ComputationId,
        /// Lowered element annotation.
        element: gandr_kernel_term::ValueTypeId,
    },
    /// Await a fold's list.
    ListInput
    {
        /// Source fold.
        at: ComputationId,
        /// Lowered element annotation.
        element: gandr_kernel_term::ValueTypeId,
        /// Lowered result annotation.
        result: gandr_kernel_term::ValueTypeId,
    },
    /// Await a fold's empty branch.
    ListNil
    {
        /// Source fold.
        at: ComputationId,
        /// Lowered element annotation.
        element: gandr_kernel_term::ValueTypeId,
        /// Lowered result annotation.
        result: gandr_kernel_term::ValueTypeId,
        /// Lowered list.
        list: gandr_kernel_term::ValueId,
    },
    /// Await a fold's cell branch.
    ListCons
    {
        /// Source fold.
        at: ComputationId,
        /// Lowered element annotation.
        element: gandr_kernel_term::ValueTypeId,
        /// Lowered result annotation.
        result: gandr_kernel_term::ValueTypeId,
        /// Lowered list.
        list: gandr_kernel_term::ValueId,
        /// Lowered empty branch.
        on_nil: gandr_kernel_term::ComputationId,
    },
    /// Await the element type of a finite list.
    ListType
    {
        /// The source list type.
        at: ValueTypeId,
    },
    /// A binary native call, awaiting its first argument.
    NativeFirst
    {
        /// The saturated source call.
        at: ComputationId,
        /// The forced native axiom.
        head: gandr_kernel_term::ComputationId,
        /// The second source operand.
        second: ValueId,
    },
    /// Await a reflexivity endpoint.
    PathRefl
    {
        /// The reflexivity value.
        at: ValueId,
    },
    /// Await an equivalence classifier.
    PathEquivType
    {
        /// The equivalence.
        at: ValueId,
        /// The forward map.
        forward: ValueId,
        /// The inverse map.
        backward: ValueId,
        /// The untrusted round-trip dialogues.
        evidence: alloc::sync::Arc<gandr_kernel_term::PathEvidence>,
    },
    /// Await a forward translator.
    PathEquivForward
    {
        /// The equivalence.
        at: ValueId,
        /// The classifier image.
        path_type: gandr_kernel_term::ValueTypeId,
        /// The inverse map.
        backward: ValueId,
        /// The untrusted round-trip dialogues.
        evidence: alloc::sync::Arc<gandr_kernel_term::PathEvidence>,
    },
    /// Await an inverse translator.
    PathEquivBackward
    {
        /// The equivalence.
        at: ValueId,
        /// The classifier image.
        path_type: gandr_kernel_term::ValueTypeId,
        /// The forward map image.
        forward: gandr_kernel_term::ValueId,
        /// The untrusted round-trip dialogues.
        evidence: alloc::sync::Arc<gandr_kernel_term::PathEvidence>,
    },
    /// Await the image of a univalence's record.
    UnivalenceRecord
    {
        /// The univalence.
        at: ValueId,
    },
    /// Await the first product path.
    PathProductFirst
    {
        /// The product path.
        at: ValueId,
        /// The second path.
        second: ValueId,
    },
    /// Await the second product path.
    PathProductSecond
    {
        /// The product path.
        at: ValueId,
        /// The first path image.
        first: gandr_kernel_term::ValueId,
    },
    /// Await a transport path.
    TransportPath
    {
        /// The transport.
        at: ComputationId,
        /// The operand.
        value: ValueId,
    },
    /// Await a transport operand.
    TransportValue
    {
        /// The transport.
        at: ComputationId,
        /// The path image.
        path: gandr_kernel_term::ValueId,
    },
    /// Await the source code of a path classifier.
    PathSource
    {
        /// The classifier.
        at: ValueTypeId,
        /// The target code.
        target_code: ValueId,
    },
    /// Await the target code of a path classifier.
    PathTarget
    {
        /// The classifier.
        at: ValueTypeId,
        /// The source code image.
        source: gandr_kernel_term::ValueId,
    },
    /// Await the source code of a universe flow type.
    FlowSource
    {
        /// The flow type.
        at: ValueTypeId,
        /// The target code.
        target_code: ValueId,
    },
    /// Await the target code of a universe flow type.
    FlowTarget
    {
        /// The flow type.
        at: ValueTypeId,
        /// The source code image.
        source: gandr_kernel_term::ValueId,
    },
    /// Await the native classifier of a session statement, then mint the
    /// kernel's session certificate over the engine's pairs.
    SessionCertificate
    {
        /// The statement, stay or composite.
        at: ValueId,
        /// Bisimilarity or simulation.
        relation: gandr_core_term::session::SessionRelation,
        /// The engine's pairs.
        evidence: alloc::sync::Arc<gandr_kernel_term::session::Evidence>,
    },
    /// Await the carrier of an element path or flow type.
    PathCarrier
    {
        /// The path or flow type.
        at: ValueTypeId,
        /// The source endpoint.
        left: ValueId,
        /// The target endpoint.
        right: ValueId,
        /// Which identity the type states.
        family: Family,
    },
    /// Await the source endpoint of an element path or flow type.
    PathLeft
    {
        /// The path or flow type.
        at: ValueTypeId,
        /// The carrier image.
        carrier: gandr_kernel_term::ValueTypeId,
        /// The target endpoint.
        right: ValueId,
        /// Which identity the type states.
        family: Family,
    },
    /// Await the target endpoint of an element path or flow type.
    PathRight
    {
        /// The path or flow type.
        at: ValueTypeId,
        /// The carrier image.
        carrier: gandr_kernel_term::ValueTypeId,
        /// The source endpoint image.
        left: gandr_kernel_term::ValueId,
        /// Which identity the type states.
        family: Family,
    },
    /// Await the point of a reflexivity `here(a)` or a stay `stay(a)`.
    Here
    {
        /// The reflexivity or stay.
        at: ValueId,
        /// Which identity the point inhabits.
        family: Family,
    },
    /// Await the motive of an element transport or a ride.
    PathTransportMotive
    {
        /// The transport or ride.
        at: ComputationId,
        /// The path or flow.
        path: ValueId,
        /// The operand.
        value: ValueId,
        /// Which identity the operand moves along.
        family: Family,
    },
    /// Await the path or flow of an element transport or a ride.
    PathTransportPath
    {
        /// The transport or ride.
        at: ComputationId,
        /// The motive image.
        motive: gandr_kernel_term::ValueTypeId,
        /// The operand.
        value: ValueId,
        /// Which identity the operand moves along.
        family: Family,
    },
    /// Await the operand of an element transport or a ride.
    PathTransportValue
    {
        /// The transport or ride.
        at: ComputationId,
        /// The motive image.
        motive: gandr_kernel_term::ValueTypeId,
        /// The path or flow image.
        path: gandr_kernel_term::ValueId,
        /// Which identity the operand moves along.
        family: Family,
    },
    /// Await the first leg of a composite flow.
    ThenFirst
    {
        /// The composite.
        at: ValueId,
        /// The second leg.
        second: ValueId,
    },
    /// Await the second leg of a composite flow.
    ThenSecond
    {
        /// The composite.
        at: ValueId,
        /// The first leg's image.
        first: gandr_kernel_term::ValueId,
    },
    /// Await the first component of a flow product.
    FlowProductFirst
    {
        /// The product.
        at: ValueId,
        /// The second component.
        second: ValueId,
    },
    /// Await the second component of a flow product.
    FlowProductSecond
    {
        /// The product.
        at: ValueId,
        /// The first component's image.
        first: gandr_kernel_term::ValueId,
    },
    /// Await the flow type a forward flow was decided at.
    ForwardType
    {
        /// The forward flow.
        at: ValueId,
        /// The translator.
        translator: ValueId,
        /// The decided images, in coverage order.
        images: alloc::sync::Arc<[ValueId]>,
        /// The decided dialogues, in coverage order.
        dialogues: alloc::sync::Arc<[gandr_kernel_term::Dialogue]>,
    },
    /// Await the translator of a forward flow.
    ForwardTranslator
    {
        /// The forward flow.
        at: ValueId,
        /// The flow type's image.
        flow_type: gandr_kernel_term::ValueTypeId,
        /// The decided images, in coverage order.
        images: alloc::sync::Arc<[ValueId]>,
        /// The decided dialogues, in coverage order.
        dialogues: alloc::sync::Arc<[gandr_kernel_term::Dialogue]>,
    },
    /// Await the next image of a forward flow.
    ForwardImages(ForwardErasure),
    /// Await the flow type a function flow was decided at.
    FunctionFlowType
    {
        /// The function flow.
        at: ValueId,
        /// The domain boundary.
        domain: ValueId,
        /// The codomain boundary.
        codomain: ValueId,
    },
    /// Await the domain boundary of a function flow.
    FunctionFlowDomain
    {
        /// The function flow.
        at: ValueId,
        /// The flow type's image.
        flow_type: gandr_kernel_term::ValueTypeId,
        /// The codomain boundary.
        codomain: ValueId,
    },
    /// Await the codomain boundary of a function flow.
    FunctionFlowCodomain
    {
        /// The function flow.
        at: ValueId,
        /// The flow type's image.
        flow_type: gandr_kernel_term::ValueTypeId,
        /// The domain boundary's image.
        domain: gandr_kernel_term::ValueId,
    },
    /// Await the motive of a telescope transport.
    TelescopeMotive
    {
        /// The transport.
        at: ComputationId,
    },
    /// Await the path of a telescope transport.
    TelescopePath
    {
        /// The transport.
        at: ComputationId,
        /// The motive image.
        motive: gandr_kernel_term::CompTypeId,
    },
    /// Await the start of a telescope transport.
    TelescopeStart
    {
        /// The transport.
        at: ComputationId,
        /// The motive image.
        motive: gandr_kernel_term::CompTypeId,
        /// The path image.
        path: gandr_kernel_term::ValueId,
    },
    /// Await the identity over the path of a telescope transport.
    TelescopeOver
    {
        /// The transport.
        at: ComputationId,
        /// The motive image.
        motive: gandr_kernel_term::CompTypeId,
        /// The path image.
        path: gandr_kernel_term::ValueId,
        /// The start image.
        start: gandr_kernel_term::ValueId,
    },
    /// Await the operand of a telescope transport.
    TelescopeValue
    {
        /// The transport.
        at: ComputationId,
        /// The motive image.
        motive: gandr_kernel_term::CompTypeId,
        /// The path image.
        path: gandr_kernel_term::ValueId,
        /// The start image.
        start: gandr_kernel_term::ValueId,
        /// The image of the identity over the path.
        over: gandr_kernel_term::ValueId,
    },
    /// Await a sum injection payload.
    Injection
    {
        /// The injection.
        at: ValueId,
        /// The summand injected into.
        summand: gandr_kernel_term::Summand,
    },
    /// Assemble a function extensionality once every normal form it records
    /// has crossed.
    FunextBuild(ValueId),
    /// A thunk, awaiting its body's computation.
    Thunk
    {
        /// The thunk.
        at: ValueId,
    },
    /// A returned endpoint, awaiting its computation.
    Returned
    {
        /// The returned endpoint.
        at: ValueId,
    },
    /// A quote, awaiting its value type.
    Quote
    {
        /// The quote.
        at: ValueId,
    },
    /// A quote of a computation type, awaiting it.
    QuoteComputation
    {
        /// The quote.
        at: ValueId,
    },
    /// A code the judgement recorded a lift at, awaiting the lift of its
    /// decode, which it quotes.
    LiftedCode
    {
        /// The code.
        at: ValueId,
    },
    /// A marked value, awaiting the image of the value it marks, which is its
    /// own: a mark is erased.
    UnmarkedValue
    {
        /// The mark.
        at: ValueId,
    },
    /// A marked computation, awaiting the image of the computation it marks.
    UnmarkedComputation
    {
        /// The mark.
        at: ComputationId,
    },
    /// A split, awaiting the image of the projection binds it reduces to.
    SplitReduct
    {
        /// The split.
        at: ComputationId,
    },
    /// A dependent split, awaiting its scrutinee's image.
    SigmaSplitScrutinee
    {
        /// The split.
        at: ComputationId,
        /// Its motive, erased next.
        motive: CompTypeId,
        /// Its body, erased after the motive.
        body: ComputationId,
    },
    /// A dependent split, awaiting its motive's image.
    SigmaSplitMotive
    {
        /// The split.
        at: ComputationId,
        /// The scrutinee's image.
        scrutinee: gandr_kernel_term::ValueId,
        /// Its body, erased next.
        body: ComputationId,
    },
    /// A dependent split, awaiting its body's image.
    SigmaSplitBody
    {
        /// The split.
        at: ComputationId,
        /// The scrutinee's image.
        scrutinee: gandr_kernel_term::ValueId,
        /// The motive's image.
        motive: gandr_kernel_term::CompTypeId,
    },
    /// A force, awaiting its value.
    Force
    {
        /// The force.
        at: ComputationId,
    },
    /// An application, awaiting its head's computation.
    ApplicationHead
    {
        /// The application.
        at: ComputationId,
        /// The argument, erased next.
        argument: ValueId,
    },
    /// An application, awaiting its argument's value.
    ApplicationArgument
    {
        /// The application.
        at: ComputationId,
        /// The head's image.
        head: gandr_kernel_term::ComputationId,
    },
    /// A lambda, awaiting its body's computation.
    Lambda
    {
        /// The lambda.
        at: ComputationId,
    },
    /// A fixpoint, awaiting its body's computation.
    Fixpoint
    {
        /// The fixpoint.
        at: ComputationId,
        /// The claim it carries across unchanged.
        evidence: gandr_kernel_term::FixpointEvidence,
    },
    /// A return, awaiting its value.
    Return
    {
        /// The return.
        at: ComputationId,
    },
    /// A bind, awaiting its bound computation.
    BindBound
    {
        /// The bind.
        at: ComputationId,
        /// The body, erased next.
        body: ComputationId,
    },
    /// A bind, awaiting its body.
    BindBody
    {
        /// The bind.
        at: ComputationId,
        /// The bound computation's image.
        bound: gandr_kernel_term::ComputationId,
    },
    /// A lazy pairing, awaiting its first component.
    WithFirst
    {
        /// The pairing.
        at: ComputationId,
        /// The second component, erased next.
        second: ComputationId,
    },
    /// A lazy pairing, awaiting its second component.
    WithSecond
    {
        /// The pairing.
        at: ComputationId,
        /// The first component's image.
        first: gandr_kernel_term::ComputationId,
    },
    /// A projection of a lazy pairing, awaiting the projected computation.
    Project
    {
        /// The projection.
        at: ComputationId,
        /// The side it observes.
        side: gandr_kernel_term::Side,
    },
    /// A thunk type, awaiting its computation type.
    ThunkType
    {
        /// The thunk type.
        at: ValueTypeId,
    },
    /// A lift of a value type, awaiting the type.
    TypeLift
    {
        /// The lift.
        at: ValueTypeId,
    },
    /// The lift a recorded crossing adds over a decode, awaiting the decode
    /// at the code's own level.
    DecodeLift
    {
        /// The universe level the code was checked at.
        target: Level,
    },
    /// A decode, awaiting the type its code denotes.
    Decoded
    {
        /// The decode.
        at: TypeNode,
    },
    /// A returner, awaiting its value type.
    Returner
    {
        /// The returner.
        at: CompTypeId,
    },
    /// An arrow, awaiting its domain's value type.
    ArrowDomain
    {
        /// The arrow.
        at: CompTypeId,
        /// The codomain, erased next.
        codomain: CompTypeId,
    },
    /// An arrow, awaiting its codomain's computation type.
    ArrowCodomain
    {
        /// The arrow.
        at: CompTypeId,
        /// The domain's image.
        domain: gandr_kernel_term::ValueTypeId,
    },
    /// A lazy product, awaiting its first computation type.
    WithTypeFirst
    {
        /// The lazy product.
        at: CompTypeId,
        /// The second computation type, erased next.
        second: CompTypeId,
    },
    /// A lazy product, awaiting its second computation type.
    WithTypeSecond
    {
        /// The lazy product.
        at: CompTypeId,
        /// The first computation type's image.
        first: gandr_kernel_term::CompTypeId,
    },
    /// A dependent arrow, awaiting its domain's value type.
    PiDomain
    {
        /// The dependent arrow.
        at: CompTypeId,
        /// The codomain, erased next.
        codomain: CompTypeId,
    },
    /// A dependent arrow, awaiting its codomain's computation type.
    PiCodomain
    {
        /// The dependent arrow.
        at: CompTypeId,
        /// The domain's image.
        domain: gandr_kernel_term::ValueTypeId,
    },
    /// A static application at a reducible head, or a `ua`, erased as its
    /// reduct or its derived path, awaiting that value's image.
    Reduced
    {
        /// The static application or the `ua`.
        at: ValueId,
    },
    /// A static application at a rigid head, awaiting its head's value.
    StaticHead
    {
        /// The static application.
        at: ValueId,
        /// The argument, erased next.
        argument: ValueId,
    },
    /// A static application at a rigid head, awaiting its argument's value.
    StaticArgument
    {
        /// The static application.
        at: ValueId,
        /// The head's image.
        head: gandr_kernel_term::ValueId,
    },
    /// A static Pi, awaiting its domain.
    StaticPiDomain
    {
        /// The static Pi.
        at: ValueTypeId,
        /// The codomain, erased next.
        codomain: ValueTypeId,
    },
    /// A static Pi, awaiting its codomain.
    StaticPiCodomain
    {
        /// The static Pi.
        at: ValueTypeId,
        /// The domain's image.
        domain: gandr_kernel_term::ValueTypeId,
    },
    /// A dependent pair, awaiting its first factor.
    SigmaFirst
    {
        /// The dependent pair.
        at: ValueTypeId,
        /// The second factor, erased next.
        second: ValueTypeId,
    },
    /// A dependent pair, awaiting its second factor.
    SigmaSecond
    {
        /// The dependent pair.
        at: ValueTypeId,
        /// The first factor's image.
        first: gandr_kernel_term::ValueTypeId,
    },
    /// A decode of a code that is a static application at a rigid head,
    /// awaiting the code's value.
    DecodeOf
    {
        /// The level the code is decoded at.
        level: Level,
        /// The sort of the universe the code inhabits.
        sort: GroundSort,
    },
}

/// The machine's next move.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Step
{
    /// Erase a node.
    Descend(CoreNode),
    /// Hand a finished node's image to the innermost frame.
    Ascend(AnyNode),
}

/// How an erasure reads static content.
///
/// # Judgement
/// - direction: an offer is erased normalizing, so the kernel receives static
///   normal forms; a certificate's sides are erased verbatim, so the kernel's
///   replay re-derives each step the trace names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode
{
    /// A static application at a reducible head is erased as its reduct, its
    /// step certified; a decode of a constant with a body as the decode of
    /// the body.
    Normalizing,
    /// Every node is erased as it stands: a static definition and a closed
    /// static lambda as a static operator numbered past the environment.
    Verbatim,
}

/// Every node one mode of an erasure reached, and its image.
#[derive(Debug, Default)]
struct Memo
{
    /// The value nodes reached, and their images.
    values: BTreeMap<ValueId, Image<gandr_kernel_term::ValueId>>,
    /// The computation nodes reached, and their images.
    computations: BTreeMap<ComputationId, Image<gandr_kernel_term::ComputationId>>,
    /// The value-type nodes reached, and their images.
    value_types: BTreeMap<ValueTypeId, Image<gandr_kernel_term::ValueTypeId>>,
    /// The computation-type nodes reached, and their images.
    comp_types: BTreeMap<CompTypeId, Image<gandr_kernel_term::CompTypeId>>,
}

/// One declaration's erasure: what it reads, the positions constants resolve
/// through, the frames waiting, every node's image so far in each mode, the
/// certificates of the steps it took and the static operators its
/// certificates' sides name.
struct Erasure<'source, 'positions>
{
    /// The arena every id resolves in, and every reduct is minted into.
    arena: &'source mut CoreArena,
    /// The recorded lifts and the definitions.
    source: Source<'source>,
    /// The kernel positions and bodies of the declarations that crossed before
    /// this one, and the static definitions' bodies.
    positions: &'positions Positions,
    /// How static content is read now.
    mode: Mode,
    /// The rules waiting on children, innermost last.
    frames: Vec<Frame>,
    /// The images the normalizing mode minted.
    normalized: Memo,
    /// The images the verbatim mode minted.
    verbatim: Memo,
    /// The certificates of the steps taken and not yet replayed.
    certificates: Vec<Certificate>,
    /// The first position a static operator is numbered at.
    base: ConstantIndex,
    /// The position each static operator a side names was numbered at.
    operators: BTreeMap<Unfolded, ConstantIndex>,
    /// The operators numbered whose bodies are not yet erased: the position,
    /// the body beneath its static lambdas, and how many those are.
    pending: Vec<(ConstantIndex, ValueId, u32)>,
    /// The replay's entry at each operator position whose body is erased.
    bodies: BTreeMap<ConstantIndex, Unfoldable>,
    /// The declarations crossing with this one, ascending: each module
    /// position and the kernel position it is about to take, which no crossed
    /// declaration holds yet — a data declaration's own, or every member of
    /// its mutual block.
    crossing: &'positions [(ConstantIndex, ConstantIndex)],
}

impl<'source, 'positions> Erasure<'source, 'positions>
{
    /// A normalizing erasure over `arena`, reading `source`, resolving
    /// constants through `positions` and numbering static operators from
    /// `base`, with nothing reached.
    ///
    /// # Specification
    /// trivial.
    fn new(
        arena: &'source mut CoreArena,
        source: Source<'source>,
        positions: &'positions Positions,
        base: ConstantIndex,
    ) -> Self
    {
        Self {
            arena,
            source,
            positions,
            mode: Mode::Normalizing,
            frames: Vec::new(),
            normalized: Memo::default(),
            verbatim: Memo::default(),
            certificates: Vec::new(),
            base,
            operators: BTreeMap::new(),
            pending: Vec::new(),
            bodies: BTreeMap::new(),
            crossing: &[],
        }
    }

    /// The same erasure crossing beside `crossing`, ascending by module
    /// position: each member's module position resolves to the kernel position
    /// it is about to take, so the block's members name each other.
    ///
    /// # Specification
    /// trivial.
    const fn crossing_block(
        mut self,
        crossing: &'positions [(ConstantIndex, ConstantIndex)],
    ) -> Self
    {
        self.crossing = crossing;
        self
    }

    /// The images the current mode minted.
    ///
    /// # Specification
    /// trivial.
    const fn memo(&mut self) -> &mut Memo
    {
        match self.mode {
            Mode::Normalizing => &mut self.normalized,
            Mode::Verbatim => &mut self.verbatim,
        }
    }

    /// Erase `offer` into `target`: its declared type, then a definition's
    /// body; or an abstract type's kind, then its representation.
    ///
    /// # Specification
    /// - requires: no earlier erasure of this machine was refused.
    /// - ensures: the images of the offer's declared type and, for a
    ///   definition, of its body, or of an abstract type's kind and
    ///   representation, as [`Self::erase`] gives them.
    /// - fails: the first refusal either erasure gives; the body is not erased
    ///   once the type is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - any [`Refusal`] [`Self::value_type`] or [`Self::value`] gives.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a checked definition and an owed declaration expose
    ///   the exact offered family at admission; a refused declared type
    ///   prevents the body from publishing. Wrong family or skipped erasure
    ///   changes this.
    /// - witness: `bridge::tests::a_lowered_value_definition_admits`
    /// - witness: `bridge::tests::a_bound_sealed_atom_lowers_to_the_kernel_atom`
    /// - witness: `bridge::tests::each_owed_hole_is_an_axiom_of_the_artifact`
    /// - witness: `bridge::tests::a_refused_declaration_leaves_the_environment_unchanged`
    #[spec(ensures: |ret| { let (matched_left_value, matched_right_value) = (offer, &ret);
if let Offer::Data(signature) = matched_left_value && let Ok(Erased::Data { ref parameters,ref constructors,ref kind }) = *matched_right_value { parameters.len() == signature.parameters().len() && constructors.iter().map(Vec::len).eq(signature.constructors().iter().map(Vec::len)) && target.value_type(*kind).is_some() && parameters.iter().chain(constructors.iter().flatten()).all(|&field| target.value_type(field).is_some()) }
 else if matches!(matched_left_value, Offer::Definition { .. }) && let Ok(Erased::Definition { ref declared, ref body, ref related, ref laws }) = *matched_right_value { target.value_type(*declared).is_some() && target.value(*body).is_some()
    && matches!(matched_left_value, Offer::Definition { relations, laws: named, .. } if relations.len() == related.len() && named.len() == laws.len())
    && related.iter().all(|pair| target.value(pair.left).is_some() && target.value(pair.right).is_some()) }
 else if matches!(matched_left_value, Offer::Axiom { .. }) && let Ok(Erased::Axiom { ref declared }) = *matched_right_value { target.value_type(*declared).is_some() }
 else if matches!(matched_left_value, Offer::Abstract(_)) && let Ok(Erased::Abstract { ref kind, ref representation }) = *matched_right_value { target.value_type(*kind).is_some() && target.value_type(*representation).is_some() }
 else { (*matched_right_value).is_err() }
})]
    fn offer(
        &mut self,
        target: &mut TermArena,
        offer: Offer<'_>,
    ) -> Result<Erased, Refusal>
    {
        match offer {
            Offer::Data(signature) => {
                let parameters = signature
                    .parameters()
                    .iter()
                    .map(|&parameter| self.value_type(target, parameter))
                    .collect::<Result<_, _>>()?;
                let constructors = signature
                    .constructors()
                    .iter()
                    .map(|fields| {
                        fields
                            .iter()
                            .map(|&field| self.value_type(target, field))
                            .collect()
                    })
                    .collect::<Result<_, _>>()?;
                let kind = self.value_type(target, signature.kind())?;
                Ok(Erased::Data {
                    parameters,
                    constructors,
                    kind,
                })
            },
            Offer::Definition {
                declared,
                body,
                relations,
                laws,
            } => {
                let offered = body;
                let declared = self.value_type(target, declared)?;
                let body = self.value(target, body)?;
                // The relations after the body, so their endpoints reuse the
                // images the declared type already minted.
                let mut related = Vec::with_capacity(relations.len());
                for relation in relations {
                    let left = self.value(target, relation.left())?;
                    let right = self.value(target, relation.right())?;
                    related.push(RelatedEndpoints {
                        left,
                        right,
                        dialogue: relation
                            .decisions()
                            .iter()
                            .map(|decision| decision.map(|_| ()))
                            .collect(),
                    });
                }
                // A law crossed before the fold that rests on it, at its
                // kernel position.
                let laws = laws
                    .iter()
                    .map(|&law| {
                        self.positions
                            .admitted
                            .get(&law)
                            .copied()
                            .ok_or(Refusal::Withheld {
                                at: offered,
                                constant: law,
                            })
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Erased::Definition {
                    declared,
                    body,
                    related,
                    laws,
                })
            },
            Offer::Axiom { declared } => {
                let declared = self.value_type(target, declared)?;
                Ok(Erased::Axiom { declared })
            },
            Offer::Abstract(declared) => {
                let kind = self.value_type(target, declared.kind())?;
                let representation = self.value_type(target, declared.representation())?;
                Ok(Erased::Abstract {
                    kind,
                    representation,
                })
            },
        }
    }

    /// Replay every distinct certificate the erasure collected, each passed
    /// through `vouch`, against the kernel's images of its redex and its
    /// reduct.
    ///
    /// # Specification
    /// - requires: the offer was erased into `target`, the staging arena the
    ///   declaration is admitted from.
    /// - ensures: one [`Replayed`] per certificate whose step and instance —
    ///   what it unfolds and the content of its redex's image — no earlier
    ///   certificate of this declaration had, in the order the erasure met the
    ///   steps, the certificates erasing a reduct collects replayed after it. A
    ///   step unfolding a definition that crossed replays between the kernel
    ///   constant and the reduct erased normalizing, as the kernel admitted the
    ///   body, by the kernel's own δ-step at that constant closed on the two
    ///   α-equal normal forms: the body the kernel holds is that normal form,
    ///   so the step is the whole derivation, where the normaliser's trace
    ///   walks the unnormalized body and names operators the normal form no
    ///   longer holds. Any other step replays between its redex and its reduct
    ///   each erased verbatim, every static operator they name numbered and its
    ///   body erased verbatim, the certificate's trace read at the kernel's
    ///   positions, a static lambda's step prefixed by the unfolding of its
    ///   operator. Each replays as a convertibility claim. `target` holds the
    ///   images minted and nothing the replay minted.
    /// - fails: [`Refusal::CertificateDeclined`] naming the first declined
    ///   certificate and preserving its [`ReplayDecline`], beside the verdicts
    ///   replayed up to it; the refusal erasing a side gives. An impossible
    ///   certified negative for a positive claim is
    ///   [`Refusal::MachineInvariant`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — as above, beside the verdicts replayed before it.
    ///
    /// # Termination
    /// - reason: the `loop` drains the certificate queue, and the `for` loop
    ///   walks one batch, not recursion.
    /// - measure: the reductions the normalizing erasure has left to take: a
    ///   batch's reducts are erased in a memo shared with the offer, and each
    ///   step consumes a redex of a well-formed code.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — the kernel's replay is the oracle: every
    ///   certificate a readmission over generated code constants and static
    ///   declarations records replays; the residue is one instance met twice,
    ///   replayed once, two instances, replayed twice, and an emptied trace,
    ///   declined.
    /// - witness: `bridge::tests::every_readmission_certificate_replays`
    /// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
    /// - witness: `bridge::tests::a_declining_certificate_faults_the_declaration`
    #[spec(ensures: |ret| match ret {
        | Ok(ref entries) => {
            self.certificates.is_empty()
                && entries.iter().all(|entry| entry.verdict == KernelVerdict::Convertible)
        },
        | Err(_) => true,
    })]
    fn replay_certificates<Vouch>(
        &mut self,
        target: &mut TermArena,
        vouch: &Vouch,
    ) -> Result<Vec<Replayed>, (Refusal, Vec<Replayed>)>
    where
        Vouch: Fn(Certificate) -> Certificate,
    {
        let mut replayed = Vec::new();
        let mut met = BTreeSet::new();
        loop {
            let pending = core::mem::take(&mut self.certificates);
            if pending.is_empty() {
                return Ok(replayed);
            }
            for certificate in pending {
                let certificate = vouch(certificate);
                let unfolded = certificate.unfolded();
                match self.replay_one(target, &certificate, &mut met) {
                    Ok(Maybe::Present(entry)) => {
                        replayed.push(entry);
                        match entry.verdict {
                            KernelVerdict::Convertible => {},
                            KernelVerdict::Declined(reason) => {
                                return Err((
                                    Refusal::CertificateDeclined { unfolded, reason },
                                    replayed,
                                ));
                            },
                            KernelVerdict::NotConvertible => {
                                return Err((Refusal::MachineInvariant, replayed));
                            },
                        }
                    },
                    Ok(Maybe::Absent(_)) => {},
                    Err(refusal) => return Err((refusal, replayed)),
                }
            }
        }
    }

    /// Replay `certificate`, unless `met` holds its step and instance.
    ///
    /// # Specification
    /// - requires: as [`Self::replay_certificates`].
    /// - ensures: as [`Self::replay_certificates`] states of one certificate;
    ///   `met` gains its step and instance; nothing when `met` held them.
    /// - fails: the refusal erasing a side gives.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — a side did not erase.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — as [`Self::replay_certificates`].
    /// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    #[spec(ensures: |ret| !matches!(ret, Ok(Maybe::Present(_))) || self.pending.is_empty())]
    fn replay_one(
        &mut self,
        target: &mut TermArena,
        certificate: &Certificate,
        met: &mut BTreeSet<(Unfolded, ContentDigest)>,
    ) -> Result<Maybe<Replayed, replay_entry::Absent>, Refusal>
    {
        let unfolded = certificate.unfolded();
        let crossed = match unfolded {
            Unfolded::Definition(constant) => self.positions.admitted.get(&constant).copied(),
            Unfolded::Abstraction(_) | Unfolded::Returned(_) => None,
        };
        let left = match crossed {
            Some(position) => target.value_constant(position),
            None => self.value_in(Mode::Verbatim, target, certificate.redex())?,
        };
        let redex = content_digest(target, AnyNode::Value(left));
        if !met.insert((unfolded, redex)) {
            return Ok(Maybe::Absent(replay_entry::Absent::Met));
        }
        let right = match crossed {
            Some(_) => self.value_in(Mode::Normalizing, target, certificate.reduct())?,
            None => self.value_in(Mode::Verbatim, target, certificate.reduct())?,
        };
        self.erase_operators(target)?;
        if certificate.derivation() == Derivation::Reading {
            let verdict = read_step(
                target,
                &self.positions.unfoldings(&self.bodies),
                left,
                right,
                ReplayBudget::DEFAULT,
            );
            return Ok(Maybe::Present(Replayed {
                unfolded,
                redex,
                verdict,
            }));
        }
        let decisions = if let Some(position) = crossed {
            Vec::from([
                ConversionDecision::Unfold {
                    constant: ReplayNode::Constant(position),
                },
                ConversionDecision::ReduceLeft {
                    redex: ReplayNode::Constant(position),
                },
                ConversionDecision::ComparedShared {
                    left: ReplayNode::Other,
                    right: ReplayNode::Other,
                },
            ])
        }
        else {
            let mut decisions = Vec::new();
            if let Unfolded::Abstraction(_) = unfolded
                && let Some(&position) = self.operators.get(&unfolded)
            {
                decisions.push(ConversionDecision::Unfold {
                    constant: ReplayNode::Constant(position),
                });
                decisions.push(ConversionDecision::ReduceLeft {
                    redex: ReplayNode::Constant(position),
                });
            }
            decisions.extend(
                certificate
                    .decisions()
                    .iter()
                    .map(|&decision| self.positions.kernel_decision(&self.operators, decision)),
            );
            decisions
        };
        let verdict = replay(
            target,
            &self.positions.unfoldings(&self.bodies),
            ReplaySides::Values(left, right),
            EngineClaim::Convertible,
            decisions,
            ReplayBudget::DEFAULT,
        );
        Ok(Maybe::Present(Replayed {
            unfolded,
            redex,
            verdict,
        }))
    }

    /// Erase the value `root` into `target` in `mode`, then return to the
    /// mode the machine was in.
    ///
    /// # Specification
    /// - requires: no earlier erasure of this machine was refused.
    /// - ensures: as [`Self::value`], read in `mode`.
    /// - fails: as [`Self::value`].
    /// - panics: none.
    ///
    /// # Errors
    /// - any [`Refusal`] [`Self::value`] gives.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both modes, reached by one certificate whose sides
    ///   are erased verbatim beside an offer erased normalizing.
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    #[spec(captures: entry = self.mode, ensures: self.mode == entry)]
    fn value_in(
        &mut self,
        mode: Mode,
        target: &mut TermArena,
        root: ValueId,
    ) -> Result<gandr_kernel_term::ValueId, Refusal>
    {
        let previous = core::mem::replace(&mut self.mode, mode);
        let image = self.value(target, root);
        self.mode = previous;
        image
    }

    /// Erase the body of every static operator numbered and not yet erased,
    /// verbatim, into the replay's entry at its position.
    ///
    /// # Specification
    /// - requires: as [`Self::value`].
    /// - ensures: every numbered operator has its entry: a body beneath no
    ///   static lambda an [`Unfoldable::Body`], any other an
    ///   [`Unfoldable::Operator`] over as many parameters as lambdas.
    /// - fails: the refusal erasing a body gives.
    /// - panics: none.
    ///
    /// # Errors
    /// - any [`Refusal`] [`Self::value`] gives.
    ///
    /// # Termination
    /// - reason: the `while let` loop drains a queue, not recursion.
    /// - measure: the static operators not yet numbered, finite since each
    ///   definition and each node is numbered once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by an operator with parameters and one
    ///   without, each replayed. The predicate compares the two tables' sizes:
    ///   each operator is numbered at a fresh position and an entry is written
    ///   only at a numbered position, so equal sizes mean every numbered
    ///   operator has its entry, read without walking either table.
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    /// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
    #[spec(ensures: |ret| ret.is_err()
        || (self.pending.is_empty() && self.bodies.len() == self.operators.len()))]
    fn erase_operators(
        &mut self,
        target: &mut TermArena,
    ) -> Result<(), Refusal>
    {
        while let Some((position, body, parameters)) = self.pending.pop() {
            let image = self.value_in(Mode::Verbatim, target, body)?;
            let entry = if parameters == 0 {
                Unfoldable::Body(image)
            }
            else {
                Unfoldable::Operator {
                    parameters: ParameterCount::from(parameters),
                    body: image,
                }
            };
            self.bodies.insert(position, entry);
        }
        Ok(())
    }

    /// The position the static operator `unfolded`, of body `body`, is
    /// numbered at: its first numbering queues its body, beneath its static
    /// lambdas, for erasure.
    ///
    /// # Specification
    /// - requires: `body` is the definition's body, or the static lambda
    ///   itself.
    /// - ensures: the same position for the same operator; a fresh one, past
    ///   every other this erasure numbered, the first time.
    /// - fails: [`Refusal::MachineInvariant`] past the position ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal::MachineInvariant`] — the position overflowed.
    ///
    /// # Termination
    /// - reason: the `while let` loop strips a lambda chain, not recursion.
    /// - measure: the arena position of the body, which a lambda holds below
    ///   its own.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a first numbering and a repeat, separated by one
    ///   operator named by both sides of a certificate.
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    #[spec(ensures: |ret| ret.is_err() || self.operators.get(&unfolded).copied() == ret.ok())]
    fn operator(
        &mut self,
        unfolded: Unfolded,
        body: ValueId,
    ) -> Result<ConstantIndex, Refusal>
    {
        if let Some(&position) = self.operators.get(&unfolded) {
            return Ok(position);
        }
        let mut stripped = body;
        let mut parameters = 0_u32;
        while let Some(&Value::StaticLambda(inner)) = self.arena.value(stripped) {
            stripped = inner;
            parameters = parameters.checked_add(1).ok_or(Refusal::MachineInvariant)?;
        }
        let position = usize::from(self.base)
            .checked_add(self.operators.len())
            .map(ConstantIndex::from)
            .ok_or(Refusal::MachineInvariant)?;
        self.operators.insert(unfolded, position);
        self.pending.push((position, stripped, parameters));
        Ok(position)
    }

    /// The kernel position the constant `at` names in the current mode: the
    /// position its declaration crossed at, the one a member of the crossing
    /// block is about to take, or, read verbatim, the static operator a
    /// static definition is numbered at.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as above.
    /// - fails: [`Refusal::Withheld`] at `at` for a constant that neither
    ///   crossed, nor crosses in this block, nor, read verbatim, names a static
    ///   definition.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal::Withheld`], or [`Self::operator`]'s refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — four arms, separated by a crossed constant, a decoder
    ///   its universe's fields name in their block, a static definition read
    ///   verbatim, and one read normalizing, withheld.
    /// - witness: `bridge::tests::a_constant_resolves_to_its_readmitted_position`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[spec(ensures: |ret| ret.is_err()
        || self.positions.admitted.get(&constant).copied() == ret.ok()
        || self.crossing.binary_search_by_key(&constant, |&(member, _)| member).is_ok_and(|found| self.crossing.get(found).map(|&(_, kernel)| kernel) == ret.as_ref().ok().copied())
        || (self.mode == Mode::Verbatim
            && self.operators.get(&Unfolded::Definition(constant)).copied() == ret.ok()))]
    fn constant_position(
        &mut self,
        at: ValueId,
        constant: ConstantIndex,
    ) -> Result<ConstantIndex, Refusal>
    {
        if let Some(&position) = self.positions.admitted.get(&constant) {
            return Ok(position);
        }
        if let Ok(found) = self
            .crossing
            .binary_search_by_key(&constant, |&(member, _)| member)
            && let Some(&(_, kernel)) = self.crossing.get(found)
        {
            return Ok(kernel);
        }
        match (self.mode, self.positions.definitions.body(constant)) {
            (Mode::Verbatim, Maybe::Present(body)) => {
                self.operator(Unfolded::Definition(constant), body)
            },
            (Mode::Verbatim | Mode::Normalizing, _) => Err(Refusal::Withheld { at, constant }),
        }
    }

    /// One certified step at `code`'s head, its certificate collected.
    ///
    /// # Specification
    /// - requires: every body the positions hold lives in the arena.
    /// - ensures: the reduct [`CodeDefinitions::reduce`] gives, minted, with
    ///   the step's certificate queued for replay; nothing for a rigid code.
    /// - fails: [`Refusal::CertificateDeclined`] with
    ///   [`ReplayDecline::EngineDeclined`] when certification yields no
    ///   dialogue; [`Refusal::DanglingNode`] for a node the arena does not
    ///   hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three arms, separated by a saturated instance, a
    ///   rigid code, and a step the normaliser declines.
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    /// - witness: `bridge::tests::a_rigid_static_instance_crosses_as_a_kernel_application`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(reduct)) => {
            self.certificates.last().is_some_and(|certificate| certificate.reduct() == reduct)
        },
        | Ok(Maybe::Absent(_)) | Err(_) => true,
    })]
    fn step(
        &mut self,
        code: ValueId,
    ) -> Result<Maybe<ValueId, unfolding::Absent>, Refusal>
    {
        let reduction = self
            .positions
            .definitions
            .reduce(self.arena, code)
            .map_err(fault)?;
        let Maybe::Present(reduction) = reduction
        else {
            return Ok(Maybe::Absent(unfolding::Absent::Rigid));
        };
        let unfolded = reduction.unfolded();
        let certificate = self
            .positions
            .definitions
            .certify(self.arena, reduction)
            .map_err(|_undecided| Refusal::CertificateDeclined {
                unfolded,
                reason: ReplayDecline::EngineDeclined,
            })?;
        let reduct = certificate.reduct();
        self.certificates.push(certificate);
        Ok(Maybe::Present(reduct))
    }

    /// Erase the value type `root` into `target`.
    ///
    /// # Specification
    /// - requires: no earlier erasure of this machine was refused.
    /// - ensures: the image of `root`, as [`Self::erase`] gives it.
    /// - fails: as [`Self::erase`]; [`Refusal::MachineInvariant`] when the
    ///   image is not a value type.
    /// - panics: none.
    ///
    /// # Errors
    /// - any [`Refusal`] [`Self::erase`] gives.
    /// - [`Refusal::MachineInvariant`] — the machine produced another family.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — base, returner-containing and universe types expose
    ///   their exact kernel formers or named refusal; returning an unrelated
    ///   family or an unminted image changes this bounded erasure evidence.
    /// - witness: `bridge::tests::returner_type_lowers`
    /// - witness: `bridge::tests::a_sorted_universe_readmits_at_its_level`
    /// - witness: `bridge::tests::the_machine_faults_are_refused_exactly`
    #[spec(ensures: |ret| match ret { | Ok(image) => target.value_type(image).is_some()
        && self.reached().value_types.get(&root) == Some(&Image::Erased(image)), | Err(_) => true })]
    fn value_type(
        &mut self,
        target: &mut TermArena,
        root: ValueTypeId,
    ) -> Result<gandr_kernel_term::ValueTypeId, Refusal>
    {
        let image = self.erase(target, CoreNode::Type(TypeNode::Value(root)))?;
        match image {
            AnyNode::ValueType(erased) => Ok(erased),
            AnyNode::Value(_) | AnyNode::Computation(_) | AnyNode::CompType(_) => {
                Err(Refusal::MachineInvariant)
            },
        }
    }

    /// Erase the value `root` into `target`.
    ///
    /// # Specification
    /// - requires: no earlier erasure of this machine was refused.
    /// - ensures: the image of `root`, as [`Self::erase`] gives it.
    /// - fails: as [`Self::erase`]; [`Refusal::MachineInvariant`] when the
    ///   image is not a value.
    /// - panics: none.
    ///
    /// # Errors
    /// - any [`Refusal`] [`Self::erase`] gives.
    /// - [`Refusal::MachineInvariant`] — the machine produced another family.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — literals, bound variables, named constants and shared
    ///   subterms expose exact kernel images or refusal; wrong remapping,
    ///   duplicated sharing and an unminted result differ on these finite
    ///   forms.
    /// - witness: `bridge::tests::returning_a_literal_lowers`
    /// - witness: `bridge::tests::a_bound_variable_resolves_to_a_de_bruijn_index`
    /// - witness: `bridge::tests::a_constant_resolves_to_its_readmitted_position`
    /// - witness: `bridge::tests::a_shared_subterm_is_erased_once`
    #[spec(ensures: |ret| match ret { | Ok(image) => target.value(image).is_some()
        && self.reached().values.get(&root) == Some(&Image::Erased(image)), | Err(_) => true })]
    fn value(
        &mut self,
        target: &mut TermArena,
        root: ValueId,
    ) -> Result<gandr_kernel_term::ValueId, Refusal>
    {
        let image = self.erase(target, CoreNode::Term(TermNode::Value(root)))?;
        match image {
            AnyNode::Value(erased) => Ok(erased),
            AnyNode::Computation(_) | AnyNode::ValueType(_) | AnyNode::CompType(_) => {
                Err(Refusal::MachineInvariant)
            },
        }
    }

    /// Erase `root` and everything it reaches into `target`.
    ///
    /// # Specification
    /// - requires: no earlier erasure of this machine was refused, so no node
    ///   is left open.
    /// - ensures: the kernel node of the same former as `root` over the images
    ///   of its children, recursively, with every literal, base type, level,
    ///   sort and de Bruijn index carried unchanged and every constant replaced
    ///   by the kernel position its declaration took. A code the judgement
    ///   recorded a lift at is the quote of the kernel's lift of its decode at
    ///   its own level; a decode of a constant that crossed with a body is the
    ///   decode of that body, its certificate collected for replay; a decode of
    ///   any other code is the kernel's decode of its image. A node already
    ///   erased by this machine is not minted again.
    /// - fails: [`Refusal::Withheld`] for a constant whose declaration did not
    ///   cross; [`Refusal::OutOfFragment`] for a former the fragment has no
    ///   rule for; [`Refusal::Session`] for a session type, a session action or
    ///   a linear-zone variable; [`Refusal::DanglingNode`] for an id `source`
    ///   does not hold; [`Refusal::Cyclic`] for a node reached again while its
    ///   own erasure waits; [`Refusal::CertificateDeclined`] for an unfolding
    ///   the normaliser does not certify. Nodes minted before the refusal stay
    ///   in `target`; the caller owns the arena and its rollback.
    /// - panics: none.
    /// - intension: one kernel node is minted per distinct core node reached,
    ///   so sharing in the source is sharing in the image.
    ///
    /// # Errors
    /// - [`Refusal::Withheld`], [`Refusal::OutOfFragment`],
    ///   [`Refusal::Session`], [`Refusal::DanglingNode`], [`Refusal::Cyclic`],
    ///   [`Refusal::CertificateDeclined`] — as above.
    /// - [`Refusal::MachineInvariant`] — a frame received an image of another
    ///   family.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the per-former table and
    ///   the memo, separated by one node of every former of the core
    ///   vocabulary, each erased to its exact image or refused with its exact
    ///   former, a shared subterm asserted to be one kernel node, and the
    ///   linear, dangling and cyclic faults each asserted exactly.
    /// - witness: `bridge::tests::returning_a_literal_lowers`
    /// - witness: `bridge::tests::returner_type_lowers`
    /// - witness: `bridge::tests::a_bound_variable_resolves_to_a_de_bruijn_index`
    /// - witness: `bridge::tests::every_former_outside_the_fragment_is_refused_by_name`
    /// - witness: `bridge::tests::a_sorted_universe_readmits_at_its_level`
    /// - witness: `bridge::tests::an_unbound_sealed_atom_is_refused`
    /// - witness: `bridge::tests::a_shared_subterm_is_erased_once`
    /// - witness: `bridge::tests::the_machine_faults_are_refused_exactly`
    #[spec(ensures: |ret| match ret {
        | Ok(image) => self.frames.is_empty() && match (root,image) {
            | (CoreNode::Term(TermNode::Value(at)), AnyNode::Value(held)) => target.value(held).is_some() && self.reached().values.get(&at) == Some(&Image::Erased(held)),
            | (CoreNode::Term(TermNode::Computation(at)), AnyNode::Computation(held)) => target.computation(held).is_some() && self.reached().computations.get(&at) == Some(&Image::Erased(held)),
            | (CoreNode::Type(TypeNode::Value(at)), AnyNode::ValueType(held)) => target.value_type(held).is_some() && self.reached().value_types.get(&at) == Some(&Image::Erased(held)),
            | (CoreNode::Type(TypeNode::Computation(at)), AnyNode::CompType(held)) => target.comp_type(held).is_some() && self.reached().comp_types.get(&at) == Some(&Image::Erased(held)),
            | _ => false,
        },
        | Err(_) => true,
    })]
    fn erase(
        &mut self,
        target: &mut TermArena,
        root: CoreNode,
    ) -> Result<AnyNode, Refusal>
    {
        let mut step = Step::Descend(root);
        loop {
            step = match step {
                Step::Descend(node) => self.descend(target, node)?,
                Step::Ascend(image) => match self.frames.pop() {
                    Some(frame) => self.resume(target, frame, image)?,
                    None => return Ok(image),
                },
            };
        }
    }

    /// Start erasing `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a node already erased ascends its image; a leaf is minted and
    ///   ascends; a node with children opens its frame and descends to its
    ///   first child.
    /// - fails: as [`Self::erase`], for the node itself.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each term/type family, a shared child and recursive
    ///   back-edges expose exact images or cyclic faults; dispatching to
    ///   another family or losing the continuation changes these observations.
    /// - witness: `bridge::tests::returning_a_literal_lowers`
    /// - witness: `bridge::tests::returner_type_lowers`
    /// - witness: `bridge::tests::a_shared_subterm_is_erased_once`
    /// - witness: `bridge::tests::every_recursive_node_family_refuses_a_back_edge`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| self.frames.len() >= before && match ret {
            | Ok(Step::Descend(_)) => self.frames.len() > before,
            | Ok(Step::Ascend(image)) => matches!((node,image),
                (CoreNode::Term(TermNode::Value(_)), AnyNode::Value(_))
                | (CoreNode::Term(TermNode::Computation(_)), AnyNode::Computation(_))
                | (CoreNode::Type(TypeNode::Value(_)), AnyNode::ValueType(_))
                | (CoreNode::Type(TypeNode::Computation(_)), AnyNode::CompType(_))),
            | Err(_) => true,
        },
    )]
    fn descend(
        &mut self,
        target: &mut TermArena,
        node: CoreNode,
    ) -> Result<Step, Refusal>
    {
        match node {
            CoreNode::Term(TermNode::Value(at)) => self.descend_value(target, at),
            CoreNode::Term(TermNode::Computation(at)) => self.descend_computation(target, at),
            CoreNode::Type(TypeNode::Value(at)) => self.descend_value_type(target, at),
            CoreNode::Type(TypeNode::Computation(at)) => self.descend_comp_type(target, at),
        }
    }

    /// Start erasing the value `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::descend`]: a code with a recorded lift opens its
    ///   frame and decodes at its own level; otherwise an intuitionistic
    ///   variable, a constant that crossed, the unit value and an integer or
    ///   string literal are minted, and a thunk, a returned endpoint, a quote
    ///   and a pair open their frames. A static application at a reducible
    ///   head, read normalizing, takes its certified step and opens the frame
    ///   awaiting its reduct; any other opens the frames of a kernel static
    ///   application. Read verbatim, a constant naming a static definition and
    ///   a closed static lambda are minted as the static operators they are
    ///   numbered at. On success the current mode's memo holds `at`.
    /// - fails: [`Refusal::Cyclic`] for an open value;
    ///   [`Refusal::DanglingNode`]; [`Refusal::Session`];
    ///   [`Refusal::Withheld`]; [`Refusal::CertificateDeclined`] for a step the
    ///   normaliser does not certify; [`Refusal::OutOfFragment`] for a numeric
    ///   literal, an injection, a value lift, and a static lambda read
    ///   normalizing or open.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::erase`], whose per-former table this is,
    ///   with the static formers separated by a saturated instance erased to
    ///   its reduct, a rigid instance erased as a kernel static application,
    ///   and a certificate's side numbering its operators.
    /// - witness: `bridge::tests::every_former_outside_the_fragment_is_refused_by_name`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    /// - witness: `bridge::tests::a_rigid_static_instance_crosses_as_a_kernel_application`
    #[spec(ensures: |ret| ret.is_err() || self.reached().values.contains_key(&at))]
    fn descend_value(
        &mut self,
        target: &mut TermArena,
        at: ValueId,
    ) -> Result<Step, Refusal>
    {
        let node = CoreNode::Term(TermNode::Value(at));
        match self.memo().values.get(&at) {
            Some(&Image::Erased(erased)) => return Ok(Step::Ascend(AnyNode::Value(erased))),
            Some(&Image::Open) => return Err(Refusal::Cyclic { node }),
            None => {},
        }
        if let Some(lift) = self.source.lifts.get(&at) {
            self.memo().values.insert(at, Image::Open);
            self.frames.push(Frame::LiftedCode { at });
            self.frames.push(Frame::DecodeLift {
                target: lift.target().clone(),
            });
            return self.decode(target, at, lift.natural().clone(), GroundSort::Value);
        }
        let Some(value) = self.arena.value(at)
        else {
            return Err(Refusal::DanglingNode { node });
        };
        let unadmitted = |former| Refusal::OutOfFragment { at: node, former };
        let (frame, child) = match *value {
            Value::Constructor { .. } | Value::Record(_) => {
                return self.prepare_native(target, node);
            },
            Value::Reify(_) => return Err(unadmitted(UnadmittedFormer::Reify)),
            Value::ListNil => return Ok(self.erased_value(at, target.value_list_nil())),
            Value::ListCons(head, tail) => (
                Frame::ListHead { at, tail },
                CoreNode::Term(TermNode::Value(head)),
            ),
            Value::Primitive { primitive, .. } => {
                let position = self
                    .positions
                    .native
                    .get(&primitive)
                    .copied()
                    .ok_or(Refusal::MachineInvariant)?;
                return Ok(self.erased_value(at, target.value_constant(position)));
            },
            Value::PathRefl(code) => (
                Frame::PathRefl { at },
                CoreNode::Term(TermNode::Value(code)),
            ),
            Value::PathProduct(first, second) => match self.source.natives.get(&at) {
                Some(&native) if native != at => {
                    self.memo().values.insert(at, Image::Open);
                    self.frames.push(Frame::Reduced { at });
                    return Ok(Step::Descend(CoreNode::Term(TermNode::Value(native))));
                },
                Some(_) | None => (
                    Frame::PathProductFirst { at, second },
                    CoreNode::Term(TermNode::Value(first)),
                ),
            },
            Value::PathEquiv {
                path_type,
                forward,
                backward,
                ref evidence,
            } => (
                Frame::PathEquivType {
                    at,
                    forward,
                    backward,
                    evidence: alloc::sync::Arc::clone(evidence),
                },
                CoreNode::Type(TypeNode::Value(path_type)),
            ),
            Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            } => return Ok(self.erased_value(at, target.value_variable(index))),
            Value::Variable {
                zone: Zone::Linear, ..
            } => {
                return Err(Refusal::Session {
                    at: CoreNode::Term(TermNode::Value(at)),
                });
            },
            Value::Constant(constant) => {
                let position = self.constant_position(at, constant)?;
                return Ok(self.erased_value(at, target.value_constant(position)));
            },
            Value::Literal(ref literal) => match literal.base_type() {
                BaseType::Integer | BaseType::String => {
                    return Ok(self.erased_value(at, target.value_literal(literal.clone())));
                },
                BaseType::Numeric => return Err(unadmitted(UnadmittedFormer::NumericLiteral)),
            },
            Value::Thunk(body) => (
                Frame::Thunk { at },
                CoreNode::Term(TermNode::Computation(body)),
            ),
            Value::Quote(quoted) => (Frame::Quote { at }, CoreNode::Type(TypeNode::Value(quoted))),
            Value::QuoteComputation(quoted) => (
                Frame::QuoteComputation { at },
                CoreNode::Type(TypeNode::Computation(quoted)),
            ),
            Value::Tuple(_) => return self.prepare_native(target, node),
            Value::Injection(summand, body) => (
                Frame::Injection { at, summand },
                CoreNode::Term(TermNode::Value(body)),
            ),
            Value::Lift { .. } => return Err(unadmitted(UnadmittedFormer::ValueLift)),
            Value::StaticLambda(_) => {
                let position = self.abstraction(at)?;
                return Ok(self.erased_value(at, target.value_constant(position)));
            },
            Value::Hole(hole) => return Err(Refusal::Hole { at: node, hole }),
            Value::Here(point) => (
                Frame::Here {
                    at,
                    family: Family::Path,
                },
                CoreNode::Term(TermNode::Value(point)),
            ),
            Value::Funext(..) => return self.prepare_funext(target, at),
            Value::Equiv(forward, backward) => {
                let Some(decided) = self.source.equivalences.get(&at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                (
                    Frame::PathEquivType {
                        at,
                        forward,
                        backward,
                        evidence: alloc::sync::Arc::clone(decided.evidence()),
                    },
                    CoreNode::Type(TypeNode::Value(decided.classifier())),
                )
            },
            // The forward map is the lowering's derived copy of the record's
            // first projection, and the record's type names the identity; the
            // kernel derives both from the record, so only the record crosses.
            Value::Univalence(record, _) => (
                Frame::UnivalenceRecord { at },
                CoreNode::Term(TermNode::Value(record)),
            ),
            Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..)
                if self.source.flows.contains_key(&at) =>
            {
                let Some(decided) = self.source.flows.get(&at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                (
                    Frame::SessionCertificate {
                        at,
                        relation: decided.relation(),
                        evidence: alloc::sync::Arc::clone(decided.evidence()),
                    },
                    CoreNode::Type(TypeNode::Value(decided.classifier())),
                )
            },
            Value::Stay(point) => (
                Frame::Here {
                    at,
                    family: Family::Flow,
                },
                CoreNode::Term(TermNode::Value(point)),
            ),
            Value::Then(first, second) => (
                Frame::ThenFirst { at, second },
                CoreNode::Term(TermNode::Value(first)),
            ),
            Value::FlowProduct(first, second) => (
                Frame::FlowProductFirst { at, second },
                CoreNode::Term(TermNode::Value(first)),
            ),
            Value::Forward(translator) => match self.source.directed.get(&at) {
                Some(&crate::forward::Directed::Forward(ref decided)) => (
                    Frame::ForwardType {
                        at,
                        translator,
                        images: alloc::sync::Arc::from(decided.images()),
                        dialogues: alloc::sync::Arc::from(decided.dialogues()),
                    },
                    CoreNode::Type(TypeNode::Value(decided.classifier())),
                ),
                Some(&crate::forward::Directed::Function(_)) | None => {
                    return Err(Refusal::MachineInvariant);
                },
            },
            Value::FunctionFlow(domain, codomain) => match self.source.directed.get(&at) {
                Some(&crate::forward::Directed::Function(classifier)) => (
                    Frame::FunctionFlowType {
                        at,
                        domain,
                        codomain,
                    },
                    CoreNode::Type(TypeNode::Value(classifier)),
                ),
                Some(&crate::forward::Directed::Forward(_)) | None => {
                    return Err(Refusal::MachineInvariant);
                },
            },
            Value::Recorded(_) => return Err(unadmitted(UnadmittedFormer::Run)),
            Value::Ua { .. } => {
                let Some(&path) = self.source.natives.get(&at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.memo().values.insert(at, Image::Open);
                self.frames.push(Frame::Reduced { at });
                return Ok(Step::Descend(CoreNode::Term(TermNode::Value(path))));
            },
            // Elaboration replaces every nested computation and written run
            // before a verdict's body is answered, so none reaches the kernel;
            // a session statement is always recorded.
            Value::Nested(_) | Value::Run(_) | Value::SessionRelated { .. } => {
                return Err(Refusal::MachineInvariant);
            },
            Value::Returned(computation) => (
                Frame::Returned { at },
                CoreNode::Term(TermNode::Computation(computation)),
            ),
            Value::Mark { body, .. } => (
                Frame::UnmarkedValue { at },
                CoreNode::Term(TermNode::Value(body)),
            ),
            Value::StaticApplication(head, argument) => {
                if self.mode == Mode::Normalizing
                    && let Maybe::Present(reduct) = self.step(at)?
                {
                    self.memo().values.insert(at, Image::Open);
                    self.frames.push(Frame::Reduced { at });
                    return Ok(Step::Descend(CoreNode::Term(TermNode::Value(reduct))));
                }
                (
                    Frame::StaticHead { at, argument },
                    CoreNode::Term(TermNode::Value(head)),
                )
            },
        };
        self.memo().values.insert(at, Image::Open);
        self.frames.push(frame);
        Ok(Step::Descend(child))
    }

    /// Queue the normal forms the function extensionality `at` records, so
    /// each crosses on the machine's own stack before its evaluation is
    /// assembled.
    ///
    /// # Specification
    /// - requires: the judgement accepted `at` as a function extensionality.
    /// - ensures: `at` is open; every application step's two normal forms are
    ///   visited, in step order and left before right, before [`Self::funext`]
    ///   assembles the evaluation; a record of returns alone assembles at once.
    /// - fails: [`Refusal::MachineInvariant`] when the judgement recorded
    ///   nothing at `at`; as [`Self::funext`] when it assembles at once.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the quantified witness erases its normal forms before
    ///   its evaluation and the kernel replays it; a record of returns alone
    ///   crosses as a higher evaluation.
    /// - witness: `bridge::tests::a_quantified_funext_crosses_as_a_quantified_evaluation`
    /// - witness: `bridge::tests::a_funext_crosses_as_a_higher_evaluation`
    #[spec(ensures: |ret| ret.is_err() || !matches!(ret, Ok(Step::Descend(_))) || !self.frames.is_empty())]
    fn prepare_funext(
        &mut self,
        target: &mut TermArena,
        at: ValueId,
    ) -> Result<Step, Refusal>
    {
        let source = self.source;
        let Some(record) = source.funexts.get(&at)
        else {
            return Err(Refusal::MachineInvariant);
        };
        self.memo().values.insert(at, Image::Open);
        self.frames.push(Frame::FunextBuild(at));
        for step in record.steps().iter().rev() {
            if let FunextStep::Apply {
                ref left,
                ref right,
                ..
            } = *step
            {
                self.frames.extend(
                    [right.normal(), left.normal()]
                        .map(|normal| Frame::NativeNext(CoreNode::Term(TermNode::Value(normal)))),
                );
            }
        }
        match self.frames.pop() {
            Some(Frame::NativeNext(child)) => Ok(Step::Descend(child)),
            Some(Frame::FunextBuild(node)) => self.funext(target, node),
            _ => Err(Refusal::MachineInvariant),
        }
    }

    /// Erase the function extensionality `at` into the kernel's higher
    /// evaluation when every step returns, and into its quantified evaluation
    /// otherwise: per return the value each function returns, the diagonal
    /// evidence that the two agree and the machine's two traces; per
    /// application each function's closed normal form and the machine's two
    /// traces; every trace with its anchors forgotten.
    ///
    /// # Specification
    /// - requires: the judgement accepted `at` as a function extensionality;
    ///   every application step's normal forms have crossed in the current
    ///   mode.
    /// - ensures: when every recorded step returns, one kernel component per
    ///   step, in order, each carrying the images of the two returned values
    ///   and the diagonal of the first — the unit value at the unit type, a
    ///   base atom and a sum's absent payload, a pair at a pair, an injection's
    ///   payload's diagonal at an injection — and one dialogue pair per
    ///   component, the machine's decisions with every anchor erased. Otherwise
    ///   one kernel step per recorded step, in order: a return as a component
    ///   is, its three children in that order; an application with its fibre
    ///   and the images its two normal forms crossed as. The two functions are
    ///   not erased: the kernel reads them from the identity type it checks the
    ///   evaluation at.
    /// - provides: the evidence the kernel's higher or quantified evaluation
    ///   replays, the core's decision recomputed rather than trusted.
    /// - fails: [`Refusal::MachineInvariant`] when the judgement recorded no
    ///   steps at `at`, a returned value is not first order or a normal form
    ///   has no image; [`Refusal::Hole`] at a hole a returned value holds; a
    ///   constant's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — as above.
    ///
    /// # Termination
    /// - reason: a `for` loop over the recorded steps and, per value, a `while
    ///   let` worklist over its finite tree, not recursion; the normal forms
    ///   crossed on the machine's own stack before.
    /// - measure: the steps left, then the nodes left to visit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `funext(not ∘ not, id)` over a binary sum of units
    ///   crosses as a higher evaluation and the kernel replays it; a dropped
    ///   component or a swapped trace is refused by the kernel; `λf. f(true)`
    ///   related to its bind form crosses as a quantified evaluation the kernel
    ///   replays.
    /// - witness: `bridge::tests::a_funext_crosses_as_a_higher_evaluation`
    /// - witness: `bridge::tests::a_quantified_funext_crosses_as_a_quantified_evaluation`
    #[spec(ensures: |ret| ret.is_err() || self.reached().values.contains_key(&at))]
    fn funext(
        &mut self,
        target: &mut TermArena,
        at: ValueId,
    ) -> Result<Step, Refusal>
    {
        let source = self.source;
        let Some(record) = source.funexts.get(&at)
        else {
            return Err(Refusal::MachineInvariant);
        };
        let forget = |decisions: &[ConversionDecision<TraceNode>]| {
            decisions
                .iter()
                .map(|decision| decision.map(|_| ()))
                .collect::<Vec<_>>()
        };
        let quantified = record
            .steps()
            .iter()
            .any(|step| matches!(step, FunextStep::Apply { .. }));
        let image = if quantified {
            let mut steps = Vec::with_capacity(record.steps().len());
            let mut children = Vec::new();
            for step in record.steps() {
                match *step {
                    FunextStep::Return {
                        ref left,
                        ref right,
                    } => {
                        let (left_image, evidence) = self.returned(target, left.returned())?;
                        let (right_image, _) = self.returned(target, right.returned())?;
                        steps.push(QuantifiedStep::Return(EvaluationDialogues {
                            left: forget(left.decisions()),
                            right: forget(right.decisions()),
                        }));
                        children.extend([left_image, right_image, evidence]);
                    },
                    FunextStep::Apply {
                        fibre,
                        ref left,
                        ref right,
                    } => {
                        let [left_image, right_image] =
                            [left.normal(), right.normal()].map(|normal| {
                                match self.reached().values.get(&normal) {
                                    Some(&Image::Erased(image)) => Ok(image),
                                    _ => Err(Refusal::MachineInvariant),
                                }
                            });
                        steps.push(QuantifiedStep::Apply {
                            fibre,
                            dialogues: EvaluationDialogues {
                                left: forget(left.decisions()),
                                right: forget(right.decisions()),
                            },
                        });
                        children.extend([left_image?, right_image?]);
                    },
                }
            }
            target.value_quantified_evaluation(
                alloc::sync::Arc::from(steps),
                children.into_boxed_slice(),
            )
        }
        else {
            let mut dialogues = Vec::with_capacity(record.steps().len());
            let mut components = Vec::with_capacity(record.steps().len());
            for step in record.steps() {
                let FunextStep::Return {
                    ref left,
                    ref right,
                } = *step
                else {
                    return Err(Refusal::MachineInvariant);
                };
                let (left_image, evidence) = self.returned(target, left.returned())?;
                let (right_image, _) = self.returned(target, right.returned())?;
                dialogues.push(EvaluationDialogues {
                    left: forget(left.decisions()),
                    right: forget(right.decisions()),
                });
                components.push(EvaluationComponent {
                    left: left_image,
                    right: right_image,
                    evidence,
                });
            }
            target.value_higher_evaluation(
                alloc::sync::Arc::from(dialogues),
                components.into_boxed_slice(),
            )
        };
        Ok(self.erased_value(at, image))
    }

    /// The kernel image of `value`, a first-order value a function returned,
    /// beside its diagonal evidence at the identity of its type.
    ///
    /// # Specification
    /// - requires: `value` is a normal form of a type built from the unit type,
    ///   the base atoms and binary sums and products.
    /// - ensures: the image, with tuples, injections, intuitionistic variables,
    ///   literals and constants rebuilt as they stand and marks read through;
    ///   the evidence as [`Self::funext`] states it.
    /// - fails: [`Refusal::Hole`] at a hole; [`Refusal::MachineInvariant`] at
    ///   any other former; a constant's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — as above.
    ///
    /// # Termination
    /// - reason: a `while let` worklist over the value's finite tree, not
    ///   recursion.
    /// - measure: the nodes left to visit, each replaced by its children.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both injections of a binary sum of units cross with
    ///   unit evidence, and the kernel accepts the evidence at their fibre.
    /// - witness: `bridge::tests::a_funext_crosses_as_a_higher_evaluation`
    /// - witness: `bridge::tests::a_funext_returning_a_literal_crosses_with_the_literal`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|(image, evidence)| target.value(image).is_some() && target.value(evidence).is_some()))]
    fn returned(
        &mut self,
        target: &mut TermArena,
        value: ValueId,
    ) -> Result<(gandr_kernel_term::ValueId, gandr_kernel_term::ValueId), Refusal>
    {
        /// One step of the walk.
        #[derive(Clone, Copy)]
        enum Task
        {
            /// Rebuild the node.
            Visit(ValueId),
            /// Pair the two images on top.
            Pair,
            /// Inject the image on top.
            Inject(Summand),
        }
        let mut tasks = Vec::from([Task::Visit(value)]);
        let mut built: Vec<(gandr_kernel_term::ValueId, gandr_kernel_term::ValueId)> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(node) => {
                    let Some(former) = self.arena.value(node)
                    else {
                        return Err(Refusal::DanglingNode {
                            node: CoreNode::Term(TermNode::Value(node)),
                        });
                    };
                    let image = match *former {
                        Value::Tuple(ref parts) => match **parts {
                            [] => target.value_unit(),
                            [first, second] => {
                                tasks.extend([Task::Pair, Task::Visit(second), Task::Visit(first)]);
                                continue;
                            },
                            _ => return Err(Refusal::MachineInvariant),
                        },
                        Value::Injection(summand, body) => {
                            tasks.extend([Task::Inject(summand), Task::Visit(body)]);
                            continue;
                        },
                        Value::Mark { body, .. } => {
                            tasks.push(Task::Visit(body));
                            continue;
                        },
                        Value::Variable {
                            zone: Zone::Intuitionistic,
                            index,
                        } => target.value_variable(index),
                        Value::Literal(ref literal)
                            if matches!(
                                literal.base_type(),
                                BaseType::Integer | BaseType::String
                            ) =>
                        {
                            target.value_literal(literal.clone())
                        },
                        Value::Constant(constant) => {
                            let position = self.constant_position(node, constant)?;
                            target.value_constant(position)
                        },
                        Value::Hole(hole) => {
                            return Err(Refusal::Hole {
                                at: CoreNode::Term(TermNode::Value(node)),
                                hole,
                            });
                        },
                        Value::Primitive { .. }
                        | Value::PathRefl(_)
                        | Value::PathProduct(..)
                        | Value::PathEquiv { .. }
                        | Value::Here(_)
                        | Value::Funext(..)
                        | Value::Equiv(..)
                        | Value::Univalence(..)
                        | Value::Ua { .. }
                        | Value::SessionRelated { .. }
                        | Value::Stay(_)
                        | Value::Then(..)
                        | Value::FlowProduct(..)
                        | Value::Forward(_)
                        | Value::FunctionFlow(..)
                        | Value::Recorded(_)
                        | Value::Returned(_)
                        | Value::Nested(_)
                        | Value::Run(_)
                        | Value::Variable { .. }
                        | Value::Literal(_)
                        | Value::ListNil
                        | Value::ListCons(..)
                        | Value::Thunk(_)
                        | Value::Lift { .. }
                        | Value::Quote(_)
                        | Value::QuoteComputation(_)
                        | Value::StaticLambda(_)
                        | Value::StaticApplication(..)
                        | Value::Constructor { .. }
                        | Value::Record(_)
                        | Value::Reify(_) => return Err(Refusal::MachineInvariant),
                    };
                    let unit = target.value_unit();
                    built.push((image, unit));
                },
                Task::Pair => {
                    let (Some(second), Some(first)) = (built.pop(), built.pop())
                    else {
                        return Err(Refusal::MachineInvariant);
                    };
                    let image = target.value_tuple(&[first.0, second.0]);
                    let evidence = target.value_tuple(&[first.1, second.1]);
                    built.push((image, evidence));
                },
                Task::Inject(summand) => {
                    let Some((payload, evidence)) = built.pop()
                    else {
                        return Err(Refusal::MachineInvariant);
                    };
                    built.push((target.value_injection(summand, payload), evidence));
                },
            }
        }
        match (built.pop(), built.is_empty()) {
            (Some(image), true) => Ok(image),
            _ => Err(Refusal::MachineInvariant),
        }
    }

    /// The static operator the static lambda `at` is numbered at, read
    /// verbatim.
    ///
    /// # Specification
    /// - requires: `at` is a static lambda.
    /// - ensures: [`Self::operator`]'s position for the lambda, whose body
    ///   beneath its lambda chain is the operator's.
    /// - fails: [`Refusal::OutOfFragment`] naming
    ///   [`UnadmittedFormer::StaticLambda`] when read normalizing — the kernel
    ///   has no static lambda, and a static normal form holds none — or when
    ///   the lambda reaches a binder outside itself, which no closed operator
    ///   can stand for; the reach's fault, converted.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three arms, separated by a closed lambda read
    ///   verbatim, an open one, and one read normalizing.
    /// - witness: `bridge::tests::a_static_lambda_crosses_only_as_a_closed_operator`
    #[spec(ensures: |ret| ret.is_err()
        || (self.mode == Mode::Verbatim
            && self.operators.get(&Unfolded::Abstraction(at)).copied() == ret.ok()))]
    fn abstraction(
        &mut self,
        at: ValueId,
    ) -> Result<ConstantIndex, Refusal>
    {
        let node = CoreNode::Term(TermNode::Value(at));
        let refused = Refusal::OutOfFragment {
            at: node,
            former: UnadmittedFormer::StaticLambda,
        };
        if self.mode == Mode::Normalizing
            || loose_reach(self.arena, node).map_err(fault)? != BinderDepth::default()
        {
            return Err(refused);
        }
        self.operator(Unfolded::Abstraction(at), at)
    }

    /// The images the current mode minted, read.
    ///
    /// # Specification
    /// trivial.
    const fn reached(&self) -> &Memo
    {
        match self.mode {
            Mode::Normalizing => &self.normalized,
            Mode::Verbatim => &self.verbatim,
        }
    }

    /// Start erasing the computation `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: ordinary computations open one continuation; a native case
    ///   queues its motive and every branch after the scrutinee; a sum case
    ///   queues every branch after the scrutinee.
    /// - fails: [`Refusal::Cyclic`] for an open computation or
    ///   [`Refusal::DanglingNode`] for an absent source.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — admitted computation formers, a shared child and a
    ///   back-edge expose exact images or cyclic refusal. Missing open marks,
    ///   wrong cache hits and absent continuation frames change these answers.
    /// - witness: `bridge::tests::returning_a_literal_lowers`
    /// - witness: `bridge::tests::a_shared_subterm_is_erased_once`
    /// - witness: `bridge::tests::every_recursive_node_family_refuses_a_back_edge`
    /// - witness: `tests::native_formers::empty_data_elimination_preserves_the_ambient_scope`
    /// - witness: `tests::native_formers::dependent_data_parameters_and_case_motives`
    #[spec(
        captures: [before = self.frames.len(), held = self.reached().computations.get(&at).copied(), continuations = self.arena.computation(at).map_or(Some(1_usize), |node| match *node { Computation::DataCase { ref branches, .. } => branches.len().checked_add(2), Computation::Case { ref branches, .. } => branches.len().checked_add(1), Computation::Ascribe { .. } => Some(2_usize), Computation::Primitive { .. } | Computation::Transport(..) | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Application(..) | Computation::Return(_) | Computation::Bind(..) | Computation::Force(_) | Computation::Split { .. } | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Hole(_) | Computation::Mark { .. } | Computation::ListFold { .. } | Computation::Perform { .. } | Computation::Handle { .. } | Computation::Exercise { .. } | Computation::Scope { .. } | Computation::Resume(..) | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..) | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => Some(1_usize) })],
        ensures: |ret| match held {
            | Some(Image::Erased(image)) => ret == Ok(Step::Ascend(AnyNode::Computation(image))) && self.frames.len() == before,
            | Some(Image::Open) => ret == Err(Refusal::Cyclic { node: CoreNode::Term(TermNode::Computation(at)) }) && self.frames.len() == before,
            | None => ret.is_err() || (matches!(ret, Ok(Step::Descend(_))) && self.frames.len().checked_sub(before) == continuations
                && self.reached().computations.get(&at) == Some(&Image::Open)),
        },
    )]
    fn descend_computation(
        &mut self,
        target: &mut TermArena,
        at: ComputationId,
    ) -> Result<Step, Refusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        match self.memo().computations.get(&at) {
            Some(&Image::Erased(erased)) => {
                return Ok(Step::Ascend(AnyNode::Computation(erased)));
            },
            Some(&Image::Open) => return Err(Refusal::Cyclic { node }),
            None => {},
        }
        let Some(computation) = self.arena.computation(at)
        else {
            return Err(Refusal::DanglingNode { node });
        };
        let unadmitted = |former| Refusal::OutOfFragment { at: node, former };
        let (frame, child) = match *computation {
            Computation::DataCase { .. }
            | Computation::RecordProjection(..)
            | Computation::TupleProjection(..)
            | Computation::Ascribe { .. } => {
                return self.prepare_native(target, node);
            },
            Computation::Perform { .. } => return Err(unadmitted(UnadmittedFormer::Perform)),
            Computation::Handle { .. } => return Err(unadmitted(UnadmittedFormer::Handle)),
            Computation::Resume(..) => return Err(unadmitted(UnadmittedFormer::Resume)),
            Computation::Reset(_) => return Err(unadmitted(UnadmittedFormer::Reset)),
            Computation::Shift(_) => return Err(unadmitted(UnadmittedFormer::Shift)),
            Computation::Exercise { .. } => return Err(unadmitted(UnadmittedFormer::Exercise)),
            Computation::Scope { .. } => return Err(unadmitted(UnadmittedFormer::Scope)),
            Computation::Memory(_) => return Err(unadmitted(UnadmittedFormer::Memory)),
            Computation::World(_) => return Err(Refusal::Located { at: node }),
            Computation::Ride {
                motive,
                flow,
                value,
            } => {
                self.memo().computations.insert(at, Image::Open);
                self.frames.push(Frame::PathTransportMotive {
                    at,
                    path: flow,
                    value,
                    family: Family::Flow,
                });
                return Ok(Step::Descend(CoreNode::Type(TypeNode::Value(motive))));
            },
            Computation::With(first, second) => (
                Frame::WithFirst { at, second },
                TermNode::Computation(first),
            ),
            Computation::Project(side, pair) => {
                (Frame::Project { at, side }, TermNode::Computation(pair))
            },
            Computation::ListFold { element, .. } => {
                self.memo().computations.insert(at, Image::Open);
                self.frames.push(Frame::ListElement { at });
                return Ok(Step::Descend(CoreNode::Type(TypeNode::Value(element))));
            },
            Computation::Primitive {
                primitive,
                arguments,
            } => {
                use gandr_core_term::primitive::Arguments;
                let position = self
                    .positions
                    .native
                    .get(&primitive)
                    .copied()
                    .ok_or(Refusal::MachineInvariant)?;
                let value = target.value_constant(position);
                let head = target.computation_force(value);
                match arguments {
                    Arguments::Unary(argument) => (
                        Frame::ApplicationArgument { at, head },
                        TermNode::Value(argument),
                    ),
                    Arguments::Binary([first, second]) => (
                        Frame::NativeFirst { at, head, second },
                        TermNode::Value(first),
                    ),
                }
            },
            Computation::Transport(path, value) => {
                (Frame::TransportPath { at, value }, TermNode::Value(path))
            },
            Computation::PathTransport {
                motive,
                path,
                value,
            } => {
                self.memo().computations.insert(at, Image::Open);
                self.frames.push(Frame::PathTransportMotive {
                    at,
                    path,
                    value,
                    family: Family::Path,
                });
                return Ok(Step::Descend(CoreNode::Type(TypeNode::Value(motive))));
            },
            Computation::TelescopeTransport { motive, .. } => {
                self.memo().computations.insert(at, Image::Open);
                self.frames.push(Frame::TelescopeMotive { at });
                return Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(motive))));
            },
            Computation::Lambda(body) => (Frame::Lambda { at }, TermNode::Computation(body)),
            Computation::Fixpoint { body, evidence } => (
                Frame::Fixpoint { at, evidence },
                TermNode::Computation(body),
            ),
            Computation::Application(head, argument) => (
                Frame::ApplicationHead { at, argument },
                TermNode::Computation(head),
            ),
            Computation::Return(value) => (Frame::Return { at }, TermNode::Value(value)),
            Computation::Force(value) => (Frame::Force { at }, TermNode::Value(value)),
            Computation::Bind(bound, body) => {
                (Frame::BindBound { at, body }, TermNode::Computation(bound))
            },
            Computation::Case { .. } => return self.prepare_native(target, node),
            Computation::Split {
                scrutinee,
                motive: SplitMotive::Scrutinee(motive),
                body,
                ..
            } => (
                Frame::SigmaSplitScrutinee { at, motive, body },
                TermNode::Value(scrutinee),
            ),
            Computation::Split {
                scrutinee,
                arity,
                motive: SplitMotive::Ambient,
                body,
            } => (
                Frame::SplitReduct { at },
                TermNode::Computation(self.split_reduct(scrutinee, arity, body)),
            ),
            Computation::Session(_) => return Err(Refusal::Session { at: node }),
            Computation::Hole(hole) => return Err(Refusal::Hole { at: node, hole }),
            Computation::Mark { body, .. } => (
                Frame::UnmarkedComputation { at },
                TermNode::Computation(body),
            ),
        };
        self.memo().computations.insert(at, Image::Open);
        self.frames.push(frame);
        Ok(Step::Descend(CoreNode::Term(child)))
    }

    /// Start erasing the value type `at`, read through the fragment's view.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::descend`]: the integer and string atoms, the unit
    ///   type and a universe are minted; a sealed atom is minted at the kernel
    ///   position its abstract type was admitted at; a thunk type, a lift, an
    ///   eager product and a static Pi open their frames; a decode opens its
    ///   frame and decodes its code.
    /// - fails: [`Refusal::Cyclic`] for an open value type;
    ///   [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Abstract`] for a
    ///   sealed atom whose abstract type did not cross, so nothing is minted at
    ///   a guessed position, and naming [`UnadmittedFormer::Stage`] for a
    ///   staged type, whose stage the kernel never reads from a term; whatever
    ///   the view or the decode refuses, converted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — atom, compound, universe and decode types expose
    ///   their exact kernel images; a sealed atom bound and unbound separates
    ///   the position map; a value-type back-edge is refused. Wrong family,
    ///   absent memo publication or dropped cycle detection differs.
    /// - witness: `bridge::tests::a_sorted_universe_readmits_at_its_level`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    /// - witness: `bridge::tests::every_recursive_node_family_refuses_a_back_edge`
    /// - witness: `bridge::tests::a_bound_sealed_atom_lowers_to_the_kernel_atom`
    /// - witness: `bridge::tests::an_unbound_sealed_atom_is_refused`
    #[spec(ensures: |ret| match ret {
        | Ok(Step::Ascend(AnyNode::ValueType(_)) | Step::Descend(_)) => self.reached().value_types.contains_key(&at),
        | Ok(Step::Ascend(_)) => false,
        | Err(Refusal::Cyclic { node }) => node == CoreNode::Type(TypeNode::Value(at)),
        | Err(_) => true,
    })]
    fn descend_value_type(
        &mut self,
        target: &mut TermArena,
        at: ValueTypeId,
    ) -> Result<Step, Refusal>
    {
        match self.memo().value_types.get(&at) {
            Some(&Image::Erased(erased)) => return Ok(Step::Ascend(AnyNode::ValueType(erased))),
            Some(&Image::Open) => {
                return Err(Refusal::Cyclic {
                    node: CoreNode::Type(TypeNode::Value(at)),
                });
            },
            None => {},
        }
        let (frame, child) = match value_type_view(self.arena, at)? {
            ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Sum(_)
            | ValueTypeView::Product(_) => {
                return self.prepare_native(target, CoreNode::Type(TypeNode::Value(at)));
            },
            ValueTypeView::Session(session) => {
                if session.state() != session.protocol().root() {
                    return Err(Refusal::Session {
                        at: CoreNode::Type(TypeNode::Value(at)),
                    });
                }
                return self.prepare_native(target, CoreNode::Type(TypeNode::Value(at)));
            },
            ValueTypeView::Flow {
                carrier,
                source,
                target: target_code,
            } => {
                let Ok(ValueTypeView::Universe {
                    sort: GroundSort::Value,
                    level,
                }) = value_type_view(self.arena, carrier)
                else {
                    self.memo().value_types.insert(at, Image::Open);
                    self.frames.push(Frame::PathCarrier {
                        at,
                        left: source,
                        right: target_code,
                        family: Family::Flow,
                    });
                    return Ok(Step::Descend(CoreNode::Type(TypeNode::Value(carrier))));
                };
                if *level != Level::zero() {
                    return Err(Refusal::OutOfFragment {
                        at: CoreNode::Type(TypeNode::Value(at)),
                        former: UnadmittedFormer::HigherFlow,
                    });
                }
                (
                    Frame::FlowSource { at, target_code },
                    CoreNode::Term(TermNode::Value(source)),
                )
            },
            ValueTypeView::World(_) => {
                return Err(Refusal::Located {
                    at: CoreNode::Type(TypeNode::Value(at)),
                });
            },
            ValueTypeView::Run(_) => {
                return Err(Refusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(at)),
                    former: UnadmittedFormer::Run,
                });
            },
            ValueTypeView::Stack { .. } => {
                return Err(Refusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(at)),
                    former: UnadmittedFormer::Stack,
                });
            },
            ValueTypeView::Capability { .. } => {
                return Err(Refusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(at)),
                    former: UnadmittedFormer::Capability,
                });
            },
            ValueTypeView::List(element) => (
                Frame::ListType { at },
                CoreNode::Type(TypeNode::Value(element)),
            ),
            ValueTypeView::PathUniverse(source, target_code) => (
                Frame::PathSource { at, target_code },
                CoreNode::Term(TermNode::Value(source)),
            ),
            ValueTypeView::Path {
                carrier,
                left,
                right,
            } => (
                Frame::PathCarrier {
                    at,
                    left,
                    right,
                    family: Family::Path,
                },
                CoreNode::Type(TypeNode::Value(carrier)),
            ),
            ValueTypeView::Integer => {
                return Ok(self.erased_value_type(at, target.value_type_base(BaseType::Integer)));
            },
            ValueTypeView::String => {
                return Ok(self.erased_value_type(at, target.value_type_base(BaseType::String)));
            },
            ValueTypeView::Unit => {
                return Ok(self.erased_value_type(at, target.value_type_unit()));
            },
            ValueTypeView::Universe { sort, level } => {
                let erased = target.value_type_universe(sort, level.clone());
                return Ok(self.erased_value_type(at, erased));
            },
            ValueTypeView::Abstract(atom) => {
                let Some(&position) = self.positions.admitted.get(&atom)
                else {
                    return Err(Refusal::OutOfFragment {
                        at: CoreNode::Type(TypeNode::Value(at)),
                        former: UnadmittedFormer::Abstract,
                    });
                };
                return Ok(self.erased_value_type(at, target.value_type_abstract(position)));
            },
            ValueTypeView::Staged { .. } => {
                return Err(Refusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(at)),
                    former: UnadmittedFormer::Stage,
                });
            },
            ValueTypeView::Thunk(body) => (
                Frame::ThunkType { at },
                CoreNode::Type(TypeNode::Computation(body)),
            ),
            ValueTypeView::Lift { inner, .. } => (
                Frame::TypeLift { at },
                CoreNode::Type(TypeNode::Value(inner)),
            ),
            ValueTypeView::Element { .. } | ValueTypeView::Unknown => {
                let Some(&gandr_core_term::ValueType::Element {
                    code,
                    target: ref level,
                }) = self.arena.value_type(at)
                else {
                    return Err(Refusal::Unknown {
                        at: CoreNode::Type(TypeNode::Value(at)),
                    });
                };
                let level = level.clone();
                self.memo().value_types.insert(at, Image::Open);
                self.frames.push(Frame::Decoded {
                    at: TypeNode::Value(at),
                });
                return self.decode(target, code, level, GroundSort::Value);
            },
            ValueTypeView::StaticPi { domain, codomain } => (
                Frame::StaticPiDomain { at, codomain },
                CoreNode::Type(TypeNode::Value(domain)),
            ),
            ValueTypeView::Sigma { first, second } => (
                Frame::SigmaFirst { at, second },
                CoreNode::Type(TypeNode::Value(first)),
            ),
        };
        self.memo().value_types.insert(at, Image::Open);
        self.frames.push(frame);
        Ok(Step::Descend(child))
    }

    /// Start erasing the computation type `at`, read through the fragment's
    /// view.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::descend`]: a returner, an arrow, a dependent arrow
    ///   and a lazy product open their frames; a decode opens its frame and
    ///   decodes its code.
    /// - fails: [`Refusal::Cyclic`] for an open computation type; whatever the
    ///   view or the decode refuses, converted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — returners, arrows, lazy products and decodes expose
    ///   their exact kernel family; a computation-type back-edge is refused.
    ///   Wrong family, missing memo publication and lost cycle detection change
    ///   these results.
    /// - witness: `bridge::tests::returner_type_lowers`
    /// - witness: `bridge::tests::every_checked_function_definition_is_readmitted`
    /// - witness: `bridge::tests::a_lazy_product_crosses_as_its_kernel_nodes`
    /// - witness: `bridge::tests::every_recursive_node_family_refuses_a_back_edge`
    #[spec(ensures: |ret| match ret {
        | Ok(Step::Ascend(AnyNode::CompType(_)) | Step::Descend(_)) => self.reached().comp_types.contains_key(&at),
        | Ok(Step::Ascend(_)) => false,
        | Err(Refusal::Cyclic { node }) => node == CoreNode::Type(TypeNode::Computation(at)),
        | Err(_) => true,
    })]
    fn descend_comp_type(
        &mut self,
        target: &mut TermArena,
        at: CompTypeId,
    ) -> Result<Step, Refusal>
    {
        match self.memo().comp_types.get(&at) {
            Some(&Image::Erased(erased)) => return Ok(Step::Ascend(AnyNode::CompType(erased))),
            Some(&Image::Open) => {
                return Err(Refusal::Cyclic {
                    node: CoreNode::Type(TypeNode::Computation(at)),
                });
            },
            None => {},
        }
        let (frame, child) = match comp_type_view(self.arena, at)? {
            CompTypeView::With(first, second) => {
                self.memo().comp_types.insert(at, Image::Open);
                self.frames.push(Frame::WithTypeFirst { at, second });
                return Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(first))));
            },
            CompTypeView::Returner { result, effects } => {
                if effects.purity() != gandr_core_term::effect::Purity::Pure {
                    return Err(Refusal::OutOfFragment {
                        at: CoreNode::Type(TypeNode::Computation(at)),
                        former: UnadmittedFormer::EffectRow,
                    });
                }
                (Frame::Returner { at }, result)
            },
            CompTypeView::Arrow { domain, codomain } => {
                (Frame::ArrowDomain { at, codomain }, domain)
            },
            CompTypeView::Pi { domain, codomain } => (Frame::PiDomain { at, codomain }, domain),
            CompTypeView::Element { .. } | CompTypeView::Unknown => {
                let Some(&gandr_core_term::CompType::Element {
                    code,
                    target: ref level,
                }) = self.arena.comp_type(at)
                else {
                    return Err(Refusal::Unknown {
                        at: CoreNode::Type(TypeNode::Computation(at)),
                    });
                };
                let level = level.clone();
                self.memo().comp_types.insert(at, Image::Open);
                self.frames.push(Frame::Decoded {
                    at: TypeNode::Computation(at),
                });
                return self.decode(target, code, level, GroundSort::Computation);
            },
        };
        self.memo().comp_types.insert(at, Image::Open);
        self.frames.push(frame);
        Ok(Step::Descend(CoreNode::Type(TypeNode::Value(child))))
    }

    /// Erase the decode of `code` at `level` into the type of `sort` it
    /// denotes: read normalizing, step the code at its head, collecting each
    /// certificate, until it is a quote, whose type is erased, or rigid, whose
    /// decode is minted.
    ///
    /// # Specification
    /// - requires: `code` was checked at the universe of `sort` at `level`.
    /// - ensures: for a quote of a type of `sort`, the descent into that type;
    ///   for a variable or a constant, the kernel's decode of its image at
    ///   `level`; for a static application or a returned code, the descent into
    ///   its image with the decode awaiting it. Read normalizing, a constant
    ///   with a body, a reducible static application or a closed returned code
    ///   first takes its certified step, and the reduct is decoded in its place
    ///   — the judgement defined a constant's body at the constant's own
    ///   universe, a step preserves the type, and a returned code's run returns
    ///   a code of the universe its call returns, so at `level` still. A minted
    ///   decode is of `sort`'s family.
    /// - fails: [`Refusal::CertificateDeclined`] for a step the normaliser does
    ///   not certify; [`Refusal::Withheld`] for a constant that did not cross;
    ///   [`Refusal::Session`]; [`Refusal::DanglingNode`];
    ///   [`Refusal::MachineInvariant`] for a code that is no code.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — as above.
    ///
    /// # Termination
    /// - reason: the `loop` takes one certified step per turn, not recursion.
    /// - measure: the code's distance to its static normal form, which each δ-
    ///   or β-step of a well-formed code shortens; the admission order bounds a
    ///   constant's unfolding chain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the arms, separated by a quote, a rigid constant, a
    ///   code constant unfolded, a saturated instance reduced, a rigid instance
    ///   decoded, a closed returned code run, and a code of the wrong sort.
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    /// - witness: `bridge::tests::a_rigid_static_instance_crosses_as_a_kernel_application`
    /// - witness: `bridge::tests::an_unquoted_function_call_crosses_with_its_run_certified`
    #[spec(ensures: |ret| match ret {
        | Err(_) | Ok(Step::Descend(_)) => true,
        | Ok(Step::Ascend(AnyNode::ValueType(_))) => sort == GroundSort::Value,
        | Ok(Step::Ascend(AnyNode::CompType(_))) => sort == GroundSort::Computation,
        | Ok(Step::Ascend(AnyNode::Value(_) | AnyNode::Computation(_))) => false,
    })]
    fn decode(
        &mut self,
        target: &mut TermArena,
        code: ValueId,
        level: Level,
        sort: GroundSort,
    ) -> Result<Step, Refusal>
    {
        let mut code = code;
        loop {
            let Some(node) = self.arena.value(code).cloned()
            else {
                return Err(Refusal::DanglingNode {
                    node: CoreNode::Term(TermNode::Value(code)),
                });
            };
            if self.mode == Mode::Normalizing
                && let Value::Constant(_) | Value::StaticApplication(..) | Value::Returned(_) = node
                && let Maybe::Present(reduct) = self.step(code)?
            {
                code = reduct;
                continue;
            }
            let image = match (node, sort) {
                (Value::Reify(_), _) => {
                    return Err(Refusal::OutOfFragment {
                        at: CoreNode::Term(TermNode::Value(code)),
                        former: UnadmittedFormer::Reify,
                    });
                },
                (Value::Quote(quoted), GroundSort::Value) => {
                    return Ok(Step::Descend(CoreNode::Type(TypeNode::Value(quoted))));
                },
                (Value::QuoteComputation(quoted), GroundSort::Computation) => {
                    return Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(quoted))));
                },
                (
                    Value::Variable {
                        zone: Zone::Intuitionistic,
                        index,
                    },
                    _,
                ) => target.value_variable(index),
                (
                    Value::Variable {
                        zone: Zone::Linear, ..
                    },
                    _,
                ) => {
                    return Err(Refusal::Session {
                        at: CoreNode::Term(TermNode::Value(code)),
                    });
                },
                (Value::Constant(constant), _) => {
                    let position = self.constant_position(code, constant)?;
                    target.value_constant(position)
                },
                (Value::StaticApplication(..) | Value::Returned(_), _) => {
                    self.frames.push(Frame::DecodeOf { level, sort });
                    return Ok(Step::Descend(CoreNode::Term(TermNode::Value(code))));
                },
                (Value::Hole(hole), _) => {
                    return Err(Refusal::Hole {
                        at: CoreNode::Term(TermNode::Value(code)),
                        hole,
                    });
                },
                (Value::Mark { body, .. }, _) => {
                    code = body;
                    continue;
                },
                (Value::Quote(_), GroundSort::Computation)
                | (Value::QuoteComputation(_), GroundSort::Value)
                | (
                    Value::PathRefl(_)
                    | Value::Here(_)
                    | Value::Funext(..)
                    | Value::Equiv(..)
                    | Value::Univalence(..)
                    | Value::Ua { .. }
                    | Value::Nested(_)
                    | Value::Run(_)
                    | Value::Constructor { .. }
                    | Value::Record(_)
                    | Value::Primitive { .. }
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Tuple(_)
                    | Value::Literal(_)
                    | Value::Thunk(_)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Injection(..)
                    | Value::Lift { .. }
                    | Value::StaticLambda(_)
                    | Value::SessionRelated { .. }
                    | Value::Stay(_)
                    | Value::Then(..)
                    | Value::FlowProduct(..)
                    | Value::Forward(_)
                    | Value::FunctionFlow(..)
                    | Value::Recorded(_),
                    _,
                ) => return Err(Refusal::MachineInvariant),
            };
            return Ok(Step::Ascend(decoded(target, image, level, sort)));
        }
    }

    /// Start erasing `argument`, the value an application passes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: read normalizing, for a code constant without a recorded lift
    ///   whose unfolding chain reaches a quote or a static application, one
    ///   certificate per constant on the chain, outermost first, and the
    ///   descent into the code the chain ends at, which records no image for
    ///   the constant; for any other value, and read verbatim, its descent.
    ///   Every success descends into a value.
    /// - provides: an instantiation at a code substitutes the type the code
    ///   stands for, so the kernel's types hold no decode of a constant with a
    ///   body.
    /// - fails: [`Refusal::CertificateDeclined`] for an unfolding the
    ///   normaliser does not certify.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — as above.
    ///
    /// # Termination
    /// - reason: two `loop`s over the unfolding chain, not recursion: the first
    ///   finds its end without collecting, so a chain ending at a rigid
    ///   constant certifies nothing.
    /// - measure: the admission position of the constant reached, which a body
    ///   names only below its own.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a code constant unfolding to a quote, a
    ///   chain ending at a rigid constant, and a lifted argument.
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `bridge::tests::every_readmission_certificate_replays`
    /// - witness: `bridge::tests::a_code_constant_argument_crosses_as_written_in_a_run`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Step::Descend(CoreNode::Term(TermNode::Value(_))))))]
    fn argument(
        &mut self,
        argument: ValueId,
    ) -> Result<Step, Refusal>
    {
        let descend = Step::Descend(CoreNode::Term(TermNode::Value(argument)));
        if self.mode == Mode::Verbatim || self.source.lifts.contains_key(&argument) {
            return Ok(descend);
        }
        let mut reached = argument;
        loop {
            match self.arena.value(reached) {
                Some(
                    &(Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticApplication(..)),
                ) => break,
                Some(&Value::Constant(constant)) => {
                    match self.positions.definitions.body(constant) {
                        Maybe::Present(body) => reached = body,
                        Maybe::Absent(_) => return Ok(descend),
                    }
                },
                _ => return Ok(descend),
            }
        }
        let mut code = argument;
        while let Some(&Value::Constant(_)) = self.arena.value(code) {
            let Maybe::Present(reduct) = self.step(code)?
            else {
                return Err(Refusal::MachineInvariant);
            };
            code = reduct;
        }
        Ok(Step::Descend(CoreNode::Term(TermNode::Value(code))))
    }

    /// Cross the next image of the forward flow `erasure` holds, or mint the
    /// kernel's forward flow once every image has crossed.
    ///
    /// # Specification
    /// - requires: `erasure` holds the images crossed so far, in coverage
    ///   order.
    /// - ensures: while an image remains, the erasure waits on it and the next
    ///   image is the next goal; once none remains, the kernel's forward flow
    ///   over the flow type, the translator, every image in order and the
    ///   decided dialogues is recorded at the flow and ascends.
    /// - panics: none.
    /// - executable: none — the kernel node is minted into the target arena the
    ///   frame stack hands back later, out of the predicate's reach.
    ///
    /// # Errors
    /// - [`Refusal`] — as [`Self::argument`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a migration's forward flow crosses with one image per
    ///   pattern and replays in the kernel.
    /// - witness: `forward::tests::directed_statements_cross_and_replay`
    fn forward_images(
        &mut self,
        target: &mut TermArena,
        erasure: ForwardErasure,
    ) -> Result<Step, Refusal>
    {
        if let Some(&next) = erasure.images.get(erasure.erased.len()) {
            self.frames.push(Frame::ForwardImages(erasure));
            return self.argument(next);
        }
        let ForwardErasure {
            at,
            flow_type,
            translator,
            erased,
            dialogues,
            ..
        } = erasure;
        let image =
            target.value_forward_flow(flow_type, translator, erased.into_boxed_slice(), dialogues);
        Ok(self.erased_value(at, image))
    }

    /// Hand `image` to the rule `frame` holds.
    ///
    /// # Specification
    /// - requires: `frame` was pushed by this machine.
    /// - ensures: a frame awaiting its last child mints its node over the
    ///   children's images, records the image and ascends it; an application, a
    ///   bind, a lazy pairing, an arrow, a dependent arrow, a lazy product, a
    ///   pair, an eager product, a static Pi or a rigid static application
    ///   awaiting its first child descends to its second; a decode records the
    ///   type its code denotes; a lift a crossing added wraps the decode
    ///   beneath it; a static application erased as its reduct records the
    ///   reduct's image as its own. A descent always leaves the frame awaiting
    ///   it on the stack.
    /// - fails: [`Refusal::MachineInvariant`] when `image` is not of the family
    ///   the frame awaits.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::erase`], whose frame table this is, with
    ///   the static frames reached by a readmitted static instance, a rigid
    ///   instance and an eager pair.
    /// - witness: `bridge::tests::every_former_outside_the_fragment_is_refused_by_name`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    /// - witness: `bridge::tests::a_rigid_static_instance_crosses_as_a_kernel_application`
    /// - witness: `bridge::tests::a_lazy_product_crosses_as_its_kernel_nodes`
    #[spec(ensures: |ret| !matches!(ret, Ok(Step::Descend(_))) || !self.frames.is_empty())]
    fn resume(
        &mut self,
        target: &mut TermArena,
        frame: Frame,
        image: AnyNode,
    ) -> Result<Step, Refusal>
    {
        match (frame, image) {
            (Frame::NativeNext(child), _) => Ok(Step::Descend(child)),
            (Frame::NativeBuild(root), _) => self.finish_native(target, root),
            (Frame::FunextBuild(at), _) => self.funext(target, at),
            (Frame::ListHead { at, tail }, AnyNode::Value(head)) => {
                self.frames.push(Frame::ListTail { at, head });
                self.argument(tail)
            },
            (Frame::ListTail { at, head }, AnyNode::Value(tail)) => {
                Ok(self.erased_value(at, target.value_list_cons(head, tail)))
            },
            (Frame::ListElement { at }, AnyNode::ValueType(element)) => {
                let Some(&Computation::ListFold { result, .. }) = self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::ListResult { at, element });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Value(result))))
            },
            (Frame::ListResult { at, element }, AnyNode::ValueType(result)) => {
                let Some(&Computation::ListFold { list, .. }) = self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::ListInput {
                    at,
                    element,
                    result,
                });
                self.argument(list)
            },
            (
                Frame::ListInput {
                    at,
                    element,
                    result,
                },
                AnyNode::Value(list),
            ) => {
                let Some(&Computation::ListFold { on_nil, .. }) = self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::ListNil {
                    at,
                    element,
                    result,
                    list,
                });
                Ok(Step::Descend(CoreNode::Term(TermNode::Computation(on_nil))))
            },
            (
                Frame::ListNil {
                    at,
                    element,
                    result,
                    list,
                },
                AnyNode::Computation(on_nil),
            ) => {
                let Some(&Computation::ListFold { on_cons, .. }) = self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::ListCons {
                    at,
                    element,
                    result,
                    list,
                    on_nil,
                });
                Ok(Step::Descend(CoreNode::Term(TermNode::Computation(
                    on_cons,
                ))))
            },
            (
                Frame::ListCons {
                    at,
                    element,
                    result,
                    list,
                    on_nil,
                },
                AnyNode::Computation(on_cons),
            ) => Ok(self.erased_computation(
                at,
                target.computation_list_fold(element, result, list, on_nil, on_cons),
            )),
            (Frame::PathRefl { at }, AnyNode::Value(code)) => {
                Ok(self.erased_value(at, target.value_path_refl(code)))
            },
            (Frame::PathProductFirst { at, second }, AnyNode::Value(first)) => {
                self.frames.push(Frame::PathProductSecond { at, first });
                self.argument(second)
            },
            (Frame::PathProductSecond { at, first }, AnyNode::Value(second)) => {
                Ok(self.erased_value(at, target.value_path_product(first, second)))
            },
            (
                Frame::PathEquivType {
                    at,
                    forward,
                    backward,
                    evidence,
                },
                AnyNode::ValueType(path_type),
            ) => {
                self.frames.push(Frame::PathEquivForward {
                    at,
                    path_type,
                    backward,
                    evidence,
                });
                self.argument(forward)
            },
            (
                Frame::PathEquivForward {
                    at,
                    path_type,
                    backward,
                    evidence,
                },
                AnyNode::Value(forward),
            ) => {
                self.frames.push(Frame::PathEquivBackward {
                    at,
                    path_type,
                    forward,
                    evidence,
                });
                self.argument(backward)
            },
            (
                Frame::PathEquivBackward {
                    at,
                    path_type,
                    forward,
                    evidence,
                },
                AnyNode::Value(backward),
            ) => Ok(self.erased_value(
                at,
                target.value_path_equiv(path_type, forward, backward, evidence),
            )),
            (Frame::UnivalenceRecord { at }, AnyNode::Value(record)) => {
                Ok(self.erased_value(at, target.value_univalence(record)))
            },
            (Frame::PathSource { at, target_code }, AnyNode::Value(source)) => {
                self.frames.push(Frame::PathTarget { at, source });
                self.argument(target_code)
            },
            (Frame::PathTarget { at, source }, AnyNode::Value(target_code)) => Ok(
                self.erased_value_type(at, target.value_type_path_universe(source, target_code))
            ),
            (Frame::FlowSource { at, target_code }, AnyNode::Value(source)) => {
                self.frames.push(Frame::FlowTarget { at, source });
                self.argument(target_code)
            },
            (Frame::FlowTarget { at, source }, AnyNode::Value(target_code)) => Ok(
                self.erased_value_type(at, target.value_type_flow_universe(source, target_code))
            ),
            (
                Frame::SessionCertificate {
                    at,
                    relation,
                    ref evidence,
                },
                AnyNode::ValueType(classifier),
            ) => {
                let evidence = alloc::sync::Arc::clone(evidence);
                let unit = target.value_tuple(&[]);
                let image = match relation {
                    gandr_core_term::session::SessionRelation::Equivalence => {
                        target.value_session_path(classifier, evidence, unit)
                    },
                    gandr_core_term::session::SessionRelation::Subtyping => {
                        target.value_session_flow(classifier, evidence, unit)
                    },
                };
                Ok(self.erased_value(at, image))
            },
            (Frame::Injection { at, summand }, AnyNode::Value(body)) => {
                Ok(self.erased_value(at, target.value_injection(summand, body)))
            },
            (Frame::TransportPath { at, value }, AnyNode::Value(path)) => {
                self.frames.push(Frame::TransportValue { at, path });
                self.argument(value)
            },
            (Frame::TransportValue { at, path }, AnyNode::Value(value)) => {
                Ok(self.erased_computation(at, target.computation_transport(path, value)))
            },
            (
                Frame::PathCarrier {
                    at,
                    left,
                    right,
                    family,
                },
                AnyNode::ValueType(carrier),
            ) => {
                self.frames.push(Frame::PathLeft {
                    at,
                    carrier,
                    right,
                    family,
                });
                self.argument(left)
            },
            (
                Frame::PathLeft {
                    at,
                    carrier,
                    right,
                    family,
                },
                AnyNode::Value(left),
            ) => {
                self.frames.push(Frame::PathRight {
                    at,
                    carrier,
                    left,
                    family,
                });
                self.argument(right)
            },
            (
                Frame::PathRight {
                    at,
                    carrier,
                    left,
                    family,
                },
                AnyNode::Value(right),
            ) => {
                let image = match family {
                    Family::Path => target.value_type_path(carrier, left, right),
                    Family::Flow => target.value_type_flow(carrier, left, right),
                };
                Ok(self.erased_value_type(at, image))
            },
            // A reflexivity checked against a path type carries the
            // dialogues relating its point to each endpoint; one only
            // synthesised relates it to itself and carries none.
            (Frame::Here { at, family }, AnyNode::Value(point)) => {
                let dialogues = self.source.reflexivities.get(&at).map(|reflexivity| {
                    alloc::sync::Arc::new(EndpointDialogues {
                        left: reflexivity
                            .left()
                            .iter()
                            .map(|decision| decision.map(|_| ()))
                            .collect(),
                        right: reflexivity
                            .right()
                            .iter()
                            .map(|decision| decision.map(|_| ()))
                            .collect(),
                    })
                });
                let image = match (family, dialogues) {
                    (Family::Path, Some(dialogues)) => target.value_here_relating(point, dialogues),
                    (Family::Path, None) => target.value_here(point),
                    (Family::Flow, Some(dialogues)) => target.value_stay_relating(point, dialogues),
                    (Family::Flow, None) => target.value_stay(point),
                };
                Ok(self.erased_value(at, image))
            },
            (
                Frame::PathTransportMotive {
                    at,
                    path,
                    value,
                    family,
                },
                AnyNode::ValueType(motive),
            ) => {
                self.frames.push(Frame::PathTransportPath {
                    at,
                    motive,
                    value,
                    family,
                });
                Ok(Step::Descend(CoreNode::Term(TermNode::Value(path))))
            },
            (
                Frame::PathTransportPath {
                    at,
                    motive,
                    value,
                    family,
                },
                AnyNode::Value(path),
            ) => {
                self.frames.push(Frame::PathTransportValue {
                    at,
                    motive,
                    path,
                    family,
                });
                self.argument(value)
            },
            (
                Frame::PathTransportValue {
                    at,
                    motive,
                    path,
                    family,
                },
                AnyNode::Value(value),
            ) => {
                let image = match family {
                    Family::Path => target.computation_path_transport(motive, path, value),
                    Family::Flow => target.computation_ride(motive, path, value),
                };
                Ok(self.erased_computation(at, image))
            },
            (Frame::ThenFirst { at, second }, AnyNode::Value(first)) => {
                self.frames.push(Frame::ThenSecond { at, first });
                self.argument(second)
            },
            (Frame::ThenSecond { at, first }, AnyNode::Value(second)) => {
                Ok(self.erased_value(at, target.value_then(first, second, Seam::Sequence)))
            },
            (Frame::FlowProductFirst { at, second }, AnyNode::Value(first)) => {
                self.frames.push(Frame::FlowProductSecond { at, first });
                self.argument(second)
            },
            (Frame::FlowProductSecond { at, first }, AnyNode::Value(second)) => {
                Ok(self.erased_value(at, target.value_flow_product(first, second)))
            },
            (
                Frame::ForwardType {
                    at,
                    translator,
                    images,
                    dialogues,
                },
                AnyNode::ValueType(flow_type),
            ) => {
                self.frames.push(Frame::ForwardTranslator {
                    at,
                    flow_type,
                    images,
                    dialogues,
                });
                self.argument(translator)
            },
            (
                Frame::ForwardTranslator {
                    at,
                    flow_type,
                    images,
                    dialogues,
                },
                AnyNode::Value(translator),
            ) => self.forward_images(target, ForwardErasure {
                at,
                flow_type,
                translator,
                images,
                erased: Vec::new(),
                dialogues,
            }),
            (Frame::ForwardImages(mut erasure), AnyNode::Value(image)) => {
                erasure.erased.push(image);
                self.forward_images(target, erasure)
            },
            (
                Frame::FunctionFlowType {
                    at,
                    domain,
                    codomain,
                },
                AnyNode::ValueType(flow_type),
            ) => {
                self.frames.push(Frame::FunctionFlowDomain {
                    at,
                    flow_type,
                    codomain,
                });
                self.argument(domain)
            },
            (
                Frame::FunctionFlowDomain {
                    at,
                    flow_type,
                    codomain,
                },
                AnyNode::Value(domain),
            ) => {
                self.frames.push(Frame::FunctionFlowCodomain {
                    at,
                    flow_type,
                    domain,
                });
                self.argument(codomain)
            },
            (
                Frame::FunctionFlowCodomain {
                    at,
                    flow_type,
                    domain,
                },
                AnyNode::Value(codomain),
            ) => Ok(self.erased_value(at, target.value_function_flow(flow_type, domain, codomain))),
            (Frame::TelescopeMotive { at }, AnyNode::CompType(motive)) => {
                let Some(&Computation::TelescopeTransport { path, .. }) =
                    self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::TelescopePath { at, motive });
                Ok(Step::Descend(CoreNode::Term(TermNode::Value(path))))
            },
            (Frame::TelescopePath { at, motive }, AnyNode::Value(path)) => {
                let Some(&Computation::TelescopeTransport { start, .. }) =
                    self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::TelescopeStart { at, motive, path });
                Ok(Step::Descend(CoreNode::Term(TermNode::Value(start))))
            },
            (Frame::TelescopeStart { at, motive, path }, AnyNode::Value(start)) => {
                let Some(&Computation::TelescopeTransport { over, .. }) =
                    self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::TelescopeOver {
                    at,
                    motive,
                    path,
                    start,
                });
                Ok(Step::Descend(CoreNode::Term(TermNode::Value(over))))
            },
            (
                Frame::TelescopeOver {
                    at,
                    motive,
                    path,
                    start,
                },
                AnyNode::Value(over),
            ) => {
                let Some(&Computation::TelescopeTransport { value, .. }) =
                    self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::TelescopeValue {
                    at,
                    motive,
                    path,
                    start,
                    over,
                });
                self.argument(value)
            },
            (
                Frame::TelescopeValue {
                    at,
                    motive,
                    path,
                    start,
                    over,
                },
                AnyNode::Value(value),
            ) => Ok(self.erased_computation(
                at,
                target.computation_telescope_transport(motive, path, start, over, value),
            )),
            (Frame::Thunk { at }, AnyNode::Computation(body)) => {
                Ok(self.erased_value(at, target.value_thunk(body)))
            },
            (Frame::Returned { at }, AnyNode::Computation(computation)) => {
                Ok(self.erased_value(at, target.value_returned(computation)))
            },
            (Frame::Quote { at } | Frame::LiftedCode { at }, AnyNode::ValueType(quoted)) => {
                Ok(self.erased_value(at, target.value_quote(quoted)))
            },
            (Frame::QuoteComputation { at }, AnyNode::CompType(quoted)) => {
                Ok(self.erased_value(at, target.value_quote_computation(quoted)))
            },
            (Frame::Force { at }, AnyNode::Value(value)) => {
                Ok(self.erased_computation(at, target.computation_force(value)))
            },
            (Frame::NativeFirst { at, head, second }, AnyNode::Value(first)) => {
                let head = target.computation_application(head, first);
                self.frames.push(Frame::ApplicationArgument { at, head });
                self.argument(second)
            },
            (Frame::ApplicationHead { at, argument }, AnyNode::Computation(head)) => {
                self.frames.push(Frame::ApplicationArgument { at, head });
                self.argument(argument)
            },
            (Frame::ApplicationArgument { at, head }, AnyNode::Value(argument)) => {
                Ok(self.erased_computation(at, target.computation_application(head, argument)))
            },
            (Frame::Lambda { at }, AnyNode::Computation(body)) => {
                Ok(self.erased_computation(at, target.computation_lambda(body)))
            },
            (Frame::Fixpoint { at, evidence }, AnyNode::Computation(body)) => {
                Ok(self.erased_computation(at, target.computation_fixpoint(body, evidence)))
            },
            (Frame::Return { at }, AnyNode::Value(value)) => {
                Ok(self.erased_computation(at, target.computation_return(value)))
            },
            (Frame::BindBound { at, body }, AnyNode::Computation(bound)) => {
                self.frames.push(Frame::BindBody { at, bound });
                Ok(Step::Descend(CoreNode::Term(TermNode::Computation(body))))
            },
            (Frame::BindBody { at, bound }, AnyNode::Computation(body)) => {
                Ok(self.erased_computation(at, target.computation_bind(bound, body)))
            },
            (Frame::WithFirst { at, second }, AnyNode::Computation(first)) => {
                self.frames.push(Frame::WithSecond { at, first });
                Ok(Step::Descend(CoreNode::Term(TermNode::Computation(second))))
            },
            (Frame::WithSecond { at, first }, AnyNode::Computation(second)) => {
                Ok(self.erased_computation(at, target.computation_with(first, second)))
            },
            (Frame::Project { at, side }, AnyNode::Computation(pair)) => {
                Ok(self.erased_computation(at, target.computation_project(side, pair)))
            },
            (Frame::ThunkType { at }, AnyNode::CompType(body)) => {
                Ok(self.erased_value_type(at, target.value_type_thunk(body)))
            },
            (Frame::TypeLift { at }, AnyNode::ValueType(inner)) => {
                let ValueTypeView::Lift { target: level, .. } = value_type_view(self.arena, at)?
                else {
                    return Err(Refusal::MachineInvariant);
                };
                let erased = target.value_type_lift(inner, level.clone());
                Ok(self.erased_value_type(at, erased))
            },
            (Frame::DecodeLift { target: level }, AnyNode::ValueType(inner)) => Ok(Step::Ascend(
                AnyNode::ValueType(target.value_type_lift(inner, level)),
            )),
            (
                Frame::Decoded {
                    at: TypeNode::Value(at),
                },
                AnyNode::ValueType(decoded),
            ) => Ok(self.erased_value_type(at, decoded)),
            (
                Frame::Decoded {
                    at: TypeNode::Computation(at),
                },
                AnyNode::CompType(decoded),
            ) => Ok(self.erased_comp_type(at, decoded)),
            (Frame::Returner { at }, AnyNode::ValueType(result)) => {
                Ok(self.erased_comp_type(at, target.comp_type_returner(result)))
            },
            (Frame::ArrowDomain { at, codomain }, AnyNode::ValueType(domain)) => {
                self.frames.push(Frame::ArrowCodomain { at, domain });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(
                    codomain,
                ))))
            },
            (Frame::ArrowCodomain { at, domain }, AnyNode::CompType(codomain)) => {
                Ok(self.erased_comp_type(at, target.comp_type_arrow(domain, codomain)))
            },
            (Frame::WithTypeFirst { at, second }, AnyNode::CompType(first)) => {
                self.frames.push(Frame::WithTypeSecond { at, first });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(second))))
            },
            (Frame::WithTypeSecond { at, first }, AnyNode::CompType(second)) => {
                Ok(self.erased_comp_type(at, target.comp_type_with(first, second)))
            },
            (Frame::PiDomain { at, codomain }, AnyNode::ValueType(domain)) => {
                self.frames.push(Frame::PiCodomain { at, domain });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(
                    codomain,
                ))))
            },
            (Frame::PiCodomain { at, domain }, AnyNode::CompType(codomain)) => {
                Ok(self.erased_comp_type(at, target.comp_type_pi(domain, codomain)))
            },
            (Frame::Reduced { at } | Frame::UnmarkedValue { at }, AnyNode::Value(reduct)) => {
                Ok(self.erased_value(at, reduct))
            },
            (
                Frame::UnmarkedComputation { at } | Frame::SplitReduct { at },
                AnyNode::Computation(image),
            ) => Ok(self.erased_computation(at, image)),
            (Frame::SigmaSplitScrutinee { at, motive, body }, AnyNode::Value(scrutinee)) => {
                self.frames.push(Frame::SigmaSplitMotive {
                    at,
                    scrutinee,
                    body,
                });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(motive))))
            },
            (
                Frame::SigmaSplitMotive {
                    at,
                    scrutinee,
                    body,
                },
                AnyNode::CompType(motive),
            ) => {
                self.frames.push(Frame::SigmaSplitBody {
                    at,
                    scrutinee,
                    motive,
                });
                Ok(Step::Descend(CoreNode::Term(TermNode::Computation(body))))
            },
            (
                Frame::SigmaSplitBody {
                    at,
                    scrutinee,
                    motive,
                },
                AnyNode::Computation(body),
            ) => Ok(self
                .erased_computation(at, target.computation_sigma_split(scrutinee, motive, body))),
            (Frame::StaticHead { at, argument }, AnyNode::Value(head)) => {
                self.frames.push(Frame::StaticArgument { at, head });
                Ok(Step::Descend(CoreNode::Term(TermNode::Value(argument))))
            },
            (Frame::StaticArgument { at, head }, AnyNode::Value(argument)) => {
                Ok(self.erased_value(at, target.value_static_application(head, argument)))
            },
            (Frame::ListType { at }, AnyNode::ValueType(element)) => {
                Ok(self.erased_value_type(at, target.value_type_list(element)))
            },
            (Frame::StaticPiDomain { at, codomain }, AnyNode::ValueType(domain)) => {
                self.frames.push(Frame::StaticPiCodomain { at, domain });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Value(codomain))))
            },
            (Frame::StaticPiCodomain { at, domain }, AnyNode::ValueType(codomain)) => {
                Ok(self.erased_value_type(at, target.value_type_static_pi(domain, codomain)))
            },
            (Frame::SigmaFirst { at, second }, AnyNode::ValueType(first)) => {
                self.frames.push(Frame::SigmaSecond { at, first });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Value(second))))
            },
            (Frame::SigmaSecond { at, first }, AnyNode::ValueType(second)) => {
                Ok(self.erased_value_type(at, target.value_type_sigma(first, second)))
            },
            (Frame::DecodeOf { level, sort }, AnyNode::Value(code)) => {
                Ok(Step::Ascend(decoded(target, code, level, sort)))
            },
            (
                Frame::ListNil { .. }
                | Frame::ListCons { .. }
                | Frame::Thunk { .. }
                | Frame::Returned { .. }
                | Frame::ApplicationHead { .. }
                | Frame::Lambda { .. }
                | Frame::Fixpoint { .. }
                | Frame::BindBound { .. }
                | Frame::BindBody { .. }
                | Frame::WithFirst { .. }
                | Frame::WithSecond { .. }
                | Frame::Project { .. }
                | Frame::UnmarkedComputation { .. }
                | Frame::SplitReduct { .. }
                | Frame::SigmaSplitBody { .. },
                AnyNode::Value(_) | AnyNode::ValueType(_) | AnyNode::CompType(_),
            )
            | (
                Frame::ThunkType { .. }
                | Frame::QuoteComputation { .. }
                | Frame::ArrowCodomain { .. }
                | Frame::WithTypeFirst { .. }
                | Frame::WithTypeSecond { .. }
                | Frame::PiCodomain { .. }
                | Frame::SigmaSplitMotive { .. }
                | Frame::TelescopeMotive { .. }
                | Frame::Decoded {
                    at: TypeNode::Computation(_),
                },
                AnyNode::Value(_) | AnyNode::Computation(_) | AnyNode::ValueType(_),
            )
            | (
                Frame::PathRefl { .. }
                | Frame::PathProductFirst { .. }
                | Frame::PathProductSecond { .. }
                | Frame::PathEquivForward { .. }
                | Frame::PathEquivBackward { .. }
                | Frame::UnivalenceRecord { .. }
                | Frame::PathSource { .. }
                | Frame::PathTarget { .. }
                | Frame::FlowSource { .. }
                | Frame::FlowTarget { .. }
                | Frame::PathLeft { .. }
                | Frame::PathRight { .. }
                | Frame::Here { .. }
                | Frame::TransportPath { .. }
                | Frame::TransportValue { .. }
                | Frame::PathTransportPath { .. }
                | Frame::PathTransportValue { .. }
                | Frame::TelescopePath { .. }
                | Frame::TelescopeStart { .. }
                | Frame::TelescopeOver { .. }
                | Frame::TelescopeValue { .. }
                | Frame::Injection { .. }
                | Frame::ListHead { .. }
                | Frame::ListTail { .. }
                | Frame::ListInput { .. }
                | Frame::Force { .. }
                | Frame::ApplicationArgument { .. }
                | Frame::NativeFirst { .. }
                | Frame::Return { .. }
                | Frame::Reduced { .. }
                | Frame::UnmarkedValue { .. }
                | Frame::StaticHead { .. }
                | Frame::StaticArgument { .. }
                | Frame::DecodeOf { .. }
                | Frame::ThenFirst { .. }
                | Frame::ThenSecond { .. }
                | Frame::FlowProductFirst { .. }
                | Frame::FlowProductSecond { .. }
                | Frame::ForwardTranslator { .. }
                | Frame::ForwardImages(_)
                | Frame::FunctionFlowDomain { .. }
                | Frame::FunctionFlowCodomain { .. }
                | Frame::SigmaSplitScrutinee { .. },
                AnyNode::Computation(_) | AnyNode::ValueType(_) | AnyNode::CompType(_),
            )
            | (
                Frame::PathEquivType { .. }
                | Frame::SessionCertificate { .. }
                | Frame::ListType { .. }
                | Frame::PathCarrier { .. }
                | Frame::PathTransportMotive { .. }
                | Frame::ListElement { .. }
                | Frame::ListResult { .. }
                | Frame::Quote { .. }
                | Frame::LiftedCode { .. }
                | Frame::TypeLift { .. }
                | Frame::DecodeLift { .. }
                | Frame::Returner { .. }
                | Frame::ArrowDomain { .. }
                | Frame::PiDomain { .. }
                | Frame::StaticPiDomain { .. }
                | Frame::StaticPiCodomain { .. }
                | Frame::SigmaFirst { .. }
                | Frame::SigmaSecond { .. }
                | Frame::ForwardType { .. }
                | Frame::FunctionFlowType { .. }
                | Frame::Decoded {
                    at: TypeNode::Value(_),
                },
                AnyNode::Value(_) | AnyNode::Computation(_) | AnyNode::CompType(_),
            ) => Err(Refusal::MachineInvariant),
        }
    }

    /// Record `erased` as the image of the value `at`, and ascend it.
    ///
    /// # Specification
    /// - requires: the image belongs to the caller's target arena.
    /// - ensures: the current mode records this exact image and ascends it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — admitted formers and shared descendants expose exact
    ///   kernel images and preserved sharing; storing the wrong image or
    ///   returning another family changes these observations.
    /// - witness: `bridge::tests::returning_a_literal_lowers`
    /// - witness: `bridge::tests::a_shared_subterm_is_erased_once`
    #[spec(ensures: |ret| self.reached().values.get(&at) == Some(&Image::Erased(erased)) && ret == Step::Ascend(AnyNode::Value(erased)))]
    fn erased_value(
        &mut self,
        at: ValueId,
        erased: gandr_kernel_term::ValueId,
    ) -> Step
    {
        self.memo().values.insert(at, Image::Erased(erased));
        Step::Ascend(AnyNode::Value(erased))
    }

    /// Record `erased` as the image of the computation `at`, and ascend it.
    ///
    /// # Specification
    /// - requires: the image belongs to the caller's target arena.
    /// - ensures: the current mode records this exact image and ascends it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — admitted formers and shared descendants expose exact
    ///   kernel images and preserved sharing; storing the wrong image or
    ///   returning another family changes these observations.
    /// - witness: `bridge::tests::a_shared_subterm_is_erased_once`
    #[spec(ensures: |ret| self.reached().computations.get(&at) == Some(&Image::Erased(erased)) && ret == Step::Ascend(AnyNode::Computation(erased)))]
    fn erased_computation(
        &mut self,
        at: ComputationId,
        erased: gandr_kernel_term::ComputationId,
    ) -> Step
    {
        self.memo().computations.insert(at, Image::Erased(erased));
        Step::Ascend(AnyNode::Computation(erased))
    }

    /// The projection binds a split of `scrutinee` into `body` reduces to,
    /// minted into the source arena: component zero is bound outermost, each
    /// projection reading the scrutinee shifted past the binds before it, so a
    /// split of no components is its body.
    ///
    /// # Specification
    /// - requires: `body` is scoped under `arity` binders beyond `scrutinee`.
    /// - ensures: a chain of `arity` binds, each of the next component, ending
    ///   in `body`; the kernel has no split, and every component crosses as the
    ///   projection the kernel already judges.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a split reading each of three components crosses as
    ///   the binds that read them, and a split of the unit crosses as its body;
    ///   a wrong shift or order changes the kernel's verdict.
    /// - witness: `tests::native_formers::a_split_crosses_as_its_projection_binds`
    #[spec(ensures: |ret| usize::from(arity) != 0_usize || ret == body)]
    fn split_reduct(
        &mut self,
        scrutinee: ValueId,
        arity: gandr_core_term::ComponentCount,
        body: ComputationId,
    ) -> ComputationId
    {
        (0_usize .. usize::from(arity))
            .rev()
            .fold(body, |rest, component| {
                let shift = u32::try_from(component).unwrap_or(u32::MAX);
                let read = gandr_core_term::shift_value(
                    self.arena,
                    scrutinee,
                    gandr_core_term::Binders::from(shift),
                );
                let projected = self.arena.computation_tuple_projection(
                    read,
                    gandr_core_term::Component::from(component),
                );
                self.arena.computation_bind(projected, rest)
            })
    }

    /// Record `erased` as the image of the value type `at`, and ascend it.
    ///
    /// # Specification
    /// - requires: the image belongs to the caller's target arena.
    /// - ensures: the current mode records this exact image and ascends it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — admitted formers and shared descendants expose exact
    ///   kernel images and preserved sharing; storing the wrong image or
    ///   returning another family changes these observations.
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    /// - witness: `bridge::tests::a_shared_subterm_is_erased_once`
    #[spec(ensures: |ret| self.reached().value_types.get(&at) == Some(&Image::Erased(erased)) && ret == Step::Ascend(AnyNode::ValueType(erased)))]
    fn erased_value_type(
        &mut self,
        at: ValueTypeId,
        erased: gandr_kernel_term::ValueTypeId,
    ) -> Step
    {
        self.memo().value_types.insert(at, Image::Erased(erased));
        Step::Ascend(AnyNode::ValueType(erased))
    }

    /// Record `erased` as the image of the computation type `at`, and ascend
    /// it.
    ///
    /// # Specification
    /// - requires: the image belongs to the caller's target arena.
    /// - ensures: the current mode records this exact image and ascends it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — admitted formers and shared descendants expose exact
    ///   kernel images and preserved sharing; storing the wrong image or
    ///   returning another family changes these observations.
    /// - witness: `bridge::tests::returner_type_lowers`
    /// - witness: `bridge::tests::a_shared_subterm_is_erased_once`
    #[spec(ensures: |ret| self.reached().comp_types.get(&at) == Some(&Image::Erased(erased)) && ret == Step::Ascend(AnyNode::CompType(erased)))]
    fn erased_comp_type(
        &mut self,
        at: CompTypeId,
        erased: gandr_kernel_term::CompTypeId,
    ) -> Step
    {
        self.memo().comp_types.insert(at, Image::Erased(erased));
        Step::Ascend(AnyNode::CompType(erased))
    }
}

/// The kernel's decode of the code `image` at `level`, in `sort`'s family.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a value type for the value sort and a computation type for the
///   computation sort, each the decode of `image` at `level`, minted.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two arms, one per sort, each reached by a decode of a
///   rigid code of that sort.
/// - witness: `bridge::tests::a_sorted_universe_readmits_at_its_level`
/// - witness: `bridge::tests::a_rigid_static_instance_crosses_as_a_kernel_application`
#[spec(ensures: |ret| match sort {
    | GroundSort::Value => matches!(ret, AnyNode::ValueType(_)),
    | GroundSort::Computation => matches!(ret, AnyNode::CompType(_)),
})]
fn decoded(
    target: &mut TermArena,
    image: gandr_kernel_term::ValueId,
    level: Level,
    sort: GroundSort,
) -> AnyNode
{
    match sort {
        GroundSort::Value => AnyNode::ValueType(target.value_type_element(image, level)),
        GroundSort::Computation => AnyNode::CompType(target.comp_type_element(image, level)),
    }
}

#[cfg(test)]
mod tests;
