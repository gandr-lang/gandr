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
//! `native_formers::native_formers::a_split_crosses_as_its_projection_binds`
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
        | CheckRefusal::DanglingNode { node } => Refusal::DanglingNode { node },
        | _ => Refusal::MachineInvariant,
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
        | Self::OutOfFragment { .. } | Self::Session { .. } => matches!(ret, FailureClass::Unrepresentable),
        | Self::DanglingNode { .. } | Self::Cyclic { .. }
            | Self::CertificateDeclined { .. } | Self::MachineInvariant => matches!(ret, FailureClass::EngineFault),
        | Self::Hole { .. } | Self::Unknown { .. } => matches!(ret, FailureClass::UserAbsence),
    })]
    #[inline]
    #[must_use]
    pub const fn classify(&self) -> FailureClass
    {
        match *self {
            | Self::Withheld { .. } | Self::WithheldData { .. } => FailureClass::MalformedSource,
            | Self::OutOfFragment { .. } | Self::Session { .. } => FailureClass::Unrepresentable,
            | Self::DanglingNode { .. }
            | Self::Cyclic { .. }
            | Self::CertificateDeclined { .. }
            | Self::MachineInvariant => FailureClass::EngineFault,
            | Self::Hole { .. } | Self::Unknown { .. } => FailureClass::UserAbsence,
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
            | FragmentRefusal::DanglingNode { node } => Self::DanglingNode { node },
            | FragmentRefusal::OutOfFragment { at, former } => Self::OutOfFragment { at, former },
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
    /// The declaration is static: a type operator, classified by a static
    /// Pi, whose body normalizes away at every use. The kernel was offered
    /// nothing; each instance a later declaration reaches is reduced, and its
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
    /// - witness: `native_formers::native_formers::data_declarations_and_refusals_agree_with_kernel`
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
        natives: report.natives(),
        definitions: report.definitions(),
    };
    for judged in report.judged() {
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
        let definition = match judged.verdict() {
            | Verdict::Checked { declared, body, .. } => Some((declared.id(), body)),
            | Verdict::Synthesised { body, synthesised } => {
                Some((synthesised.produced().id(), body))
            },
            | Verdict::Data | Verdict::Owed(_) | Verdict::Refused(_) => None,
        };
        // A type operator — a definition whose type views as a static Pi — stays
        // on the checker's side; a type the view refuses is not one, and its
        // own erasure refuses it.
        let (outcome, certificates) = match (definition, judged.verdict()) {
            | (None, Verdict::Data) => {
                let offer = match (
                    report.data_signatures().get(&constant),
                    report.abstract_types().get(&constant),
                ) {
                    | (Some(signature), _) => Offer::Data(signature),
                    | (None, Some(&declared)) => Offer::Abstract(declared),
                    | (None, None) => {
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
            | (Some((declared, body)), _)
                if matches!(
                    value_type_view(arena, declared),
                    Ok(ValueTypeView::StaticPi { .. })
                ) =>
            {
                let defined = source.definitions.get(&constant).copied().unwrap_or(body);
                positions.definitions.define(constant, defined);
                (Outcome::Static, Vec::new())
            },
            | (Some((declared, body)), _) => cross(
                &mut environment,
                arena,
                source,
                &mut positions,
                constant,
                Offer::Definition {
                    declared,
                    body,
                    relations: source.relations.get(&constant).map_or(&[], Vec::as_slice),
                },
                &vouch,
            ),
            | (None, Verdict::Owed(entry)) => cross(
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
            | (None, Verdict::Refused(refusal)) => (Outcome::Marked(refusal), Vec::new()),
            | (None, Verdict::Checked { .. } | Verdict::Synthesised { .. }) => {
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
            | Ok(extent) => {
                if let Some(export) = positions.exports.get_mut(usize::from(seal.atom.position())) {
                    *export = export.clone().closed(extent);
                }
            },
            | Err(error) => {
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
        | Outcome::Marked(_) | Outcome::Static => false,
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
    let base = ConstantIndex::from(environment.entries().len().saturating_add(1));
    let next = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let erased = {
        let mut erasure = Erasure::new(arena, source, positions, base);
        if let Offer::Data(_) = offer {
            erasure = erasure.crossing_block(constant, next);
        }
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
        | Ok(crossing) => crossing,
        | Err((refusal, replayed)) => {
            staging.discard();
            return (Outcome::Refused(refusal), replayed);
        },
    };
    let defined_image = match erased {
        | Erased::Definition { ref body, .. } => Some(*body),
        | Erased::Data { .. } | Erased::Axiom { .. } | Erased::Abstract { .. } => None,
    };
    let staged = match erased {
        | Erased::Data {
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
            // they cross unchanged.
            match offer {
                | Offer::Data(signature) => staged.presented(signature.presentation().clone()),
                | Offer::Abstract(_) | Offer::Definition { .. } | Offer::Axiom { .. } => staged,
            }
        },
        | Erased::Definition {
            declared,
            body,
            related,
        } => staging
            .def(LevelSignature::monomorphic(), declared, body)
            .relating(related),
        | Erased::Axiom { declared } => staging.axiom(LevelSignature::monomorphic(), declared),
        | Erased::Abstract {
            kind,
            representation,
        } => staging.abstract_type(
            LevelSignature::monomorphic(),
            kind,
            representation,
            SealScope::Open,
        ),
    };
    let staged_as = staged.declaration().clone();
    let admitted = match environment.add_decl(staged) {
        | Ok(admitted) => admitted,
        | Err(error) => return (Outcome::Rejected(error), replayed),
    };
    positions.exports.push(staged_as);
    let audit = environment.audit(admitted);
    match (offer, defined_image) {
        | (Offer::Definition { body, .. }, Some(image)) => {
            let defined = source.definitions.get(&constant).copied().unwrap_or(body);
            positions.define(constant, admitted, defined, image);
            (Outcome::Defined { admitted, audit }, replayed)
        },
        | (Offer::Data(signature), _) => {
            positions.declare(constant, admitted);
            if !signature.presentation().rules().is_empty() {
                positions.definitions.present(constant, signature);
                positions.presentations = Presentations::of(environment.entries());
            }
            (Outcome::Data { admitted, audit }, replayed)
        },
        | (Offer::Abstract(_), _) => {
            positions.declare(constant, admitted);
            (Outcome::Data { admitted, audit }, replayed)
        },
        | (Offer::Axiom { .. } | Offer::Definition { .. }, _) => {
            positions.declare(constant, admitted);
            (Outcome::Assumed { admitted, audit }, replayed)
        },
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
                | PrimitiveType::Integer => arena.value_type_base(BaseType::Integer),
                | PrimitiveType::Boolean => {
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
    /// - witness: `native_formers::native_formers::data_declarations_and_refusals_agree_with_kernel`
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
            | TraceNode::Constant(constant) => match self.admitted.get(&constant) {
                | Some(&position) => ReplayNode::Constant(position),
                | None => match operators.get(&Unfolded::Definition(constant)) {
                    | Some(&position) => ReplayNode::Constant(position),
                    | None => ReplayNode::Other,
                },
            },
            | TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
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
    /// The data declaration whose own signature this erasure crosses.
    block: Block,
}

/// The data declaration whose signature an erasure crosses: its fields name
/// it at the kernel position it is about to take, which no crossed
/// declaration holds yet.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Block
{
    /// No data declaration is crossing.
    Closed,
    /// The data declaration at `source` is crossing to `kernel`.
    Open
    {
        /// Its module position.
        source: ConstantIndex,
        /// The kernel position it will take.
        kernel: ConstantIndex,
    },
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
            block: Block::Closed,
        }
    }

    /// The same erasure, crossing the data declaration at `source` to the
    /// kernel position `kernel`, so its fields' self references resolve.
    ///
    /// # Specification
    /// trivial.
    const fn crossing_block(
        mut self,
        source: ConstantIndex,
        kernel: ConstantIndex,
    ) -> Self
    {
        self.block = Block::Open { source, kernel };
        self
    }

    /// The images the current mode minted.
    ///
    /// # Specification
    /// trivial.
    const fn memo(&mut self) -> &mut Memo
    {
        match self.mode {
            | Mode::Normalizing => &mut self.normalized,
            | Mode::Verbatim => &mut self.verbatim,
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
 else if matches!(matched_left_value, Offer::Definition { .. }) && let Ok(Erased::Definition { ref declared, ref body, ref related }) = *matched_right_value { target.value_type(*declared).is_some() && target.value(*body).is_some()
    && matches!(matched_left_value, Offer::Definition { relations, .. } if relations.len() == related.len())
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
            | Offer::Data(signature) => {
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
            | Offer::Definition {
                declared,
                body,
                relations,
            } => {
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
                Ok(Erased::Definition {
                    declared,
                    body,
                    related,
                })
            },
            | Offer::Axiom { declared } => {
                let declared = self.value_type(target, declared)?;
                Ok(Erased::Axiom { declared })
            },
            | Offer::Abstract(declared) => {
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
                    | Ok(Maybe::Present(entry)) => {
                        replayed.push(entry);
                        match entry.verdict {
                            | KernelVerdict::Convertible => {},
                            | KernelVerdict::Declined(reason) => {
                                return Err((
                                    Refusal::CertificateDeclined { unfolded, reason },
                                    replayed,
                                ));
                            },
                            | KernelVerdict::NotConvertible => {
                                return Err((Refusal::MachineInvariant, replayed));
                            },
                        }
                    },
                    | Ok(Maybe::Absent(_)) => {},
                    | Err(refusal) => return Err((refusal, replayed)),
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
            | Unfolded::Definition(constant) => self.positions.admitted.get(&constant).copied(),
            | Unfolded::Abstraction(_) | Unfolded::Returned(_) => None,
        };
        let left = match crossed {
            | Some(position) => target.value_constant(position),
            | None => self.value_in(Mode::Verbatim, target, certificate.redex())?,
        };
        let redex = content_digest(target, AnyNode::Value(left));
        if !met.insert((unfolded, redex)) {
            return Ok(Maybe::Absent(replay_entry::Absent::Met));
        }
        let right = match crossed {
            | Some(_) => self.value_in(Mode::Normalizing, target, certificate.reduct())?,
            | None => self.value_in(Mode::Verbatim, target, certificate.reduct())?,
        };
        self.erase_operators(target)?;
        let decisions =
            match crossed {
                | Some(position) => Vec::from([
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
                ]),
                | None => {
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
                    decisions.extend(certificate.decisions().iter().map(|&decision| {
                        self.positions.kernel_decision(&self.operators, decision)
                    }));
                    decisions
                },
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
    /// position its declaration crossed at, or, read verbatim, the static
    /// operator a static definition is numbered at.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as above.
    /// - fails: [`Refusal::Withheld`] at `at` for a constant that neither
    ///   crossed nor, read verbatim, names a static definition.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal::Withheld`], or [`Self::operator`]'s refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three arms, separated by a crossed constant, a static
    ///   definition read verbatim, and one read normalizing, withheld.
    /// - witness: `bridge::tests::a_constant_resolves_to_its_readmitted_position`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    #[spec(ensures: |ret| ret.is_err()
        || self.positions.admitted.get(&constant).copied() == ret.ok()
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
        match (self.mode, self.positions.definitions.body(constant)) {
            | (Mode::Verbatim, Maybe::Present(body)) => {
                self.operator(Unfolded::Definition(constant), body)
            },
            | (Mode::Verbatim | Mode::Normalizing, _) => Err(Refusal::Withheld { at, constant }),
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
            | AnyNode::ValueType(erased) => Ok(erased),
            | AnyNode::Value(_) | AnyNode::Computation(_) | AnyNode::CompType(_) => {
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
            | AnyNode::Value(erased) => Ok(erased),
            | AnyNode::Computation(_) | AnyNode::ValueType(_) | AnyNode::CompType(_) => {
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
                | Step::Descend(node) => self.descend(target, node)?,
                | Step::Ascend(image) => match self.frames.pop() {
                    | Some(frame) => self.resume(target, frame, image)?,
                    | None => return Ok(image),
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
            | CoreNode::Term(TermNode::Value(at)) => self.descend_value(target, at),
            | CoreNode::Term(TermNode::Computation(at)) => self.descend_computation(target, at),
            | CoreNode::Type(TypeNode::Value(at)) => self.descend_value_type(target, at),
            | CoreNode::Type(TypeNode::Computation(at)) => self.descend_comp_type(target, at),
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
            | Some(&Image::Erased(erased)) => return Ok(Step::Ascend(AnyNode::Value(erased))),
            | Some(&Image::Open) => return Err(Refusal::Cyclic { node }),
            | None => {},
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
            | Value::Constructor { .. } | Value::Record(_) => {
                return self.prepare_native(target, node);
            },
            | Value::Reify(_) => return Err(unadmitted(UnadmittedFormer::Reify)),
            | Value::ListNil => return Ok(self.erased_value(at, target.value_list_nil())),
            | Value::ListCons(head, tail) => (
                Frame::ListHead { at, tail },
                CoreNode::Term(TermNode::Value(head)),
            ),
            | Value::Primitive { primitive, .. } => {
                let position = self
                    .positions
                    .native
                    .get(&primitive)
                    .copied()
                    .ok_or(Refusal::MachineInvariant)?;
                return Ok(self.erased_value(at, target.value_constant(position)));
            },
            | Value::PathRefl(code) => (
                Frame::PathRefl { at },
                CoreNode::Term(TermNode::Value(code)),
            ),
            | Value::PathProduct(first, second) => match self.source.natives.get(&at) {
                | Some(&native) if native != at => {
                    self.memo().values.insert(at, Image::Open);
                    self.frames.push(Frame::Reduced { at });
                    return Ok(Step::Descend(CoreNode::Term(TermNode::Value(native))));
                },
                | Some(_) | None => (
                    Frame::PathProductFirst { at, second },
                    CoreNode::Term(TermNode::Value(first)),
                ),
            },
            | Value::PathEquiv {
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
            | Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            } => return Ok(self.erased_value(at, target.value_variable(index))),
            | Value::Variable {
                zone: Zone::Linear, ..
            } => {
                return Err(Refusal::Session {
                    at: CoreNode::Term(TermNode::Value(at)),
                });
            },
            | Value::Constant(constant) => {
                let position = self.constant_position(at, constant)?;
                return Ok(self.erased_value(at, target.value_constant(position)));
            },
            | Value::Literal(ref literal) => match literal.base_type() {
                | BaseType::Integer | BaseType::String => {
                    return Ok(self.erased_value(at, target.value_literal(literal.clone())));
                },
                | BaseType::Numeric => return Err(unadmitted(UnadmittedFormer::NumericLiteral)),
            },
            | Value::Thunk(body) => (
                Frame::Thunk { at },
                CoreNode::Term(TermNode::Computation(body)),
            ),
            | Value::Quote(quoted) => {
                (Frame::Quote { at }, CoreNode::Type(TypeNode::Value(quoted)))
            },
            | Value::QuoteComputation(quoted) => (
                Frame::QuoteComputation { at },
                CoreNode::Type(TypeNode::Computation(quoted)),
            ),
            | Value::Tuple(_) => return self.prepare_native(target, node),
            | Value::Injection(summand, body) => (
                Frame::Injection { at, summand },
                CoreNode::Term(TermNode::Value(body)),
            ),
            | Value::Lift { .. } => return Err(unadmitted(UnadmittedFormer::ValueLift)),
            | Value::StaticLambda(_) => {
                let position = self.abstraction(at)?;
                return Ok(self.erased_value(at, target.value_constant(position)));
            },
            | Value::Hole(hole) => return Err(Refusal::Hole { at: node, hole }),
            | Value::Here(point) => (
                Frame::Here {
                    at,
                    family: Family::Path,
                },
                CoreNode::Term(TermNode::Value(point)),
            ),
            | Value::Funext(..) => return self.prepare_funext(target, at),
            | Value::Equiv(forward, backward) => {
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
            | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..)
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
            | Value::Stay(point) => (
                Frame::Here {
                    at,
                    family: Family::Flow,
                },
                CoreNode::Term(TermNode::Value(point)),
            ),
            | Value::Then(first, second) => (
                Frame::ThenFirst { at, second },
                CoreNode::Term(TermNode::Value(first)),
            ),
            | Value::FlowProduct(first, second) => (
                Frame::FlowProductFirst { at, second },
                CoreNode::Term(TermNode::Value(first)),
            ),
            | Value::Forward(translator) => match self.source.directed.get(&at) {
                | Some(&crate::forward::Directed::Forward(ref decided)) => (
                    Frame::ForwardType {
                        at,
                        translator,
                        images: alloc::sync::Arc::from(decided.images()),
                        dialogues: alloc::sync::Arc::from(decided.dialogues()),
                    },
                    CoreNode::Type(TypeNode::Value(decided.classifier())),
                ),
                | Some(&crate::forward::Directed::Function(_)) | None => {
                    return Err(Refusal::MachineInvariant);
                },
            },
            | Value::FunctionFlow(domain, codomain) => match self.source.directed.get(&at) {
                | Some(&crate::forward::Directed::Function(classifier)) => (
                    Frame::FunctionFlowType {
                        at,
                        domain,
                        codomain,
                    },
                    CoreNode::Type(TypeNode::Value(classifier)),
                ),
                | Some(&crate::forward::Directed::Forward(_)) | None => {
                    return Err(Refusal::MachineInvariant);
                },
            },
            | Value::Recorded(_) => return Err(unadmitted(UnadmittedFormer::Run)),
            | Value::Ua { .. } => {
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
            | Value::Nested(_) | Value::Run(_) | Value::SessionRelated { .. } => {
                return Err(Refusal::MachineInvariant);
            },
            | Value::Returned(computation) => (
                Frame::Returned { at },
                CoreNode::Term(TermNode::Computation(computation)),
            ),
            | Value::Mark { body, .. } => (
                Frame::UnmarkedValue { at },
                CoreNode::Term(TermNode::Value(body)),
            ),
            | Value::StaticApplication(head, argument) => {
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
            | Some(Frame::NativeNext(child)) => Ok(Step::Descend(child)),
            | Some(Frame::FunextBuild(node)) => self.funext(target, node),
            | _ => Err(Refusal::MachineInvariant),
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
                    | FunextStep::Return {
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
                    | FunextStep::Apply {
                        fibre,
                        ref left,
                        ref right,
                    } => {
                        let [left_image, right_image] =
                            [left.normal(), right.normal()].map(|normal| {
                                match self.reached().values.get(&normal) {
                                    | Some(&Image::Erased(image)) => Ok(image),
                                    | _ => Err(Refusal::MachineInvariant),
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
                | Task::Visit(node) => {
                    let Some(former) = self.arena.value(node)
                    else {
                        return Err(Refusal::DanglingNode {
                            node: CoreNode::Term(TermNode::Value(node)),
                        });
                    };
                    let image = match *former {
                        | Value::Tuple(ref parts) => match **parts {
                            | [] => target.value_unit(),
                            | [first, second] => {
                                tasks.extend([Task::Pair, Task::Visit(second), Task::Visit(first)]);
                                continue;
                            },
                            | _ => return Err(Refusal::MachineInvariant),
                        },
                        | Value::Injection(summand, body) => {
                            tasks.extend([Task::Inject(summand), Task::Visit(body)]);
                            continue;
                        },
                        | Value::Mark { body, .. } => {
                            tasks.push(Task::Visit(body));
                            continue;
                        },
                        | Value::Variable {
                            zone: Zone::Intuitionistic,
                            index,
                        } => target.value_variable(index),
                        | Value::Literal(ref literal)
                            if matches!(
                                literal.base_type(),
                                BaseType::Integer | BaseType::String
                            ) =>
                        {
                            target.value_literal(literal.clone())
                        },
                        | Value::Constant(constant) => {
                            let position = self.constant_position(node, constant)?;
                            target.value_constant(position)
                        },
                        | Value::Hole(hole) => {
                            return Err(Refusal::Hole {
                                at: CoreNode::Term(TermNode::Value(node)),
                                hole,
                            });
                        },
                        | _ => return Err(Refusal::MachineInvariant),
                    };
                    let unit = target.value_unit();
                    built.push((image, unit));
                },
                | Task::Pair => {
                    let (Some(second), Some(first)) = (built.pop(), built.pop())
                    else {
                        return Err(Refusal::MachineInvariant);
                    };
                    let image = target.value_tuple(&[first.0, second.0]);
                    let evidence = target.value_tuple(&[first.1, second.1]);
                    built.push((image, evidence));
                },
                | Task::Inject(summand) => {
                    let Some((payload, evidence)) = built.pop()
                    else {
                        return Err(Refusal::MachineInvariant);
                    };
                    built.push((target.value_injection(summand, payload), evidence));
                },
            }
        }
        match (built.pop(), built.is_empty()) {
            | (Some(image), true) => Ok(image),
            | _ => Err(Refusal::MachineInvariant),
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
            | Mode::Normalizing => &self.normalized,
            | Mode::Verbatim => &self.verbatim,
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
    /// - witness: `native_formers::native_formers::empty_data_elimination_preserves_the_ambient_scope`
    /// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
    #[spec(
        captures: [before = self.frames.len(), held = self.reached().computations.get(&at).copied(), continuations = self.arena.computation(at).map_or(Some(1_usize), |node| match *node { Computation::DataCase { ref branches, .. } => branches.len().checked_add(2), Computation::Case { ref branches, .. } => branches.len().checked_add(1), _ => Some(1_usize) })],
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
            | Some(&Image::Erased(erased)) => {
                return Ok(Step::Ascend(AnyNode::Computation(erased)));
            },
            | Some(&Image::Open) => return Err(Refusal::Cyclic { node }),
            | None => {},
        }
        let Some(computation) = self.arena.computation(at)
        else {
            return Err(Refusal::DanglingNode { node });
        };
        let unadmitted = |former| Refusal::OutOfFragment { at: node, former };
        let (frame, child) = match *computation {
            | Computation::DataCase { .. }
            | Computation::RecordProjection(..)
            | Computation::TupleProjection(..) => {
                return self.prepare_native(target, node);
            },
            | Computation::Perform { .. } => return Err(unadmitted(UnadmittedFormer::Perform)),
            | Computation::Handle { .. } => return Err(unadmitted(UnadmittedFormer::Handle)),
            | Computation::Resume(..) => return Err(unadmitted(UnadmittedFormer::Resume)),
            | Computation::Reset(_) => return Err(unadmitted(UnadmittedFormer::Reset)),
            | Computation::Shift(_) => return Err(unadmitted(UnadmittedFormer::Shift)),
            | Computation::Exercise { .. } => return Err(unadmitted(UnadmittedFormer::Exercise)),
            | Computation::Scope { .. } => return Err(unadmitted(UnadmittedFormer::Scope)),
            | Computation::Ride {
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
            | Computation::With(first, second) => (
                Frame::WithFirst { at, second },
                TermNode::Computation(first),
            ),
            | Computation::Project(side, pair) => {
                (Frame::Project { at, side }, TermNode::Computation(pair))
            },
            | Computation::ListFold { element, .. } => {
                self.memo().computations.insert(at, Image::Open);
                self.frames.push(Frame::ListElement { at });
                return Ok(Step::Descend(CoreNode::Type(TypeNode::Value(element))));
            },
            | Computation::Primitive {
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
                    | Arguments::Unary(argument) => (
                        Frame::ApplicationArgument { at, head },
                        TermNode::Value(argument),
                    ),
                    | Arguments::Binary([first, second]) => (
                        Frame::NativeFirst { at, head, second },
                        TermNode::Value(first),
                    ),
                }
            },
            | Computation::Transport(path, value) => {
                (Frame::TransportPath { at, value }, TermNode::Value(path))
            },
            | Computation::PathTransport {
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
            | Computation::TelescopeTransport { motive, .. } => {
                self.memo().computations.insert(at, Image::Open);
                self.frames.push(Frame::TelescopeMotive { at });
                return Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(motive))));
            },
            | Computation::Lambda(body) => (Frame::Lambda { at }, TermNode::Computation(body)),
            | Computation::Fixpoint { body, evidence } => (
                Frame::Fixpoint { at, evidence },
                TermNode::Computation(body),
            ),
            | Computation::Application(head, argument) => (
                Frame::ApplicationHead { at, argument },
                TermNode::Computation(head),
            ),
            | Computation::Return(value) => (Frame::Return { at }, TermNode::Value(value)),
            | Computation::Force(value) => (Frame::Force { at }, TermNode::Value(value)),
            | Computation::Bind(bound, body) => {
                (Frame::BindBound { at, body }, TermNode::Computation(bound))
            },
            | Computation::Case { .. } => return self.prepare_native(target, node),
            | Computation::Split {
                scrutinee,
                motive: SplitMotive::Scrutinee(motive),
                body,
                ..
            } => (
                Frame::SigmaSplitScrutinee { at, motive, body },
                TermNode::Value(scrutinee),
            ),
            | Computation::Split {
                scrutinee,
                arity,
                motive: SplitMotive::Ambient,
                body,
            } => (
                Frame::SplitReduct { at },
                TermNode::Computation(self.split_reduct(scrutinee, arity, body)),
            ),
            | Computation::Session(_) => return Err(Refusal::Session { at: node }),
            | Computation::Hole(hole) => return Err(Refusal::Hole { at: node, hole }),
            | Computation::Mark { body, .. } => (
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
    ///   a guessed position; whatever the view or the decode refuses,
    ///   converted.
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
            | Some(&Image::Erased(erased)) => return Ok(Step::Ascend(AnyNode::ValueType(erased))),
            | Some(&Image::Open) => {
                return Err(Refusal::Cyclic {
                    node: CoreNode::Type(TypeNode::Value(at)),
                });
            },
            | None => {},
        }
        let (frame, child) = match value_type_view(self.arena, at)? {
            | ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Sum(_)
            | ValueTypeView::Product(_) => {
                return self.prepare_native(target, CoreNode::Type(TypeNode::Value(at)));
            },
            | ValueTypeView::Session(session) => {
                if session.state() != session.protocol().root() {
                    return Err(Refusal::Session {
                        at: CoreNode::Type(TypeNode::Value(at)),
                    });
                }
                return self.prepare_native(target, CoreNode::Type(TypeNode::Value(at)));
            },
            | ValueTypeView::Flow {
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
            | ValueTypeView::Run(_) => {
                return Err(Refusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(at)),
                    former: UnadmittedFormer::Run,
                });
            },
            | ValueTypeView::Stack { .. } => {
                return Err(Refusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(at)),
                    former: UnadmittedFormer::Stack,
                });
            },
            | ValueTypeView::Capability { .. } => {
                return Err(Refusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(at)),
                    former: UnadmittedFormer::Capability,
                });
            },
            | ValueTypeView::List(element) => (
                Frame::ListType { at },
                CoreNode::Type(TypeNode::Value(element)),
            ),
            | ValueTypeView::PathUniverse(source, target_code) => (
                Frame::PathSource { at, target_code },
                CoreNode::Term(TermNode::Value(source)),
            ),
            | ValueTypeView::Path {
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
            | ValueTypeView::Integer => {
                return Ok(self.erased_value_type(at, target.value_type_base(BaseType::Integer)));
            },
            | ValueTypeView::String => {
                return Ok(self.erased_value_type(at, target.value_type_base(BaseType::String)));
            },
            | ValueTypeView::Unit => {
                return Ok(self.erased_value_type(at, target.value_type_unit()));
            },
            | ValueTypeView::Universe { sort, level } => {
                let erased = target.value_type_universe(sort, level.clone());
                return Ok(self.erased_value_type(at, erased));
            },
            | ValueTypeView::Abstract(atom) => {
                let Some(&position) = self.positions.admitted.get(&atom)
                else {
                    return Err(Refusal::OutOfFragment {
                        at: CoreNode::Type(TypeNode::Value(at)),
                        former: UnadmittedFormer::Abstract,
                    });
                };
                return Ok(self.erased_value_type(at, target.value_type_abstract(position)));
            },
            | ValueTypeView::Thunk(body) => (
                Frame::ThunkType { at },
                CoreNode::Type(TypeNode::Computation(body)),
            ),
            | ValueTypeView::Lift { inner, .. } => (
                Frame::TypeLift { at },
                CoreNode::Type(TypeNode::Value(inner)),
            ),
            | ValueTypeView::Element { .. } | ValueTypeView::Unknown => {
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
            | ValueTypeView::StaticPi { domain, codomain } => (
                Frame::StaticPiDomain { at, codomain },
                CoreNode::Type(TypeNode::Value(domain)),
            ),
            | ValueTypeView::Sigma { first, second } => (
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
            | Some(&Image::Erased(erased)) => return Ok(Step::Ascend(AnyNode::CompType(erased))),
            | Some(&Image::Open) => {
                return Err(Refusal::Cyclic {
                    node: CoreNode::Type(TypeNode::Computation(at)),
                });
            },
            | None => {},
        }
        let (frame, child) = match comp_type_view(self.arena, at)? {
            | CompTypeView::With(first, second) => {
                self.memo().comp_types.insert(at, Image::Open);
                self.frames.push(Frame::WithTypeFirst { at, second });
                return Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(first))));
            },
            | CompTypeView::Returner { result, effects } => {
                if effects.purity() != gandr_core_term::effect::Purity::Pure {
                    return Err(Refusal::OutOfFragment {
                        at: CoreNode::Type(TypeNode::Computation(at)),
                        former: UnadmittedFormer::EffectRow,
                    });
                }
                (Frame::Returner { at }, result)
            },
            | CompTypeView::Arrow { domain, codomain } => {
                (Frame::ArrowDomain { at, codomain }, domain)
            },
            | CompTypeView::Pi { domain, codomain } => (Frame::PiDomain { at, codomain }, domain),
            | CompTypeView::Element { .. } | CompTypeView::Unknown => {
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
                | (Value::Reify(_), _) => {
                    return Err(Refusal::OutOfFragment {
                        at: CoreNode::Term(TermNode::Value(code)),
                        former: UnadmittedFormer::Reify,
                    });
                },
                | (Value::Quote(quoted), GroundSort::Value) => {
                    return Ok(Step::Descend(CoreNode::Type(TypeNode::Value(quoted))));
                },
                | (Value::QuoteComputation(quoted), GroundSort::Computation) => {
                    return Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(quoted))));
                },
                | (
                    Value::Variable {
                        zone: Zone::Intuitionistic,
                        index,
                    },
                    _,
                ) => target.value_variable(index),
                | (
                    Value::Variable {
                        zone: Zone::Linear, ..
                    },
                    _,
                ) => {
                    return Err(Refusal::Session {
                        at: CoreNode::Term(TermNode::Value(code)),
                    });
                },
                | (Value::Constant(constant), _) => {
                    let position = self.constant_position(code, constant)?;
                    target.value_constant(position)
                },
                | (Value::StaticApplication(..) | Value::Returned(_), _) => {
                    self.frames.push(Frame::DecodeOf { level, sort });
                    return Ok(Step::Descend(CoreNode::Term(TermNode::Value(code))));
                },
                | (Value::Hole(hole), _) => {
                    return Err(Refusal::Hole {
                        at: CoreNode::Term(TermNode::Value(code)),
                        hole,
                    });
                },
                | (Value::Mark { body, .. }, _) => {
                    code = body;
                    continue;
                },
                | (Value::Quote(_), GroundSort::Computation)
                | (Value::QuoteComputation(_), GroundSort::Value)
                | (
                    Value::PathRefl(_)
                    | Value::Here(_)
                    | Value::Funext(..)
                    | Value::Equiv(..)
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
                | Some(
                    &(Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticApplication(..)),
                ) => break,
                | Some(&Value::Constant(constant)) => {
                    match self.positions.definitions.body(constant) {
                        | Maybe::Present(body) => reached = body,
                        | Maybe::Absent(_) => return Ok(descend),
                    }
                },
                | _ => return Ok(descend),
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
            | (Frame::NativeNext(child), _) => Ok(Step::Descend(child)),
            | (Frame::NativeBuild(root), _) => self.finish_native(target, root),
            | (Frame::FunextBuild(at), _) => self.funext(target, at),
            | (Frame::ListHead { at, tail }, AnyNode::Value(head)) => {
                self.frames.push(Frame::ListTail { at, head });
                self.argument(tail)
            },
            | (Frame::ListTail { at, head }, AnyNode::Value(tail)) => {
                Ok(self.erased_value(at, target.value_list_cons(head, tail)))
            },
            | (Frame::ListElement { at }, AnyNode::ValueType(element)) => {
                let Some(&Computation::ListFold { result, .. }) = self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::ListResult { at, element });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Value(result))))
            },
            | (Frame::ListResult { at, element }, AnyNode::ValueType(result)) => {
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
            | (
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
            | (
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
            | (
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
            | (Frame::PathRefl { at }, AnyNode::Value(code)) => {
                Ok(self.erased_value(at, target.value_path_refl(code)))
            },
            | (Frame::PathProductFirst { at, second }, AnyNode::Value(first)) => {
                self.frames.push(Frame::PathProductSecond { at, first });
                self.argument(second)
            },
            | (Frame::PathProductSecond { at, first }, AnyNode::Value(second)) => {
                Ok(self.erased_value(at, target.value_path_product(first, second)))
            },
            | (
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
            | (
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
            | (
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
            | (Frame::PathSource { at, target_code }, AnyNode::Value(source)) => {
                self.frames.push(Frame::PathTarget { at, source });
                self.argument(target_code)
            },
            | (Frame::PathTarget { at, source }, AnyNode::Value(target_code)) => Ok(
                self.erased_value_type(at, target.value_type_path_universe(source, target_code))
            ),
            | (Frame::FlowSource { at, target_code }, AnyNode::Value(source)) => {
                self.frames.push(Frame::FlowTarget { at, source });
                self.argument(target_code)
            },
            | (Frame::FlowTarget { at, source }, AnyNode::Value(target_code)) => Ok(
                self.erased_value_type(at, target.value_type_flow_universe(source, target_code))
            ),
            | (
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
                    | gandr_core_term::session::SessionRelation::Equivalence => {
                        target.value_session_path(classifier, evidence, unit)
                    },
                    | gandr_core_term::session::SessionRelation::Subtyping => {
                        target.value_session_flow(classifier, evidence, unit)
                    },
                };
                Ok(self.erased_value(at, image))
            },
            | (Frame::Injection { at, summand }, AnyNode::Value(body)) => {
                Ok(self.erased_value(at, target.value_injection(summand, body)))
            },
            | (Frame::TransportPath { at, value }, AnyNode::Value(path)) => {
                self.frames.push(Frame::TransportValue { at, path });
                self.argument(value)
            },
            | (Frame::TransportValue { at, path }, AnyNode::Value(value)) => {
                Ok(self.erased_computation(at, target.computation_transport(path, value)))
            },
            | (
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
            | (
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
            | (
                Frame::PathRight {
                    at,
                    carrier,
                    left,
                    family,
                },
                AnyNode::Value(right),
            ) => {
                let image = match family {
                    | Family::Path => target.value_type_path(carrier, left, right),
                    | Family::Flow => target.value_type_flow(carrier, left, right),
                };
                Ok(self.erased_value_type(at, image))
            },
            // A reflexivity checked against a path type carries the
            // dialogues relating its point to each endpoint; one only
            // synthesised relates it to itself and carries none.
            | (Frame::Here { at, family }, AnyNode::Value(point)) => {
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
                    | (Family::Path, Some(dialogues)) => {
                        target.value_here_relating(point, dialogues)
                    },
                    | (Family::Path, None) => target.value_here(point),
                    | (Family::Flow, Some(dialogues)) => {
                        target.value_stay_relating(point, dialogues)
                    },
                    | (Family::Flow, None) => target.value_stay(point),
                };
                Ok(self.erased_value(at, image))
            },
            | (
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
            | (
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
            | (
                Frame::PathTransportValue {
                    at,
                    motive,
                    path,
                    family,
                },
                AnyNode::Value(value),
            ) => {
                let image = match family {
                    | Family::Path => target.computation_path_transport(motive, path, value),
                    | Family::Flow => target.computation_ride(motive, path, value),
                };
                Ok(self.erased_computation(at, image))
            },
            | (Frame::ThenFirst { at, second }, AnyNode::Value(first)) => {
                self.frames.push(Frame::ThenSecond { at, first });
                self.argument(second)
            },
            | (Frame::ThenSecond { at, first }, AnyNode::Value(second)) => {
                Ok(self.erased_value(at, target.value_then(first, second, Seam::Sequence)))
            },
            | (Frame::FlowProductFirst { at, second }, AnyNode::Value(first)) => {
                self.frames.push(Frame::FlowProductSecond { at, first });
                self.argument(second)
            },
            | (Frame::FlowProductSecond { at, first }, AnyNode::Value(second)) => {
                Ok(self.erased_value(at, target.value_flow_product(first, second)))
            },
            | (
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
            | (
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
            | (Frame::ForwardImages(mut erasure), AnyNode::Value(image)) => {
                erasure.erased.push(image);
                self.forward_images(target, erasure)
            },
            | (
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
            | (
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
            | (
                Frame::FunctionFlowCodomain {
                    at,
                    flow_type,
                    domain,
                },
                AnyNode::Value(codomain),
            ) => Ok(self.erased_value(at, target.value_function_flow(flow_type, domain, codomain))),
            | (Frame::TelescopeMotive { at }, AnyNode::CompType(motive)) => {
                let Some(&Computation::TelescopeTransport { path, .. }) =
                    self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::TelescopePath { at, motive });
                Ok(Step::Descend(CoreNode::Term(TermNode::Value(path))))
            },
            | (Frame::TelescopePath { at, motive }, AnyNode::Value(path)) => {
                let Some(&Computation::TelescopeTransport { start, .. }) =
                    self.arena.computation(at)
                else {
                    return Err(Refusal::MachineInvariant);
                };
                self.frames.push(Frame::TelescopeStart { at, motive, path });
                Ok(Step::Descend(CoreNode::Term(TermNode::Value(start))))
            },
            | (Frame::TelescopeStart { at, motive, path }, AnyNode::Value(start)) => {
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
            | (
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
            | (
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
            | (Frame::Thunk { at }, AnyNode::Computation(body)) => {
                Ok(self.erased_value(at, target.value_thunk(body)))
            },
            | (Frame::Returned { at }, AnyNode::Computation(computation)) => {
                Ok(self.erased_value(at, target.value_returned(computation)))
            },
            | (Frame::Quote { at } | Frame::LiftedCode { at }, AnyNode::ValueType(quoted)) => {
                Ok(self.erased_value(at, target.value_quote(quoted)))
            },
            | (Frame::QuoteComputation { at }, AnyNode::CompType(quoted)) => {
                Ok(self.erased_value(at, target.value_quote_computation(quoted)))
            },
            | (Frame::Force { at }, AnyNode::Value(value)) => {
                Ok(self.erased_computation(at, target.computation_force(value)))
            },
            | (Frame::NativeFirst { at, head, second }, AnyNode::Value(first)) => {
                let head = target.computation_application(head, first);
                self.frames.push(Frame::ApplicationArgument { at, head });
                self.argument(second)
            },
            | (Frame::ApplicationHead { at, argument }, AnyNode::Computation(head)) => {
                self.frames.push(Frame::ApplicationArgument { at, head });
                self.argument(argument)
            },
            | (Frame::ApplicationArgument { at, head }, AnyNode::Value(argument)) => {
                Ok(self.erased_computation(at, target.computation_application(head, argument)))
            },
            | (Frame::Lambda { at }, AnyNode::Computation(body)) => {
                Ok(self.erased_computation(at, target.computation_lambda(body)))
            },
            | (Frame::Fixpoint { at, evidence }, AnyNode::Computation(body)) => {
                Ok(self.erased_computation(at, target.computation_fixpoint(body, evidence)))
            },
            | (Frame::Return { at }, AnyNode::Value(value)) => {
                Ok(self.erased_computation(at, target.computation_return(value)))
            },
            | (Frame::BindBound { at, body }, AnyNode::Computation(bound)) => {
                self.frames.push(Frame::BindBody { at, bound });
                Ok(Step::Descend(CoreNode::Term(TermNode::Computation(body))))
            },
            | (Frame::BindBody { at, bound }, AnyNode::Computation(body)) => {
                Ok(self.erased_computation(at, target.computation_bind(bound, body)))
            },
            | (Frame::WithFirst { at, second }, AnyNode::Computation(first)) => {
                self.frames.push(Frame::WithSecond { at, first });
                Ok(Step::Descend(CoreNode::Term(TermNode::Computation(second))))
            },
            | (Frame::WithSecond { at, first }, AnyNode::Computation(second)) => {
                Ok(self.erased_computation(at, target.computation_with(first, second)))
            },
            | (Frame::Project { at, side }, AnyNode::Computation(pair)) => {
                Ok(self.erased_computation(at, target.computation_project(side, pair)))
            },
            | (Frame::ThunkType { at }, AnyNode::CompType(body)) => {
                Ok(self.erased_value_type(at, target.value_type_thunk(body)))
            },
            | (Frame::TypeLift { at }, AnyNode::ValueType(inner)) => {
                let ValueTypeView::Lift { target: level, .. } = value_type_view(self.arena, at)?
                else {
                    return Err(Refusal::MachineInvariant);
                };
                let erased = target.value_type_lift(inner, level.clone());
                Ok(self.erased_value_type(at, erased))
            },
            | (Frame::DecodeLift { target: level }, AnyNode::ValueType(inner)) => Ok(Step::Ascend(
                AnyNode::ValueType(target.value_type_lift(inner, level)),
            )),
            | (
                Frame::Decoded {
                    at: TypeNode::Value(at),
                },
                AnyNode::ValueType(decoded),
            ) => Ok(self.erased_value_type(at, decoded)),
            | (
                Frame::Decoded {
                    at: TypeNode::Computation(at),
                },
                AnyNode::CompType(decoded),
            ) => Ok(self.erased_comp_type(at, decoded)),
            | (Frame::Returner { at }, AnyNode::ValueType(result)) => {
                Ok(self.erased_comp_type(at, target.comp_type_returner(result)))
            },
            | (Frame::ArrowDomain { at, codomain }, AnyNode::ValueType(domain)) => {
                self.frames.push(Frame::ArrowCodomain { at, domain });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(
                    codomain,
                ))))
            },
            | (Frame::ArrowCodomain { at, domain }, AnyNode::CompType(codomain)) => {
                Ok(self.erased_comp_type(at, target.comp_type_arrow(domain, codomain)))
            },
            | (Frame::WithTypeFirst { at, second }, AnyNode::CompType(first)) => {
                self.frames.push(Frame::WithTypeSecond { at, first });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(second))))
            },
            | (Frame::WithTypeSecond { at, first }, AnyNode::CompType(second)) => {
                Ok(self.erased_comp_type(at, target.comp_type_with(first, second)))
            },
            | (Frame::PiDomain { at, codomain }, AnyNode::ValueType(domain)) => {
                self.frames.push(Frame::PiCodomain { at, domain });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(
                    codomain,
                ))))
            },
            | (Frame::PiCodomain { at, domain }, AnyNode::CompType(codomain)) => {
                Ok(self.erased_comp_type(at, target.comp_type_pi(domain, codomain)))
            },
            | (Frame::Reduced { at } | Frame::UnmarkedValue { at }, AnyNode::Value(reduct)) => {
                Ok(self.erased_value(at, reduct))
            },
            | (
                Frame::UnmarkedComputation { at } | Frame::SplitReduct { at },
                AnyNode::Computation(image),
            ) => Ok(self.erased_computation(at, image)),
            | (Frame::SigmaSplitScrutinee { at, motive, body }, AnyNode::Value(scrutinee)) => {
                self.frames.push(Frame::SigmaSplitMotive {
                    at,
                    scrutinee,
                    body,
                });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(motive))))
            },
            | (
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
            | (
                Frame::SigmaSplitBody {
                    at,
                    scrutinee,
                    motive,
                },
                AnyNode::Computation(body),
            ) => Ok(self
                .erased_computation(at, target.computation_sigma_split(scrutinee, motive, body))),
            | (Frame::StaticHead { at, argument }, AnyNode::Value(head)) => {
                self.frames.push(Frame::StaticArgument { at, head });
                Ok(Step::Descend(CoreNode::Term(TermNode::Value(argument))))
            },
            | (Frame::StaticArgument { at, head }, AnyNode::Value(argument)) => {
                Ok(self.erased_value(at, target.value_static_application(head, argument)))
            },
            | (Frame::ListType { at }, AnyNode::ValueType(element)) => {
                Ok(self.erased_value_type(at, target.value_type_list(element)))
            },
            | (Frame::StaticPiDomain { at, codomain }, AnyNode::ValueType(domain)) => {
                self.frames.push(Frame::StaticPiCodomain { at, domain });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Value(codomain))))
            },
            | (Frame::StaticPiCodomain { at, domain }, AnyNode::ValueType(codomain)) => {
                Ok(self.erased_value_type(at, target.value_type_static_pi(domain, codomain)))
            },
            | (Frame::SigmaFirst { at, second }, AnyNode::ValueType(first)) => {
                self.frames.push(Frame::SigmaSecond { at, first });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Value(second))))
            },
            | (Frame::SigmaSecond { at, first }, AnyNode::ValueType(second)) => {
                Ok(self.erased_value_type(at, target.value_type_sigma(first, second)))
            },
            | (Frame::DecodeOf { level, sort }, AnyNode::Value(code)) => {
                Ok(Step::Ascend(decoded(target, code, level, sort)))
            },
            | (
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
    /// - witness: `native_formers::native_formers::a_split_crosses_as_its_projection_binds`
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
        | GroundSort::Value => AnyNode::ValueType(target.value_type_element(image, level)),
        | GroundSort::Computation => AnyNode::CompType(target.comp_type_element(image, level)),
    }
}

#[cfg(test)]
mod tests
{

    #[test]
    fn native_operations_cross_as_audited_assumptions()
    {
        use gandr_core_term::primitive::Arguments;
        use gandr_core_term::primitive::PRELUDE;
        let mut arena = CoreArena::new();
        let sub = PRELUDE
            .iter()
            .copied()
            .find(|primitive| primitive.name().as_ref() == "sub")
            .unwrap();
        let function = sub.thunk(&mut arena);
        let function_type = sub.declared_type(&mut arena);
        let function_type = arena.value_type_thunk(function_type);
        let zero = arena.value_literal(integer_literal());
        let saturated = arena.computation_primitive(sub, Arguments::Binary([zero, zero]));
        let result = arena.value_thunk(saturated);
        let integer = arena.value_type_base(BaseType::Integer);
        let returns = arena.comp_type_returner(integer);
        let result_type = arena.value_type_thunk(returns);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(
                At(0),
                Maybe::Present(function_type),
                Maybe::Present(function),
            ),
            declaration(At(1), Maybe::Present(result_type), Maybe::Present(result)),
        ]);
        assert!(
            readmission
                .readmitted()
                .iter()
                .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. }))
        );
        assert_eq!(readmission.audit().axioms(), &[ConstantIndex::from(
            0_usize
        )]);
        assert!(readmission.audit().unchecked_admissions().is_empty());
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let native = artifact.declarations().first().unwrap().declaration();
        assert!(matches!(native.content(), DeclarationContent::Axiom { .. }));
        assert_eq!(
            native
                .name()
                .segments()
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<&str>>(),
            ["sub"]
        );
        assert_eq!(
            crossed_at(&readmission, At(0)),
            ConstantIndex::from(1_usize)
        );
        assert_eq!(
            crossed_at(&readmission, At(1)),
            ConstantIndex::from(2_usize)
        );
    }

    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_nbe::TraceNode;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_core_term::Sort;
    use gandr_core_term::SortParameter;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueType;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_check_memo::ContentDigest;
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_core::KernelVerdict;
    use gandr_kernel_core::ReplayDecline;
    use gandr_kernel_core::ReplayRefusal;
    use gandr_kernel_core::TracePosition;
    use gandr_kernel_core::content_digest;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::AdmissionMark;
    use gandr_kernel_term::AnyNode;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value as KernelValue;
    use gandr_kernel_term::ValueType as KernelValueType;
    use gandr_kernel_term::decode;
    use proptest::prelude::ProptestConfig;
    use proptest::prelude::prop_assert;
    use proptest::prelude::prop_assert_eq;
    use proptest::prelude::proptest;
    use proptest::test_runner::TestCaseError;
    use quenchant_shape::shape::Maybe;

    use super::Erasure;
    use super::Frame;
    use super::Mode as Reading;
    use super::Outcome;
    use super::Positions;
    use super::Readmission;
    use super::Readmitted;
    use super::Refusal;
    use super::Replayed;
    use super::Source;
    use super::fault;
    use super::readmit;
    use super::readmit_with;
    use crate::code::Lift;
    use crate::code::Unfolded;
    use crate::context::CheckBudget;
    use crate::context::CheckingContext;
    use crate::declaration::Declaration;
    use crate::declaration::OriginToken;
    use crate::declaration::body;
    use crate::declaration::signature;
    use crate::fixture::Mode;
    use crate::fixture::Typing;
    use crate::fixture::dangling_value;
    use crate::fixture::dangling_value_type;
    use crate::fixture::function_recipe;
    use crate::fixture::integer_literal;
    use crate::fixture::numeric_literal;
    use crate::fixture::seed;
    use crate::fixture::term_recipe;
    use crate::fixture::text_literal;
    use crate::fixture::typed_recipe;
    use crate::judgement::synthesise_comp;
    use crate::module::Judged;
    use crate::module::ModuleReport;
    use crate::module::Verdict;
    use crate::module::check_module;
    use crate::refusal::CheckRefusal;
    use crate::refusal::CheckingForm;
    use crate::refusal::CoreNode;
    use crate::refusal::Mismatch;
    use crate::refusal::StaticArity;
    use crate::refusal::TermNode;
    use crate::refusal::TypeNode;
    use crate::refusal::UnadmittedFormer;

    /// A module position in a fixture.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct At(usize);

    /// The origin a fixture gives the declaration at `position`: the position
    /// plus one hundred, so an origin is never mistaken for a position.
    ///
    /// # Specification
    /// - requires: the position plus one hundred fits in `usize`.
    /// - ensures: that sum, preserving the distinction from a module position.
    /// - panics: the sum overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L1 over bounded generated modules observes each exact
    ///   declaration origin after readmission; replacing the offset with a
    ///   module position or dropping the origin changes the per-declaration
    ///   comparison.
    /// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
    #[spec(requires: position.0.checked_add(100).is_some(), ensures: |ret| position.0.checked_add(100) == Some(usize::from(ret)))]
    fn origin(position: At) -> OriginToken
    {
        OriginToken::from(position.0.checked_add(100).unwrap())
    }

    /// The declaration at `position` with these halves.
    ///
    /// # Specification
    /// - requires: the position plus one hundred fits in `usize`.
    /// - ensures: the supplied halves, position and offset origin.
    /// - panics: the origin offset overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L1 over bounded generated typed and free terms observes
    ///   each declaration outcome, hole and origin; dropping a half or
    ///   confusing source and kernel positions changes the independent
    ///   admission checks.
    /// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
    #[spec(
        requires: position.0.checked_add(100).is_some(),
        ensures: |ret| ret.constant() == ConstantIndex::from(position.0)
            && matches!(ret.content(), &crate::DeclarationContent::Value {signature,body} if signature == declared && body == defined)
            && position.0.checked_add(100) == Some(usize::from(ret.origin())),
    )]
    fn declaration(
        position: At,
        declared: Maybe<ValueTypeId, signature::Absent>,
        defined: Maybe<ValueId, body::Absent>,
    ) -> Declaration
    {
        Declaration::new(
            ConstantIndex::from(position.0),
            declared,
            defined,
            origin(position),
        )
    }

    /// No declared type.
    const UNSIGNED: Maybe<ValueTypeId, signature::Absent> =
        Maybe::Absent(signature::Absent::Unsigned);

    /// No body.
    const HOLE: Maybe<ValueId, body::Absent> = Maybe::Absent(body::Absent::Hole);

    /// Judge `module` over `arena`, then readmit what the judgement accepted.
    ///
    /// # Specification
    /// - requires: the module's ids belong to the supplied arena.
    /// - ensures: one judgement and one located readmission per declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 over bounded typed and free-term modules compares
    ///   judgement and readmission outcomes, origins and owed axioms; losing or
    ///   reordering declarations changes the per-entry oracle.
    /// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
    #[spec(ensures: |ret| ret.0.judged().len() == module.len() && ret.1.readmitted().len() == module.len()
        && ret.1.readmitted().iter().zip(module).all(|(entry,source)| entry.constant() == source.constant() && entry.origin() == source.origin()))]
    fn judge_and_readmit(
        arena: &mut CoreArena,
        module: &[Declaration],
    ) -> (ModuleReport, Readmission)
    {
        let report = {
            let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
            check_module(&mut context, module)
        };
        let readmission = readmit(arena, &report);
        (report, readmission)
    }

    /// Erase `root` from `arena` into a fresh kernel arena, with no module
    /// declaration crossed.
    ///
    /// # Specification
    /// - requires: nothing; absent or cyclic nodes are refused.
    /// - ensures: a successful image belongs to the returned fresh arena and to
    ///   the root's family; no constant has a crossed declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite former tables, missing ids and back-edges
    ///   observe exact target nodes and refusals; dropping the arena or
    ///   selecting a different node family changes these observations.
    /// - witness: `bridge::tests::returning_a_literal_lowers`
    /// - witness: `bridge::tests::returner_type_lowers`
    /// - witness: `bridge::tests::every_recursive_node_family_refuses_a_back_edge`
    #[spec(ensures: |ret| match ret.1 {
        | Ok(AnyNode::Value(at)) => matches!(root, CoreNode::Term(TermNode::Value(_))) && ret.0.value(at).is_some(),
        | Ok(AnyNode::Computation(at)) => matches!(root, CoreNode::Term(TermNode::Computation(_))) && ret.0.computation(at).is_some(),
        | Ok(AnyNode::ValueType(at)) => matches!(root, CoreNode::Type(TypeNode::Value(_))) && ret.0.value_type(at).is_some(),
        | Ok(AnyNode::CompType(at)) => matches!(root, CoreNode::Type(TypeNode::Computation(_))) && ret.0.comp_type(at).is_some(),
        | Err(_) => true,
    })]
    fn erase(
        arena: &mut CoreArena,
        root: CoreNode,
    ) -> (TermArena, Result<AnyNode, Refusal>)
    {
        let positions = Positions::default();
        let lifts = alloc::collections::BTreeMap::new();
        let definitions = alloc::collections::BTreeMap::new();
        let mut target = TermArena::new();
        let source = Source {
            lifts: &lifts,
            funexts: &BTreeMap::new(),
            equivalences: &BTreeMap::new(),
            flows: &BTreeMap::new(),
            directed: &BTreeMap::new(),
            reflexivities: &BTreeMap::new(),
            relations: &BTreeMap::new(),
            natives: &BTreeMap::new(),
            definitions: &definitions,
        };
        let image = Erasure::new(arena, source, &positions, ConstantIndex::from(0_usize))
            .erase(&mut target, root);
        (target, image)
    }

    /// What each certificate `entry` replayed unfolded, beside its verdict.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every recorded unfolding and verdict, in certificate order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — defined codes and two instances of one static
    ///   definition expose exact replay sequences; omission, reversal or
    ///   verdict substitution changes those certificate observations.
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
    #[spec(ensures: |ret| ret.len() == entry.certificates().len() && ret.iter().zip(entry.certificates()).all(|(pair,replay)| *pair == (replay.unfolded(),replay.verdict())))]
    fn steps(entry: &Readmitted) -> Vec<(Unfolded, KernelVerdict)>
    {
        entry
            .certificates()
            .iter()
            .map(|replayed| (replayed.unfolded(), replayed.verdict()))
            .collect()
    }

    /// A convertible replay of the definition at `position`.
    ///
    /// # Specification
    /// trivial.
    fn convertible(position: At) -> (Unfolded, KernelVerdict)
    {
        (
            Unfolded::Definition(ConstantIndex::from(position.0)),
            KernelVerdict::Convertible,
        )
    }

    /// The kernel position the entry at `position` crossed at.
    ///
    /// # Specification
    /// - requires: the indexed entry exists and crossed as a definition or
    ///   axiom.
    /// - ensures: its admitted kernel position, not its module position.
    /// - panics: the entry is absent or did not cross.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — marked entries before crossed ones separate module
    ///   from kernel positions; exact references in the decoded artifact expose
    ///   using the wrong coordinate or choosing another receipt.
    /// - witness: `bridge::tests::a_constant_resolves_to_its_readmitted_position`
    /// - witness: `bridge::tests::an_export_names_each_crossed_declaration_at_its_position`
    #[spec(
        requires: readmission.readmitted().get(position.0).is_some_and(|entry| matches!(entry.outcome(), Outcome::Defined { .. } | Outcome::Assumed { .. } | Outcome::Data { .. })),
        ensures: |ret| readmission.readmitted().get(position.0).is_some_and(|entry| match *entry.outcome() {
            | Outcome::Defined { admitted, .. } | Outcome::Assumed { admitted, .. } | Outcome::Data { admitted, .. } => ret == admitted.position(),
            | _ => false,
        }),
    )]
    fn crossed_at(
        readmission: &Readmission,
        position: At,
    ) -> ConstantIndex
    {
        match *readmission.readmitted()[position.0].outcome() {
            | Outcome::Defined { admitted, .. }
            | Outcome::Assumed { admitted, .. }
            | Outcome::Data { admitted, .. } => admitted.position(),
            | Outcome::Marked(_) | Outcome::Static | Outcome::Refused(_) | Outcome::Rejected(_) => {
                panic!("the declaration at this position crosses")
            },
        }
    }

    /// Every declaration `report` accepted crossed and every refused one is
    /// marked with its refusal, each at its declaration's origin; every owed
    /// hole, and nothing else, crossed as an axiom; and the artifact rests on
    /// exactly those axioms, so its audit is empty exactly when the ledger is.
    ///
    /// # Specification
    /// - requires: the report and readmission concern the same module.
    /// - ensures: success only when every acceptance, refusal, origin and owed
    ///   axiom agrees, with no unchecked admission.
    /// - fails: an assertion reports the first differing observation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 over bounded typed, free, function and universe modules
    ///   compares all located outcomes and axioms against judgement; missing,
    ///   reordered or misclassified readmissions differ. Static-only
    ///   declarations are outside this helper's accepted-module domain.
    /// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
    /// - witness: `bridge::tests::every_checked_function_definition_is_readmitted`
    /// - witness: `bridge::tests::every_checked_universe_declaration_is_readmitted`
    #[spec(ensures: |ret| ret.is_err() || (readmission.readmitted().len() == report.judged().len()
        && readmission.readmitted().iter().zip(report.judged()).all(|(entry,judged)| entry.constant() == judged.constant() && entry.origin() == judged.origin())
        && readmission.audit().unchecked_admissions().is_empty()
        && readmission.audit().axioms().is_empty() == report.ledger().entries().is_empty()))]
    fn assert_crossed(
        report: &ModuleReport,
        readmission: &Readmission,
    ) -> Result<(), TestCaseError>
    {
        prop_assert_eq!(
            readmission.readmitted().len(),
            report.judged().len(),
            "one outcome per judged declaration"
        );
        for (judged, readmitted) in report.judged().iter().zip(readmission.readmitted()) {
            prop_assert_eq!(
                (readmitted.constant(), readmitted.origin()),
                (judged.constant(), judged.origin()),
                "each outcome is located at its declaration"
            );
            prop_assert!(
                matches!(
                    (judged.verdict(), readmitted.outcome()),
                    (
                        Verdict::Checked { .. } | Verdict::Synthesised { .. },
                        &Outcome::Defined { .. }
                    ) | (Verdict::Owed(_), &Outcome::Assumed { .. })
                        | (Verdict::Refused(_), &Outcome::Marked(_))
                ),
                "{:?} crossed as {:?}",
                judged.verdict(),
                readmitted.outcome()
            );
            if let (Verdict::Refused(refusal), &Outcome::Marked(mark)) =
                (judged.verdict(), readmitted.outcome())
            {
                prop_assert_eq!(mark, refusal, "the mark is the judgement's refusal");
            }
        }
        let owed: Vec<_> = report
            .ledger()
            .entries()
            .iter()
            .map(|entry| entry.absence().constant())
            .collect();
        let mut assumed = Vec::new();
        let mut axioms = Vec::new();
        for entry in readmission.readmitted() {
            if let Outcome::Assumed { admitted, .. } = *entry.outcome() {
                assumed.push(entry.constant());
                axioms.push(admitted.position());
            }
        }
        prop_assert_eq!(
            &assumed,
            &owed,
            "every owed hole crossed as an axiom, in ledger order, and nothing else did"
        );
        prop_assert_eq!(
            readmission.audit().axioms(),
            axioms.as_slice(),
            "the artifact rests on exactly the axioms the owed holes became"
        );
        prop_assert_eq!(
            readmission.audit().axioms().is_empty(),
            report.ledger().entries().is_empty(),
            "the artifact's audit is empty exactly when the ledger is"
        );
        prop_assert!(
            readmission.audit().unchecked_admissions().is_empty(),
            "the bridge admits nothing unchecked"
        );
        Ok(())
    }

    #[test]
    fn returning_a_literal_lowers()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_literal(integer_literal());
        let returned = arena.computation_return(zero);
        let (target, image) = erase(&mut arena, CoreNode::Term(TermNode::Computation(returned)));
        let Ok(AnyNode::Computation(image)) = image
        else {
            panic!("a returned literal erases to a computation");
        };
        let Some(&gandr_kernel_term::Computation::Return(value)) = target.computation(image)
        else {
            panic!("the image is a return");
        };
        assert_eq!(
            target.value(value),
            Some(&gandr_kernel_term::Value::Literal(integer_literal())),
            "the literal carries over unchanged"
        );
    }

    #[test]
    fn returner_type_lowers()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        let (target, image) = erase(&mut arena, CoreNode::Type(TypeNode::Computation(returner)));
        let Ok(AnyNode::CompType(image)) = image
        else {
            panic!("a returner erases to a computation type");
        };
        let Some(&gandr_kernel_term::CompType::Returner(result)) = target.comp_type(image)
        else {
            panic!("the image is a returner");
        };
        assert_eq!(
            target.value_type(result),
            Some(&gandr_kernel_term::ValueType::Base(BaseType::Integer)),
            "F Integer erases to the kernel's F Integer"
        );
    }

    #[test]
    fn a_bound_variable_resolves_to_a_de_bruijn_index()
    {
        let mut arena = CoreArena::new();
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(bound);
        let lambda = arena.computation_lambda(returned);
        let (target, image) = erase(&mut arena, CoreNode::Term(TermNode::Computation(lambda)));
        let Ok(AnyNode::Computation(image)) = image
        else {
            panic!("a lambda erases to a computation");
        };
        let Some(&gandr_kernel_term::Computation::Lambda(body)) = target.computation(image)
        else {
            panic!("the image is a lambda");
        };
        let Some(&gandr_kernel_term::Computation::Return(value)) = target.computation(body)
        else {
            panic!("the lambda's body is a return");
        };
        assert_eq!(
            target.value(value),
            Some(&gandr_kernel_term::Value::Variable(DeBruijnIndex::from(
                0_u32
            ))),
            "the bound variable keeps its de Bruijn index"
        );
    }

    #[test]
    fn a_lowered_value_definition_admits()
    {
        // def answer : Integer = 0 ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let zero = arena.value_literal(integer_literal());
        let (_, readmission) = judge_and_readmit(&mut arena, &[declaration(
            At(0),
            Maybe::Present(integer),
            Maybe::Present(zero),
        )]);
        let [ref answer] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        let Outcome::Defined {
            admitted,
            ref audit,
        } = *answer.outcome()
        else {
            panic!("the definition crosses");
        };
        assert_eq!(
            admitted.position(),
            ConstantIndex::from(0_usize),
            "the first crossing takes the first kernel position"
        );
        assert!(
            audit.axioms().is_empty() && audit.unchecked_admissions().is_empty(),
            "a closed definition rests on nothing"
        );
    }

    #[test]
    fn a_lowered_computation_definition_admits()
    {
        // def greet : U (F String) = thunk { return "" } ;
        let mut arena = CoreArena::new();
        let string = arena.value_type_base(BaseType::String);
        let returns_string = arena.comp_type_returner(string);
        let suspended = arena.value_type_thunk(returns_string);
        let text = arena.value_literal(text_literal());
        let returned = arena.computation_return(text);
        let thunk = arena.value_thunk(returned);
        let (_, readmission) = judge_and_readmit(&mut arena, &[declaration(
            At(0),
            Maybe::Present(suspended),
            Maybe::Present(thunk),
        )]);
        assert!(
            matches!(
                *readmission.readmitted()[0].outcome(),
                Outcome::Defined { .. }
            ),
            "a computation declared as a thunk crosses as a value definition"
        );
    }

    #[test]
    fn a_constant_reference_across_declarations_admits()
    {
        // def first : Unit = () ; def second : Unit = first ;
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let first = arena.value_constant(ConstantIndex::from(0_usize));
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(unit_type), Maybe::Present(unit)),
            declaration(At(1), Maybe::Present(unit_type), Maybe::Present(first)),
        ]);
        let Outcome::Defined {
            admitted,
            ref audit,
        } = *readmission.readmitted()[1].outcome()
        else {
            panic!("the referring definition crosses");
        };
        assert_eq!(
            admitted.position(),
            ConstantIndex::from(1_usize),
            "the second declaration takes the second kernel position"
        );
        assert!(
            audit.axioms().is_empty(),
            "resting on a definition rests on no axiom"
        );
    }

    #[test]
    fn hole_unknown_class_rejects_exactly()
    {
        // def hole ;
        //
        // A declaration hole with no signature has no type to assume; a term
        // hole written as a body is the other member of the class.
        let mut arena = CoreArena::new();
        let (_, readmission) = judge_and_readmit(&mut arena, &[declaration(At(0), UNSIGNED, HOLE)]);
        let [ref hole] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        assert_eq!(
            (hole.origin(), hole.outcome()),
            (
                origin(At(0)),
                &Outcome::Marked(CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Hole(ConstantIndex::from(0_usize)),
                })
            ),
            "a hole with no type to owe is refused naming the hole, at its origin"
        );
        assert!(
            readmission.environment().entries().is_empty(),
            "no axiom stands in for a hole with no type"
        );
    }

    #[test]
    fn a_sorted_universe_readmits_at_its_level()
    {
        // def small : Type[+, 1] = Type ;
        // def number : Type = Integer ;
        // def action : Type[-, 0] = F Integer ;
        let mut arena = CoreArena::new();
        let one = Level::constant(LevelConstant::from(1_u64));
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
        let negative =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        let small_code = arena.value_quote(small);
        let number_code = arena.value_quote(integer);
        let action_code = arena.value_quote_computation(returns_integer);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(large), Maybe::Present(small_code)),
            declaration(At(1), Maybe::Present(small), Maybe::Present(number_code)),
            declaration(At(2), Maybe::Present(negative), Maybe::Present(action_code)),
        ]);
        let expected = [
            (GroundSort::Value, one),
            (GroundSort::Value, Level::zero()),
            (GroundSort::Computation, Level::zero()),
        ];
        for (position, (sort, level)) in expected.into_iter().enumerate() {
            let admitted = crossed_at(&readmission, At(position));
            let entry = &readmission.environment().entries()[usize::from(admitted)];
            assert_eq!(
                readmission
                    .environment()
                    .arena()
                    .value_type(entry.declared_id()),
                Some(&KernelValueType::Universe { sort, level }),
                "each code is admitted at the universe of its sort and level"
            );
        }
    }

    #[test]
    fn a_smaller_type_at_a_larger_universe_readmits_with_a_lift()
    {
        // def big : Type[+, 1] = Integer ;
        // def give : U (F Type[+, 1]) = thunk { return Integer } ;
        //
        // The kernel has no cumulativity, so each crossing admits only with the
        // lift the judgement recorded written where it stands.
        let mut arena = CoreArena::new();
        let one = Level::constant(LevelConstant::from(1_u64));
        let integer = arena.value_type_base(BaseType::Integer);
        let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
        let returns_large = arena.comp_type_returner(large);
        let suspended = arena.value_type_thunk(returns_large);
        let code = arena.value_quote(integer);
        let returned_code = arena.value_quote(integer);
        let returned = arena.computation_return(returned_code);
        let thunk = arena.value_thunk(returned);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(large), Maybe::Present(code)),
            declaration(At(1), Maybe::Present(suspended), Maybe::Present(thunk)),
        ]);
        let lift = Lift::new(Level::zero(), one);
        assert_eq!(
            (
                report.lifts().get(&code),
                report.lifts().get(&returned_code)
            ),
            (Some(&lift), Some(&lift)),
            "the judgement records the lift at both crossings"
        );
        for entry in readmission.readmitted() {
            assert!(
                matches!(*entry.outcome(), Outcome::Defined { .. }),
                "{:?} is admitted with its lift",
                entry.outcome()
            );
        }
    }

    #[test]
    fn a_code_constant_unfolds_in_conversion_and_its_trace_replays()
    {
        // def Num : Type = Integer ; def Alias : Type = Num ;
        // def n : Num = 0 ; def m : Alias = 0 ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let code = arena.value_quote(integer);
        let num = arena.value_constant(ConstantIndex::from(0_usize));
        let alias = arena.value_constant(ConstantIndex::from(1_usize));
        let decoded_num = arena.value_type_element(num, Level::zero());
        let decoded_alias = arena.value_type_element(alias, Level::zero());
        let zero = arena.value_literal(integer_literal());
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(small), Maybe::Present(code)),
            declaration(At(1), Maybe::Present(small), Maybe::Present(num)),
            declaration(At(2), Maybe::Present(decoded_num), Maybe::Present(zero)),
            declaration(At(3), Maybe::Present(decoded_alias), Maybe::Present(zero)),
        ]);
        for judged in report.judged() {
            assert!(
                matches!(judged.verdict(), Verdict::Checked { .. }),
                "the decode converts with the integer atom by unfolding: {:?}",
                judged.verdict()
            );
        }
        assert_eq!(
            steps(&readmission.readmitted()[2]),
            [convertible(At(0))],
            "the kernel replays the one unfolding the erasure of `Num` took"
        );
        assert_eq!(
            steps(&readmission.readmitted()[3]),
            [convertible(At(1)), convertible(At(0))],
            "a chain unfolds one certificate per constant, outermost first"
        );
        for entry in readmission.readmitted() {
            assert!(
                matches!(*entry.outcome(), Outcome::Defined { .. }),
                "{:?} is admitted",
                entry.outcome()
            );
        }
    }

    /// Products, sums, tuples, injections and cases of any arity cross into
    /// the kernel as the one n-ary former each is, and the kernel admits
    /// them: a triple, an injection into the last of three summands, a case
    /// of three branches and the empty sum's case of none.
    #[test]
    fn n_ary_formers_cross_the_kernel_at_their_arity()
    {
        // def t : Integer * String * Unit = (0, "a", unit) ;
        // def i : Integer + String + Unit = Inj2(unit) ;
        // def p : U (Integer + String + Unit -> F Integer) =
        //     thunk λ. case x { y => return y ; _ => return 0 ; _ => return 0 } ;
        // def v : U (Void -> F Integer) = thunk λ. case x {} ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let unit_type = arena.value_type_unit();
        let triple_type = arena.value_type_product(&[integer, string, unit_type]);
        let three = arena.value_type_sum(&[integer, string, unit_type]);
        let void = arena.value_type_sum(&[]);
        let returns_integer = arena.comp_type_returner(integer);
        let picks = arena.comp_type_arrow(three, returns_integer);
        let picks = arena.value_type_thunk(picks);
        let absurd_type = arena.comp_type_arrow(void, returns_integer);
        let absurd_type = arena.value_type_thunk(absurd_type);
        let zero = arena.value_literal(integer_literal());
        let text = arena.value_literal(text_literal());
        let unit = arena.value_unit();
        let triple = arena.value_tuple(&[zero, text, unit]);
        let injected = arena.value_injection(gandr_core_term::Summand::from(2_usize), unit);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let payload = arena.computation_return(bound);
        let constant = arena.computation_return(zero);
        let case = arena.computation_case(bound, &[payload, constant, constant]);
        let pick = arena.computation_lambda(case);
        let pick = arena.value_thunk(pick);
        let absurd = arena.computation_case(bound, &[]);
        let absurd = arena.computation_lambda(absurd);
        let absurd = arena.value_thunk(absurd);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(triple_type), Maybe::Present(triple)),
            declaration(At(1), Maybe::Present(three), Maybe::Present(injected)),
            declaration(At(2), Maybe::Present(picks), Maybe::Present(pick)),
            declaration(At(3), Maybe::Present(absurd_type), Maybe::Present(absurd)),
        ]);
        for judged in report.judged() {
            assert!(
                matches!(judged.verdict(), Verdict::Checked { .. }),
                "the n-ary former checks in the core: {:?}",
                judged.verdict()
            );
        }
        assert_eq!(readmission.readmitted().len(), 4);
        for entry in readmission.readmitted() {
            assert!(
                matches!(*entry.outcome(), Outcome::Defined { .. }),
                "the kernel admits the n-ary former: {:?}",
                entry.outcome()
            );
        }
    }

    #[test]
    fn a_code_constant_argument_unfolds_at_export()
    {
        // def Num : Type = Integer ; def n : Num = 0 ;
        // def id : U ((a : Type) -> El a -> F (El a)) = thunk λ λ. return x ;
        // def k : U (F Num) = thunk ((force id) Num) n ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let code = arena.value_quote(integer);
        let num = arena.value_constant(ConstantIndex::from(0_usize));
        let decoded_num = arena.value_type_element(num, Level::zero());
        let zero = arena.value_literal(integer_literal());
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(bound, Level::zero());
        let returns_element = arena.comp_type_returner(element);
        let arrow = arena.comp_type_arrow(element, returns_element);
        let polymorphic = arena.comp_type_pi(small, arrow);
        let identity_type = arena.value_type_thunk(polymorphic);
        let returned = arena.computation_return(bound);
        let inner = arena.computation_lambda(returned);
        let outer = arena.computation_lambda(inner);
        let identity = arena.value_thunk(outer);
        let returns_num = arena.comp_type_returner(decoded_num);
        let suspended = arena.value_type_thunk(returns_num);
        let id = arena.value_constant(ConstantIndex::from(2_usize));
        let n = arena.value_constant(ConstantIndex::from(1_usize));
        let head = arena.computation_force(id);
        let instantiated = arena.computation_application(head, num);
        let applied = arena.computation_application(instantiated, n);
        let thunk = arena.value_thunk(applied);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(small), Maybe::Present(code)),
            declaration(At(1), Maybe::Present(decoded_num), Maybe::Present(zero)),
            declaration(
                At(2),
                Maybe::Present(identity_type),
                Maybe::Present(identity),
            ),
            declaration(At(3), Maybe::Present(suspended), Maybe::Present(thunk)),
        ]);
        for judged in report.judged() {
            assert!(
                matches!(judged.verdict(), Verdict::Checked { .. }),
                "the identity instantiates at the code constant: {:?}",
                judged.verdict()
            );
        }
        for entry in readmission.readmitted() {
            assert!(
                matches!(*entry.outcome(), Outcome::Defined { .. }),
                "{:?} is admitted",
                entry.outcome()
            );
        }
        assert_eq!(
            steps(&readmission.readmitted()[3]),
            [convertible(At(0))],
            "the argument unfolds in term position and the declared type at its decode: \
             one instance, certified once"
        );
    }

    /// `El` as unquote: a function to a universe, called where a type is read,
    /// stands for the type its call returns the quote of. The checker runs
    /// the closed call under a certificate that holds each δ-step, the kernel
    /// replays it reading the returned code as its computation, a call that
    /// returns another quote is refused at the type it does return, a call on
    /// a binder stays a decode that converts with another node of the same
    /// call, and a trace stripped of its steps is declined.
    #[test]
    fn an_unquoted_function_call_crosses_with_its_run_certified()
    {
        // def pick : U (Integer + Unit -> F Type) =
        //     thunk λ. case x { _ => return ⌜Integer⌝ ; _ => return ⌜Unit⌝ } ;
        // def n : El (returned ((force pick) (Inj0 0))) = 0 ;
        // def m : El (returned ((force pick) (Inj1 unit))) = 0 ;
        // def keep : U ((t : Integer + Unit) -> El (returned ((force pick) t))
        //     -> F El (returned ((force pick) t))) = thunk λ λ. return x ;
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let integer = arena.value_type_base(BaseType::Integer);
        let unit_type = arena.value_type_unit();
        let tagged = arena.value_type_sum(&[integer, unit_type]);
        let returns_code = arena.comp_type_returner(small);
        let picking = arena.comp_type_arrow(tagged, returns_code);
        let picking = arena.value_type_thunk(picking);
        let integer_code = arena.value_quote(integer);
        let unit_code = arena.value_quote(unit_type);
        let to_integer = arena.computation_return(integer_code);
        let to_unit = arena.computation_return(unit_code);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_case(bound, &[to_integer, to_unit]);
        let pick = arena.computation_lambda(case);
        let pick = arena.value_thunk(pick);
        let zero = arena.value_literal(integer_literal());
        let unit = arena.value_unit();
        let call = |arena: &mut CoreArena, argument: ValueId| {
            let head = arena.value_constant(ConstantIndex::from(0_usize));
            let forced = arena.computation_force(head);
            let applied = arena.computation_application(forced, argument);
            arena.value_returned(applied)
        };
        let first = arena.value_injection(gandr_core_term::Summand::from(0_usize), zero);
        let integer_call = call(&mut arena, first);
        let picked_integer = arena.value_type_element(integer_call, Level::zero());
        let second = arena.value_injection(gandr_core_term::Summand::from(1_usize), unit);
        let unit_call = call(&mut arena, second);
        let picked_unit = arena.value_type_element(unit_call, Level::zero());
        let held_call = call(&mut arena, bound);
        let held = arena.value_type_element(held_call, Level::zero());
        let returned_call = call(&mut arena, bound);
        let returned = arena.value_type_element(returned_call, Level::zero());
        let returns_held = arena.comp_type_returner(returned);
        let keeping = arena.comp_type_arrow(held, returns_held);
        let keeping = arena.comp_type_pi(tagged, keeping);
        let keeping = arena.value_type_thunk(keeping);
        let kept = arena.computation_return(bound);
        let kept = arena.computation_lambda(kept);
        let kept = arena.computation_lambda(kept);
        let kept = arena.value_thunk(kept);
        assert_ne!(held_call, returned_call, "the two calls are two nodes");
        let module = [
            declaration(At(0), Maybe::Present(picking), Maybe::Present(pick)),
            declaration(At(1), Maybe::Present(picked_integer), Maybe::Present(zero)),
            declaration(At(2), Maybe::Present(picked_unit), Maybe::Present(zero)),
            declaration(At(3), Maybe::Present(keeping), Maybe::Present(kept)),
        ];
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            check_module(&mut context, &module)
        };
        let [ref function, ref selected, ref other, ref keep] = *report.judged()
        else {
            panic!("one verdict per declaration");
        };
        assert!(matches!(function.verdict(), Verdict::Checked { .. }));
        assert!(
            matches!(selected.verdict(), Verdict::Checked { .. }),
            "the call runs to the integer quote and `0` checks at it: {:?}",
            selected.verdict()
        );
        assert!(
            matches!(other.verdict(), Verdict::Refused(_)),
            "the other call runs to the unit quote, where `0` does not check: {:?}",
            other.verdict()
        );
        assert!(
            matches!(keep.verdict(), Verdict::Checked { .. }),
            "a call on a binder is rigid, and two nodes of it convert: {:?}",
            keep.verdict()
        );
        let readmission = readmit_with(&mut arena, &report, |certificate| certificate);
        let [ref function_entry, ref selected_entry, _, ref keep_entry] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        assert!(matches!(*function_entry.outcome(), Outcome::Defined { .. }));
        assert!(
            matches!(*selected_entry.outcome(), Outcome::Defined { .. }),
            "the kernel admits the declaration at the type the call returns: {:?}",
            selected_entry.outcome()
        );
        assert_eq!(
            steps(selected_entry),
            [(Unfolded::Returned(integer_call), KernelVerdict::Convertible)],
            "one run, certified once, replayed convertible"
        );
        assert!(
            matches!(*keep_entry.outcome(), Outcome::Defined { .. }),
            "the kernel admits the decode of the held call: {:?}",
            keep_entry.outcome()
        );
        let stripped = readmit_with(&mut arena, &report, |certificate| {
            certificate.with_decisions(Vec::new())
        });
        assert!(
            matches!(
                stripped.readmitted()[1].outcome(),
                Outcome::Refused(Refusal::CertificateDeclined {
                    unfolded: Unfolded::Returned(at),
                    ..
                }) if *at == integer_call
            ),
            "the replay needs the held unfolding the trace records: {:?}",
            stripped.readmitted()[1].outcome()
        );
    }

    #[test]
    fn a_declining_certificate_faults_the_declaration()
    {
        // def Pair : Type -> Type = \X. El X * El X ;
        // def instance : Type = Pair Integer ;
        //
        // Missing dialogue and a foreign answer retain different reasons.
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let operator_type = arena.value_type_static_pi(small, small);
        let operator = pair_operator(&mut arena);
        let integer = arena.value_type_base(BaseType::Integer);
        let integer_code = arena.value_quote(integer);
        let pair = arena.value_constant(ConstantIndex::from(0_usize));
        let instance = arena.value_static_application(pair, integer_code);
        let module = [
            declaration(
                At(0),
                Maybe::Present(operator_type),
                Maybe::Present(operator),
            ),
            declaration(At(1), Maybe::Present(small), Maybe::Present(instance)),
        ];
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            check_module(&mut context, &module)
        };
        let foreign = [ConversionDecision::Force {
            thunk: TraceNode::Constant(ConstantIndex::from(0_usize)),
        }];
        for (decisions, reason) in [
            (&[][..], ReplayRefusal::Exhausted),
            (foreign.as_slice(), ReplayRefusal::Inapplicable {
                at: TracePosition::from(0),
            }),
        ] {
            let readmission = readmit_with(&mut arena, &report, |certificate| {
                certificate.with_decisions(decisions.to_vec())
            });
            let [ref operator_entry, ref faulted] = *readmission.readmitted()
            else {
                panic!("one outcome per declaration");
            };
            assert_eq!(
                operator_entry.outcome(),
                &Outcome::Static,
                "the operator itself replays nothing"
            );
            let reason = ReplayDecline::Refused(reason);
            let refusal = Refusal::CertificateDeclined {
                unfolded: Unfolded::Definition(ConstantIndex::from(0_usize)),
                reason,
            };
            assert_eq!(faulted.outcome(), &Outcome::Refused(refusal));
            assert!(
                matches!(faulted.certificates(), [Replayed {
                    verdict: KernelVerdict::Declined(recorded),
                    ..
                }] if *recorded == reason),
                "the refusal and replay record preserve the same reason"
            );
            assert_eq!(refusal.classify(), FailureClass::EngineFault);
            assert!(
                readmission.environment().entries().is_empty(),
                "the refused declaration left the environment as it was"
            );
        }
    }

    #[test]
    fn an_unbound_sealed_atom_is_refused()
    {
        let mut arena = CoreArena::new();
        let atom = arena.value_type_abstract(ConstantIndex::from(3_usize));
        let at = CoreNode::Type(TypeNode::Value(atom));
        let (target, image) = erase(&mut arena, at);
        assert_eq!(
            image,
            Err(Refusal::OutOfFragment {
                at,
                former: UnadmittedFormer::Abstract,
            }),
            "an abstract atom is refused by name"
        );
        assert_eq!(
            target.watermark(),
            TermArena::new().watermark(),
            "nothing is minted at a guessed position"
        );
    }

    #[test]
    fn a_bound_sealed_atom_lowers_to_the_kernel_atom()
    {
        // module Counter :> #{ type T, seed : T } { type T = Integer ;
        //                                           def seed = 7 ; }
        // def client : Counter.T = Counter.seed ;
        //
        // The atom crosses first, at kernel position 0; the member checks at
        // the representation and the witness exports it at the atom, both
        // inside the seal; the client reads the atom past it.
        use gandr_kernel_core::Environment;
        use gandr_kernel_term::SealExtent;
        use gandr_kernel_term::SealScope;

        use crate::declaration::AbstractType;
        use crate::seal::ComponentOrdinal;
        use crate::seal::SealSite;
        use crate::seal::SealingSite;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let seven = arena.value_literal(integer_literal());
        let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let seed = arena.value_constant(ConstantIndex::from(1_usize));
        let exported = arena.value_constant(ConstantIndex::from(2_usize));
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            Declaration::abstract_type(
                ConstantIndex::from(0_usize),
                AbstractType::new(
                    small,
                    integer,
                    SealExtent::from(2_usize),
                    SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(0_usize)),
                ),
                origin(At(0)),
            ),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(seven)),
            declaration(At(2), Maybe::Present(atom), Maybe::Present(seed)),
            declaration(At(3), Maybe::Present(atom), Maybe::Present(exported)),
        ]);
        let positions: Vec<_> = readmission
            .readmitted()
            .iter()
            .map(|entry| match *entry.outcome() {
                | Outcome::Data { admitted, .. } => Ok(("data", usize::from(admitted.position()))),
                | Outcome::Defined { admitted, .. } => {
                    Ok(("defined", usize::from(admitted.position())))
                },
                | ref other => Err(other.clone()),
            })
            .collect();
        assert_eq!(
            positions,
            [
                Ok(("data", 0)),
                Ok(("defined", 1)),
                Ok(("defined", 2)),
                Ok(("defined", 3))
            ],
            "the atom crosses as a nominal declaration and every member and client is admitted"
        );
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let contents: Vec<_> = artifact
            .declarations()
            .iter()
            .map(|marked| marked.declaration().content().clone())
            .collect();
        let DeclarationContent::AbstractType { kind, scope, .. } = contents[0]
        else {
            panic!("the atom exports as an abstract type");
        };
        assert_eq!(
            (artifact.arena().value_type(kind), scope),
            (
                Some(&KernelValueType::Universe {
                    sort: GroundSort::Value,
                    level: Level::zero(),
                }),
                SealScope::Closed(SealExtent::from(2_usize))
            ),
            "at its kind, its seal closed over the member and the witness and not the client"
        );
        for declared in contents.iter().skip(2) {
            let &DeclarationContent::Def { declared, .. } = declared
            else {
                panic!("the witness and the client export as definitions");
            };
            assert_eq!(
                artifact.arena().value_type(declared),
                Some(&KernelValueType::Abstract(ConstantIndex::from(0_usize))),
                "each reads the kernel atom at the position its abstract type took"
            );
        }
        assert!(
            Environment::replay(artifact.arena().clone(), artifact.declarations()).is_ok(),
            "the export replays, the seal where the producer drew it"
        );
    }

    #[test]
    fn a_body_naming_a_withheld_declaration_is_refused()
    {
        // def bad : Integer = "" ; def uses : Integer = bad ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_literal(text_literal());
        let bad = arena.value_constant(ConstantIndex::from(0_usize));
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(bad)),
        ]);
        assert!(
            matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
            "the judgement reads the reference through the declared type"
        );
        let uses = &readmission.readmitted()[1];
        let withheld = Refusal::Withheld {
            at: bad,
            constant: ConstantIndex::from(0_usize),
        };
        assert_eq!(
            (uses.origin(), uses.outcome()),
            (origin(At(1)), &Outcome::Refused(withheld)),
            "the reference is refused at the referring declaration's origin, naming its node"
        );
        assert_eq!(
            withheld.classify(),
            FailureClass::MalformedSource,
            "a withheld reference is the source's"
        );
        assert!(
            readmission.environment().entries().is_empty(),
            "nothing entered the kernel"
        );
    }

    #[test]
    fn a_constant_resolves_to_its_readmitted_position()
    {
        // def bad : Integer = "" ; def number : Integer = 0 ;
        // def word : String = "" ; def copy : String = word ;
        //
        // `word` is module position 2 and kernel position 1. The reference
        // crosses only under that map: kernel position 2 is `copy` itself, and
        // kernel position 0 is an integer.
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let zero = arena.value_literal(integer_literal());
        let text = arena.value_literal(text_literal());
        let word = arena.value_constant(ConstantIndex::from(2_usize));
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
            declaration(At(2), Maybe::Present(string), Maybe::Present(text)),
            declaration(At(3), Maybe::Present(string), Maybe::Present(word)),
        ]);
        assert!(
            matches!(*readmission.readmitted()[0].outcome(), Outcome::Marked(_)),
            "the first declaration does not cross"
        );
        assert_eq!(
            [
                crossed_at(&readmission, At(1)),
                crossed_at(&readmission, At(2)),
                crossed_at(&readmission, At(3)),
            ],
            [
                ConstantIndex::from(0_usize),
                ConstantIndex::from(1_usize),
                ConstantIndex::from(2_usize),
            ],
            "each crossing takes the next kernel position, and the reference crosses"
        );
    }

    #[test]
    fn native_lists_check_and_round_trip()
    {
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let list_type = arena.value_type_list(unit_type);
        let unit = arena.value_unit();
        let nil = arena.value_list_nil();
        let cons = arena.value_list_cons(unit, nil);
        let bad_tail = arena.value_list_cons(unit, unit);
        let head = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let tail = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let cell = arena.value_list_cons(head, tail);
        let on_nil = arena.computation_return(nil);
        let on_cons = arena.computation_return(cell);
        let folded = arena.computation_list_fold(unit_type, list_type, cons, on_nil, on_cons);
        let folded = arena.value_thunk(folded);
        let result = arena.comp_type_returner(list_type);
        let fold_type = arena.value_type_thunk(result);
        let swapped = arena.value_list_cons(tail, head);
        let swapped = arena.computation_return(swapped);
        let swapped = arena.computation_list_fold(unit_type, list_type, cons, on_nil, swapped);
        let swapped = arena.value_thunk(swapped);
        let sum_nil = arena.value_injection(Side::Left.into(), unit);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(list_type), Maybe::Present(nil)),
            declaration(At(1), Maybe::Present(list_type), Maybe::Present(cons)),
            declaration(At(2), Maybe::Present(list_type), Maybe::Present(bad_tail)),
            declaration(At(3), Maybe::Present(fold_type), Maybe::Present(folded)),
            declaration(At(4), Maybe::Present(fold_type), Maybe::Present(swapped)),
            declaration(At(5), Maybe::Present(list_type), Maybe::Present(sum_nil)),
        ]);
        for admitted in &readmission.readmitted()[.. 2] {
            assert!(
                matches!(admitted.outcome(), Outcome::Defined { .. }),
                "{:?}",
                admitted.outcome()
            );
        }
        assert!(matches!(
            readmission.readmitted()[2].outcome(),
            Outcome::Marked(_)
        ));
        assert!(
            matches!(
                readmission.readmitted()[3].outcome(),
                Outcome::Defined { .. }
            ),
            "{:?}",
            readmission.readmitted()[3].outcome()
        );
        assert!(matches!(
            readmission.readmitted()[4].outcome(),
            Outcome::Marked(_)
        ));
        assert!(matches!(
            readmission.readmitted()[5].outcome(),
            Outcome::Marked(_)
        ));
        let image = readmission.export(BTreeMap::new());
        let imported = decode(image.as_image()).expect("lists decode");
        assert_eq!(
            gandr_kernel_term::encode(imported.arena(), imported.declarations()).as_image(),
            image.as_image()
        );
    }

    #[test]
    fn effectful_declarations_are_refused_by_name_at_the_pure_boundary()
    {
        use gandr_core_term::effect::EffectName;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::EffectSig;
        use gandr_core_term::effect::OperationName;
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let interface = EffectSig::new(EffectName::from("IO"), [EffectOp {
            name: OperationName::from("emit"),
            payload: unit_type,
            reply: unit_type,
        }])
        .expect("one operation");
        let effectful = arena
            .comp_type_returner_with_effects(unit_type, EffectRow::singleton(interface.clone()));
        let effectful_type = arena.value_type_thunk(effectful);
        let pure = arena.comp_type_returner(unit_type);
        let pure_type = arena.value_type_thunk(pure);
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let body = arena.value_thunk(returned);
        let requested = arena.computation_perform(interface.clone(), "emit".into(), unit);
        let requested_body = arena.value_thunk(requested);
        let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let resumed = arena.computation_resume(continuation, returned);
        let handled = arena.computation_handle(
            interface,
            requested,
            returned,
            [gandr_core_term::control::EffectClause {
                operation: "emit".into(),
                body: resumed,
            }]
            .into(),
        );
        let handled_body = arena.value_thunk(handled);
        let shifted = arena.computation_shift(resumed);
        let reset = arena.computation_reset(shifted);
        let reset_body = arena.value_thunk(reset);
        let stack_type = arena.value_type_stack(pure, pure);
        let stack = arena.value_reify([].into());
        let stack_constant = arena.value_constant(ConstantIndex::from(5_usize));
        let resumed = arena.computation_resume(stack_constant, returned);
        let resumed_body = arena.value_thunk(resumed);
        let quoted = arena.value_quote_computation(effectful);
        let quote_type = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            crate::synthesise_value(&mut context, quoted)
                .expect("a well-formed runtime computation code")
                .produced()
                .id()
        };
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(
                At(0),
                Maybe::Present(effectful_type),
                Maybe::Present(requested_body),
            ),
            declaration(At(1), Maybe::Present(effectful_type), HOLE),
            declaration(At(2), Maybe::Present(pure_type), Maybe::Present(body)),
            declaration(
                At(3),
                Maybe::Present(pure_type),
                Maybe::Present(handled_body),
            ),
            declaration(At(4), Maybe::Present(pure_type), Maybe::Present(reset_body)),
            declaration(At(5), Maybe::Present(stack_type), Maybe::Present(stack)),
            declaration(
                At(6),
                Maybe::Present(pure_type),
                Maybe::Present(resumed_body),
            ),
            declaration(At(7), Maybe::Present(quote_type), Maybe::Present(quoted)),
        ]);
        for (position, entry) in readmission.readmitted().iter().take(2).enumerate() {
            assert_eq!(entry.constant(), ConstantIndex::from(position));
            assert_eq!(
                entry.outcome(),
                &Outcome::Refused(Refusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Computation(effectful)),
                    former: UnadmittedFormer::EffectRow
                })
            );
        }
        assert!(matches!(
            readmission.readmitted()[2].outcome(),
            Outcome::Defined { .. }
        ));
        for (position, at, former) in [
            (
                3_usize,
                CoreNode::Term(TermNode::Computation(handled)),
                UnadmittedFormer::Handle,
            ),
            (
                4,
                CoreNode::Term(TermNode::Computation(reset)),
                UnadmittedFormer::Reset,
            ),
            (
                5,
                CoreNode::Type(TypeNode::Value(stack_type)),
                UnadmittedFormer::Stack,
            ),
            (
                6,
                CoreNode::Term(TermNode::Computation(resumed)),
                UnadmittedFormer::Resume,
            ),
            (
                7,
                CoreNode::Type(TypeNode::Computation(effectful)),
                UnadmittedFormer::EffectRow,
            ),
        ] {
            let entry = &readmission.readmitted()[position];
            assert_eq!(entry.constant(), ConstantIndex::from(position));
            assert_eq!(
                entry.outcome(),
                &Outcome::Refused(Refusal::OutOfFragment { at, former })
            );
        }
        assert!(readmission.audit().axioms().is_empty());
        let artifact = readmission.export(BTreeMap::new());
        let decoded = decode(artifact.as_image()).expect("the remaining pure definition exports");
        assert_eq!(decoded.declarations().len(), 1);
    }

    #[test]
    fn a_lazy_product_crosses_as_its_kernel_nodes()
    {
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_unit = arena.comp_type_returner(unit_type);
        let returns_integer = arena.comp_type_returner(integer);
        let pair_type = arena.comp_type_with(returns_unit, returns_integer);
        let suspended_pair = arena.value_type_thunk(pair_type);
        let unit = arena.value_unit();
        let zero = arena.value_literal(integer_literal());
        let first = arena.computation_return(unit);
        let second = arena.computation_return(zero);
        let pair = arena.computation_with(first, second);
        let pair_body = arena.value_thunk(pair);
        let pair_constant = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(pair_constant);
        let projected = arena.computation_project(Side::Right, forced);
        let projected_body = arena.value_thunk(projected);
        let projected_type = arena.value_type_thunk(returns_integer);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(
                At(0),
                Maybe::Present(suspended_pair),
                Maybe::Present(pair_body),
            ),
            declaration(
                At(1),
                Maybe::Present(projected_type),
                Maybe::Present(projected_body),
            ),
        ]);
        for entry in readmission.readmitted() {
            assert!(
                matches!(*entry.outcome(), Outcome::Defined { .. }),
                "the kernel re-derives the pairing at its unequal sides and the right \
                 projection at the right side's type: {:?}",
                entry.outcome()
            );
        }
        let artifact = readmission.export(BTreeMap::new());
        let decoded = decode(artifact.as_image()).expect("the lazy product exports");
        assert_eq!(decoded.declarations().len(), 2);
    }

    #[test]
    fn native_path_module_round_trips()
    {
        use alloc::sync::Arc;

        use gandr_kernel_conversion_trace::ConversionDecision;
        use gandr_kernel_core::path_universe::Dialogue;
        use gandr_kernel_core::path_universe::Transport;
        use gandr_kernel_core::path_universe::replay_transport;
        use gandr_kernel_core::replay::EngineClaim;
        use gandr_kernel_core::replay::ReplayBudget;
        use gandr_kernel_term::PathEvidence;

        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let boolean = arena.value_type_sum(&[unit_type, unit_type]);
        let code = arena.value_quote(boolean);
        let path_type = arena.value_type_path_universe(code, code);
        let unit = arena.value_unit();
        let truth = arena.value_injection(Side::Left.into(), unit);
        let falsity = arena.value_injection(Side::Right.into(), unit);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let left = arena.value_injection(Side::Right.into(), variable);
        let right = arena.value_injection(Side::Left.into(), variable);
        let left = arena.computation_return(left);
        let right = arena.computation_return(right);
        let not = arena.computation_case(variable, &[left, right]);
        let not = arena.computation_lambda(not);
        let not = arena.value_thunk(not);
        // These are untrusted candidate dialogues, not acceptance marks. The
        // native admission below derives and replays all four round trips.
        let evidence = Arc::new(PathEvidence {
            source: vec![vec![ConversionDecision::Decompose], Vec::new()],
            target: vec![Vec::new(), vec![ConversionDecision::Decompose]],
        });
        let path = arena.value_path_equiv(path_type, not, not, evidence);
        let refl = arena.value_path_refl(code);
        let product_type = arena.value_type_product(&[boolean, boolean]);
        let product_code = arena.value_quote(product_type);
        let product_path_type = arena.value_type_path_universe(product_code, product_code);
        let product_path = arena.value_path_product(path, refl);
        let input = arena.value_tuple(&[falsity, truth]);
        let transport = arena.computation_transport(product_path, input);
        let body = arena.value_thunk(transport);
        let result = arena.comp_type_returner(product_type);
        let declared = arena.value_type_thunk(result);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(path_type), Maybe::Present(path)),
            declaration(At(1), Maybe::Present(path_type), Maybe::Present(refl)),
            declaration(
                At(2),
                Maybe::Present(product_path_type),
                Maybe::Present(product_path),
            ),
            declaration(At(3), Maybe::Present(declared), Maybe::Present(body)),
        ]);
        let image = readmission.export(BTreeMap::new());
        let imported = decode(image.as_image()).expect("native module decodes");
        assert_eq!(
            gandr_kernel_term::encode(imported.arena(), imported.declarations()).as_image(),
            image.as_image()
        );
        let declarations = imported.declarations();
        let [_, _, _, ref transported] = *declarations
        else {
            panic!(
                "every native declaration must cross: {:?}",
                readmission.readmitted()
            );
        };
        let DeclarationContent::Def { body, .. } = *transported.declaration().content()
        else {
            panic!("transport is a definition");
        };
        let Some(&KernelValue::Thunk(computation)) = imported.arena().value(body)
        else {
            panic!("transport is suspended");
        };
        let Some(&gandr_kernel_term::Computation::Transport(path, value)) =
            imported.arena().computation(computation)
        else {
            panic!("transport remains native on import");
        };
        let mut kernel = imported.arena().clone();
        let unit = kernel.value_unit();
        let truth = kernel.value_injection(Side::Left.into(), unit);
        let output = kernel.value_tuple(&[truth, truth]);
        let expected = kernel.computation_return(output);
        assert_eq!(
            replay_transport(
                &mut kernel,
                Transport { path, value },
                expected,
                EngineClaim::Convertible,
                &Dialogue::default(),
                ReplayBudget::DEFAULT
            )
            .expect("imported certificate is rechecked"),
            KernelVerdict::Convertible
        );
    }

    #[test]
    fn an_export_names_each_crossed_declaration_at_its_position()
    {
        // module M { def bad : Integer = "" ; def first : Integer = 0 ;
        //            def second : Integer = first ; }
        // def top : Integer = M.second ;
        //
        // `bad` is marked and leaves the artifact. `first` crosses at kernel
        // position 0, so `second` reads 0 and `top` reads 1 whatever they are
        // named, and `top` is given no name at all.
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_literal(text_literal());
        let zero = arena.value_literal(integer_literal());
        let first = arena.value_constant(ConstantIndex::from(1_usize));
        let second = arena.value_constant(ConstantIndex::from(2_usize));
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
            declaration(At(2), Maybe::Present(integer), Maybe::Present(first)),
            declaration(At(3), Maybe::Present(integer), Maybe::Present(second)),
        ]);
        let named = |segments: [&str; 2]| {
            StructuredName::from(
                segments
                    .into_iter()
                    .map(|segment| NameSegment::from_text(String::from(segment)).unwrap())
                    .collect::<Vec<NameSegment>>(),
            )
        };
        let names = BTreeMap::from([
            (ConstantIndex::from(0_usize), named(["M", "bad"])),
            (ConstantIndex::from(1_usize), named(["M", "first"])),
            (ConstantIndex::from(2_usize), named(["M", "second"])),
        ]);
        let artifact = decode(readmission.export(names).as_image()).unwrap();

        let exported: Vec<(Vec<&str>, AdmissionMark, Option<&KernelValue>)> = artifact
            .declarations()
            .iter()
            .map(|marked| {
                let body = match *marked.declaration().content() {
                    | DeclarationContent::Def { body, .. } => artifact.arena().value(body),
                    | DeclarationContent::Axiom { .. }
                    | DeclarationContent::Data { .. }
                    | DeclarationContent::AbstractType { .. } => None,
                };
                let name = marked
                    .declaration()
                    .name()
                    .segments()
                    .iter()
                    .map(AsRef::as_ref)
                    .collect();
                (name, marked.mark(), body)
            })
            .collect();
        let at = |position: usize| Some(KernelValue::Constant(ConstantIndex::from(position)));
        assert_eq!(
            exported
                .iter()
                .map(|&(ref name, mark, _)| (name.clone(), mark))
                .collect::<Vec<_>>(),
            [
                (vec!["M", "first"], AdmissionMark::Checked),
                (vec!["M", "second"], AdmissionMark::Checked),
                (vec![], AdmissionMark::Checked),
            ],
            "each crossed declaration carries its own name, the marked one is absent, and \
             an unnamed one carries none"
        );
        assert_eq!(
            exported
                .iter()
                .skip(1)
                .map(|&(_, _, body)| body.cloned())
                .collect::<Vec<_>>(),
            [at(0), at(1)],
            "each reference reads the kernel position its target took"
        );
    }

    #[test]
    fn every_former_outside_the_fragment_is_refused_by_name()
    {
        // The abstract atom is witnessed by its own test.
        let mut arena = CoreArena::new();
        let unit = arena.value_unit();

        let rows = [
            (
                CoreNode::Term(TermNode::Value(arena.value_lift(Level::zero(), unit))),
                UnadmittedFormer::ValueLift,
            ),
            (
                CoreNode::Term(TermNode::Value(arena.value_literal(numeric_literal()))),
                UnadmittedFormer::NumericLiteral,
            ),
            (
                CoreNode::Type(TypeNode::Value(arena.value_type_base(BaseType::Numeric))),
                UnadmittedFormer::NumericAtom,
            ),
            (
                CoreNode::Type(TypeNode::Value(arena.value_type_universe(
                    Sort::Parameter(SortParameter::from(0_u32)),
                    Level::zero(),
                ))),
                UnadmittedFormer::SortParameter,
            ),
        ];
        for (at, former) in rows {
            assert_eq!(
                erase(&mut arena, at).1,
                Err(Refusal::OutOfFragment { at, former }),
                "{former:?} is refused by name, at its node"
            );
        }
    }

    #[test]
    fn element_identity_and_a_compound_endpoint_are_readmitted()
    {
        // def id        : U (Integer -> F Integer) = thunk { \x. return x } ;
        // def same      : Path(Integer, 0, 0) = here(0) ;
        // def moved     : U (F Path(Integer, 0, 0))
        //               = thunk { tr(y. Path(Integer, 0, y), here(0), here(0)) } ;
        // def compound  : Path(Integer, (id 0), 0) = here(0) ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let suspended_arrow = arena.value_type_thunk(arrow);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returns_bound = arena.computation_return(bound);
        let lambda = arena.computation_lambda(returns_bound);
        let identity = arena.value_thunk(lambda);
        let zero = arena.value_literal(integer_literal());
        let here = arena.value_here(zero);
        let path = arena.value_type_path(integer, zero, zero);
        let motive = arena.value_type_path(integer, zero, bound);
        let transport = arena.computation_path_transport(motive, here, here);
        let moved = arena.value_thunk(transport);
        let returns_path = arena.comp_type_returner(path);
        let suspended_path = arena.value_type_thunk(returns_path);
        let named = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(named);
        let applied = arena.computation_application(forced, zero);
        let compound = arena.value_returned(applied);
        let compound_path = arena.value_type_path(integer, compound, zero);
        let module = [
            declaration(
                At(0),
                Maybe::Present(suspended_arrow),
                Maybe::Present(identity),
            ),
            declaration(At(1), Maybe::Present(path), Maybe::Present(here)),
            declaration(At(2), Maybe::Present(suspended_path), Maybe::Present(moved)),
            declaration(At(3), Maybe::Present(compound_path), Maybe::Present(here)),
        ];
        let (report, readmission) = judge_and_readmit(&mut arena, &module);
        let verdicts: Vec<_> = report.judged().iter().map(Judged::verdict).collect();
        assert!(
            verdicts
                .iter()
                .all(|verdict| matches!(verdict, Verdict::Checked { .. })),
            "the judgement accepts all four: {verdicts:?}"
        );
        let [_, ref same, ref transported, ref compounded] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        assert!(
            matches!(*same.outcome(), Outcome::Defined { .. }),
            "a path type and its reflexivity cross, and the kernel re-derives them: {:?}",
            same.outcome()
        );
        assert!(
            matches!(*transported.outcome(), Outcome::Defined { .. }),
            "a transport in a motive under its binder crosses, and the kernel re-derives it: \
             {:?}",
            transported.outcome()
        );
        assert!(
            matches!(*compounded.outcome(), Outcome::Defined { .. }),
            "a compound endpoint crosses, and the kernel replays its dialogue through `id`: {:?}",
            compounded.outcome()
        );
        assert_eq!(
            [
                crossed_at(&readmission, At(0)),
                crossed_at(&readmission, At(1)),
                crossed_at(&readmission, At(2)),
                crossed_at(&readmission, At(3)),
            ],
            [
                ConstantIndex::from(0_usize),
                ConstantIndex::from(1_usize),
                ConstantIndex::from(2_usize),
                ConstantIndex::from(3_usize),
            ],
            "the definition and the three identity declarations enter in declaration order"
        );
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let declared = artifact
            .declarations()
            .last()
            .map(|marked| marked.declaration().declared_id())
            .unwrap();
        let Some(&KernelValueType::Path { left, .. }) = artifact.arena().value_type(declared)
        else {
            panic!("the compound declaration crosses at a path type");
        };
        let Some(&KernelValue::Returned(applied)) = artifact.arena().value(left)
        else {
            panic!("its source endpoint crosses as the kernel's returned endpoint");
        };
        assert!(
            matches!(
                artifact.arena().computation(applied),
                Some(&gandr_kernel_term::Computation::Application(..))
            ),
            "over the application it erases, not the value it returns"
        );
    }

    #[test]
    fn a_reflexive_transport_at_a_path_motive_is_readmitted()
    {
        // def moved_end : Path(Path(Integer, 0, 0),
        //                      ⟨tr(x. Path(Integer, x, x), here(0), here(0))⟩, here(0))
        //               = here(here(0)) ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let zero = arena.value_literal(integer_literal());
        let here = arena.value_here(zero);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let motive = arena.value_type_path(integer, bound, bound);
        let transport = arena.computation_path_transport(motive, here, here);
        let moved = arena.value_returned(transport);
        let looped = arena.value_type_path(integer, zero, zero);
        let declared = arena.value_type_path(looped, moved, here);
        let here_here = arena.value_here(here);
        let (report, readmission) = judge_and_readmit(&mut arena, &[declaration(
            At(0),
            Maybe::Present(declared),
            Maybe::Present(here_here),
        )]);
        let verdicts: Vec<_> = report.judged().iter().map(Judged::verdict).collect();
        assert!(
            matches!(*verdicts, [Verdict::Checked { .. }]),
            "the checker reduces the reflexive transport: {verdicts:?}"
        );
        let [ref entry] = *readmission.readmitted()
        else {
            panic!("one outcome");
        };
        assert!(
            matches!(*entry.outcome(), Outcome::Defined { .. }),
            "and the kernel re-derives it: {:?}",
            entry.outcome()
        );
    }

    #[test]
    fn a_dependent_pair_and_its_identity_are_readmitted()
    {
        // def ring   : Σ (n : Integer). Path(Integer, n, n) = #{0, here(0)} ;
        // def lap    : U (Π (p : Σ…). F Path(Integer, ⟨p.0⟩, ⟨p.0⟩))
        //            = thunk { \p. split p under F Path(…) as (m, w). return w } ;
        // def second : U (Π (p : Σ…). F Path(Integer, ⟨p.0⟩, ⟨p.0⟩))
        //            = thunk { \p. p.1 } ;
        // def both   : Path(Σ…, #{0, here(0)}, #{0, here(0)})
        //            = #{here(0), here(here(0))} ;
        // def moved  : U (F Integer) = thunk { tr(s. Integer, both, 0) } ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let looped = arena.value_type_path(integer, bound, bound);
        let sigma = arena.value_type_sigma(integer, looped);
        let zero = arena.value_literal(integer_literal());
        let here = arena.value_here(zero);
        let pair = arena.value_tuple(&[zero, here]);
        let projected =
            arena.computation_tuple_projection(bound, gandr_kernel_term::Component::from(0_usize));
        let projected = arena.value_returned(projected);
        let at_first = arena.value_type_path(integer, projected, projected);
        let answer = arena.comp_type_returner(at_first);
        let dependent = arena.comp_type_pi(sigma, answer);
        let suspended = arena.value_type_thunk(dependent);
        let returns_second = arena.computation_return(bound);
        let split = arena.computation_dependent_split(
            bound,
            gandr_core_term::ComponentCount::from(2_usize),
            answer,
            returns_second,
        );
        let split = arena.computation_lambda(split);
        let split = arena.value_thunk(split);
        let second =
            arena.computation_tuple_projection(bound, gandr_kernel_term::Component::from(1_usize));
        let second = arena.computation_lambda(second);
        let second = arena.value_thunk(second);
        let identity = arena.value_type_path(sigma, pair, pair);
        let here_here = arena.value_here(here);
        let paths = arena.value_tuple(&[here, here_here]);
        let both = arena.value_constant(ConstantIndex::from(3_usize));
        let constant = arena.value_type_base(BaseType::Integer);
        let transport = arena.computation_path_transport(constant, both, zero);
        let moved = arena.value_thunk(transport);
        let returns_integer = arena.comp_type_returner(integer);
        let suspended_integer = arena.value_type_thunk(returns_integer);
        let module = [
            declaration(At(0), Maybe::Present(sigma), Maybe::Present(pair)),
            declaration(At(1), Maybe::Present(suspended), Maybe::Present(split)),
            declaration(At(2), Maybe::Present(suspended), Maybe::Present(second)),
            declaration(At(3), Maybe::Present(identity), Maybe::Present(paths)),
            declaration(
                At(4),
                Maybe::Present(suspended_integer),
                Maybe::Present(moved),
            ),
        ];
        let (report, readmission) = judge_and_readmit(&mut arena, &module);
        let verdicts: Vec<_> = report.judged().iter().map(Judged::verdict).collect();
        assert!(
            verdicts
                .iter()
                .all(|verdict| matches!(verdict, Verdict::Checked { .. })),
            "the judgement accepts the pair, the split, the projection, the path and the \
             transport: {verdicts:?}"
        );
        let outcomes: Vec<_> = readmission
            .readmitted()
            .iter()
            .map(|entry| entry.outcome().clone())
            .collect();
        assert!(
            outcomes
                .iter()
                .all(|outcome| matches!(*outcome, Outcome::Defined { .. })),
            "each crosses and the kernel re-derives it: {outcomes:?}"
        );
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let declared = artifact
            .declarations()
            .first()
            .map(|marked| marked.declaration().declared_id())
            .unwrap();
        assert!(
            matches!(
                artifact.arena().value_type(declared),
                Some(&KernelValueType::Sigma { .. })
            ),
            "the dependent pair crosses as the kernel's own former"
        );
    }

    #[test]
    fn a_funext_crosses_as_a_higher_evaluation()
    {
        // def not, not_not, same : U (+{(), ()} -> F +{(), ()}) ;
        // def twice : Path(U (…), not_not, same) = funext(not_not, same) ;
        let mut arena = CoreArena::new();
        let functions = crate::fixture::booleans(&mut arena);
        let [not_not, same] =
            [1_usize, 2_usize].map(|at| arena.value_constant(ConstantIndex::from(at)));
        let path = arena.value_type_path(functions.function, not_not, same);
        let funext = arena.value_funext(not_not, same);
        let declared = Maybe::Present(functions.function);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), declared, Maybe::Present(functions.not)),
            declaration(At(1), declared, Maybe::Present(functions.not_not)),
            declaration(At(2), declared, Maybe::Present(functions.same)),
            declaration(At(3), Maybe::Present(path), Maybe::Present(funext)),
        ]);
        assert!(
            readmission
                .readmitted()
                .iter()
                .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
            "the kernel replays both functions' evaluations at every input: {:?}",
            readmission.readmitted()
        );
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let Some(&DeclarationContent::Def { body, .. }) = artifact
            .declarations()
            .last()
            .map(|marked| marked.declaration().content())
        else {
            panic!("the extensionality is the last definition");
        };
        let Some(KernelValue::HigherEvaluation {
            dialogues,
            components,
        }) = artifact.arena().value(body).cloned()
        else {
            panic!("a funext crosses as the kernel's higher evaluation");
        };
        assert_eq!((dialogues.len(), components.len()), (2, 2));
        assert!(
            dialogues
                .iter()
                .all(|component| !component.left.is_empty() && !component.right.is_empty()),
            "every component carries both functions' traces"
        );
        let arena = artifact.arena();
        let digest = |value| content_digest(arena, AnyNode::Value(value));
        assert!(
            components.iter().enumerate().all(|(summand, component)| {
                digest(component.left) == digest(component.right)
                    && arena
                        .value(component.evidence)
                        .and_then(KernelValue::components)
                        == Some(&[])
                    && matches!(
                        arena.value(component.left),
                        Some(&KernelValue::Injection(found, _)) if usize::from(found) == summand
                    )
            }),
            "each input returns itself on both sides, with the unit as its identity"
        );
    }

    #[test]
    fn a_quantified_funext_crosses_as_a_quantified_evaluation()
    {
        // def at_truth : U ((Bool -> F Bool) -> F Bool) = λh. h(true) ;
        // def bound = λh. x ← h(true); return x ;
        // def twice = λh. x ← h(true); h(x) ;
        // def twice_bound = λh. x ← h(true); y ← h(x); return y ;
        // def eta : Path(U (…), at_truth, bound) = funext(at_truth, bound) ;
        // def nested : Path(U (…), twice, twice_bound) = funext(twice, twice_bound) ;
        /// How one extensionality crossed.
        #[derive(Debug, Eq, PartialEq)]
        enum Crossed
        {
            /// A higher evaluation with this many components.
            Higher(usize),
            /// A quantified evaluation: its children, and per step whether it
            /// applies the premise at index zero.
            Quantified(usize, Vec<bool>),
        }
        let mut arena = CoreArena::new();
        let functions = crate::fixture::booleans(&mut arena);
        let returns = arena.comp_type_returner(functions.ty);
        let arrow = arena.comp_type_arrow(functions.function, returns);
        let higher = arena.value_type_thunk(arrow);
        let unit = arena.value_unit();
        let truth = arena.value_injection(0_usize.into(), unit);
        // Beneath `λh`, `h` is index zero; beneath `λh. x ← …`, `x` is zero and
        // `h` one.
        let [innermost, outer] = [0_u32, 1_u32]
            .map(|index| arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
        let forced = arena.computation_force(innermost);
        let tail = arena.computation_application(forced, truth);
        let lambda = arena.computation_lambda(tail);
        let at_truth = arena.value_thunk(lambda);
        let returned = arena.computation_return(innermost);
        let forced_again = arena.computation_force(outer);
        let again = arena.computation_application(forced_again, innermost);
        let again_bound = arena.computation_bind(again, returned);
        let [bound, twice, twice_bound] = [returned, again, again_bound].map(|rest| {
            let first = arena.computation_bind(tail, rest);
            let lambda = arena.computation_lambda(first);
            arena.value_thunk(lambda)
        });
        let constant_body = arena.computation_return(truth);
        let constant_lambda = arena.computation_lambda(constant_body);
        let constant = arena.value_thunk(constant_lambda);
        let [
            at_truth_constant,
            bound_constant,
            twice_constant,
            twice_bound_constant,
            constant_constant,
        ] = [3_usize, 4, 5, 6, 7].map(|at| arena.value_constant(ConstantIndex::from(at)));
        let eta_path = arena.value_type_path(higher, at_truth_constant, bound_constant);
        let eta = arena.value_funext(at_truth_constant, bound_constant);
        let nested_path = arena.value_type_path(higher, twice_constant, twice_bound_constant);
        let nested = arena.value_funext(twice_constant, twice_bound_constant);
        let unapplied_path = arena.value_type_path(higher, constant_constant, constant_constant);
        let unapplied = arena.value_funext(constant_constant, constant_constant);
        let declared = Maybe::Present(functions.function);
        let applying = Maybe::Present(higher);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), declared, Maybe::Present(functions.not)),
            declaration(At(1), declared, Maybe::Present(functions.not_not)),
            declaration(At(2), declared, Maybe::Present(functions.same)),
            declaration(At(3), applying, Maybe::Present(at_truth)),
            declaration(At(4), applying, Maybe::Present(bound)),
            declaration(At(5), applying, Maybe::Present(twice)),
            declaration(At(6), applying, Maybe::Present(twice_bound)),
            declaration(At(7), applying, Maybe::Present(constant)),
            declaration(At(8), Maybe::Present(eta_path), Maybe::Present(eta)),
            declaration(At(9), Maybe::Present(nested_path), Maybe::Present(nested)),
            declaration(
                At(10),
                Maybe::Present(unapplied_path),
                Maybe::Present(unapplied),
            ),
        ]);
        assert!(
            readmission
                .readmitted()
                .iter()
                .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
            "the kernel replays every step under the quantifier: {:?}",
            readmission.readmitted()
        );
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let crossed: Vec<Crossed> = artifact
            .declarations()
            .iter()
            .skip(8)
            .map(|marked| {
                let DeclarationContent::Def { body, .. } = *marked.declaration().content()
                else {
                    panic!("every extensionality is a definition");
                };
                match artifact.arena().value(body).cloned() {
                    | Some(KernelValue::HigherEvaluation { components, .. }) => {
                        Crossed::Higher(components.len())
                    },
                    | Some(KernelValue::QuantifiedEvaluation { steps, children }) => {
                        Crossed::Quantified(
                            children.len(),
                            steps
                                .iter()
                                .map(|step| matches!(step, gandr_kernel_term::QuantifiedStep::Apply { fibre, .. } if u32::from(*fibre) == 0))
                                .collect(),
                        )
                    },
                    | other => panic!("a funext crosses as an evaluation: {other:?}"),
                }
            })
            .collect();
        assert_eq!(
            crossed,
            Vec::from([
                Crossed::Quantified(8, Vec::from([true, false, false])),
                Crossed::Quantified(
                    18,
                    Vec::from([true, true, false, false, true, false, false])
                ),
                Crossed::Higher(1),
            ]),
            "pre-order steps, two children per application and three per return; a \
             body that never applies its argument crosses as a higher evaluation over \
             the single generic input"
        );
    }

    #[test]
    fn a_reflexivity_crosses_with_the_dialogues_relating_its_endpoints()
    {
        // def k : U (Integer -> F Integer) = thunk { \x. return x } ;
        // def j : U (Integer -> F Integer) = k ;
        // def law : Path(U (…), thunk { force j }, k) = here(k) ;
        // Relating `k` to `thunk { force j }` unfolds `j` under the thunk, a
        // step only the recorded dialogue names.
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns);
        let function = arena.value_type_thunk(arrow);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(bound);
        let lambda = arena.computation_lambda(returned);
        let identity = arena.value_thunk(lambda);
        let [k, j] = [0_usize, 1_usize].map(|at| arena.value_constant(ConstantIndex::from(at)));
        let forced = arena.computation_force(j);
        let delayed = arena.value_thunk(forced);
        let path = arena.value_type_path(function, delayed, k);
        let here = arena.value_here(k);
        let declared = Maybe::Present(function);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), declared, Maybe::Present(identity)),
            declaration(At(1), declared, Maybe::Present(k)),
            declaration(At(2), Maybe::Present(path), Maybe::Present(here)),
        ]);
        assert!(
            readmission
                .readmitted()
                .iter()
                .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
            "the kernel replays the dialogue unfolding `j` under the thunk: {:?}",
            readmission.readmitted()
        );
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let Some(&DeclarationContent::Def { body, .. }) = artifact
            .declarations()
            .last()
            .map(|marked| marked.declaration().content())
        else {
            panic!("the law is the last definition");
        };
        let Some(KernelValue::Here { dialogues, .. }) = artifact.arena().value(body).cloned()
        else {
            panic!("the law crosses as the kernel's reflexivity");
        };
        assert!(
            !dialogues.left.is_empty() && dialogues.right.is_empty(),
            "the delayed endpoint carries its dialogue and the point's own syntax none: \
             {dialogues:?}"
        );
        assert!(
            dialogues
                .left
                .iter()
                .any(|decision| matches!(decision, ConversionDecision::Unfold { .. })),
            "the dialogue names the unfoldings the kernel replays"
        );
    }

    #[test]
    fn an_ascription_crosses_with_the_endpoints_it_related()
    {
        // def k : U (Integer -> F Integer) = thunk { \x. return x } ;
        // def j : U (Integer -> F Integer) = k ;
        // def given : Path(U (…), thunk { force j }, k) = here(k) ;
        // def law : Path(U (…), k, k) = given ;
        // The ascription converts the two path types only through `j`'s body
        // under the thunk, which the kernel's forced reading does not unfold.
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns);
        let function = arena.value_type_thunk(arrow);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(bound);
        let lambda = arena.computation_lambda(returned);
        let identity = arena.value_thunk(lambda);
        let [k, j, given] = [0_usize, 1, 2].map(|at| arena.value_constant(ConstantIndex::from(at)));
        let forced = arena.computation_force(j);
        let delayed = arena.value_thunk(forced);
        let stated = arena.value_type_path(function, delayed, k);
        let diagonal = arena.value_type_path(function, k, k);
        let here = arena.value_here(k);
        let declared = Maybe::Present(function);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), declared, Maybe::Present(identity)),
            declaration(At(1), declared, Maybe::Present(k)),
            declaration(At(2), Maybe::Present(stated), Maybe::Present(here)),
            declaration(At(3), Maybe::Present(diagonal), Maybe::Present(given)),
        ]);
        assert!(
            readmission
                .readmitted()
                .iter()
                .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
            "the kernel replays the ascription's dialogue: {:?}",
            readmission.readmitted()
        );
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let related: Vec<usize> = artifact
            .declarations()
            .iter()
            .map(|marked| marked.declaration().related().len())
            .collect();
        assert_eq!(related, [0, 0, 0, 1], "the law alone carries a pair");
        let mut stripped = artifact.declarations().to_vec();
        if let Some(law) = stripped.last_mut() {
            *law = gandr_kernel_term::MarkedDeclaration::new(
                law.mark(),
                law.declaration().clone().relating(Vec::new()),
            );
        }
        let refusal = gandr_kernel_core::Environment::replay(artifact.arena().clone(), &stripped)
            .expect_err("without its pair the law is the refusal the ascription met before");
        assert_eq!(refusal.position(), ConstantIndex::from(3_usize));
        assert!(matches!(
            refusal.error(),
            &gandr_kernel_core::KernelError::ValueTypeMismatch(_)
        ));
    }

    /// `Flow(Type, ⌜Bool⌝, ⌜Bool⌝)`, `El(x)` and Bool's two constructors, over
    /// [`crate::fixture::booleans`].
    ///
    /// # Specification
    /// trivial.
    fn flows_of_booleans(
        arena: &mut CoreArena,
        boolean: ValueTypeId,
    ) -> (ValueTypeId, ValueTypeId, [ValueId; 2])
    {
        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let code = arena.value_quote(boolean);
        let flow_type = arena.value_type_flow(universe, code, code);
        let decoded = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(decoded, Level::zero());
        let unit = arena.value_unit();
        let constructors = [0_usize, 1].map(|summand| arena.value_injection(summand.into(), unit));
        (flow_type, element, constructors)
    }

    /// Assert that every declaration of `report` checks and the kernel
    /// readmits every one of them as a definition.
    ///
    /// # Specification
    /// trivial.
    fn checks_and_readmits(
        report: &ModuleReport,
        readmission: &Readmission,
    )
    {
        assert!(
            report
                .judged()
                .iter()
                .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
            "every declaration checks: {report:?}"
        );
        assert!(
            readmission
                .readmitted()
                .iter()
                .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
            "the kernel replays every dialogue the checker recorded: {:?}",
            readmission.readmitted()
        );
    }

    #[test]
    fn a_ride_along_a_named_flow_crosses_with_the_flows_unfolding()
    {
        // def not : U (Bool -> F Bool) = \b. case b of { .0 -> .1 ; .1 -> .0 } ;
        // def flip : Flow(Type, Bool, Bool) = forward(not) ;
        // def flipped : Path(Bool, ride(\X. X, flip, .0), .1) = here(.1) ;
        // The ride is stuck on `flip` until `flip` unfolds: a step only the
        // recorded dialogue names.
        let mut arena = CoreArena::new();
        let functions = crate::fixture::booleans(&mut arena);
        let (flow_type, element, [truth, falsity]) = flows_of_booleans(&mut arena, functions.ty);
        let [not, flip] = [0_usize, 1].map(|at| arena.value_constant(ConstantIndex::from(at)));
        let forward = arena.value_forward(not);
        let ride = arena.computation_ride(element, flip, truth);
        let ridden = arena.value_returned(ride);
        let path = arena.value_type_path(functions.ty, ridden, falsity);
        let here = arena.value_here(falsity);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(
                At(0),
                Maybe::Present(functions.function),
                Maybe::Present(functions.not),
            ),
            declaration(At(1), Maybe::Present(flow_type), Maybe::Present(forward)),
            declaration(At(2), Maybe::Present(path), Maybe::Present(here)),
        ]);
        // The checker relates the ride by unfolding `flip`, and the kernel
        // replays that unfolding at the ride's flow.
        checks_and_readmits(&report, &readmission);
    }

    #[test]
    fn a_ride_through_named_translators_crosses_with_their_unfoldings()
    {
        // def not : U (Bool -> F Bool) = \b. case b of { .0 -> .1 ; .1 -> .0 } ;
        // def both : Path(#{Bool, Bool},
        //   ride(\X. X, flowProduct(forward(not), forward(not)), #{.0, .1}),
        //   #{.1, .0}) = here(#{.1, .0}) ;
        // def each : Path(#{Bool, Bool},
        //   ride(\X. #{X, X}, forward(not), #{.0, .1}), #{.1, .0})
        //   = here(#{.1, .0}) ;
        // Each component's translator is the definition `not`, which unfolds
        // only once the components before it have returned.
        let mut arena = CoreArena::new();
        let functions = crate::fixture::booleans(&mut arena);
        let (_, element, [truth, falsity]) = flows_of_booleans(&mut arena, functions.ty);
        let not = arena.value_constant(ConstantIndex::from(0_usize));
        let forward = arena.value_forward(not);
        let paired = arena.value_flow_product(forward, forward);
        let pair = arena.value_type_product(&[functions.ty, functions.ty]);
        let doubled = arena.value_type_product(&[element, element]);
        let source = arena.value_tuple(&[truth, falsity]);
        let target = arena.value_tuple(&[falsity, truth]);
        let [both, each] = [(element, paired), (doubled, forward)].map(|(motive, flow)| {
            let ride = arena.computation_ride(motive, flow, source);
            let ridden = arena.value_returned(ride);
            arena.value_type_path(pair, ridden, target)
        });
        let here = arena.value_here(target);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(
                At(0),
                Maybe::Present(functions.function),
                Maybe::Present(functions.not),
            ),
            declaration(At(1), Maybe::Present(both), Maybe::Present(here)),
            declaration(At(2), Maybe::Present(each), Maybe::Present(here)),
        ]);
        // The checker unfolds `not` under each component's bind, in the order
        // the kernel's reduct binds them.
        checks_and_readmits(&report, &readmission);
    }

    #[test]
    fn an_equiv_crosses_as_a_universe_path()
    {
        // def not : U (+{(), ()} -> F +{(), ()}) ;
        // def negation : Path(Type, +{(), ()}, +{(), ()}) = equiv(not, not) ;
        let mut arena = CoreArena::new();
        let functions = crate::fixture::booleans(&mut arena);
        let not = arena.value_constant(ConstantIndex::from(0_usize));
        let universe = arena.value_type_universe(
            gandr_core_term::Sort::Ground(GroundSort::Value),
            Level::zero(),
        );
        let code = arena.value_quote(functions.ty);
        let path = arena.value_type_path(universe, code, code);
        let equiv = arena.value_equiv(not, not);
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            declaration(
                At(0),
                Maybe::Present(functions.function),
                Maybe::Present(functions.not),
            ),
            declaration(At(1), Maybe::Present(path), Maybe::Present(equiv)),
        ]);
        assert!(
            readmission
                .readmitted()
                .iter()
                .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
            "the kernel replays both round trips under the admitted negation: {:?}",
            readmission.readmitted()
        );
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let Some(&DeclarationContent::Def { body, .. }) = artifact
            .declarations()
            .last()
            .map(|marked| marked.declaration().content())
        else {
            panic!("the equivalence is the last definition");
        };
        let arena = artifact.arena();
        let Some(KernelValue::PathEquiv {
            path_type,
            ref evidence,
            ..
        }) = arena.value(body).cloned()
        else {
            panic!("an equiv crosses as the kernel's native universe path");
        };
        assert!(
            matches!(
                arena.value_type(path_type),
                Some(&KernelValueType::PathUniverse(source, target))
                    if content_digest(arena, AnyNode::Value(source)) == content_digest(arena, AnyNode::Value(target))
            ),
            "its classifier relates the quote of Bool to itself"
        );
        assert_eq!(
            (evidence.source.len(), evidence.target.len()),
            (2, 2),
            "one round trip per injection of each side's coverage"
        );
        assert!(
            evidence
                .source
                .iter()
                .chain(&evidence.target)
                .all(|dialogue| dialogue
                    .iter()
                    .any(|decision| matches!(decision, ConversionDecision::Unfold { .. }))),
            "every round trip unfolds the admitted negation"
        );
    }

    #[test]
    fn marks_and_holes_are_refused_beside_their_positive_controls()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let sum = arena.value_type_sum(&[integer, integer]);
        let zero = arena.value_literal(integer_literal());
        let injection = arena.value_injection(Side::Left.into(), zero);
        let text = arena.value_literal(text_literal());
        let mismatched = arena.value_constant(ConstantIndex::from(5_usize));
        let module = [
            declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
            declaration(At(1), Maybe::Present(sum), Maybe::Present(injection)),
            declaration(At(2), Maybe::Present(integer), HOLE),
            declaration(At(3), Maybe::Present(sum), HOLE),
            declaration(At(4), UNSIGNED, HOLE),
            declaration(At(5), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(6), Maybe::Present(integer), Maybe::Present(mismatched)),
        ];
        let (report, readmission) = judge_and_readmit(&mut arena, &module);
        let [
            ref control,
            ref sum_body,
            ref owed,
            ref sum_hole,
            ref hole,
            ref mismatched_entry,
            ref dependent,
        ] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        assert!(matches!(*control.outcome(), Outcome::Defined { .. }));
        assert!(
            matches!(*sum_body.outcome(), Outcome::Defined { .. }),
            "a checked sum injection crosses as a definition"
        );
        assert!(matches!(*owed.outcome(), Outcome::Assumed { .. }));
        assert!(
            matches!(*sum_hole.outcome(), Outcome::Assumed { .. }),
            "a hole with a formed sum signature crosses as an axiom"
        );
        assert_eq!(
            hole.outcome(),
            &Outcome::Marked(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Hole(ConstantIndex::from(4_usize)),
            }),
            "an unsigned hole remains refused"
        );
        assert!(
            matches!(
                *mismatched_entry.outcome(),
                Outcome::Marked(CheckRefusal::TypeMismatch(Mismatch::Value { .. }))
            ),
            "an ill-typed body remains marked"
        );
        assert!(matches!(
            report.judged()[6].verdict(),
            Verdict::Checked { .. }
        ));
        assert_eq!(
            dependent.outcome(),
            &Outcome::Refused(Refusal::Withheld {
                at: mismatched,
                constant: ConstantIndex::from(5_usize),
            }),
            "a checked reference to a marked declaration is withheld"
        );
        assert_eq!(
            [
                crossed_at(&readmission, At(0)),
                crossed_at(&readmission, At(1)),
                crossed_at(&readmission, At(2)),
                crossed_at(&readmission, At(3)),
            ],
            [
                ConstantIndex::from(0_usize),
                ConstantIndex::from(1_usize),
                ConstantIndex::from(2_usize),
                ConstantIndex::from(3_usize),
            ],
            "both checked definitions and both formed holes enter in declaration order"
        );
        assert_eq!(
            readmission.audit().axioms(),
            [ConstantIndex::from(2_usize), ConstantIndex::from(3_usize)],
            "only the two signed holes are axioms"
        );
    }

    #[test]
    fn a_hole_is_refused_where_it_stands_and_its_filling_is_admitted()
    {
        use gandr_core_term::fill_hole;
        use gandr_core_term::hole::HoleId;
        use gandr_core_term::hole::MarkIndex;
        use gandr_core_term::hole::TermId;

        // def holed  : Integer × Integer = (?h, 0) ;
        // def filled : Integer × Integer = (0, 0) ;   the same, ?h := 0
        // def kept   : Integer = mark 0 ;            a mark around a good body
        // def hidden : Integer = mark "" ;           a mark around a bad body
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let product = arena.value_type_product(&[integer, integer]);
        let zero = arena.value_literal(integer_literal());
        let text = arena.value_literal(text_literal());
        let hole = HoleId::from(0_u32);
        let standing = arena.value_hole(hole);
        let holed = arena.value_tuple(&[standing, zero]);
        let TermId::Value(filled) =
            fill_hole(&mut arena, TermId::Value(holed), hole, TermId::Value(zero))
        else {
            panic!("a value fills to a value");
        };
        let kept = arena.value_mark(MarkIndex::from(0_u32), zero);
        let hidden = arena.value_mark(MarkIndex::from(1_u32), text);
        let module = [
            declaration(At(0), Maybe::Present(product), Maybe::Present(holed)),
            declaration(At(1), Maybe::Present(product), Maybe::Present(filled)),
            declaration(At(2), Maybe::Present(integer), Maybe::Present(kept)),
            declaration(At(3), Maybe::Present(integer), Maybe::Present(hidden)),
        ];
        let (report, readmission) = judge_and_readmit(&mut arena, &module);
        assert!(
            report
                .judged()
                .iter()
                .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
            "the judgement accepts all four: a hole and a mark check against any type"
        );
        let [
            ref holed_entry,
            ref filled_entry,
            ref kept_entry,
            ref hidden_entry,
        ] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        let refusal = Refusal::Hole {
            at: CoreNode::Term(TermNode::Value(standing)),
            hole,
        };
        assert_eq!(
            holed_entry.outcome(),
            &Outcome::Refused(refusal),
            "the kernel is never offered a hole; the refusal names it where it stands"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::UserAbsence,
            "an unfilled hole is the author's absence"
        );
        assert!(
            matches!(*filled_entry.outcome(), Outcome::Defined { .. }),
            "the same declaration with the hole filled is admitted"
        );
        assert!(
            matches!(*kept_entry.outcome(), Outcome::Defined { .. }),
            "a mark is erased to its body, which the kernel re-derives"
        );
        assert!(
            matches!(*hidden_entry.outcome(), Outcome::Rejected(_)),
            "a mark never makes the kernel accept the body it wraps"
        );
        assert_eq!(
            readmission.audit().axioms(),
            [],
            "a refused hole is no axiom"
        );
    }

    #[test]
    fn an_empty_ledger_readmits_an_artifact_resting_on_no_axiom()
    {
        // An unsupported signed hole is marked, never entered as an axiom.
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unformed = arena.value_type_base(BaseType::Numeric);
        let zero = arena.value_literal(integer_literal());
        let answer = arena.value_constant(ConstantIndex::from(0_usize));
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
            declaration(At(1), UNSIGNED, Maybe::Present(answer)),
            declaration(At(2), Maybe::Present(unformed), HOLE),
        ]);
        assert!(
            report.ledger().entries().is_empty(),
            "the module owes nothing"
        );
        assert!(
            readmission.audit().axioms().is_empty()
                && readmission.audit().unchecked_admissions().is_empty(),
            "an artifact owing nothing rests on no axiom"
        );
        assert_eq!(
            (
                crossed_at(&readmission, At(0)),
                crossed_at(&readmission, At(1))
            ),
            (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)),
            "the definitions crossed, the signed one and the synthesised one"
        );
    }

    #[test]
    fn each_owed_hole_is_an_axiom_of_the_artifact()
    {
        // def first : Integer ; def uses : Integer = first ; def second : String ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let first = arena.value_constant(ConstantIndex::from(0_usize));
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(integer), HOLE),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(first)),
            declaration(At(2), Maybe::Present(string), HOLE),
        ]);
        let owed: Vec<_> = report
            .ledger()
            .entries()
            .iter()
            .map(|entry| entry.absence().origin())
            .collect();
        assert_eq!(
            owed,
            [origin(At(0)), origin(At(2))],
            "the module owes two holes"
        );
        let audits: Vec<_> = readmission
            .readmitted()
            .iter()
            .map(|entry| match *entry.outcome() {
                | Outcome::Defined { ref audit, .. }
                | Outcome::Assumed { ref audit, .. }
                | Outcome::Data { ref audit, .. } => audit.axioms().to_vec(),
                | Outcome::Marked(_)
                | Outcome::Static
                | Outcome::Refused(_)
                | Outcome::Rejected(_) => {
                    panic!("every declaration crosses")
                },
            })
            .collect();
        assert_eq!(
            audits,
            [
                Vec::from([ConstantIndex::from(0_usize)]),
                Vec::from([ConstantIndex::from(0_usize)]),
                Vec::from([ConstantIndex::from(2_usize)]),
            ],
            "an axiom's audit names itself, and a definition's names the axiom it reads"
        );
        assert!(
            matches!(
                (
                    readmission.readmitted()[0].outcome(),
                    readmission.readmitted()[2].outcome()
                ),
                (&Outcome::Assumed { .. }, &Outcome::Assumed { .. })
            ),
            "each owed hole crossed as an axiom"
        );
        assert_eq!(
            readmission.audit().axioms(),
            [ConstantIndex::from(0_usize), ConstantIndex::from(2_usize)],
            "the artifact rests on one axiom per ledger entry, in ledger order"
        );
    }

    #[test]
    fn a_refused_declaration_leaves_the_environment_unchanged()
    {
        // def id : U (Integer → F Integer) = thunk { λx. return x } ;
        // def bad : Integer = "" ;
        // def applied : U (F Integer) = thunk { (force id) bad } ;
        // def last : Integer = 0 ;
        //
        // `applied` erases its type and the head of its application before it
        // meets the withheld reference.
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let function = arena.value_type_thunk(arrow);
        let suspended = arena.value_type_thunk(returns_integer);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(bound);
        let lambda = arena.computation_lambda(returned);
        let identity = arena.value_thunk(lambda);
        let text = arena.value_literal(text_literal());
        let zero = arena.value_literal(integer_literal());
        let id = arena.value_constant(ConstantIndex::from(0_usize));
        let bad = arena.value_constant(ConstantIndex::from(1_usize));
        let head = arena.computation_force(id);
        let application = arena.computation_application(head, bad);
        let applied = arena.value_thunk(application);
        let crossing = [
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(3), Maybe::Present(integer), Maybe::Present(zero)),
        ];
        let (_, control) = judge_and_readmit(&mut arena, &crossing);
        let [first, last] = crossing;
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            first,
            declaration(At(1), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(2), Maybe::Present(suspended), Maybe::Present(applied)),
            last,
        ]);
        assert_eq!(
            readmission.readmitted()[2].outcome(),
            &Outcome::Refused(Refusal::Withheld {
                at: bad,
                constant: ConstantIndex::from(1_usize),
            }),
            "the application's argument is withheld"
        );
        assert_eq!(
            readmission.environment().arena().watermark(),
            control.environment().arena().watermark(),
            "the refused declaration left no node in the kernel arena"
        );
        assert_eq!(
            crossed_at(&readmission, At(3)),
            ConstantIndex::from(1_usize),
            "the next declaration takes the next kernel position"
        );
    }

    #[test]
    fn a_shared_subterm_is_erased_once()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_literal(integer_literal());
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(bound);
        let inner = arena.computation_lambda(returned);
        let head = arena.computation_lambda(inner);
        let first = arena.computation_application(head, zero);
        let second = arena.computation_application(first, zero);
        let (target, image) = erase(&mut arena, CoreNode::Term(TermNode::Computation(second)));
        let Ok(AnyNode::Computation(image)) = image
        else {
            panic!("an application erases to a computation");
        };
        let Some(&gandr_kernel_term::Computation::Application(first, outer_argument)) =
            target.computation(image)
        else {
            panic!("the image is an application");
        };
        let Some(&gandr_kernel_term::Computation::Application(_, inner_argument)) =
            target.computation(first)
        else {
            panic!("its head is an application");
        };
        assert_eq!(
            outer_argument, inner_argument,
            "the literal both applications share is one kernel node"
        );
    }

    #[test]
    fn the_machine_faults_are_refused_exactly()
    {
        let mut arena = CoreArena::new();
        let linear = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
        assert_eq!(
            erase(&mut arena, CoreNode::Term(TermNode::Value(linear))).1,
            Err(Refusal::Session {
                at: CoreNode::Term(TermNode::Value(linear)),
            }),
            "a linear variable has no kernel zone to count in"
        );
        let dangling = CoreNode::Term(TermNode::Value(dangling_value()));
        assert_eq!(
            erase(&mut arena, dangling).1,
            Err(Refusal::DanglingNode { node: dangling }),
            "a dangling term is refused, not read"
        );
        let dangling = CoreNode::Type(TypeNode::Value(dangling_value_type()));
        assert_eq!(
            erase(&mut arena, dangling).1,
            Err(Refusal::DanglingNode { node: dangling }),
            "a dangling type is refused through the view"
        );
        // A thunk of a computation id this arena has not minted yet, then that
        // computation as the force of the thunk: each is the other's child.
        let mut cyclic = CoreArena::new();
        let mut scratch = CoreArena::new();
        let scratch_unit = scratch.value_unit();
        let ahead = scratch.computation_return(scratch_unit);
        let thunk = cyclic.value_thunk(ahead);
        let force = cyclic.computation_force(thunk);
        assert_eq!(force, ahead, "the force takes the id the thunk names");
        let node = CoreNode::Term(TermNode::Value(thunk));
        assert_eq!(
            erase(&mut cyclic, node).1,
            Err(Refusal::Cyclic { node }),
            "a node that is its own descendant is refused, not erased forever"
        );
        let positions = Positions::default();
        let lifts = alloc::collections::BTreeMap::new();
        let definitions = alloc::collections::BTreeMap::new();
        let mut target = TermArena::new();
        let unit = target.value_unit();
        let returned = arena.computation_return(linear);
        let source = Source {
            lifts: &lifts,
            funexts: &BTreeMap::new(),
            equivalences: &BTreeMap::new(),
            flows: &BTreeMap::new(),
            directed: &BTreeMap::new(),
            reflexivities: &BTreeMap::new(),
            relations: &BTreeMap::new(),
            natives: &BTreeMap::new(),
            definitions: &definitions,
        };
        assert_eq!(
            Erasure::new(&mut arena, source, &positions, ConstantIndex::from(0_usize)).resume(
                &mut target,
                Frame::Lambda { at: returned },
                AnyNode::Value(unit),
            ),
            Err(Refusal::MachineInvariant),
            "a frame handed an image of another family reports the miscount"
        );
    }

    #[test]
    fn replay_decisions_preserve_shape_and_position_precedence()
    {
        use gandr_core_nbe::TraceNode;
        use gandr_kernel_conversion_trace::ConversionDecision;
        use gandr_kernel_conversion_trace::ConversionSide;
        use gandr_kernel_conversion_trace::SubgoalPosition;
        use gandr_kernel_core::ReplayNode;

        let crossed = ConstantIndex::from(0_usize);
        let static_only = ConstantIndex::from(1_usize);
        let missing = ConstantIndex::from(2_usize);
        let admitted = ConstantIndex::from(7_usize);
        let operator = ConstantIndex::from(9_usize);
        let mut positions = Positions::default();
        positions.admitted.insert(crossed, admitted);
        let operators = BTreeMap::from([
            (Unfolded::Definition(crossed), ConstantIndex::from(11_usize)),
            (Unfolded::Definition(static_only), operator),
        ]);
        assert_eq!(
            positions.kernel_decision(&operators, ConversionDecision::Decompose),
            ConversionDecision::Decompose
        );
        let mut arena = gandr_core_nbe::DomainArena::new();
        let unit = arena.value_unit(gandr_core_nbe::TermFace::Reduced);
        let returned = arena.comp_return(unit, gandr_core_nbe::CompTermFace::Reduced);
        let nodes = [
            (TraceNode::Constant(crossed), ReplayNode::Constant(admitted)),
            (
                TraceNode::Constant(static_only),
                ReplayNode::Constant(operator),
            ),
            (TraceNode::Constant(missing), ReplayNode::Other),
            (TraceNode::Value(unit), ReplayNode::Other),
            (TraceNode::Computation(returned), ReplayNode::Other),
        ];
        for (source, image) in nodes {
            let decisions = [
                (
                    ConversionDecision::ReduceLeft { redex: source },
                    ConversionDecision::ReduceLeft { redex: image },
                ),
                (
                    ConversionDecision::ReduceRight { redex: source },
                    ConversionDecision::ReduceRight { redex: image },
                ),
                (
                    ConversionDecision::ConstShortcut { constant: source },
                    ConversionDecision::ConstShortcut { constant: image },
                ),
                (
                    ConversionDecision::Unfold { constant: source },
                    ConversionDecision::Unfold { constant: image },
                ),
                (
                    ConversionDecision::Postpone { constant: source },
                    ConversionDecision::Postpone { constant: image },
                ),
                (
                    ConversionDecision::Freeze {
                        constant: source,
                        side: ConversionSide::Right,
                    },
                    ConversionDecision::Freeze {
                        constant: image,
                        side: ConversionSide::Right,
                    },
                ),
                (
                    ConversionDecision::EtaExpand {
                        side: ConversionSide::Left,
                        variable: source,
                    },
                    ConversionDecision::EtaExpand {
                        side: ConversionSide::Left,
                        variable: image,
                    },
                ),
                (
                    ConversionDecision::Force { thunk: source },
                    ConversionDecision::Force { thunk: image },
                ),
                (
                    ConversionDecision::ComparedShared {
                        left: source,
                        right: TraceNode::Constant(missing),
                    },
                    ConversionDecision::ComparedShared {
                        left: image,
                        right: ReplayNode::Other,
                    },
                ),
            ];
            for (decision, expected) in decisions {
                assert_eq!(positions.kernel_decision(&operators, decision), expected);
            }
        }
        let position = SubgoalPosition::from(3_u32);
        assert_eq!(
            positions.kernel_decision(&operators, ConversionDecision::NegativeSubgoal { position }),
            ConversionDecision::NegativeSubgoal { position }
        );
    }

    #[test]
    fn every_recursive_node_family_refuses_a_back_edge()
    {
        let mut foreign = CoreArena::new();
        let foreign_unit = foreign.value_unit();
        let comp_ahead = foreign.computation_return(foreign_unit);
        let type_ahead = foreign.value_type_unit();
        let mut arena = CoreArena::new();
        let thunk = arena.value_thunk(comp_ahead);
        let force = arena.computation_force(thunk);
        let returner = arena.comp_type_returner(type_ahead);
        let suspended = arena.value_type_thunk(returner);
        assert_eq!(force, comp_ahead);
        assert_eq!(suspended, type_ahead);
        for root in [
            CoreNode::Term(TermNode::Value(thunk)),
            CoreNode::Term(TermNode::Computation(force)),
            CoreNode::Type(TypeNode::Value(suspended)),
            CoreNode::Type(TypeNode::Computation(returner)),
        ] {
            assert_eq!(
                erase(&mut arena, root).1,
                Err(Refusal::Cyclic { node: root })
            );
        }
    }

    /// The small value universe `Type`.
    ///
    /// # Specification
    /// trivial.
    fn small(arena: &mut CoreArena) -> ValueTypeId
    {
        arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero())
    }

    /// `\X. El X * El X`, an operator of one parameter over small codes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one static lambda quoting a product of two decodes of its
    ///   bound variable, at de Bruijn zero and level zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one operator at two atom-code instances exposes two
    ///   distinct normalized product bodies and replayed certificates; wrong
    ///   binder index, level or product operand changes these observations.
    /// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
    #[spec(ensures: |ret| {
        let Some(&gandr_core_term::Value::StaticLambda(body)) = arena.value(ret) else { return false; };
        let Some(&gandr_core_term::Value::Quote(product)) = arena.value(body) else { return false; };
        let Some(held) = arena.value_type(product) else { return false; };
        let ValueType::Product(ref parts) = *held else { return false; };
        let [first, second] = **parts else { return false; };
        first == second && matches!(arena.value_type(first), Some(ValueType::Element { code, target })
            if bool::from(target.is_zero()) && matches!(arena.value(*code), Some(gandr_core_term::Value::Variable { zone: Zone::Intuitionistic, index }) if *index == DeBruijnIndex::from(0_u32)))
    })]
    fn pair_operator(arena: &mut CoreArena) -> ValueId
    {
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = arena.value_type_element(bound, Level::zero());
        let product = arena.value_type_product(&[decoded, decoded]);
        let code = arena.value_quote(product);
        arena.value_static_lambda(code)
    }

    /// The content digest of each exported definition's body, in export
    /// order.
    ///
    /// # Specification
    /// - requires: the readmission is a valid export.
    /// - ensures: one canonical content digest per defined body, in export
    ///   order; axioms and refused declarations contribute none.
    /// - panics: the export cannot be decoded.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two instances of one static operator expose exact
    ///   expected normalized body digests; hashing a signature, dropping a body
    ///   or retaining an unreduced application changes those comparisons.
    /// - witness: `bridge::tests::one_static_definition_at_two_instances_records_two_certificates`
    #[spec(ensures: |ret| ret.len() == readmission.admitted.iter().filter(|declaration| matches!(declaration.content(), DeclarationContent::Def { .. })).count())]
    fn exported_bodies(readmission: &Readmission) -> Vec<ContentDigest>
    {
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        artifact
            .declarations()
            .iter()
            .filter_map(|marked| match *marked.declaration().content() {
                | DeclarationContent::Def { body, .. } => {
                    Some(content_digest(artifact.arena(), AnyNode::Value(body)))
                },
                | DeclarationContent::Data { .. }
                | DeclarationContent::Axiom { .. }
                | DeclarationContent::AbstractType { .. } => None,
            })
            .collect()
    }

    #[test]
    fn a_step_fault_keeps_only_a_dangling_node()
    {
        let node = CoreNode::Term(TermNode::Value(dangling_value()));
        assert_eq!(
            fault(CheckRefusal::DanglingNode { node }),
            Refusal::DanglingNode { node },
            "a dangling node stays one, at the same node"
        );
        for refusal in [
            CheckRefusal::Undecided {
                at: dangling_value(),
            },
            CheckRefusal::BudgetExceeded {
                budget: CheckBudget::DEFAULT,
            },
        ] {
            assert_eq!(
                fault(refusal),
                Refusal::MachineInvariant,
                "a step over a judged arena meets no other fault"
            );
        }
    }

    #[test]
    fn family_applied_at_wrong_arity_raises_the_exact_variant()
    {
        // def Pair : Type -> Type = \X. El X * El X ;
        // def Num : Type = Integer ;
        // def over : Type = Pair Integer Integer ;
        // def nullary : Type = Num Integer ;
        // def control : Type = Pair Integer ;
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let operator_type = arena.value_type_static_pi(small, small);
        let operator = pair_operator(&mut arena);
        let integer = arena.value_type_base(BaseType::Integer);
        let integer_code = arena.value_quote(integer);
        let pair = arena.value_constant(ConstantIndex::from(0_usize));
        let num = arena.value_constant(ConstantIndex::from(1_usize));
        let control = arena.value_static_application(pair, integer_code);
        let over = arena.value_static_application(control, integer_code);
        let nullary = arena.value_static_application(num, integer_code);
        let (report, _) = judge_and_readmit(&mut arena, &[
            declaration(
                At(0),
                Maybe::Present(operator_type),
                Maybe::Present(operator),
            ),
            declaration(At(1), Maybe::Present(small), Maybe::Present(integer_code)),
            declaration(At(2), Maybe::Present(small), Maybe::Present(over)),
            declaration(At(3), Maybe::Present(small), Maybe::Present(nullary)),
            declaration(At(4), Maybe::Present(small), Maybe::Present(control)),
        ]);
        let arity = |count: u32| StaticArity::from(count);
        assert_eq!(
            report.judged()[2].verdict(),
            Verdict::Refused(CheckRefusal::FamilyArity {
                at: over,
                expected: arity(1),
                actual: arity(2),
            }),
            "an operator of one parameter at two arguments names both counts, at the whole \
             application"
        );
        assert_eq!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::FamilyArity {
                at: nullary,
                expected: arity(0),
                actual: arity(1),
            }),
            "a code that is no operator takes no argument"
        );
        assert!(
            matches!(report.judged()[4].verdict(), Verdict::Checked { .. }),
            "the saturated instance checks: {:?}",
            report.judged()[4].verdict()
        );
    }

    #[test]
    fn family_argument_at_wrong_classifier_raises_the_exact_variant()
    {
        // def Both : Type -> Type -> Type = \A. \B. El A * El B ;
        // def literal : Type = Both Integer 0 ;
        // def negative : Type = Both (F Integer) Integer ;
        // def control : Type = Both Integer String ;
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let inner_type = arena.value_type_static_pi(small, small);
        let operator_type = arena.value_type_static_pi(small, inner_type);
        let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let inner = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let first = arena.value_type_element(outer, Level::zero());
        let second = arena.value_type_element(inner, Level::zero());
        let product = arena.value_type_product(&[first, second]);
        let code = arena.value_quote(product);
        let inner_lambda = arena.value_static_lambda(code);
        let operator = arena.value_static_lambda(inner_lambda);
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let integer_code = arena.value_quote(integer);
        let string_code = arena.value_quote(string);
        let returns = arena.comp_type_returner(integer);
        let action_code = arena.value_quote_computation(returns);
        let zero = arena.value_literal(integer_literal());
        let both = arena.value_constant(ConstantIndex::from(0_usize));
        let at_integer = arena.value_static_application(both, integer_code);
        let literal = arena.value_static_application(at_integer, zero);
        let at_action = arena.value_static_application(both, action_code);
        let negative = arena.value_static_application(at_action, integer_code);
        let control = arena.value_static_application(at_integer, string_code);
        let (report, _) = judge_and_readmit(&mut arena, &[
            declaration(
                At(0),
                Maybe::Present(operator_type),
                Maybe::Present(operator),
            ),
            declaration(At(1), Maybe::Present(small), Maybe::Present(literal)),
            declaration(At(2), Maybe::Present(small), Maybe::Present(negative)),
            declaration(At(3), Maybe::Present(small), Maybe::Present(control)),
        ]);
        let refused = |position: usize| match report.judged()[position].verdict() {
            | Verdict::Refused(CheckRefusal::FamilyArgumentClassifier {
                at,
                position,
                synthesised,
                expected,
            }) => (
                at,
                u32::from(position),
                arena.value_type(synthesised).cloned(),
                expected,
            ),
            | verdict => panic!("refused at the argument's classifier: {verdict:?}"),
        };
        assert_eq!(
            refused(1),
            (zero, 1_u32, Some(ValueType::Base(BaseType::Integer)), small),
            "a value where a code stands names the argument, its position from the head, and \
             both classifiers"
        );
        assert_eq!(
            refused(2),
            (
                action_code,
                0_u32,
                Some(ValueType::Universe {
                    sort: Sort::Ground(GroundSort::Computation),
                    level: Level::zero(),
                }),
                small
            ),
            "a code of the other sort names the universe it synthesised, sort and level"
        );
        assert!(
            matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
            "both arguments at their classifiers check: {:?}",
            report.judged()[3].verdict()
        );
    }

    #[test]
    fn a_static_pi_over_a_type_that_classifies_no_codes_is_refused_by_name()
    {
        // def from : Integer -> Type ;
        // def into : Type -> Integer ;
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let integer = arena.value_type_base(BaseType::Integer);
        let from = arena.value_type_static_pi(integer, small);
        let into = arena.value_type_static_pi(small, integer);
        let (report, _) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(from), HOLE),
            declaration(At(1), Maybe::Present(into), HOLE),
        ]);
        let verdicts: Vec<Verdict> = report.judged().iter().map(Judged::verdict).collect();
        assert_eq!(
            verdicts,
            [
                Verdict::Refused(CheckRefusal::StaticClassifierExpected {
                    at: from,
                    found: integer,
                }),
                Verdict::Refused(CheckRefusal::StaticClassifierExpected {
                    at: into,
                    found: integer,
                }),
            ],
            "a domain and a codomain that classify no codes are each named"
        );
    }

    #[test]
    fn a_static_lambda_at_a_static_parameter_normalizes_away()
    {
        // def Apply : (Type -> Type) -> Type -> Type = \F. \X. F X ;
        // def applied : Type = Apply (\Y. El Y * El Y) Integer ;
        // def written : Type = Integer * Integer ;
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let operator_type = arena.value_type_static_pi(small, small);
        let tail = arena.value_type_static_pi(small, small);
        let apply_type = arena.value_type_static_pi(operator_type, tail);
        let function = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let applied_variable = arena.value_static_application(function, argument);
        let inner = arena.value_static_lambda(applied_variable);
        let apply = arena.value_static_lambda(inner);
        let operator = pair_operator(&mut arena);
        let integer = arena.value_type_base(BaseType::Integer);
        let integer_code = arena.value_quote(integer);
        let head = arena.value_constant(ConstantIndex::from(0_usize));
        let partial = arena.value_static_application(head, operator);
        let applied = arena.value_static_application(partial, integer_code);
        let product = arena.value_type_product(&[integer, integer]);
        let written = arena.value_quote(product);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(apply_type), Maybe::Present(apply)),
            declaration(At(1), Maybe::Present(small), Maybe::Present(applied)),
            declaration(At(2), Maybe::Present(small), Maybe::Present(written)),
        ]);
        for judged in report.judged() {
            assert!(
                matches!(judged.verdict(), Verdict::Checked { .. }),
                "the lambda checks at the static parameter: {:?}",
                judged.verdict()
            );
        }
        assert_eq!(
            readmission.readmitted()[0].outcome(),
            &Outcome::Static,
            "the operator stays on the checker's side"
        );
        assert!(
            matches!(steps(&readmission.readmitted()[1]).as_slice(), [
                (Unfolded::Definition(position), KernelVerdict::Convertible),
                (Unfolded::Abstraction(_), KernelVerdict::Convertible),
            ] if *position == ConstantIndex::from(0_usize)),
            "the definition unfolds, then the lambda it was handed, each certified: {:?}",
            steps(&readmission.readmitted()[1])
        );
        let bodies = exported_bodies(&readmission);
        assert_eq!(
            bodies.len(),
            2_usize,
            "the instance and the written type cross, the operator does not"
        );
        assert_eq!(
            bodies.first(),
            bodies.last(),
            "the instance crosses as the static normal form, the lambda gone"
        );
    }

    #[test]
    fn a_static_lambda_at_a_dynamic_parameter_is_refused_by_name()
    {
        // def use : U ((F : Type -> Type) -> F Unit) ;
        // def Pair : Type -> Type = \X. El X * El X ;
        // def G : Type -> Type ;
        // def lambda : U (F Unit) = thunk ((force use) (\X. X)) ;
        // def named : U (F Unit) = thunk ((force use) Pair) ;
        // def rigid : U (F Unit) = thunk ((force use) G) ;
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let operator_type = arena.value_type_static_pi(small, small);
        let unit_type = arena.value_type_unit();
        let returns_unit = arena.comp_type_returner(unit_type);
        let takes_operator = arena.comp_type_pi(operator_type, returns_unit);
        let use_type = arena.value_type_thunk(takes_operator);
        let suspended = arena.value_type_thunk(returns_unit);
        let operator = pair_operator(&mut arena);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let identity = arena.value_static_lambda(bound);
        let used = arena.value_constant(ConstantIndex::from(0_usize));
        let pair = arena.value_constant(ConstantIndex::from(1_usize));
        let opaque = arena.value_constant(ConstantIndex::from(2_usize));
        let forced = arena.computation_force(used);
        let mut thunk_of = |argument: ValueId| {
            let applied = arena.computation_application(forced, argument);
            arena.value_thunk(applied)
        };
        let lambda = thunk_of(identity);
        let named = thunk_of(pair);
        let rigid = thunk_of(opaque);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(use_type), HOLE),
            declaration(
                At(1),
                Maybe::Present(operator_type),
                Maybe::Present(operator),
            ),
            declaration(At(2), Maybe::Present(operator_type), HOLE),
            declaration(At(3), Maybe::Present(suspended), Maybe::Present(lambda)),
            declaration(At(4), Maybe::Present(suspended), Maybe::Present(named)),
            declaration(At(5), Maybe::Present(suspended), Maybe::Present(rigid)),
        ]);
        assert_eq!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::StaticLambdaArgument { at: identity }),
            "a static lambda handed to a dynamic parameter is refused at the lambda"
        );
        assert_eq!(
            report.judged()[4].verdict(),
            Verdict::Refused(CheckRefusal::StaticLambdaArgument { at: pair }),
            "so is a static definition that unfolds to one"
        );
        assert!(
            matches!(report.judged()[5].verdict(), Verdict::Checked { .. }),
            "an opaque operator is a value the kernel types: {:?}",
            report.judged()[5].verdict()
        );
        assert!(
            matches!(
                *readmission.readmitted()[5].outcome(),
                Outcome::Defined { .. }
            ),
            "and the kernel admits it: {:?}",
            readmission.readmitted()[5].outcome()
        );
    }

    #[test]
    fn one_static_definition_at_two_instances_records_two_certificates()
    {
        // def Pair : Type -> Type = \X. El X * El X ;
        // def both : Type = El (Pair Integer) * El (Pair String) ;
        // def twice : Type = El (Pair Integer) * El (Pair Integer) ;
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let operator_type = arena.value_type_static_pi(small, small);
        let operator = pair_operator(&mut arena);
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let integer_code = arena.value_quote(integer);
        let again = arena.value_quote(integer);
        let string_code = arena.value_quote(string);
        let pair = arena.value_constant(ConstantIndex::from(0_usize));
        let at_integer = arena.value_static_application(pair, integer_code);
        let at_string = arena.value_static_application(pair, string_code);
        let at_again = arena.value_static_application(pair, again);
        let first = arena.value_type_element(at_integer, Level::zero());
        let second = arena.value_type_element(at_string, Level::zero());
        let repeated = arena.value_type_element(at_again, Level::zero());
        let both = arena.value_type_product(&[first, second]);
        let twice = arena.value_type_product(&[first, repeated]);
        let both_code = arena.value_quote(both);
        let twice_code = arena.value_quote(twice);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(
                At(0),
                Maybe::Present(operator_type),
                Maybe::Present(operator),
            ),
            declaration(At(1), Maybe::Present(small), Maybe::Present(both_code)),
            declaration(At(2), Maybe::Present(small), Maybe::Present(twice_code)),
        ]);
        for judged in report.judged() {
            assert!(
                matches!(judged.verdict(), Verdict::Checked { .. }),
                "every declaration checks: {:?}",
                judged.verdict()
            );
        }
        let [ref operator_entry, ref both_entry, ref twice_entry] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        assert_eq!(
            operator_entry.outcome(),
            &Outcome::Static,
            "the operator itself crosses as nothing"
        );
        assert_eq!(
            steps(both_entry),
            [convertible(At(0)), convertible(At(0))],
            "two instances of one definition each record a certificate naming it: {:?}",
            both_entry.outcome()
        );
        let [ref at_one, ref at_other] = *both_entry.certificates()
        else {
            panic!("two certificates");
        };
        assert_ne!(
            at_one.redex(),
            at_other.redex(),
            "each certificate is addressed by its own instance"
        );
        assert_eq!(
            steps(twice_entry),
            [convertible(At(0))],
            "one instance written twice is certified once, whatever its nodes"
        );
        for entry in [both_entry, twice_entry] {
            assert!(
                matches!(*entry.outcome(), Outcome::Defined { .. }),
                "{:?} is admitted",
                entry.outcome()
            );
        }
    }

    #[test]
    fn a_rigid_static_instance_crosses_as_a_kernel_application()
    {
        // def G : Type -> Type ;
        // def applied : Type = G Integer ;
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let operator_type = arena.value_type_static_pi(small, small);
        let integer = arena.value_type_base(BaseType::Integer);
        let integer_code = arena.value_quote(integer);
        let opaque = arena.value_constant(ConstantIndex::from(0_usize));
        let applied = arena.value_static_application(opaque, integer_code);
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(operator_type), HOLE),
            declaration(At(1), Maybe::Present(small), Maybe::Present(applied)),
        ]);
        assert!(
            matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
            "an instance of an opaque operator checks"
        );
        let [ref axiom, ref instance] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        assert!(
            matches!(*axiom.outcome(), Outcome::Assumed { .. })
                && matches!(*instance.outcome(), Outcome::Defined { .. }),
            "the opaque operator crosses as an axiom and its instance as a definition: {:?}",
            instance.outcome()
        );
        assert!(
            instance.certificates().is_empty(),
            "nothing unfolds at a rigid head"
        );
        let artifact = decode(readmission.export(BTreeMap::new()).as_image()).unwrap();
        let body = artifact
            .declarations()
            .iter()
            .find_map(|marked| match *marked.declaration().content() {
                | DeclarationContent::Def { body, .. } => Some(body),
                | DeclarationContent::Data { .. }
                | DeclarationContent::Axiom { .. }
                | DeclarationContent::AbstractType { .. } => None,
            })
            .unwrap();
        let Some(&KernelValue::StaticApplication(head, argument)) = artifact.arena().value(body)
        else {
            panic!("the instance crosses as the kernel's static application");
        };
        assert_eq!(
            artifact.arena().value(head),
            Some(&KernelValue::Constant(crossed_at(&readmission, At(0)))),
            "its head is the axiom's position"
        );
        let Some(&KernelValue::Quote(quoted)) = artifact.arena().value(argument)
        else {
            panic!("its argument is a quote");
        };
        assert_eq!(
            artifact.arena().value_type(quoted),
            Some(&KernelValueType::Base(BaseType::Integer)),
            "of the atom it was applied at"
        );
    }

    #[test]
    fn a_static_lambda_crosses_only_as_a_closed_operator()
    {
        let mut arena = CoreArena::new();
        let closed = pair_operator(&mut arena);
        let free = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let open = arena.value_static_lambda(free);
        let positions = Positions::default();
        let lifts = alloc::collections::BTreeMap::new();
        let definitions = alloc::collections::BTreeMap::new();
        let source = Source {
            lifts: &lifts,
            funexts: &BTreeMap::new(),
            equivalences: &BTreeMap::new(),
            flows: &BTreeMap::new(),
            directed: &BTreeMap::new(),
            reflexivities: &BTreeMap::new(),
            relations: &BTreeMap::new(),
            natives: &BTreeMap::new(),
            definitions: &definitions,
        };
        let base = ConstantIndex::from(3_usize);
        let mut erasure = Erasure::new(&mut arena, source, &positions, base);
        let refused = |at: ValueId| {
            Err(Refusal::OutOfFragment {
                at: CoreNode::Term(TermNode::Value(at)),
                former: UnadmittedFormer::StaticLambda,
            })
        };
        assert_eq!(
            erasure.abstraction(closed),
            refused(closed),
            "a static normal form holds no lambda"
        );
        erasure.mode = Reading::Verbatim;
        assert_eq!(
            erasure.abstraction(closed),
            Ok(base),
            "a closed lambda read verbatim is the first operator, numbered from the base"
        );
        assert_eq!(
            erasure.abstraction(closed),
            Ok(base),
            "and keeps its number when met again"
        );
        assert_eq!(
            erasure.abstraction(open),
            refused(open),
            "a lambda reaching a binder outside itself stands for no closed operator"
        );
    }

    #[test]
    fn every_checked_static_declaration_is_readmitted()
    {
        // def RawRelMonad : (Type -> Type[-]) -> Type -> Type -> Type ;
        // def RawRelMonad = \T. \A. \B.
        //   U (El A -> T A) * U (U (T A) -> U (El A -> T B) -> T B) ;
        // def Witness : Type = RawRelMonad (\X. F (El X * El X)) Integer Integer ;
        // def Elided : Type =
        //   U (Integer -> F (Integer * Integer))
        //   * U (U (F (Integer * Integer)) -> U (Integer -> F (Integer * Integer)) -> F
        //     (Integer * Integer)) ;
        // def unit_and_bind : El Witness ;
        //
        // The kernel is the oracle: the instance crosses as the same content
        // the elided spelling does, every step it took replays, and a hole at
        // its decode is an axiom of the normal form.
        let mut arena = CoreArena::new();
        let small = small(&mut arena);
        let negative =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        let family_type = arena.value_type_static_pi(small, negative);
        let last = arena.value_type_static_pi(small, small);
        let middle = arena.value_type_static_pi(small, last);
        let monad_type = arena.value_type_static_pi(family_type, middle);
        let result = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let carrier = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let family = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let element = arena.value_type_element(carrier, Level::zero());
        let at_carrier = arena.value_static_application(family, carrier);
        let at_result = arena.value_static_application(family, result);
        let acts_on_carrier = arena.comp_type_element(at_carrier, Level::zero());
        let acts_on_result = arena.comp_type_element(at_result, Level::zero());
        let unit_arrow = arena.comp_type_arrow(element, acts_on_carrier);
        let unit_thunk = arena.value_type_thunk(unit_arrow);
        let suspended_carrier = arena.value_type_thunk(acts_on_carrier);
        let continuation_arrow = arena.comp_type_arrow(element, acts_on_result);
        let continuation = arena.value_type_thunk(continuation_arrow);
        let bind_tail = arena.comp_type_arrow(continuation, acts_on_result);
        let bind_arrow = arena.comp_type_arrow(suspended_carrier, bind_tail);
        let bind_thunk = arena.value_type_thunk(bind_arrow);
        let monad_product = arena.value_type_product(&[unit_thunk, bind_thunk]);
        let monad_code = arena.value_quote(monad_product);
        let over_result = arena.value_static_lambda(monad_code);
        let over_carrier = arena.value_static_lambda(over_result);
        let monad = arena.value_static_lambda(over_carrier);

        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = arena.value_type_element(bound, Level::zero());
        let squared = arena.value_type_product(&[decoded, decoded]);
        let returns_squared = arena.comp_type_returner(squared);
        let squared_code = arena.value_quote_computation(returns_squared);
        let squaring = arena.value_static_lambda(squared_code);
        let integer = arena.value_type_base(BaseType::Integer);
        let carrier_code = arena.value_quote(integer);
        let result_code = arena.value_quote(integer);
        let head = arena.value_constant(ConstantIndex::from(0_usize));
        let at_family = arena.value_static_application(head, squaring);
        let at_carrier_code = arena.value_static_application(at_family, carrier_code);
        let witness = arena.value_static_application(at_carrier_code, result_code);

        let pair = arena.value_type_product(&[integer, integer]);
        let returns_pair = arena.comp_type_returner(pair);
        let unit_spelled = arena.comp_type_arrow(integer, returns_pair);
        let unit_spelled = arena.value_type_thunk(unit_spelled);
        let suspended_pair = arena.value_type_thunk(returns_pair);
        let continuation_spelled = arena.comp_type_arrow(integer, returns_pair);
        let continuation_spelled = arena.value_type_thunk(continuation_spelled);
        let bind_tail_spelled = arena.comp_type_arrow(continuation_spelled, returns_pair);
        let bind_spelled = arena.comp_type_arrow(suspended_pair, bind_tail_spelled);
        let bind_spelled = arena.value_type_thunk(bind_spelled);
        let elided_product = arena.value_type_product(&[unit_spelled, bind_spelled]);
        let elided = arena.value_quote(elided_product);
        let witness_constant = arena.value_constant(ConstantIndex::from(1_usize));
        let decoded_witness = arena.value_type_element(witness_constant, Level::zero());

        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(monad_type), Maybe::Present(monad)),
            declaration(At(1), Maybe::Present(small), Maybe::Present(witness)),
            declaration(At(2), Maybe::Present(small), Maybe::Present(elided)),
            declaration(At(3), Maybe::Present(decoded_witness), HOLE),
        ]);
        assert!(
            matches!(
                report
                    .judged()
                    .iter()
                    .map(Judged::verdict)
                    .collect::<Vec<_>>()
                    .as_slice(),
                [
                    Verdict::Checked { .. },
                    Verdict::Checked { .. },
                    Verdict::Checked { .. },
                    Verdict::Owed(_),
                ]
            ),
            "the operator, its instance and the elided spelling check, and the hole is owed: \
             {:?}",
            report
                .judged()
                .iter()
                .map(Judged::verdict)
                .collect::<Vec<_>>()
        );
        let [ref operator, ref instance, ref spelled, ref hole] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        assert_eq!(
            operator.outcome(),
            &Outcome::Static,
            "the operator stays on the checker's side"
        );
        assert!(
            matches!(*instance.outcome(), Outcome::Defined { .. })
                && matches!(*spelled.outcome(), Outcome::Defined { .. })
                && matches!(*hole.outcome(), Outcome::Assumed { .. }),
            "the instance and the spelling cross as definitions and the hole as an axiom: \
             {:?}",
            readmission.readmitted()
        );
        assert!(
            matches!(steps(instance).first(), Some(&(Unfolded::Definition(position), _))
                if position == ConstantIndex::from(0_usize)),
            "the instance unfolds the operator first: {:?}",
            steps(instance)
        );
        for entry in [instance, hole] {
            assert!(
                !entry.certificates().is_empty()
                    && entry
                        .certificates()
                        .iter()
                        .all(|replayed| replayed.verdict() == KernelVerdict::Convertible),
                "every step the kernel replays converts: {:?}",
                steps(entry)
            );
        }
        let bodies = exported_bodies(&readmission);
        assert_eq!(
            bodies.len(),
            2_usize,
            "the instance and the spelling are the definitions that cross"
        );
        assert_eq!(
            bodies.first(),
            bodies.last(),
            "the instance crosses as exactly the content the elided spelling writes"
        );
    }

    /// One generated code declaration: which code it defines, the level the
    /// code is built at, how far above the code's own universe a value code is
    /// declared, and which earlier code a reference names.
    #[derive(Clone, Copy, Debug)]
    struct CodeRecipe
    {
        /// The shape of the code: an atom's quote, a universe's of either sort,
        /// a thunk type's, a returner's, an arrow's, or an earlier code.
        shape: u8,
        /// The level the code's universe is built at.
        level: u8,
        /// How many levels above its own universe a value code is declared.
        bump: u8,
        /// The earlier code a reference names, counted round.
        earlier: u8,
    }

    /// The code recipe strategy.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: recipes choose one of seven shapes, levels below three, bumps
    ///   below two and an arbitrary byte selecting an earlier code.
    /// - panics: none.
    /// - executable: none — constructing a strategy cannot observe its future
    ///   draws or shrink tree; generated recipes are checked by the builder.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — one to five generated recipes build checked modules
    ///   and replayable certificates; wrong sort, natural level or
    ///   earlier-reference policy changes acceptance or replay. Sampling is not
    ///   an exhaustive claim about random draws or shrinking.
    /// - witness: `bridge::tests::every_checked_universe_declaration_is_readmitted`
    /// - witness: `bridge::tests::every_readmission_certificate_replays`
    fn code_recipe() -> impl proptest::strategy::Strategy<Value = CodeRecipe>
    {
        use proptest::prelude::any;
        use proptest::strategy::Strategy as _;
        (0_u8 .. 7_u8, 0_u8 .. 3_u8, 0_u8 .. 2_u8, any::<u8>()).prop_map(
            |(shape, level, bump, earlier)| CodeRecipe {
                shape,
                level,
                bump,
                earlier,
            },
        )
    }

    /// The module `recipes` build: one code declaration per recipe, each
    /// declared at the universe of its sort, a value code at or above its own
    /// level; then one declaration over each code's decode — a value code's as
    /// the identity on it, a computation code's as an owed suspension of it.
    /// The second list is the positions of the declarations over decodes.
    ///
    /// # Specification
    /// - requires: fewer than six recipes, each with shape below seven, level
    ///   below three and bump below two.
    /// - ensures: one declared code per recipe followed by one declaration
    ///   using each decode, consecutively numbered and located by the returned
    ///   use positions; every declared type and present body resolves.
    /// - panics: none within the bounded recipe domain.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — one to five bounded code recipes expose complete
    ///   readmission, exact axioms and convertible certificates; wrong decode
    ///   family, numbering, level or reference changes these observations.
    /// - witness: `bridge::tests::every_checked_universe_declaration_is_readmitted`
    /// - witness: `bridge::tests::every_readmission_certificate_replays`
    #[spec(
        requires: recipes.len() < 6 && recipes.iter().all(|recipe| recipe.shape < 7 && recipe.level < 3 && recipe.bump < 2),
        ensures: |ret| ret.0.len() == recipes.len().saturating_mul(2) && ret.1.len() == recipes.len()
            && ret.1.iter().enumerate().all(|(index,at)| at.0 == recipes.len().saturating_add(index))
            && ret.0.iter().enumerate().all(|(index,declaration)| declaration.constant() == ConstantIndex::from(index)
                && match declaration.content() {
                    &crate::DeclarationContent::Value {signature:Maybe::Present(ty),body} => arena.value_type(ty).is_some() && match body { Maybe::Present(body) => arena.value(body).is_some(), Maybe::Absent(_) => true },
                    _ => false,
                }),
    )]
    fn universe_module(
        arena: &mut CoreArena,
        recipes: &[CodeRecipe],
    ) -> (Vec<Declaration>, Vec<At>)
    {
        let level_at = |n: u8| Level::constant(LevelConstant::from(u64::from(n)));
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let mut module = Vec::new();
        let mut codes: Vec<(GroundSort, u8)> = Vec::new();
        for recipe in recipes {
            let own = level_at(recipe.level);
            let above = recipe.level.saturating_add(1_u8);
            let (code, sort, natural) = match recipe.shape {
                | 1_u8 => {
                    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), own);
                    (arena.value_quote(universe), GroundSort::Value, above)
                },
                | 2_u8 => {
                    let universe =
                        arena.value_type_universe(Sort::Ground(GroundSort::Computation), own);
                    (arena.value_quote(universe), GroundSort::Value, above)
                },
                | 3_u8 => {
                    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), own);
                    let returner = arena.comp_type_returner(universe);
                    let thunk = arena.value_type_thunk(returner);
                    (arena.value_quote(thunk), GroundSort::Value, above)
                },
                | 4_u8 => (
                    arena.value_quote_computation(returns_integer),
                    GroundSort::Computation,
                    0_u8,
                ),
                | 5_u8 => {
                    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), own);
                    let returner = arena.comp_type_returner(universe);
                    let arrow = arena.comp_type_arrow(integer, returner);
                    (
                        arena.value_quote_computation(arrow),
                        GroundSort::Computation,
                        above,
                    )
                },
                | 6_u8 if !codes.is_empty() => {
                    let position = usize::from(recipe.earlier)
                        .checked_rem(codes.len())
                        .expect("an earlier code exists");
                    let (sort, natural) = codes[position];
                    (
                        arena.value_constant(ConstantIndex::from(position)),
                        sort,
                        natural,
                    )
                },
                | _ => (arena.value_quote(integer), GroundSort::Value, 0_u8),
            };
            let declared_level = match sort {
                | GroundSort::Value => natural.saturating_add(recipe.bump),
                | GroundSort::Computation => natural,
            };
            let universe = arena.value_type_universe(Sort::Ground(sort), level_at(declared_level));
            module.push(declaration(
                At(module.len()),
                Maybe::Present(universe),
                Maybe::Present(code),
            ));
            codes.push((sort, declared_level));
        }
        let mut uses = Vec::new();
        for (position, &(sort, declared_level)) in codes.iter().enumerate() {
            let name = arena.value_constant(ConstantIndex::from(position));
            uses.push(At(module.len()));
            match sort {
                | GroundSort::Value => {
                    let decoded = arena.value_type_element(name, level_at(declared_level));
                    let returner = arena.comp_type_returner(decoded);
                    let arrow = arena.comp_type_arrow(decoded, returner);
                    let suspended = arena.value_type_thunk(arrow);
                    let bound =
                        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                    let returned = arena.computation_return(bound);
                    let lambda = arena.computation_lambda(returned);
                    let thunk = arena.value_thunk(lambda);
                    module.push(declaration(
                        At(module.len()),
                        Maybe::Present(suspended),
                        Maybe::Present(thunk),
                    ));
                },
                | GroundSort::Computation => {
                    let decoded = arena.comp_type_element(name, level_at(declared_level));
                    let suspended = arena.value_type_thunk(decoded);
                    module.push(declaration(
                        At(module.len()),
                        Maybe::Present(suspended),
                        HOLE,
                    ));
                },
            }
        }
        (module, uses)
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn every_fixture_the_checker_accepts_is_readmitted(
            typed in typed_recipe(),
            free in term_recipe(),
        )
        {
            // The well-typed set: every constant owed, every term declared at
            // its type — a computation as its thunk — and every synthesising
            // value declared unsigned as well.
            let mut arena = CoreArena::new();
            let terms = typed.build(&mut arena);
            let mut module = Vec::new();
            for &declared in &terms.constants {
                module.push(declaration(At(module.len()), Maybe::Present(declared), HOLE));
            }
            for &(value, declared, mode) in &terms.values {
                module.push(declaration(At(module.len()), Maybe::Present(declared), Maybe::Present(value)));
                if mode == Mode::Synthesising {
                    module.push(declaration(At(module.len()), UNSIGNED, Maybe::Present(value)));
                }
            }
            for &(comp, comp_type, _) in &terms.comps {
                let thunk = arena.value_thunk(comp);
                let suspended = arena.value_type_thunk(comp_type);
                module.push(declaration(At(module.len()), Maybe::Present(suspended), Maybe::Present(thunk)));
            }
            let (report, readmission) = judge_and_readmit(&mut arena, &module);
            prop_assert!(
                report.judged().iter().all(|judged| !matches!(judged.verdict(), Verdict::Refused(_))),
                "the well-typed set is accepted whole"
            );
            assert_crossed(&report, &readmission)?;

            // The free set: six owed constants, every value declared unsigned,
            // and every computation that synthesises declared as its thunk.
            let mut arena = CoreArena::new();
            let terms = free.build(&mut arena);
            let integer = arena.value_type_base(BaseType::Integer);
            let string = arena.value_type_base(BaseType::String);
            let unit_type = arena.value_type_unit();
            let returns_integer = arena.comp_type_returner(integer);
            let returns_string = arena.comp_type_returner(string);
            let suspended = arena.value_type_thunk(returns_integer);
            let arrow = arena.comp_type_arrow(integer, returns_integer);
            let function = arena.value_type_thunk(arrow);
            let unit_arrow = arena.comp_type_arrow(unit_type, returns_string);
            let unit_function = arena.value_type_thunk(unit_arrow);
            let constants = [integer, string, unit_type, suspended, function, unit_function];
            let synthesised: Vec<_> = {
                let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
                seed(&mut context, &constants);
                terms
                    .comps
                    .iter()
                    .filter_map(|&comp| match synthesise_comp(&mut context, comp) {
                        | Ok(found) => Some((comp, found.produced().id())),
                        | Err(_) => None,
                    })
                    .collect()
            };
            let mut module = Vec::new();
            for &declared in &constants {
                module.push(declaration(At(module.len()), Maybe::Present(declared), HOLE));
            }
            for &value in &terms.values {
                module.push(declaration(At(module.len()), UNSIGNED, Maybe::Present(value)));
            }
            for (comp, comp_type) in synthesised {
                let thunk = arena.value_thunk(comp);
                let suspended = arena.value_type_thunk(comp_type);
                module.push(declaration(At(module.len()), Maybe::Present(suspended), Maybe::Present(thunk)));
            }
            let (report, readmission) = judge_and_readmit(&mut arena, &module);
            assert_crossed(&report, &readmission)?;
        }

        #[test]
        fn every_checked_function_definition_is_readmitted(
            recipes in proptest::collection::vec(function_recipe(), 1 .. 4),
        )
        {
            // Every constant a statement forces owed first, then every
            // function declared at its type: the shape a lowered function
            // tail takes, well or ill typed by the value it returns.
            let mut arena = CoreArena::new();
            let mut constants = Vec::new();
            let functions: Vec<_> = recipes
                .iter()
                .map(|recipe| recipe.build(&mut arena, &mut constants))
                .collect();
            let mut module = Vec::new();
            for &declared in &constants {
                module.push(declaration(At(module.len()), Maybe::Present(declared), HOLE));
            }
            for function in &functions {
                module.push(declaration(
                    At(module.len()),
                    Maybe::Present(function.declared),
                    Maybe::Present(function.body),
                ));
            }
            let (report, readmission) = judge_and_readmit(&mut arena, &module);
            for (recipe, judged) in recipes.iter().zip(&report.judged()[constants.len()..]) {
                prop_assert_eq!(
                    matches!(judged.verdict(), Verdict::Checked { .. }),
                    recipe.typing() == Typing::WellTyped,
                    "the checker accepts a function exactly when it is well typed: {:?}",
                    judged.verdict()
                );
            }
            assert_crossed(&report, &readmission)?;
        }

        #[test]
        fn every_checked_universe_declaration_is_readmitted(
            recipes in proptest::collection::vec(code_recipe(), 1 .. 6),
        )
        {
            let mut arena = CoreArena::new();
            let (module, _) = universe_module(&mut arena, &recipes);
            let (report, readmission) = judge_and_readmit(&mut arena, &module);
            prop_assert!(
                report.judged().iter().all(|judged| !matches!(judged.verdict(), Verdict::Refused(_))),
                "every code, every reference and every decode is accepted: {:?}",
                report.judged().iter().map(Judged::verdict).collect::<Vec<_>>()
            );
            assert_crossed(&report, &readmission)?;
        }

        #[test]
        fn every_readmission_certificate_replays(
            recipes in proptest::collection::vec(code_recipe(), 1 .. 6),
        )
        {
            let mut arena = CoreArena::new();
            let (module, uses) = universe_module(&mut arena, &recipes);
            let (_, readmission) = judge_and_readmit(&mut arena, &module);
            for position in uses {
                let entry = &readmission.readmitted()[position.0];
                prop_assert!(
                    !entry.certificates().is_empty(),
                    "a decode of a defined code unfolds at export"
                );
                for certificate in entry.certificates() {
                    prop_assert_eq!(
                        certificate.verdict(),
                        KernelVerdict::Convertible,
                        "the kernel re-derives the unfolding of {:?}",
                        certificate.unfolded()
                    );
                }
            }
        }
    }
}
