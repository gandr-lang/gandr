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
//! # An uncompleted signature enters as an axiom
//!
//! An owed hole is a declaration with a type and no body, which is exactly the
//! kernel's bodiless declaration: it is staged through [`Staging::axiom`], and
//! the hole never becomes a term. A hole the judgement refused — in synthesis
//! position, where its refusal names the hole, or under a signature that did
//! not form — crosses as nothing. An axiom's constant is rigid: no decode of
//! it unfolds.
//!
//! # A mark crosses as nothing
//!
//! A refused declaration carries its refusal as its mark, and the bridge offers
//! the kernel nothing for it: not its body, which the kernel may accept where
//! the judgement did not, and not its signature as an axiom, which would put an
//! assumption in the artifact's audit that the ledger never owed. A later
//! declaration reading it is [`Refusal::Withheld`], located at the reference.
//!
//! # The ledger and the kernel's audit agree entry for entry
//!
//! The kernel's audit of a declaration names every axiom it transitively rests
//! on, an axiom's own position included. The [`ArtifactAudit`] is the union of
//! those audits over the artifact, so its axioms are exactly the owed holes the
//! kernel admitted: it is empty exactly when the module's ledger is, which is
//! the kernel-side witness of sealedness. The bridge reports it and gates
//! nothing on it.
//!
//! # The bridge owns its staging, so it owns the rollback
//!
//! Each declaration is erased into a staging session the bridge opened, and a
//! refused erasure or a declined certificate discards it; a rejected admission
//! is truncated by the kernel's choke point. A declaration that does not cross
//! leaves the environment as it found it.
//!
//! # One machine, no recursion
//!
//! Erasure is a machine of goals and frames over an explicit stack. A node is
//! open while its frame waits, so a node that is its own descendant —
//! constructible only from ids of another arena — is refused instead of erased
//! forever.
//!
//! [`Staging::axiom`]: gandr_kernel_core::Staging::axiom

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_nbe::TraceNode;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_core::AxiomReport;
use gandr_kernel_core::CheckedId;
use gandr_kernel_core::EngineClaim;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_core::KernelVerdict;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_core::ReplayNode;
use gandr_kernel_core::ReplaySides;
use gandr_kernel_core::Unfoldable;
use gandr_kernel_core::Unfoldings;
use gandr_kernel_core::replay;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Declaration as KernelDeclaration;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::StructuredName;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::encode;
use quenchant_shape::shape::Maybe;

use crate::code::Certificate;
use crate::code::CodeDefinitions;
use crate::code::Lift;
use crate::declaration::OriginToken;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;
use crate::view::CompTypeView;
use crate::view::FragmentRefusal;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// Why the bridge offered the kernel nothing for a declaration the judgement
/// accepted.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Refusal
{
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
    /// A variable counts in the linear zone, which the kernel's context does
    /// not have. No former of the fragment binds linearly, so a judged term
    /// never holds one.
    LinearVariable
    {
        /// The variable.
        at: ValueId,
        /// The index.
        index: DeBruijnIndex,
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
    /// The unfolding of a code constant was not certified: the normaliser's
    /// conversion did not answer convertible, or the kernel's replay of its
    /// trace did not re-derive it.
    CertificateDeclined
    {
        /// The module position of the constant unfolded.
        constant: ConstantIndex,
    },
    /// The machine's own bookkeeping disagreed with itself: a frame received
    /// an image of another family than it awaits. Unreachable while the
    /// machine's own pushes are the only source of frames; reported rather
    /// than asserted.
    MachineInvariant,
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
    ///   fragment is unrepresentable; a linear variable, a dangling id, a
    ///   cyclic node, a declined certificate and a machine invariant are engine
    ///   faults, because a judged term from the judged arena holds none of them
    ///   and an unfolding holds by definition; nothing is a user absence.
    /// - provides: the fact a report groups by, in the same four classes the
    ///   judgement's refusals answer to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively against a pinned class table, with two inhabitants of
    ///   each payload-carrying variant differing in every field asserted to
    ///   classify alike.
    /// - witness: `bridge::tests::every_refusal_carries_its_pinned_class`
    #[inline]
    #[must_use]
    pub const fn classify(&self) -> FailureClass
    {
        match *self {
            | Self::Withheld { .. } => FailureClass::MalformedSource,
            | Self::OutOfFragment { .. } => FailureClass::Unrepresentable,
            | Self::LinearVariable { .. }
            | Self::DanglingNode { .. }
            | Self::Cyclic { .. }
            | Self::CertificateDeclined { .. }
            | Self::MachineInvariant => FailureClass::EngineFault,
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
    /// The bridge refused to offer the declaration.
    Refused(Refusal),
    /// The kernel rejected the erased declaration: the judgement accepted what
    /// the kernel does not, the disagreement the oracle exists to report.
    Rejected(KernelError),
}

/// One certificate the kernel replayed for a declaration: the code constant
/// unfolded and the kernel's verdict on its trace.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Replayed
{
    /// The module position of the constant unfolded.
    constant: ConstantIndex,
    /// The kernel's verdict on the certificate's trace.
    verdict: KernelVerdict,
}

impl Replayed
{
    /// The module position of the constant unfolded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
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
    fn of(readmitted: &[Readmitted]) -> Self
    {
        let mut axioms = BTreeSet::new();
        let mut unchecked = BTreeSet::new();
        for entry in readmitted {
            if let Outcome::Defined { ref audit, .. } | Outcome::Assumed { ref audit, .. } =
                entry.outcome
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
    ///   judged declarations carry.
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
    ///   reference reads.
    /// - witness: `bridge::tests::an_export_names_each_crossed_declaration_at_its_position`
    #[inline]
    #[must_use]
    pub fn export(
        &self,
        mut names: BTreeMap<ConstantIndex, StructuredName>,
    ) -> EncodedArtifact
    {
        let mut marked = Vec::with_capacity(self.admitted.len());
        for entry in &self.readmitted {
            let (Outcome::Defined { admitted, .. } | Outcome::Assumed { admitted, .. }) =
                entry.outcome
            else {
                continue;
            };
            let Some(declaration) = self.admitted.get(usize::from(admitted.position()))
            else {
                continue;
            };
            let name = names.remove(&entry.constant).unwrap_or_default();
            marked.push(MarkedDeclaration::new(
                AdmissionMark::Checked,
                declaration.clone().named(name),
            ));
        }

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
///   or [`Outcome::Assumed`] when the kernel admits it. A refused declaration
///   is [`Outcome::Marked`] with its refusal, and the kernel is offered nothing
///   for it. An offer whose erasure refuses, or one of whose certificates the
///   kernel does not replay to convertible, is [`Outcome::Refused`], one the
///   kernel rejects [`Outcome::Rejected`], and either leaves the environment as
///   it was. A constant naming a declaration that crossed is erased to the
///   kernel position that declaration took; a code recorded with a lift is
///   erased to the kernel's lift of its decode; a decode of a constant that
///   crossed as a definition is erased as the decode of its body, each such
///   unfolding certified and replayed.
/// - provides: the environment holding exactly the declarations that crossed,
///   and the [`ArtifactAudit`], whose axioms are the positions of the owed
///   holes the kernel admitted — empty exactly when the report's ledger is,
///   while every owed hole crosses.
/// - fails: never; every declaration gets an outcome.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the kernel is the external oracle: every declaration
///   the judgement accepts over the generated well-typed and free fixture sets
///   and over generated universe declarations crosses, every certificate a
///   generated code constant's readmission records replays, and the artifact's
///   axioms agree with the ledger entry for entry in both directions. The L3
///   residues are the routing of each verdict, separated by one artifact
///   holding a marked body and a marked signed hole the kernel alone admits, a
///   hole in synthesis position and a reference to a marked declaration, beside
///   a checked and an owed positive control; the position remapping, separated
///   by a module whose later references would misresolve under any other map;
///   the rollback, separated by a refusal met after part of a body was minted;
///   a sorted universe, a lifted code and a code constant's unfolding, each
///   readmitted; and a certificate whose trace was emptied, refused.
/// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `bridge::tests::every_checked_function_definition_is_readmitted`
/// - witness: `bridge::tests::every_checked_universe_declaration_is_readmitted`
/// - witness: `bridge::tests::every_readmission_certificate_replays`
/// - witness: `bridge::tests::marks_and_holes_are_refused_beside_their_positive_controls`
/// - witness: `bridge::tests::an_empty_ledger_readmits_an_artifact_resting_on_no_axiom`
/// - witness: `bridge::tests::each_owed_hole_is_an_axiom_of_the_artifact`
/// - witness: `bridge::tests::a_constant_resolves_to_its_readmitted_position`
/// - witness: `bridge::tests::a_refused_declaration_leaves_the_environment_unchanged`
/// - witness: `bridge::tests::a_lowered_value_definition_admits`
/// - witness: `bridge::tests::a_lowered_computation_definition_admits`
/// - witness: `bridge::tests::a_constant_reference_across_declarations_admits`
/// - witness: `bridge::tests::a_sorted_universe_readmits_at_its_level`
/// - witness: `bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
/// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
/// - witness: `bridge::tests::a_declining_certificate_faults_the_declaration`
#[inline]
#[must_use]
pub fn readmit(
    arena: &CoreArena,
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
fn readmit_with<Vouch>(
    arena: &CoreArena,
    report: &ModuleReport,
    vouch: Vouch,
) -> Readmission
where
    Vouch: Fn(Certificate) -> Certificate,
{
    let mut environment = Environment::new();
    let mut positions = Positions::default();
    let mut admitted = Vec::new();
    let mut readmitted = Vec::with_capacity(report.judged().len());
    for judged in report.judged() {
        let source = Source {
            arena,
            lifts: report.lifts(),
            definitions: report.definitions(),
        };
        let (outcome, certificates) = match judged.verdict() {
            | Verdict::Checked { declared, body, .. } => cross(
                &mut environment,
                source,
                &mut positions,
                &mut admitted,
                judged.constant(),
                Offer::Definition {
                    declared: declared.id(),
                    body,
                },
                &vouch,
            ),
            | Verdict::Synthesised { body, synthesised } => cross(
                &mut environment,
                source,
                &mut positions,
                &mut admitted,
                judged.constant(),
                Offer::Definition {
                    declared: synthesised.produced().id(),
                    body,
                },
                &vouch,
            ),
            | Verdict::Owed(entry) => cross(
                &mut environment,
                source,
                &mut positions,
                &mut admitted,
                judged.constant(),
                Offer::Axiom {
                    declared: entry.absence().declared().id(),
                },
                &vouch,
            ),
            | Verdict::Refused(refusal) => (Outcome::Marked(refusal), Vec::new()),
        };
        readmitted.push(Readmitted {
            constant: judged.constant(),
            origin: judged.origin(),
            outcome,
            certificates,
        });
    }
    let audit = ArtifactAudit::of(&readmitted);
    Readmission {
        environment,
        readmitted,
        audit,
        admitted,
    }
}

/// What every erasure reads besides the positions: the arena, the lifts the
/// judgement recorded and the bodies it defined its constants as.
#[derive(Clone, Copy, Debug)]
struct Source<'source>
{
    /// The arena every id resolves in.
    arena: &'source CoreArena,
    /// The codes the judgement checked above their own universe, by node.
    lifts: &'source BTreeMap<ValueId, Lift>,
    /// The body each accepted declaration defines its constant as, elaborated
    /// to the universe it was declared at.
    definitions: &'source BTreeMap<ConstantIndex, ValueId>,
}

/// What an accepted declaration offers the kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Offer
{
    /// A definition: a body at the type it was judged at.
    Definition
    {
        /// The type the body was judged at.
        declared: ValueTypeId,
        /// The body.
        body: ValueId,
    },
    /// An axiom: the type an owed hole owes.
    Axiom
    {
        /// The type owed.
        declared: ValueTypeId,
    },
}

/// An offer's image in the kernel arena.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Erased
{
    /// A definition's declared type and body.
    Definition
    {
        /// The declared type's image.
        declared: gandr_kernel_term::ValueTypeId,
        /// The body's image.
        body: gandr_kernel_term::ValueId,
    },
    /// An axiom's declared type.
    Axiom
    {
        /// The declared type's image.
        declared: gandr_kernel_term::ValueTypeId,
    },
}

/// Erase `offer`, the declaration at `constant`, into a staging session of
/// `environment`, replay its certificates, and admit it.
///
/// # Specification
/// - requires: `positions` holds the kernel position, and for a definition the
///   bodies, of every module declaration that crossed so far, and `exports` the
///   declarations they crossed as, in kernel admission order.
/// - ensures: the offer erased into one staging session; every certificate the
///   erasure collected, passed through `vouch`, replayed by the kernel in that
///   session; and, when each replays to convertible, the offer admitted:
///   [`Outcome::Defined`] for a definition and [`Outcome::Assumed`] for an
///   axiom, each with the kernel's receipt and audit, when the kernel admits
///   it, recorded in `positions` and its staged declaration appended to
///   `exports`. A refused erasure or a declined certificate discards the
///   session and a rejection is truncated by the kernel, so the environment is
///   as it was on every outcome but an admission. The replayed verdicts are
///   returned beside the outcome.
/// - fails: never; a refusal is [`Outcome::Refused`] and a rejection
///   [`Outcome::Rejected`].
/// - panics: none.
fn cross<Vouch>(
    environment: &mut Environment,
    source: Source<'_>,
    positions: &mut Positions,
    exports: &mut Vec<KernelDeclaration>,
    constant: ConstantIndex,
    offer: Offer,
    vouch: &Vouch,
) -> (Outcome, Vec<Replayed>)
where
    Vouch: Fn(Certificate) -> Certificate,
{
    let mut staging = environment.stage();
    let erased = {
        let mut erasure = Erasure::new(source, positions);
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
    let staged = match erased {
        | Erased::Definition { declared, body } => {
            staging.def(LevelSignature::monomorphic(), declared, body)
        },
        | Erased::Axiom { declared } => staging.axiom(LevelSignature::monomorphic(), declared),
    };
    let staged_as = staged.declaration().clone();
    let admitted = match environment.add_decl(staged) {
        | Ok(admitted) => admitted,
        | Err(error) => return (Outcome::Rejected(error), replayed),
    };
    exports.push(staged_as);
    let audit = environment.audit(admitted);
    match (offer, erased) {
        | (Offer::Definition { body, .. }, Erased::Definition { body: image, .. }) => {
            let defined = source.definitions.get(&constant).copied().unwrap_or(body);
            positions.define(constant, admitted, defined, image);
            (Outcome::Defined { admitted, audit }, replayed)
        },
        | (Offer::Axiom { .. } | Offer::Definition { .. }, _) => {
            positions.assume(constant, admitted);
            (Outcome::Assumed { admitted, audit }, replayed)
        },
    }
}

/// The kernel position each module declaration that crossed took, and the
/// bodies the crossed definitions unfold to on either side.
#[derive(Clone, Debug, Default)]
struct Positions
{
    /// Module position to kernel position.
    admitted: BTreeMap<ConstantIndex, ConstantIndex>,
    /// The crossed definitions' core bodies, by module position: what a decode
    /// of a code naming one unfolds to, and what its certificate is asked
    /// over.
    definitions: CodeDefinitions,
    /// The crossed definitions' kernel bodies, by kernel position: what the
    /// kernel's replay may unfold.
    unfoldings: BTreeMap<ConstantIndex, gandr_kernel_term::ValueId>,
}

impl Positions
{
    /// Record that the module definition at `constant`, of core body `body`,
    /// crossed as `admitted` with kernel body `image`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Self::kernel_position`] answers `admitted`'s position for
    ///   `constant`; a decode of a code naming `constant` unfolds to `body`;
    ///   the kernel's replay may unfold `admitted` to `image`.
    /// - panics: none.
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

    /// Record that the module declaration at `constant` crossed as the axiom
    /// `admitted`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Self::kernel_position`] answers `admitted`'s position for
    ///   `constant`, which stays rigid on both sides.
    /// - panics: none.
    fn assume(
        &mut self,
        constant: ConstantIndex,
        admitted: CheckedId,
    )
    {
        self.admitted.insert(constant, admitted.position());
    }

    /// The kernel position of the module declaration the constant `at` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the position recorded for `constant`.
    /// - fails: [`Refusal::Withheld`] at `at` when no declaration at `constant`
    ///   crossed.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal::Withheld`] — the declaration did not cross.
    fn kernel_position(
        &self,
        at: ValueId,
        constant: ConstantIndex,
    ) -> Result<ConstantIndex, Refusal>
    {
        match self.admitted.get(&constant) {
            | Some(&position) => Ok(position),
            | None => Err(Refusal::Withheld { at, constant }),
        }
    }

    /// The definitions the kernel's replay may unfold, by kernel position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Unfoldable::Body`] at each crossed definition's kernel
    ///   position, [`Unfoldable::Opaque`] at every other position below the
    ///   highest.
    /// - panics: none.
    fn unfoldings(&self) -> Unfoldings
    {
        let mut bodies = Vec::new();
        for (&position, &body) in &self.unfoldings {
            while bodies.len() < usize::from(position) {
                bodies.push(Unfoldable::Opaque);
            }
            bodies.push(Unfoldable::Body(body));
        }
        Unfoldings::new(bodies)
    }

    /// The decision the kernel's replay reads for the normaliser's `decision`:
    /// a constant that crossed at its kernel position, and every other node
    /// opaque to the replay.
    ///
    /// # Specification
    /// trivial.
    fn kernel_decision(
        &self,
        decision: ConversionDecision<TraceNode>,
    ) -> ConversionDecision<ReplayNode>
    {
        let node = |node: TraceNode| match node {
            | TraceNode::Constant(constant) => match self.admitted.get(&constant) {
                | Some(&position) => ReplayNode::Constant(position),
                | None => ReplayNode::Other,
            },
            | TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
        };
        match decision {
            | ConversionDecision::ReduceLeft { redex } => {
                ConversionDecision::ReduceLeft { redex: node(redex) }
            },
            | ConversionDecision::ReduceRight { redex } => {
                ConversionDecision::ReduceRight { redex: node(redex) }
            },
            | ConversionDecision::ConstShortcut { constant } => ConversionDecision::ConstShortcut {
                constant: node(constant),
            },
            | ConversionDecision::Unfold { constant } => ConversionDecision::Unfold {
                constant: node(constant),
            },
            | ConversionDecision::Postpone { constant } => ConversionDecision::Postpone {
                constant: node(constant),
            },
            | ConversionDecision::Freeze { constant, side } => ConversionDecision::Freeze {
                constant: node(constant),
                side,
            },
            | ConversionDecision::EtaExpand { side, variable } => ConversionDecision::EtaExpand {
                side,
                variable: node(variable),
            },
            | ConversionDecision::Force { thunk } => {
                ConversionDecision::Force { thunk: node(thunk) }
            },
            | ConversionDecision::ComparedShared { left, right } => {
                ConversionDecision::ComparedShared {
                    left: node(left),
                    right: node(right),
                }
            },
            | ConversionDecision::NegativeSubgoal { position } => {
                ConversionDecision::NegativeSubgoal { position }
            },
        }
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

/// A rule waiting on the image of a child.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Frame
{
    /// A thunk, awaiting its body's computation.
    Thunk
    {
        /// The thunk.
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

/// One declaration's erasure: what it reads, the positions constants resolve
/// through, the frames waiting, every node's image so far, and the
/// certificates of the unfoldings it took.
struct Erasure<'source, 'positions>
{
    /// The arena and the recorded lifts.
    source: Source<'source>,
    /// The kernel positions and bodies of the declarations that crossed before
    /// this one.
    positions: &'positions Positions,
    /// The rules waiting on children, innermost last.
    frames: Vec<Frame>,
    /// The value nodes reached, and their images.
    values: BTreeMap<ValueId, Image<gandr_kernel_term::ValueId>>,
    /// The computation nodes reached, and their images.
    computations: BTreeMap<ComputationId, Image<gandr_kernel_term::ComputationId>>,
    /// The value-type nodes reached, and their images.
    value_types: BTreeMap<ValueTypeId, Image<gandr_kernel_term::ValueTypeId>>,
    /// The computation-type nodes reached, and their images.
    comp_types: BTreeMap<CompTypeId, Image<gandr_kernel_term::CompTypeId>>,
    /// The certificates of the unfoldings taken and not yet replayed.
    certificates: Vec<Certificate>,
}

impl<'source, 'positions> Erasure<'source, 'positions>
{
    /// An erasure reading `source`, resolving constants through `positions`,
    /// with nothing reached.
    ///
    /// # Specification
    /// trivial.
    const fn new(
        source: Source<'source>,
        positions: &'positions Positions,
    ) -> Self
    {
        Self {
            source,
            positions,
            frames: Vec::new(),
            values: BTreeMap::new(),
            computations: BTreeMap::new(),
            value_types: BTreeMap::new(),
            comp_types: BTreeMap::new(),
            certificates: Vec::new(),
        }
    }

    /// Erase `offer` into `target`: its declared type, then a definition's
    /// body.
    ///
    /// # Specification
    /// - requires: no earlier erasure of this machine was refused.
    /// - ensures: the images of the offer's declared type and, for a
    ///   definition, of its body, as [`Self::erase`] gives them.
    /// - fails: the first refusal either erasure gives; the body is not erased
    ///   once the type is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - any [`Refusal`] [`Self::value_type`] or [`Self::value`] gives.
    fn offer(
        &mut self,
        target: &mut TermArena,
        offer: Offer,
    ) -> Result<Erased, Refusal>
    {
        match offer {
            | Offer::Definition { declared, body } => {
                let declared = self.value_type(target, declared)?;
                let body = self.value(target, body)?;
                Ok(Erased::Definition { declared, body })
            },
            | Offer::Axiom { declared } => {
                let declared = self.value_type(target, declared)?;
                Ok(Erased::Axiom { declared })
            },
        }
    }

    /// Replay every certificate the erasure collected, each passed through
    /// `vouch`, against the kernel's images of its constant and its body.
    ///
    /// # Specification
    /// - requires: the offer was erased into `target`, the staging arena the
    ///   declaration is admitted from.
    /// - ensures: one [`Replayed`] per certificate, in the order the erasure
    ///   met the unfoldings, the certificates erasing a body collects replayed
    ///   after it; each replays the certificate's trace, read at the kernel's
    ///   positions, as a convertibility claim between the kernel constant and
    ///   the body's image, unfolding only the crossed definitions. `target`
    ///   holds the images minted and nothing the replay minted.
    /// - fails: [`Refusal::CertificateDeclined`] naming the first certificate
    ///   that does not replay to convertible, beside the verdicts replayed up
    ///   to it; the refusal erasing a body gives.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refusal`] — as above, beside the verdicts replayed before it.
    fn replay_certificates<Vouch>(
        &mut self,
        target: &mut TermArena,
        vouch: &Vouch,
    ) -> Result<Vec<Replayed>, (Refusal, Vec<Replayed>)>
    where
        Vouch: Fn(Certificate) -> Certificate,
    {
        let unfoldings = self.positions.unfoldings();
        let mut replayed = Vec::new();
        loop {
            let pending = core::mem::take(&mut self.certificates);
            if pending.is_empty() {
                return Ok(replayed);
            }
            for certificate in pending {
                let certificate = vouch(certificate);
                let constant = certificate.constant();
                let left = match self.positions.kernel_position(certificate.body(), constant) {
                    | Ok(position) => target.value_constant(position),
                    | Err(refusal) => return Err((refusal, replayed)),
                };
                let right = match self.value(target, certificate.body()) {
                    | Ok(image) => image,
                    | Err(refusal) => return Err((refusal, replayed)),
                };
                let verdict = replay(
                    target,
                    &unfoldings,
                    ReplaySides::Values(left, right),
                    EngineClaim::Convertible,
                    certificate
                        .decisions()
                        .iter()
                        .map(|&decision| self.positions.kernel_decision(decision)),
                    ReplayBudget::DEFAULT,
                );
                replayed.push(Replayed { constant, verdict });
                if verdict != KernelVerdict::Convertible {
                    return Err((Refusal::CertificateDeclined { constant }, replayed));
                }
            }
        }
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
    ///   rule for; [`Refusal::LinearVariable`] for a linear-zone variable;
    ///   [`Refusal::DanglingNode`] for an id `source` does not hold;
    ///   [`Refusal::Cyclic`] for a node reached again while its own erasure
    ///   waits; [`Refusal::CertificateDeclined`] for an unfolding the
    ///   normaliser does not certify. Nodes minted before the refusal stay in
    ///   `target`; the caller owns the arena and its rollback.
    /// - panics: none.
    /// - intension: one kernel node is minted per distinct core node reached,
    ///   so sharing in the source is sharing in the image.
    ///
    /// # Errors
    /// - [`Refusal::Withheld`], [`Refusal::OutOfFragment`],
    ///   [`Refusal::LinearVariable`], [`Refusal::DanglingNode`],
    ///   [`Refusal::Cyclic`], [`Refusal::CertificateDeclined`] — as above.
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
    fn descend(
        &mut self,
        target: &mut TermArena,
        node: CoreNode,
    ) -> Result<Step, Refusal>
    {
        match node {
            | CoreNode::Term(TermNode::Value(at)) => self.descend_value(target, at),
            | CoreNode::Term(TermNode::Computation(at)) => self.descend_computation(at),
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
    ///   string literal are minted, and a thunk and a quote open their frames.
    /// - fails: [`Refusal::Cyclic`] for an open value;
    ///   [`Refusal::DanglingNode`]; [`Refusal::LinearVariable`];
    ///   [`Refusal::Withheld`]; [`Refusal::OutOfFragment`] for a numeric
    ///   literal, a pair, an injection, a value lift, a static lambda or a
    ///   static application.
    /// - panics: none.
    fn descend_value(
        &mut self,
        target: &mut TermArena,
        at: ValueId,
    ) -> Result<Step, Refusal>
    {
        let node = CoreNode::Term(TermNode::Value(at));
        match self.values.get(&at) {
            | Some(&Image::Erased(erased)) => return Ok(Step::Ascend(AnyNode::Value(erased))),
            | Some(&Image::Open) => return Err(Refusal::Cyclic { node }),
            | None => {},
        }
        if let Some(lift) = self.source.lifts.get(&at) {
            self.values.insert(at, Image::Open);
            self.frames.push(Frame::LiftedCode { at });
            self.frames.push(Frame::DecodeLift {
                target: lift.target().clone(),
            });
            return self.decode(target, at, lift.natural().clone(), GroundSort::Value);
        }
        let Some(value) = self.source.arena.value(at)
        else {
            return Err(Refusal::DanglingNode { node });
        };
        let unadmitted = |former| Refusal::OutOfFragment { at: node, former };
        let (frame, child) = match *value {
            | Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            } => return Ok(self.erased_value(at, target.value_variable(index))),
            | Value::Variable {
                zone: Zone::Linear,
                index,
            } => return Err(Refusal::LinearVariable { at, index }),
            | Value::Constant(constant) => {
                let position = self.positions.kernel_position(at, constant)?;
                return Ok(self.erased_value(at, target.value_constant(position)));
            },
            | Value::Unit => return Ok(self.erased_value(at, target.value_unit())),
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
            | Value::Pair(..) => return Err(unadmitted(UnadmittedFormer::Pair)),
            | Value::Injection(..) => return Err(unadmitted(UnadmittedFormer::Injection)),
            | Value::Lift { .. } => return Err(unadmitted(UnadmittedFormer::ValueLift)),
            | Value::StaticLambda(_) => return Err(unadmitted(UnadmittedFormer::StaticLambda)),
            | Value::StaticApplication(..) => {
                return Err(unadmitted(UnadmittedFormer::StaticApplication));
            },
        };
        self.values.insert(at, Image::Open);
        self.frames.push(frame);
        Ok(Step::Descend(child))
    }

    /// Start erasing the computation `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::descend`]: a lambda, an application, a return, a
    ///   force and a bind open their frames.
    /// - fails: [`Refusal::Cyclic`] for an open computation;
    ///   [`Refusal::DanglingNode`]; [`Refusal::OutOfFragment`] for a case.
    /// - panics: none.
    fn descend_computation(
        &mut self,
        at: ComputationId,
    ) -> Result<Step, Refusal>
    {
        let node = CoreNode::Term(TermNode::Computation(at));
        match self.computations.get(&at) {
            | Some(&Image::Erased(erased)) => {
                return Ok(Step::Ascend(AnyNode::Computation(erased)));
            },
            | Some(&Image::Open) => return Err(Refusal::Cyclic { node }),
            | None => {},
        }
        let Some(computation) = self.source.arena.computation(at)
        else {
            return Err(Refusal::DanglingNode { node });
        };
        let (frame, child) = match *computation {
            | Computation::Lambda(body) => (Frame::Lambda { at }, TermNode::Computation(body)),
            | Computation::Application(head, argument) => (
                Frame::ApplicationHead { at, argument },
                TermNode::Computation(head),
            ),
            | Computation::Return(value) => (Frame::Return { at }, TermNode::Value(value)),
            | Computation::Force(value) => (Frame::Force { at }, TermNode::Value(value)),
            | Computation::Bind(bound, body) => {
                (Frame::BindBound { at, body }, TermNode::Computation(bound))
            },
            | Computation::Case { .. } => {
                return Err(Refusal::OutOfFragment {
                    at: node,
                    former: UnadmittedFormer::Case,
                });
            },
        };
        self.computations.insert(at, Image::Open);
        self.frames.push(frame);
        Ok(Step::Descend(CoreNode::Term(child)))
    }

    /// Start erasing the value type `at`, read through the fragment's view.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::descend`]: the integer and string atoms, the unit
    ///   type and a universe are minted; a thunk type and a lift open their
    ///   frames; a decode opens its frame and decodes its code.
    /// - fails: [`Refusal::Cyclic`] for an open value type; whatever the view
    ///   or the decode refuses, converted.
    /// - panics: none.
    fn descend_value_type(
        &mut self,
        target: &mut TermArena,
        at: ValueTypeId,
    ) -> Result<Step, Refusal>
    {
        match self.value_types.get(&at) {
            | Some(&Image::Erased(erased)) => return Ok(Step::Ascend(AnyNode::ValueType(erased))),
            | Some(&Image::Open) => {
                return Err(Refusal::Cyclic {
                    node: CoreNode::Type(TypeNode::Value(at)),
                });
            },
            | None => {},
        }
        let (frame, child) = match value_type_view(self.source.arena, at)? {
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
            | ValueTypeView::Thunk(body) => (
                Frame::ThunkType { at },
                CoreNode::Type(TypeNode::Computation(body)),
            ),
            | ValueTypeView::Lift { inner, .. } => (
                Frame::TypeLift { at },
                CoreNode::Type(TypeNode::Value(inner)),
            ),
            | ValueTypeView::Element {
                code,
                target: level,
            } => {
                let level = level.clone();
                self.value_types.insert(at, Image::Open);
                self.frames.push(Frame::Decoded {
                    at: TypeNode::Value(at),
                });
                return self.decode(target, code, level, GroundSort::Value);
            },
        };
        self.value_types.insert(at, Image::Open);
        self.frames.push(frame);
        Ok(Step::Descend(child))
    }

    /// Start erasing the computation type `at`, read through the fragment's
    /// view.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::descend`]: a returner, an arrow and a dependent
    ///   arrow open their frames; a decode opens its frame and decodes its
    ///   code.
    /// - fails: [`Refusal::Cyclic`] for an open computation type; whatever the
    ///   view or the decode refuses, converted.
    /// - panics: none.
    fn descend_comp_type(
        &mut self,
        target: &mut TermArena,
        at: CompTypeId,
    ) -> Result<Step, Refusal>
    {
        match self.comp_types.get(&at) {
            | Some(&Image::Erased(erased)) => return Ok(Step::Ascend(AnyNode::CompType(erased))),
            | Some(&Image::Open) => {
                return Err(Refusal::Cyclic {
                    node: CoreNode::Type(TypeNode::Computation(at)),
                });
            },
            | None => {},
        }
        let (frame, child) = match comp_type_view(self.source.arena, at)? {
            | CompTypeView::Returner(result) => (Frame::Returner { at }, result),
            | CompTypeView::Arrow { domain, codomain } => {
                (Frame::ArrowDomain { at, codomain }, domain)
            },
            | CompTypeView::Pi { domain, codomain } => (Frame::PiDomain { at, codomain }, domain),
            | CompTypeView::Element {
                code,
                target: level,
            } => {
                let level = level.clone();
                self.comp_types.insert(at, Image::Open);
                self.frames.push(Frame::Decoded {
                    at: TypeNode::Computation(at),
                });
                return self.decode(target, code, level, GroundSort::Computation);
            },
        };
        self.comp_types.insert(at, Image::Open);
        self.frames.push(frame);
        Ok(Step::Descend(CoreNode::Type(TypeNode::Value(child))))
    }

    /// Erase the decode of `code` at `level` into the type of `sort` it
    /// denotes: unfold a constant that crossed with a body, collecting its
    /// certificate, until the code is a quote, whose type is erased, or a
    /// variable or a rigid constant, whose decode is minted.
    ///
    /// # Specification
    /// - requires: `code` was checked at the universe of `sort` at `level`.
    /// - ensures: for a quote of a type of `sort`, the descent into that type;
    ///   for a variable or a constant without a body, the kernel's decode of
    ///   its image at `level`; for a constant with a body, its certificate
    ///   collected and the decode of the body, which the judgement defined at
    ///   the constant's own universe, so at `level` still.
    /// - fails: [`Refusal::CertificateDeclined`] for an unfolding the
    ///   normaliser does not certify; [`Refusal::Withheld`] for a constant that
    ///   did not cross; [`Refusal::LinearVariable`]; [`Refusal::DanglingNode`];
    ///   [`Refusal::OutOfFragment`] for a static application;
    ///   [`Refusal::MachineInvariant`] for a code that is no code.
    /// - panics: none.
    /// - intension: a loop over the unfolding chain, which the admission order
    ///   makes finite.
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
            let Some(node) = self.source.arena.value(code)
            else {
                return Err(Refusal::DanglingNode {
                    node: CoreNode::Term(TermNode::Value(code)),
                });
            };
            let image = match (node, sort) {
                | (&Value::Quote(quoted), GroundSort::Value) => {
                    return Ok(Step::Descend(CoreNode::Type(TypeNode::Value(quoted))));
                },
                | (&Value::QuoteComputation(quoted), GroundSort::Computation) => {
                    return Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(quoted))));
                },
                | (
                    &Value::Variable {
                        zone: Zone::Intuitionistic,
                        index,
                    },
                    _,
                ) => target.value_variable(index),
                | (
                    &Value::Variable {
                        zone: Zone::Linear,
                        index,
                    },
                    _,
                ) => return Err(Refusal::LinearVariable { at: code, index }),
                | (&Value::Constant(constant), _) => {
                    if let Maybe::Present(body) = self.positions.definitions.body(constant) {
                        let certificate = self
                            .positions
                            .definitions
                            .certify(self.source.arena, code, constant)
                            .map_err(|_undecided| Refusal::CertificateDeclined { constant })?;
                        self.certificates.push(certificate);
                        code = body;
                        continue;
                    }
                    let position = self.positions.kernel_position(code, constant)?;
                    target.value_constant(position)
                },
                | (&Value::StaticApplication(..), _) => {
                    return Err(Refusal::OutOfFragment {
                        at: CoreNode::Term(TermNode::Value(code)),
                        former: UnadmittedFormer::StaticApplication,
                    });
                },
                | (&Value::Quote(_), GroundSort::Computation)
                | (&Value::QuoteComputation(_), GroundSort::Value)
                | (
                    &(Value::Unit
                    | Value::Literal(_)
                    | Value::Thunk(_)
                    | Value::Pair(..)
                    | Value::Injection(..)
                    | Value::Lift { .. }
                    | Value::StaticLambda(_)),
                    _,
                ) => return Err(Refusal::MachineInvariant),
            };
            let decoded = match sort {
                | GroundSort::Value => AnyNode::ValueType(target.value_type_element(image, level)),
                | GroundSort::Computation => {
                    AnyNode::CompType(target.comp_type_element(image, level))
                },
            };
            return Ok(Step::Ascend(decoded));
        }
    }

    /// Start erasing `argument`, the value an application passes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a code constant without a recorded lift whose unfolding
    ///   reaches a quote, one certificate per constant on the chain, outermost
    ///   first, and the descent into that quote, which records no image for the
    ///   constant; for any other value, its descent.
    /// - provides: an instantiation at a code substitutes the type the code
    ///   stands for, so the kernel's types hold no decode of a constant with a
    ///   body.
    /// - fails: [`Refusal::CertificateDeclined`] for an unfolding the
    ///   normaliser does not certify.
    /// - panics: none.
    /// - intension: two loops over the unfolding chain, which the admission
    ///   order makes finite: the first finds the quote without collecting, so a
    ///   chain ending at a rigid constant certifies nothing.
    fn argument(
        &mut self,
        argument: ValueId,
    ) -> Result<Step, Refusal>
    {
        let descend = Step::Descend(CoreNode::Term(TermNode::Value(argument)));
        if self.source.lifts.contains_key(&argument) {
            return Ok(descend);
        }
        let mut reached = argument;
        let quote = loop {
            match self.source.arena.value(reached) {
                | Some(&(Value::Quote(_) | Value::QuoteComputation(_))) => break reached,
                | Some(&Value::Constant(constant)) => {
                    match self.positions.definitions.body(constant) {
                        | Maybe::Present(body) => reached = body,
                        | Maybe::Absent(_) => return Ok(descend),
                    }
                },
                | _ => return Ok(descend),
            }
        };
        let mut code = argument;
        while let Some(&Value::Constant(constant)) = self.source.arena.value(code) {
            let Maybe::Present(body) = self.positions.definitions.body(constant)
            else {
                return Err(Refusal::MachineInvariant);
            };
            let certificate = self
                .positions
                .definitions
                .certify(self.source.arena, code, constant)
                .map_err(|_undecided| Refusal::CertificateDeclined { constant })?;
            self.certificates.push(certificate);
            code = body;
        }
        Ok(Step::Descend(CoreNode::Term(TermNode::Value(quote))))
    }

    /// Hand `image` to the rule `frame` holds.
    ///
    /// # Specification
    /// - requires: `frame` was pushed by this machine.
    /// - ensures: a frame awaiting its last child mints its node over the
    ///   children's images, records the image and ascends it; an application, a
    ///   bind, an arrow or a dependent arrow awaiting its first child descends
    ///   to its second; a decode records the type its code denotes; a lift a
    ///   crossing added wraps the decode beneath it.
    /// - fails: [`Refusal::MachineInvariant`] when `image` is not of the family
    ///   the frame awaits.
    /// - panics: none.
    fn resume(
        &mut self,
        target: &mut TermArena,
        frame: Frame,
        image: AnyNode,
    ) -> Result<Step, Refusal>
    {
        match (frame, image) {
            | (Frame::Thunk { at }, AnyNode::Computation(body)) => {
                Ok(self.erased_value(at, target.value_thunk(body)))
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
            | (Frame::ThunkType { at }, AnyNode::CompType(body)) => {
                Ok(self.erased_value_type(at, target.value_type_thunk(body)))
            },
            | (Frame::TypeLift { at }, AnyNode::ValueType(inner)) => {
                let ValueTypeView::Lift { target: level, .. } =
                    value_type_view(self.source.arena, at)?
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
            | (Frame::PiDomain { at, codomain }, AnyNode::ValueType(domain)) => {
                self.frames.push(Frame::PiCodomain { at, domain });
                Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(
                    codomain,
                ))))
            },
            | (Frame::PiCodomain { at, domain }, AnyNode::CompType(codomain)) => {
                Ok(self.erased_comp_type(at, target.comp_type_pi(domain, codomain)))
            },
            | (
                Frame::Thunk { .. }
                | Frame::ApplicationHead { .. }
                | Frame::Lambda { .. }
                | Frame::BindBound { .. }
                | Frame::BindBody { .. },
                AnyNode::Value(_) | AnyNode::ValueType(_) | AnyNode::CompType(_),
            )
            | (
                Frame::ThunkType { .. }
                | Frame::QuoteComputation { .. }
                | Frame::ArrowCodomain { .. }
                | Frame::PiCodomain { .. }
                | Frame::Decoded {
                    at: TypeNode::Computation(_),
                },
                AnyNode::Value(_) | AnyNode::Computation(_) | AnyNode::ValueType(_),
            )
            | (
                Frame::Force { .. } | Frame::ApplicationArgument { .. } | Frame::Return { .. },
                AnyNode::Computation(_) | AnyNode::ValueType(_) | AnyNode::CompType(_),
            )
            | (
                Frame::Quote { .. }
                | Frame::LiftedCode { .. }
                | Frame::TypeLift { .. }
                | Frame::DecodeLift { .. }
                | Frame::Returner { .. }
                | Frame::ArrowDomain { .. }
                | Frame::PiDomain { .. }
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
    /// trivial.
    fn erased_value(
        &mut self,
        at: ValueId,
        erased: gandr_kernel_term::ValueId,
    ) -> Step
    {
        self.values.insert(at, Image::Erased(erased));
        Step::Ascend(AnyNode::Value(erased))
    }

    /// Record `erased` as the image of the computation `at`, and ascend it.
    ///
    /// # Specification
    /// trivial.
    fn erased_computation(
        &mut self,
        at: ComputationId,
        erased: gandr_kernel_term::ComputationId,
    ) -> Step
    {
        self.computations.insert(at, Image::Erased(erased));
        Step::Ascend(AnyNode::Computation(erased))
    }

    /// Record `erased` as the image of the value type `at`, and ascend it.
    ///
    /// # Specification
    /// trivial.
    fn erased_value_type(
        &mut self,
        at: ValueTypeId,
        erased: gandr_kernel_term::ValueTypeId,
    ) -> Step
    {
        self.value_types.insert(at, Image::Erased(erased));
        Step::Ascend(AnyNode::ValueType(erased))
    }

    /// Record `erased` as the image of the computation type `at`, and ascend
    /// it.
    ///
    /// # Specification
    /// trivial.
    fn erased_comp_type(
        &mut self,
        at: CompTypeId,
        erased: gandr_kernel_term::CompTypeId,
    ) -> Step
    {
        self.comp_types.insert(at, Image::Erased(erased));
        Step::Ascend(AnyNode::CompType(erased))
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_core_term::Sort;
    use gandr_core_term::SortParameter;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::KernelVerdict;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::AdmissionMark;
    use gandr_kernel_term::AnyNode;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
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
    use super::Outcome;
    use super::Positions;
    use super::Readmission;
    use super::Refusal;
    use super::Replayed;
    use super::Source;
    use super::readmit;
    use super::readmit_with;
    use crate::code::Lift;
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
    /// trivial.
    fn origin(position: At) -> OriginToken
    {
        OriginToken::from(position.0.checked_add(100).unwrap())
    }

    /// The declaration at `position` with these halves.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
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
    /// trivial.
    fn erase(
        arena: &CoreArena,
        root: CoreNode,
    ) -> (TermArena, Result<AnyNode, Refusal>)
    {
        let positions = Positions::default();
        let lifts = alloc::collections::BTreeMap::new();
        let definitions = alloc::collections::BTreeMap::new();
        let mut target = TermArena::new();
        let source = Source {
            arena,
            lifts: &lifts,
            definitions: &definitions,
        };
        let image = Erasure::new(source, &positions).erase(&mut target, root);
        (target, image)
    }

    /// The kernel position the entry at `position` crossed at.
    ///
    /// # Specification
    /// trivial.
    fn crossed_at(
        readmission: &Readmission,
        position: At,
    ) -> ConstantIndex
    {
        match *readmission.readmitted()[position.0].outcome() {
            | Outcome::Defined { admitted, .. } | Outcome::Assumed { admitted, .. } => {
                admitted.position()
            },
            | Outcome::Marked(_) | Outcome::Refused(_) | Outcome::Rejected(_) => {
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
    /// trivial.
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
        let (target, image) = erase(&arena, CoreNode::Term(TermNode::Computation(returned)));
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
        let (target, image) = erase(&arena, CoreNode::Type(TypeNode::Computation(returner)));
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
        let (target, image) = erase(&arena, CoreNode::Term(TermNode::Computation(lambda)));
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
        // The core vocabulary has no unknown type, so the hole is the whole of
        // this class.
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
        let convertible = |position: usize| Replayed {
            constant: ConstantIndex::from(position),
            verdict: KernelVerdict::Convertible,
        };
        assert_eq!(
            readmission.readmitted()[2].certificates(),
            [convertible(0)],
            "the kernel replays the one unfolding the erasure of `Num` took"
        );
        assert_eq!(
            readmission.readmitted()[3].certificates(),
            [convertible(1), convertible(0)],
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
        let convertible = Replayed {
            constant: ConstantIndex::from(0_usize),
            verdict: KernelVerdict::Convertible,
        };
        assert_eq!(
            readmission.readmitted()[3].certificates(),
            [convertible, convertible],
            "the argument unfolds in term position and the declared type at its decode, \
             each certified"
        );
    }

    #[test]
    fn a_declining_certificate_faults_the_declaration()
    {
        // def Num : Type = Integer ; def n : Num = 0 ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let code = arena.value_quote(integer);
        let num = arena.value_constant(ConstantIndex::from(0_usize));
        let decoded = arena.value_type_element(num, Level::zero());
        let zero = arena.value_literal(integer_literal());
        let module = [
            declaration(At(0), Maybe::Present(small), Maybe::Present(code)),
            declaration(At(1), Maybe::Present(decoded), Maybe::Present(zero)),
        ];
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            check_module(&mut context, &module)
        };
        let readmission = readmit_with(&arena, &report, |certificate| {
            certificate.with_decisions(Vec::new())
        });
        let [ref defined, ref faulted] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        assert!(
            matches!(*defined.outcome(), Outcome::Defined { .. }),
            "the code constant itself needs no unfolding"
        );
        let refusal = Refusal::CertificateDeclined {
            constant: ConstantIndex::from(0_usize),
        };
        assert_eq!(
            faulted.outcome(),
            &Outcome::Refused(refusal),
            "an emptied trace does not replay, and the declaration resting on it is refused"
        );
        assert!(
            matches!(faulted.certificates(), [Replayed {
                verdict: KernelVerdict::Declined(_),
                ..
            }]),
            "the kernel's decline travels on the outcome"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::EngineFault,
            "a decline is the engine's"
        );
        assert_eq!(
            readmission.environment().entries().len(),
            1_usize,
            "the refused declaration left the environment as it was"
        );
    }

    #[test]
    fn an_unbound_sealed_atom_is_refused()
    {
        let mut arena = CoreArena::new();
        let atom = arena.value_type_abstract(ConstantIndex::from(3_usize));
        let at = CoreNode::Type(TypeNode::Value(atom));
        let (target, image) = erase(&arena, at);
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
        let unit_type = arena.value_type_unit();
        let returned = arena.computation_return(unit);
        let rows = [
            (
                CoreNode::Term(TermNode::Value(arena.value_pair(unit, unit))),
                UnadmittedFormer::Pair,
            ),
            (
                CoreNode::Term(TermNode::Value(arena.value_injection(Side::Left, unit))),
                UnadmittedFormer::Injection,
            ),
            (
                CoreNode::Term(TermNode::Value(arena.value_lift(Level::zero(), unit))),
                UnadmittedFormer::ValueLift,
            ),
            (
                CoreNode::Term(TermNode::Value(arena.value_literal(numeric_literal()))),
                UnadmittedFormer::NumericLiteral,
            ),
            (
                CoreNode::Term(TermNode::Computation(
                    arena.computation_case(unit, returned, returned),
                )),
                UnadmittedFormer::Case,
            ),
            (
                CoreNode::Type(TypeNode::Value(arena.value_type_base(BaseType::Numeric))),
                UnadmittedFormer::NumericAtom,
            ),
            (
                CoreNode::Type(TypeNode::Value(
                    arena.value_type_product(unit_type, unit_type),
                )),
                UnadmittedFormer::Product,
            ),
            (
                CoreNode::Type(TypeNode::Value(arena.value_type_sum(unit_type, unit_type))),
                UnadmittedFormer::Sum,
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
                erase(&arena, at).1,
                Err(Refusal::OutOfFragment { at, former }),
                "{former:?} is refused by name, at its node"
            );
        }
    }

    #[test]
    fn every_refusal_carries_its_pinned_class()
    {
        let mut arena = CoreArena::new();
        let first_value = arena.value_unit();
        let second_value = arena.value_unit();
        let first_comp = arena.computation_return(first_value);
        let first_type = arena.value_type_unit();
        let returner = arena.comp_type_returner(first_type);
        let rows = [
            (
                Refusal::Withheld {
                    at: first_value,
                    constant: ConstantIndex::from(0_usize),
                },
                Refusal::Withheld {
                    at: second_value,
                    constant: ConstantIndex::from(1_usize),
                },
                FailureClass::MalformedSource,
            ),
            (
                Refusal::OutOfFragment {
                    at: CoreNode::Term(TermNode::Value(first_value)),
                    former: UnadmittedFormer::Pair,
                },
                Refusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Computation(returner)),
                    former: UnadmittedFormer::SortParameter,
                },
                FailureClass::Unrepresentable,
            ),
            (
                Refusal::LinearVariable {
                    at: first_value,
                    index: DeBruijnIndex::from(0_u32),
                },
                Refusal::LinearVariable {
                    at: second_value,
                    index: DeBruijnIndex::from(2_u32),
                },
                FailureClass::EngineFault,
            ),
            (
                Refusal::DanglingNode {
                    node: CoreNode::Term(TermNode::Computation(first_comp)),
                },
                Refusal::DanglingNode {
                    node: CoreNode::Type(TypeNode::Value(first_type)),
                },
                FailureClass::EngineFault,
            ),
            (
                Refusal::Cyclic {
                    node: CoreNode::Term(TermNode::Value(first_value)),
                },
                Refusal::Cyclic {
                    node: CoreNode::Type(TypeNode::Computation(returner)),
                },
                FailureClass::EngineFault,
            ),
            (
                Refusal::CertificateDeclined {
                    constant: ConstantIndex::from(0_usize),
                },
                Refusal::CertificateDeclined {
                    constant: ConstantIndex::from(4_usize),
                },
                FailureClass::EngineFault,
            ),
            (
                Refusal::MachineInvariant,
                Refusal::MachineInvariant,
                FailureClass::EngineFault,
            ),
        ];
        let mut covered = [false; 7];
        for (first, second, class) in rows {
            let row = match first {
                | Refusal::Withheld { .. } => 0_usize,
                | Refusal::OutOfFragment { .. } => 1_usize,
                | Refusal::LinearVariable { .. } => 2_usize,
                | Refusal::DanglingNode { .. } => 3_usize,
                | Refusal::Cyclic { .. } => 4_usize,
                | Refusal::CertificateDeclined { .. } => 5_usize,
                | Refusal::MachineInvariant => 6_usize,
            };
            covered[row] = true;
            assert_eq!(
                (first.classify(), second.classify()),
                (class, class),
                "{first:?} and {second:?} classify as {class}, whatever their payloads"
            );
            assert_ne!(
                class,
                FailureClass::UserAbsence,
                "no bridge refusal may become an obligation"
            );
        }
        assert_eq!(covered, [true; 7], "the table names every variant once");
    }

    #[test]
    fn marks_and_holes_are_refused_beside_their_positive_controls()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let product = arena.value_type_product(integer, integer);
        let zero = arena.value_literal(integer_literal());
        let pair = arena.value_pair(zero, zero);
        let text = arena.value_literal(text_literal());
        let mismatched = arena.value_constant(ConstantIndex::from(5_usize));
        let module = [
            // def control : Integer = 0 ;
            declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
            // def marked_body : Integer * Integer = (0, 0) ;
            declaration(At(1), Maybe::Present(product), Maybe::Present(pair)),
            // def owed : Integer ;
            declaration(At(2), Maybe::Present(integer), HOLE),
            // def marked_hole : Integer * Integer ;
            declaration(At(3), Maybe::Present(product), HOLE),
            // def hole ;
            declaration(At(4), UNSIGNED, HOLE),
            // def mismatched : Integer = "" ;
            declaration(At(5), Maybe::Present(integer), Maybe::Present(text)),
            // def dependent : Integer = mismatched ;
            declaration(At(6), Maybe::Present(integer), Maybe::Present(mismatched)),
        ];
        let (report, readmission) = judge_and_readmit(&mut arena, &module);
        for (entry, offered) in readmission.readmitted().iter().zip(&module) {
            assert_eq!(
                (entry.constant(), entry.origin()),
                (offered.constant(), offered.origin()),
                "every outcome is located at its declaration's origin"
            );
        }
        let [
            ref control,
            ref marked_body,
            ref owed,
            ref marked_hole,
            ref hole,
            ref mismatched_entry,
            ref dependent,
        ] = *readmission.readmitted()
        else {
            panic!("one outcome per declaration");
        };
        let product_mark = CheckRefusal::OutOfFragment {
            at: CoreNode::Type(TypeNode::Value(product)),
            former: UnadmittedFormer::Product,
        };
        assert!(
            matches!(*control.outcome(), Outcome::Defined { .. }),
            "the positive control for a mark crosses as a definition"
        );
        assert!(
            matches!(*owed.outcome(), Outcome::Assumed { .. }),
            "the positive control for a hole crosses as an axiom"
        );
        assert_eq!(
            marked_body.outcome(),
            &Outcome::Marked(product_mark),
            "a marked body crosses as nothing, though the kernel alone admits it"
        );
        assert_eq!(
            marked_hole.outcome(),
            &Outcome::Marked(product_mark),
            "a marked signed hole crosses as no axiom, though the kernel alone admits one"
        );
        assert_eq!(
            hole.outcome(),
            &Outcome::Marked(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Hole(ConstantIndex::from(4_usize)),
            }),
            "a hole in synthesis position is refused naming the hole"
        );
        assert!(
            matches!(
                *mismatched_entry.outcome(),
                Outcome::Marked(CheckRefusal::TypeMismatch(Mismatch::Value { .. }))
            ),
            "an ill-typed body is marked with its mismatch"
        );
        assert!(
            matches!(report.judged()[6].verdict(), Verdict::Checked { .. }),
            "the judgement accepts the dependent through the declared type"
        );
        assert_eq!(
            dependent.outcome(),
            &Outcome::Refused(Refusal::Withheld {
                at: mismatched,
                constant: ConstantIndex::from(5_usize),
            }),
            "a reference to a marked declaration is withheld, located at the reference"
        );
        assert_eq!(
            (
                crossed_at(&readmission, At(0)),
                crossed_at(&readmission, At(2)),
                readmission.environment().entries().len()
            ),
            (
                ConstantIndex::from(0_usize),
                ConstantIndex::from(1_usize),
                2_usize
            ),
            "the two positive controls, and nothing else, entered the kernel"
        );
        assert_eq!(
            readmission.audit().axioms(),
            [ConstantIndex::from(1_usize)],
            "the artifact rests on the owed hole's axiom alone"
        );
        // The kernel alone admits the content of both marked declarations, so
        // the refusals above are the bridge's.
        let mut kernel = Environment::new();
        let mut staging = kernel.stage();
        let target = staging.arena();
        let kernel_integer = target.value_type_base(BaseType::Integer);
        let kernel_product = target.value_type_product(kernel_integer, kernel_integer);
        let kernel_zero = target.value_literal(integer_literal());
        let kernel_pair = target.value_pair(kernel_zero, kernel_zero);
        let definition = staging.def(LevelSignature::monomorphic(), kernel_product, kernel_pair);
        assert!(
            kernel.add_decl(definition).is_ok(),
            "the kernel admits the marked body's content"
        );
        let mut staging = kernel.stage();
        let target = staging.arena();
        let kernel_integer = target.value_type_base(BaseType::Integer);
        let kernel_product = target.value_type_product(kernel_integer, kernel_integer);
        let axiom = staging.axiom(LevelSignature::monomorphic(), kernel_product);
        assert!(
            kernel.add_decl(axiom).is_ok(),
            "the kernel admits the marked hole's content as an axiom"
        );
    }

    #[test]
    fn an_empty_ledger_readmits_an_artifact_resting_on_no_axiom()
    {
        // def answer : Integer = 0 ; def copy = answer ;
        // def pair : Integer * Integer ;
        //
        // The signed hole's signature does not form, so it is marked rather
        // than owed, and the ledger is empty.
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let product = arena.value_type_product(integer, integer);
        let zero = arena.value_literal(integer_literal());
        let answer = arena.value_constant(ConstantIndex::from(0_usize));
        let (report, readmission) = judge_and_readmit(&mut arena, &[
            declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
            declaration(At(1), UNSIGNED, Maybe::Present(answer)),
            declaration(At(2), Maybe::Present(product), HOLE),
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
                | Outcome::Defined { ref audit, .. } | Outcome::Assumed { ref audit, .. } => {
                    audit.axioms().to_vec()
                },
                | Outcome::Marked(_) | Outcome::Refused(_) | Outcome::Rejected(_) => {
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
        let (_, readmission) = judge_and_readmit(&mut arena, &[
            crossing[0],
            declaration(At(1), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(2), Maybe::Present(suspended), Maybe::Present(applied)),
            crossing[1],
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
        let (target, image) = erase(&arena, CoreNode::Term(TermNode::Computation(second)));
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
            erase(&arena, CoreNode::Term(TermNode::Value(linear))).1,
            Err(Refusal::LinearVariable {
                at: linear,
                index: DeBruijnIndex::from(0_u32),
            }),
            "a linear variable has no kernel zone to count in"
        );
        let dangling = CoreNode::Term(TermNode::Value(dangling_value()));
        assert_eq!(
            erase(&arena, dangling).1,
            Err(Refusal::DanglingNode { node: dangling }),
            "a dangling term is refused, not read"
        );
        let dangling = CoreNode::Type(TypeNode::Value(dangling_value_type()));
        assert_eq!(
            erase(&arena, dangling).1,
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
            erase(&cyclic, node).1,
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
            arena: &arena,
            lifts: &lifts,
            definitions: &definitions,
        };
        assert_eq!(
            Erasure::new(source, &positions).resume(
                &mut target,
                Frame::Lambda { at: returned },
                AnyNode::Value(unit),
            ),
            Err(Refusal::MachineInvariant),
            "a frame handed an image of another family reports the miscount"
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
    /// trivial.
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
    /// trivial.
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
                        certificate.constant()
                    );
                }
            }
        }
    }
}
