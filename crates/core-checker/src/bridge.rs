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
//! Bruijn indices, admission positions — so erasing a node mints the kernel
//! node of the same former over its children's images. Two things are
//! remapped: a node to the node its image is in the kernel arena, and a
//! module's admission position to the position its declaration took in the
//! kernel environment, which differs once an earlier declaration did not
//! cross. Erasure covers the fragment the judgement has rules for, reads types
//! through the same views the judgement does, and refuses every other former by
//! name. Each distinct node is erased once per declaration, so the kernel sees
//! the sharing the producer built and no more.
//!
//! # An uncompleted signature enters as an axiom
//!
//! An owed hole is a declaration with a type and no body, which is exactly the
//! kernel's bodiless declaration: it is staged through [`Staging::axiom`], and
//! the hole never becomes a term. A hole the judgement refused — in synthesis
//! position, where its refusal names the hole, or under a signature that did
//! not form — crosses as nothing.
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
//! refused erasure discards it; a rejected admission is truncated by the
//! kernel's choke point. A declaration that does not cross leaves the
//! environment as it found it.
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

use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_core::AxiomReport;
use gandr_kernel_core::CheckedId;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::TermArena;

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
    ///   cyclic node and a machine invariant are engine faults, because a
    ///   judged term from the judged arena holds none of them; nothing is a
    ///   user absence.
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

/// One declaration's outcome, beside the position and origin the judgement
/// echoed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Readmitted
{
    /// The declaration's module position.
    constant: ConstantIndex,
    /// The declaration's origin, echoed back.
    origin: OriginToken,
    /// What became of it.
    outcome: Outcome,
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
/// declaration, and the artifact's audit.
#[derive(Clone, Debug)]
pub struct Readmission
{
    /// The environment every crossing declaration was admitted into.
    environment: Environment,
    /// One entry per judged declaration, in the report's order.
    readmitted: Vec<Readmitted>,
    /// The union of the admitted declarations' audits.
    audit: ArtifactAudit,
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
///   for it. An offer whose erasure refuses is [`Outcome::Refused`], one the
///   kernel rejects [`Outcome::Rejected`], and either leaves the environment as
///   it was. A constant naming a declaration that crossed is erased to the
///   kernel position that declaration took.
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
///   crosses, and the artifact's axioms agree with the ledger entry for entry
///   in both directions. The L3 residues are the routing of each verdict,
///   separated by one artifact holding a marked body and a marked signed hole
///   the kernel alone admits, a hole in synthesis position and a reference to a
///   marked declaration, beside a checked and an owed positive control; the
///   position remapping, separated by a module whose later references would
///   misresolve under any other map; and the rollback, separated by a refusal
///   met after part of a body was minted.
/// - witness: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `bridge::tests::every_checked_function_definition_is_readmitted`
/// - witness: `bridge::tests::marks_and_holes_are_refused_beside_their_positive_controls`
/// - witness: `bridge::tests::an_empty_ledger_readmits_an_artifact_resting_on_no_axiom`
/// - witness: `bridge::tests::each_owed_hole_is_an_axiom_of_the_artifact`
/// - witness: `bridge::tests::a_constant_resolves_to_its_readmitted_position`
/// - witness: `bridge::tests::a_refused_declaration_leaves_the_environment_unchanged`
/// - witness: `bridge::tests::a_lowered_value_definition_admits`
/// - witness: `bridge::tests::a_lowered_computation_definition_admits`
/// - witness: `bridge::tests::a_constant_reference_across_declarations_admits`
#[inline]
#[must_use]
pub fn readmit(
    arena: &CoreArena,
    report: &ModuleReport,
) -> Readmission
{
    let mut environment = Environment::new();
    let mut positions = Positions::default();
    let mut readmitted = Vec::with_capacity(report.judged().len());
    for judged in report.judged() {
        let outcome = match judged.verdict() {
            | Verdict::Checked { declared, body, .. } => {
                cross(&mut environment, arena, &positions, Offer::Definition {
                    declared: declared.id(),
                    body,
                })
            },
            | Verdict::Synthesised { body, synthesised } => {
                cross(&mut environment, arena, &positions, Offer::Definition {
                    declared: synthesised.produced().id(),
                    body,
                })
            },
            | Verdict::Owed(entry) => cross(&mut environment, arena, &positions, Offer::Axiom {
                declared: entry.absence().declared().id(),
            }),
            | Verdict::Refused(refusal) => Outcome::Marked(refusal),
        };
        if let Outcome::Defined { admitted, .. } | Outcome::Assumed { admitted, .. } = outcome {
            positions.record(judged.constant(), admitted);
        }
        readmitted.push(Readmitted {
            constant: judged.constant(),
            origin: judged.origin(),
            outcome,
        });
    }
    let audit = ArtifactAudit::of(&readmitted);
    Readmission {
        environment,
        readmitted,
        audit,
    }
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

/// Erase `offer` into a staging session of `environment` and admit it.
///
/// # Specification
/// - requires: `positions` holds the kernel position of every module
///   declaration that crossed so far.
/// - ensures: the offer erased into one staging session and admitted:
///   [`Outcome::Defined`] for a definition and [`Outcome::Assumed`] for an
///   axiom, each with the kernel's receipt and audit, when the kernel admits
///   it. A refused erasure discards the session and a rejection is truncated by
///   the kernel, so the environment is as it was on every outcome but an
///   admission.
/// - fails: never; a refusal is [`Outcome::Refused`] and a rejection
///   [`Outcome::Rejected`].
/// - panics: none.
fn cross(
    environment: &mut Environment,
    source: &CoreArena,
    positions: &Positions,
    offer: Offer,
) -> Outcome
{
    let mut staging = environment.stage();
    let erased = Erasure::new(source, positions).offer(staging.arena(), offer);
    let staged = match erased {
        | Ok(Erased::Definition { declared, body }) => {
            staging.def(LevelSignature::monomorphic(), declared, body)
        },
        | Ok(Erased::Axiom { declared }) => staging.axiom(LevelSignature::monomorphic(), declared),
        | Err(refusal) => {
            staging.discard();
            return Outcome::Refused(refusal);
        },
    };
    let admitted = match environment.add_decl(staged) {
        | Ok(admitted) => admitted,
        | Err(error) => return Outcome::Rejected(error),
    };
    let audit = environment.audit(admitted);
    match offer {
        | Offer::Definition { .. } => Outcome::Defined { admitted, audit },
        | Offer::Axiom { .. } => Outcome::Assumed { admitted, audit },
    }
}

/// The kernel position each module declaration that crossed took.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Positions
{
    /// Module position to kernel position.
    admitted: BTreeMap<ConstantIndex, ConstantIndex>,
}

impl Positions
{
    /// Record that the module declaration at `constant` crossed as `admitted`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Self::kernel_position`] answers `admitted`'s position for
    ///   `constant`.
    /// - panics: none.
    fn record(
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Frame
{
    /// A thunk, awaiting its body's computation.
    Thunk
    {
        /// The thunk.
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

/// One declaration's erasure: the arena it reads, the positions constants
/// resolve through, the frames waiting, and every node's image so far.
struct Erasure<'source, 'positions>
{
    /// The arena every id the erasure reads resolves in.
    source: &'source CoreArena,
    /// The kernel positions of the declarations that crossed before this one.
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
}

impl<'source, 'positions> Erasure<'source, 'positions>
{
    /// An erasure reading `source`, resolving constants through `positions`,
    /// with nothing reached.
    ///
    /// # Specification
    /// trivial.
    const fn new(
        source: &'source CoreArena,
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
        mut self,
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
    ///   of its children, recursively, with every literal, base type and de
    ///   Bruijn index carried unchanged and every constant replaced by the
    ///   kernel position its declaration took. A node already erased by this
    ///   machine is not minted again.
    /// - fails: [`Refusal::Withheld`] for a constant whose declaration did not
    ///   cross; [`Refusal::OutOfFragment`] for a former the fragment has no
    ///   rule for; [`Refusal::LinearVariable`] for a linear-zone variable;
    ///   [`Refusal::DanglingNode`] for an id `source` does not hold;
    ///   [`Refusal::Cyclic`] for a node reached again while its own erasure
    ///   waits. Nodes minted before the refusal stay in `target`; the caller
    ///   owns the arena and its rollback.
    /// - panics: none.
    /// - intension: one kernel node is minted per distinct core node reached,
    ///   so sharing in the source is sharing in the image.
    ///
    /// # Errors
    /// - [`Refusal::Withheld`], [`Refusal::OutOfFragment`],
    ///   [`Refusal::LinearVariable`], [`Refusal::DanglingNode`],
    ///   [`Refusal::Cyclic`] — as above.
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
    /// - witness: `bridge::tests::value_universe_rejects_with_universe_type`
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
            | CoreNode::Type(TypeNode::Computation(at)) => self.descend_comp_type(at),
        }
    }

    /// Start erasing the value `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::descend`]: an intuitionistic variable, a constant
    ///   that crossed, the unit value and an integer or string literal are
    ///   minted; a thunk opens its frame.
    /// - fails: [`Refusal::Cyclic`] for an open value;
    ///   [`Refusal::DanglingNode`]; [`Refusal::LinearVariable`];
    ///   [`Refusal::Withheld`]; [`Refusal::OutOfFragment`] for a numeric
    ///   literal, a pair, an injection or a value lift.
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
        let Some(value) = self.source.value(at)
        else {
            return Err(Refusal::DanglingNode { node });
        };
        let unadmitted = |former| Refusal::OutOfFragment { at: node, former };
        let erased = match *value {
            | Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            } => target.value_variable(index),
            | Value::Variable {
                zone: Zone::Linear,
                index,
            } => return Err(Refusal::LinearVariable { at, index }),
            | Value::Constant(constant) => {
                let position = self.positions.kernel_position(at, constant)?;
                target.value_constant(position)
            },
            | Value::Unit => target.value_unit(),
            | Value::Literal(ref literal) => match literal.base_type() {
                | BaseType::Integer | BaseType::String => target.value_literal(literal.clone()),
                | BaseType::Numeric => return Err(unadmitted(UnadmittedFormer::NumericLiteral)),
            },
            | Value::Thunk(body) => {
                self.values.insert(at, Image::Open);
                self.frames.push(Frame::Thunk { at });
                return Ok(Step::Descend(CoreNode::Term(TermNode::Computation(body))));
            },
            | Value::Pair(..) => return Err(unadmitted(UnadmittedFormer::Pair)),
            | Value::Injection(..) => return Err(unadmitted(UnadmittedFormer::Injection)),
            | Value::Lift { .. } => return Err(unadmitted(UnadmittedFormer::ValueLift)),
            | Value::Quote(_) | Value::QuoteComputation(_) => {
                return Err(unadmitted(UnadmittedFormer::Quote));
            },
        };
        Ok(self.erased_value(at, erased))
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
        let Some(computation) = self.source.computation(at)
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
    /// - ensures: as [`Self::descend`]: the integer and string atoms and the
    ///   unit type are minted; a thunk type opens its frame.
    /// - fails: [`Refusal::Cyclic`] for an open value type; whatever the view
    ///   refuses, converted.
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
        let view = value_type_view(self.source, at)?;
        let erased = match view {
            | ValueTypeView::Integer => target.value_type_base(BaseType::Integer),
            | ValueTypeView::String => target.value_type_base(BaseType::String),
            | ValueTypeView::Unit => target.value_type_unit(),
            | ValueTypeView::Thunk(body) => {
                self.value_types.insert(at, Image::Open);
                self.frames.push(Frame::ThunkType { at });
                return Ok(Step::Descend(CoreNode::Type(TypeNode::Computation(body))));
            },
        };
        self.value_types.insert(at, Image::Erased(erased));
        Ok(Step::Ascend(AnyNode::ValueType(erased)))
    }

    /// Start erasing the computation type `at`, read through the fragment's
    /// view.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::descend`]: a returner and an arrow open their
    ///   frames.
    /// - fails: [`Refusal::Cyclic`] for an open computation type; whatever the
    ///   view refuses, converted.
    /// - panics: none.
    fn descend_comp_type(
        &mut self,
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
        let view = comp_type_view(self.source, at)?;
        let (frame, child) = match view {
            | CompTypeView::Returner(result) => (Frame::Returner { at }, result),
            | CompTypeView::Arrow { domain, codomain } => {
                (Frame::ArrowDomain { at, codomain }, domain)
            },
        };
        self.comp_types.insert(at, Image::Open);
        self.frames.push(frame);
        Ok(Step::Descend(CoreNode::Type(TypeNode::Value(child))))
    }

    /// Hand `image` to the rule `frame` holds.
    ///
    /// # Specification
    /// - requires: `frame` was pushed by this machine.
    /// - ensures: a frame awaiting its last child mints its node over the
    ///   children's images, records the image and ascends it; an application, a
    ///   bind or an arrow awaiting its first child descends to its second.
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
            | (Frame::Force { at }, AnyNode::Value(value)) => {
                Ok(self.erased_computation(at, target.computation_force(value)))
            },
            | (Frame::ApplicationHead { at, argument }, AnyNode::Computation(head)) => {
                self.frames.push(Frame::ApplicationArgument { at, head });
                Ok(Step::Descend(CoreNode::Term(TermNode::Value(argument))))
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
                let erased = target.value_type_thunk(body);
                self.value_types.insert(at, Image::Erased(erased));
                Ok(Step::Ascend(AnyNode::ValueType(erased)))
            },
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
            | (
                Frame::Thunk { .. }
                | Frame::ApplicationHead { .. }
                | Frame::Lambda { .. }
                | Frame::BindBound { .. }
                | Frame::BindBody { .. },
                AnyNode::Value(_) | AnyNode::ValueType(_) | AnyNode::CompType(_),
            )
            | (
                Frame::Force { .. } | Frame::ApplicationArgument { .. } | Frame::Return { .. },
                AnyNode::Computation(_) | AnyNode::ValueType(_) | AnyNode::CompType(_),
            )
            | (
                Frame::ThunkType { .. } | Frame::ArrowCodomain { .. },
                AnyNode::Value(_) | AnyNode::Computation(_) | AnyNode::ValueType(_),
            )
            | (
                Frame::Returner { .. } | Frame::ArrowDomain { .. },
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
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_core_term::Sort;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_core::Environment;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::AnyNode;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::TermArena;
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
    use super::readmit;
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
        let mut target = TermArena::new();
        let image = Erasure::new(arena, &positions).erase(&mut target, root);
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
    fn value_universe_rejects_with_universe_type()
    {
        let mut arena = CoreArena::new();
        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let at = CoreNode::Type(TypeNode::Value(universe));
        let (_, image) = erase(&arena, at);
        assert_eq!(
            image,
            Err(Refusal::OutOfFragment {
                at,
                former: UnadmittedFormer::Universe,
            }),
            "a universe is refused by name"
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
    fn every_former_outside_the_fragment_is_refused_by_name()
    {
        // The universe and the abstract atom are witnessed by their own tests.
        let mut arena = CoreArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let returned = arena.computation_return(unit);
        let returner = arena.comp_type_returner(unit_type);
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
                CoreNode::Type(TypeNode::Value(
                    arena.value_type_lift(unit_type, Level::zero()),
                )),
                UnadmittedFormer::TypeLift,
            ),
            (
                CoreNode::Type(TypeNode::Value(
                    arena.value_type_element(unit, Level::zero()),
                )),
                UnadmittedFormer::Element,
            ),
            (
                CoreNode::Type(TypeNode::Computation(
                    arena.comp_type_pi(unit_type, returner),
                )),
                UnadmittedFormer::Pi,
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
                    former: UnadmittedFormer::Pi,
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
                Refusal::MachineInvariant,
                Refusal::MachineInvariant,
                FailureClass::EngineFault,
            ),
        ];
        let mut covered = [false; 6];
        for (first, second, class) in rows {
            let row = match first {
                | Refusal::Withheld { .. } => 0_usize,
                | Refusal::OutOfFragment { .. } => 1_usize,
                | Refusal::LinearVariable { .. } => 2_usize,
                | Refusal::DanglingNode { .. } => 3_usize,
                | Refusal::Cyclic { .. } => 4_usize,
                | Refusal::MachineInvariant => 5_usize,
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
        assert_eq!(covered, [true; 6], "the table names every variant once");
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
        let mut target = TermArena::new();
        let unit = target.value_unit();
        let returned = arena.computation_return(linear);
        assert_eq!(
            Erasure::new(&arena, &positions).resume(
                &mut target,
                Frame::Lambda { at: returned },
                AnyNode::Value(unit),
            ),
            Err(Refusal::MachineInvariant),
            "a frame handed an image of another family reports the miscount"
        );
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
    }
}
