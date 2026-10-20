//! An item's typing: the checker's verdict, projected to a form free of arena
//! ids and admission positions.
//!
//! # A coordinate change, nothing more
//!
//! A [`Verdict`] names arena ids and positions, which differ between two runs
//! over two arenas even when the runs agree. The projection replaces each id
//! with the content it names — a term node with its index in the item's
//! table, a type with its type table — and each position with the reference
//! it resolves to. Two runs agree exactly when their projections are equal,
//! which is what "incremental equals batch" compares. The origin token is not
//! projected: it is the producer's coordinate for the item, echoed from the
//! edited declaration, never reused from a checkpoint.

use anodized::spec;
use gandr_core_checker::ArgumentPosition;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::ConversionCount;
use gandr_core_checker::CoreNode;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::Mismatch;
use gandr_core_checker::StaticArity;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::Verdict;
use gandr_core_checker::session::Capture;
use gandr_core_checker::session::Endpoint;
use gandr_core_checker::session::ForkSide;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_checker::session::ProtocolDefect;
use gandr_core_term::BinderDepth;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::Stage;
use gandr_kernel_term::Standing;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemOrdinal;
use crate::boundary::NodeIndex;
use crate::content::ArenaNode;
use crate::content::Sites;
use crate::content::TypeContent;
use crate::content::TypeMemo;
use crate::content::encode_item;
use crate::region::Layout;
use crate::region::Program;
use crate::region::Reference;

/// Where in its item a refusal stood.
///
/// # Specification
/// - requires: a node site is interpreted against its associated item's table.
/// - ensures: a reached node names its table index; an unreached node invents
///   no index. The variant alone does not certify an arbitrary index.
/// - executable: none — this declaration has no call boundary; the owning table
///   and arena-node correspondence are external to a stored site.
///
/// # Adequacy
/// - hypothesis: L3 — the projection witnesses use fixed breadth-first table
///   coordinates for all four arena-node sorts and a node outside the walk.
///   They certify projected sites, not arbitrary constructed indices.
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Site
{
    /// The node at this index of the item's table.
    Node(NodeIndex),
    /// A node the item's walk did not reach; the judgement names none, and the
    /// projection stays total without inventing an index.
    Unreached,
}

/// A checking-only form met where a type had to be synthesised.
///
/// # Specification
/// - requires: a projected checking form is interpreted in its item's table.
/// - ensures: projection retains the checking-only former and its site, or the
///   hole marker without the producer's origin coordinate.
/// - executable: none — this declaration has no call boundary; the source
///   checking form and its arena are not part of a stored value.
///
/// # Adequacy
/// - hypothesis: L3 — real hole and thunk refusals and structural lambda,
///   return and static-lambda payloads separate the five tags and their node
///   sorts. The structural corpus does not establish checker reachability.
/// - witness: `typing::tests::each_verdict_projects_to_its_typing`
/// - witness: `typing::tests::each_refusal_projects_its_payload`
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Form
{
    /// A literal stack.
    Reify(Site),
    /// A deep handler.
    Handle(Site),
    /// An answer delimiter.
    Reset(Site),
    /// A continuation capture.
    Shift(Site),
    /// A lazy pair.
    With(Site),
    /// A native List introduction.
    List(Site),
    /// A sum injection.
    Injection(Site),
    /// A sum case.
    Case(Site),
    /// A product split.
    Split(Site),
    /// A thunk.
    Thunk(Site),
    /// A lambda.
    Lambda(Site),
    /// A return.
    Return(Site),
    /// A static lambda.
    StaticLambda(Site),
    /// The item's own hole.
    Hole,
    /// A fixpoint.
    Fixpoint(Site),
    /// A computation written where a value is read.
    Nested(Site),
    /// An offer.
    Offer(Site),
    /// A capability scope.
    Scope(Site),
    /// A recorded run.
    Run(Site),
}

/// An endpoint, by the site of the fork that bound it and its side.
///
/// # Specification
/// - requires: the fork's site is interpreted in its item's table.
/// - ensures: projection keeps the side and maps the fork to its item site.
/// - executable: none — this declaration has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a residue at a fork's child end projects the fork's item
///   site and the side.
/// - witness: `typing::tests::session_refusals_project_their_endpoints_and_states`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EndpointSite
{
    /// The fork.
    pub fork: Site,
    /// Which of its ends.
    pub side: ForkSide,
}

/// How an endpoint escaped its one linear use, projected: endpoints and arms
/// as item sites, a residue's session type as its own type table.
///
/// # Specification
/// - requires: sites are interpreted in their item's table.
/// - ensures: projection preserves the defect kind and its scalar payloads.
/// - executable: none — this declaration has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a residue and an arm disagreement project their endpoint,
///   state and arm sites.
/// - witness: `typing::tests::session_refusals_project_their_endpoints_and_states`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Linearity
{
    /// A half of a fork finished with the endpoint unconsumed.
    Residue
    {
        /// The endpoint.
        endpoint: EndpointSite,
        /// Its session type when the half finished.
        state: TypeContent,
    },
    /// The endpoint was acted on after it was closed.
    Closed
    {
        /// The endpoint.
        endpoint: EndpointSite,
    },
    /// The endpoint was used twice in one action.
    UsedTwice
    {
        /// The endpoint.
        endpoint: EndpointSite,
    },
    /// The endpoint was named where its use may run other than once.
    Captured
    {
        /// The endpoint.
        endpoint: EndpointSite,
        /// What may run it.
        by: Capture,
    },
    /// An endpoint, or a session type, was sent as a payload.
    Delegated,
    /// The endpoint was read as a value outside an action.
    AsValue
    {
        /// The endpoint.
        endpoint: EndpointSite,
    },
    /// Two arms of an offer left the endpoint in different states.
    ArmsDisagree
    {
        /// The endpoint.
        endpoint: EndpointSite,
        /// The first arm.
        first: Site,
        /// The arm that disagrees with it.
        other: Site,
    },
    /// A declaration's type is a session type.
    Unrestricted,
    /// An action names a linear index no fork bound.
    Unbound
    {
        /// The index.
        index: DeBruijnIndex,
    },
}

/// The world a located refusal names, projected: the host's, or the
/// reference of the world declaration.
///
/// # Specification
/// - executable: none — this declaration has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a missing capability projects its declared world.
/// - witness: `typing::tests::a_located_refusal_projects_its_worlds_and_types`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Place
{
    /// The host's world.
    Host,
    /// The world the declaration at this reference declares.
    Declared(Reference),
}

/// How a located judgement broke, projected: types as their own tables,
/// worlds and positions as references.
///
/// # Specification
/// - requires: tables are interpreted in their own coordinates.
/// - ensures: projection preserves the defect kind and its scalar payloads.
/// - executable: none — this declaration has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a missing capability and an unfounded mark project their
///   world, atom and former.
/// - witness: `typing::tests::a_located_refusal_projects_its_worlds_and_types`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Located
{
    /// A value crosses to a world where its type does not.
    Immobile
    {
        /// What crosses.
        crossed: gandr_core_checker::worlds::Crossed,
        /// Its type.
        ty: TypeContent,
        /// The former that fails.
        former: TypeContent,
        /// The predicate it fails.
        predicate: gandr_core_checker::worlds::Predicate,
    },
    /// A migration found no capability for its world.
    CapabilityMissing
    {
        /// The world migrated to.
        world: Place,
    },
    /// A migration under a former that may run it other than once.
    CapabilityCaptured
    {
        /// The world migrated to.
        world: Place,
        /// What may run it again.
        by: Capture,
    },
    /// A hypothesis or a resident used at a world other than its own.
    Elsewhere
    {
        /// The world it was bound at.
        bound: Place,
    },
    /// A hold checked against a handle at another world.
    HoldElsewhere
    {
        /// The world the handle was wanted at.
        wanted: Place,
    },
    /// A hold or a `leta` at the host's world.
    Unlocated,
    /// A world position no world declaration holds.
    UndeclaredWorld
    {
        /// The position named.
        world: Reference,
    },
    /// The host's entry names a world the source declares nowhere.
    HostWorldUndeclared,
    /// A `mobile` mark over a representation that does not cross.
    MarkUnfounded
    {
        /// The abstract type.
        atom: Reference,
        /// The former that fails.
        former: TypeContent,
        /// The predicate it fails.
        predicate: gandr_core_checker::worlds::Predicate,
    },
    /// An entry named from another declaration.
    EntryNamed
    {
        /// The entry.
        constant: Reference,
    },
    /// A stated entry the host's does not hold.
    EntryUngranted
    {
        /// The declaration stating it.
        constant: Reference,
    },
    /// A `leta` of a value whose type is no handle.
    NotAHandle
    {
        /// The type the value synthesised.
        found: TypeContent,
    },
}

/// A refusal, projected.
///
/// # Specification
/// - requires: a projected refusal is interpreted in its item's table and
///   reference layout; type tables use their own discovery coordinates.
/// - ensures: projection preserves the refusal kind, semantic payloads and
///   mapped sites, omitting only admission-order positions and origins.
/// - executable: none — this declaration has no call boundary; a stored refusal
///   does not retain the source judgement or coordinate context.
///
/// # Adequacy
/// - hypothesis: L3 — real checking refusals and a finite structural payload
///   corpus distinguish item sites, independent type-table roots, named and
///   unoccupied references, classifier direction and arity direction. The
///   corpus does not certify arbitrary stored values or establish that the
///   checker emits each structural case. Internal admission-order and
///   machine-invariant refusals remain outside its witnessed domain.
/// - witness: `typing::tests::each_refusal_projects_its_payload`
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Refusal
{
    /// The nominal identity has no admitted signature.
    NotADataType(Reference),
    /// The declaration kind is not a value universe.
    DataKindNotUniverse(Site),
    /// A constructor field exceeds the declaration universe.
    DataFieldLevel
    {
        /// The offending field classifier.
        field: Site,
        /// The declared universe.
        kind: TypeContent,
    },
    /// A data declaration's rules do not present its type.
    RuleNotPresentable
    {
        /// The declaration's universe, which locates the declaration.
        kind: Site,
        /// The first rule that does not present the type, and why.
        refusal: gandr_kernel_term::RuleRefusal,
    },
    /// A case over a presented type is not shown to respect a rule. The rule's
    /// two sides the checker built are not kept: the rule rebuilds them, and
    /// they are no source site.
    RuleNotRespected
    {
        /// The case.
        at: Site,
        /// The first rule the case is not shown to respect.
        rule: gandr_kernel_term::RuleIndex,
    },
    /// A case of no branches over a path whose endpoints are not shown apart.
    NotApart
    {
        /// The case.
        at: Site,
        /// Why the endpoints are not apart.
        reason: gandr_kernel_term::Apartness,
    },
    /// A case over a sort its words loop at is not shown to respect a loop.
    /// The two sides the checker built are not kept: the loop rebuilds them,
    /// and they are no source site.
    LoopNotRespected
    {
        /// The case.
        at: Site,
        /// The first loop the case is not shown to respect.
        cell: gandr_kernel_term::CellIndex,
        /// Why the loop is not shown respected.
        reason: gandr_core_checker::LoopRespect,
    },
    /// A case's obligation for a loop ran past the budget of the conversion
    /// that decides it.
    LoopUndecided
    {
        /// The case.
        at: Site,
        /// The loop whose obligation was left undecided.
        cell: gandr_kernel_term::CellIndex,
    },
    /// A nominal application has the wrong parameter count.
    DataArgumentArity(Site),
    /// A constructor tag is absent from its declaration.
    UnknownConstructor
    {
        /// The constructor value.
        at: Site,
        /// The unknown tag.
        tag: gandr_core_term::ConstructorTag,
    },
    /// A constructor has the wrong field count.
    ConstructorArity(Site),
    /// A case scrutinises a value of an indexed family.
    IndexedCase(Site),
    /// A case has the wrong branch count.
    NonExhaustiveDataCase(Site),
    /// A leaf of a match's tree is one of its pattern holes.
    UndecidedCoverage(Site),
    /// A projection names no field in its operand's type.
    AbsentRecordField(Site),
    /// A tuple projection names a component past its operand's arity.
    AbsentTupleComponent(Site),
    /// A record omits a required field.
    MissingRecordField
    {
        /// The record value.
        at: Site,
        /// The required record classifier.
        expected: TypeContent,
    },
    /// An operation absent from its inline interface.
    UnknownOperation
    {
        /// The request.
        at: Site,
    },
    /// A handler's clauses do not cover its interface exactly.
    HandlerCoverage
    {
        /// The handler.
        at: Site,
    },
    /// A capture has no enclosing answer delimiter.
    ShiftWithoutReset
    {
        /// The capture.
        at: Site,
    },
    /// A stack frame's result depends on its discharged value binder.
    DependentStack
    {
        /// The stack literal.
        at: Site,
        /// The escaping computation type.
        synthesised: TypeContent,
    },
    /// A native path endpoint is not a closed first-order code.
    PathCode(Site),
    /// Reflexivity met a path type whose endpoints its point does not both
    /// convert to.
    EndpointMismatch
    {
        /// The reflexivity.
        at: Site,
        /// The path type's left endpoint.
        left: Site,
        /// The path type's right endpoint.
        right: Site,
    },
    /// A compound endpoint whose computation returns no pure value.
    CompoundEndpoint
    {
        /// The compound endpoint.
        at: Site,
        /// The type its computation synthesised.
        synthesised: TypeContent,
    },
    /// A function extensionality past the first-order boundary: open
    /// functions, whose free variables no coverage reaches; a classifier that
    /// is no thunk of a pure non-dependent arrow; or a result, or a function
    /// argument's domain or result, outside the first-order fragment whose
    /// coverage is finite by the description codes' decidability choice.
    FunextUnsupported
    {
        /// The function extensionality.
        at: Site,
        /// The type its first function synthesised.
        classifier: TypeContent,
    },
    /// A function extensionality whose functions are not identified: they
    /// disagree at some covering input, the rule's verdict rather than a gap.
    PointwiseDistinct(Site),
    /// A universe equivalence the rule does not decide: open translators, a
    /// classifier that is no thunk of a pure non-dependent arrow, or a code
    /// outside the universe-path vocabulary.
    EquivUnsupported
    {
        /// The universe equivalence.
        at: Site,
        /// The forward translator's type, or the code the coverage stopped at.
        classifier: TypeContent,
    },
    /// A universe equivalence over a recursive code.
    UncertifiedStratum
    {
        /// The universe equivalence.
        at: Site,
        /// The List code the coverage reached.
        code: TypeContent,
    },
    /// A universe equivalence one of whose round trips does not return its
    /// input at some covering pattern.
    RoundTripDistinct(Site),
    /// A telescope transport's second identity does not lie over its path.
    NotOver
    {
        /// The identity over the path.
        at: Site,
        /// The type it synthesised.
        synthesised: TypeContent,
        /// The identity over the path the transport owes.
        expected: TypeContent,
    },
    /// Univalence at a stratum the checker does not certify.
    UaUncertified
    {
        /// The `ua`.
        at: Site,
        /// Why the stratum is not certified.
        stratum: gandr_core_checker::ua::StratumDefect,
    },
    /// Univalence at a certified stratum whose translators are no
    /// equivalence of the species there.
    UaInequivalent
    {
        /// The `ua`.
        at: Site,
        /// What the translators fail.
        defect: gandr_core_checker::ua::UaDefect,
    },
    /// A synthesised type did not convert to the expected one.
    TypeMismatch
    {
        /// The term checked.
        at: Site,
        /// The type it synthesised.
        synthesised: TypeContent,
        /// The type expected.
        expected: TypeContent,
    },
    /// A rule met a type of another former than it requires.
    ShapeMismatch
    {
        /// The term whose type lacks the shape.
        at: Site,
        /// The former required.
        wanted: ExpectedShape,
        /// The type met.
        found: TypeContent,
    },
    /// A checking-only form stood in synthesis position.
    NotSynthesisable
    {
        /// The form.
        form: Form,
    },
    /// A constant named nothing with a type.
    UnknownConstant
    {
        /// The constant.
        at: Site,
        /// What its position names.
        constant: Reference,
    },
    /// A former the judgement has no rule for.
    OutOfFragment
    {
        /// The node carrying the former.
        at: Site,
        /// The former.
        former: UnadmittedFormer,
    },
    /// A variable counted past its zone's binders.
    UnboundIndex
    {
        /// The variable.
        at: Site,
        /// Its zone.
        zone: Zone,
        /// Its index.
        index: DeBruijnIndex,
        /// The binders the zone held.
        depth: BinderDepth,
    },
    /// The allowance ran out.
    BudgetExceeded
    {
        /// The allowance.
        budget: CheckBudget,
    },
    /// An id named no node of the arena.
    DanglingNode
    {
        /// The unresolved node.
        at: Site,
    },
    /// The item was admitted out of order, which a program never allows.
    AdmissionOrder,
    /// The machine's bookkeeping disagreed with itself.
    MachineInvariant,
    /// A code was checked at a universe of the other sort.
    SortMismatch
    {
        /// The code.
        at: Site,
        /// The universe it synthesised.
        synthesised: TypeContent,
        /// The universe expected.
        expected: TypeContent,
    },
    /// A code was checked at a universe of its sort it does not fit.
    LevelMismatch
    {
        /// The code.
        at: Site,
        /// The universe it synthesised.
        synthesised: TypeContent,
        /// The universe expected.
        expected: TypeContent,
    },
    /// A bind's body synthesised a type that mentions the bound name.
    DependentBind
    {
        /// The bind.
        at: Site,
        /// The type its body synthesised, under the binder.
        synthesised: TypeContent,
    },
    /// The normaliser did not certify the unfolding of a code constant.
    Undecided
    {
        /// The code.
        at: Site,
    },
    /// A static application passed more arguments than its head takes.
    FamilyArity
    {
        /// The static application.
        at: Site,
        /// The static Pis the head's type opens.
        expected: StaticArity,
        /// The arguments passed.
        actual: StaticArity,
    },
    /// A static application passed an argument at the wrong classifier.
    FamilyArgumentClassifier
    {
        /// The argument.
        at: Site,
        /// Its position among the arguments.
        position: ArgumentPosition,
        /// The classifier it synthesised.
        synthesised: TypeContent,
        /// The domain it was passed at.
        expected: TypeContent,
    },
    /// A dynamic application passed a type operator that does not normalize
    /// away.
    StaticLambdaArgument
    {
        /// The argument.
        at: Site,
    },
    /// A static Pi stood over a type that classifies no codes.
    StaticClassifierExpected
    {
        /// The static Pi.
        at: Site,
        /// The child that classifies no codes.
        found: TypeContent,
    },
    /// A data declaration's own family occurs under a function's domain where
    /// no stage reaches it.
    NegativeOccurrence(OccurrenceSite),
    /// A data declaration's own family occurs nested where no stage reaches it.
    NestedOccurrence(OccurrenceSite),
    /// A data declaration's own family occurs inside a term a type reads.
    IndexOccurrence(OccurrenceSite),
    /// A data declaration's own family is applied off its parameters.
    NonUniformOccurrence(OccurrenceSite),
    /// A data declaration names a position after its own.
    CrossBlockReference
    {
        /// The parameter or field that names it.
        site: OccurrenceSite,
        /// What the later position names.
        index: Reference,
    },
    /// A value checked where the recursion typing wants a stage it does not
    /// stand at or below.
    StageNotBelow
    {
        /// The value.
        at: Site,
        /// Where it stands.
        found: Standing,
        /// The stage it was wanted at or below.
        bound: Stage,
    },
    /// Two accumulated rows assign different operation types to one interface.
    EffectSignatureConflict
    {
        /// The bind that combines the rows.
        at: Site,
        /// The first returner type.
        first: TypeContent,
        /// The conflicting returner type.
        second: TypeContent,
    },
    /// An abstract type's kind is not a value universe.
    AbstractKindNotUniverse(Site),
    /// A sealed representation forms above its abstract type's universe.
    RepresentationAboveKind
    {
        /// The representation.
        representation: Site,
        /// The declared universe.
        kind: TypeContent,
    },
    /// A sealed atom names a position no abstract type was admitted at.
    NotAnAbstractType(Reference),
    /// A sealing site minted a second atom.
    SealSiteRepeated(gandr_core_checker::SealSite),
    /// A run with no computation enclosing it to run before.
    UnenclosedRun
    {
        /// The nested computation or written run.
        at: Site,
    },
    /// An action the endpoint's session type does not admit.
    SessionMismatch
    {
        /// The action.
        at: Site,
        /// The endpoint it acts on.
        endpoint: EndpointSite,
        /// The endpoint's session type when it was acted on.
        state: TypeContent,
        /// What the state admits instead.
        defect: ProtocolDefect,
    },
    /// An endpoint escaped its one linear use.
    Linearity
    {
        /// The node where the escape was found.
        at: Site,
        /// How it escaped.
        defect: Linearity,
    },
    /// A term stood at a capability type that is no capability hypothesis.
    CapabilityForged
    {
        /// The term.
        at: Site,
        /// The capability type it was checked at.
        expected: TypeContent,
    },
    /// A capability stood where one granting more was expected.
    CapabilityAmplified
    {
        /// The term checked.
        at: Site,
        /// The capability type it synthesised.
        synthesised: TypeContent,
        /// The wider capability type expected.
        expected: TypeContent,
    },
    /// An operation was exercised through a capability that does not grant
    /// it.
    CapabilityOutsideAuthority
    {
        /// The exercise.
        at: Site,
        /// The capability's type.
        capability: TypeContent,
    },
    /// A scoped capability would outlive its region.
    CapabilityEscaped
    {
        /// The term or scope it would escape through.
        at: Site,
        /// The type that carries it out.
        found: TypeContent,
    },
    /// A capability of the consumable grade.
    CapabilityConsumable(Site),
    /// A held capability claims authority the host did not grant.
    CapabilityUngranted(Site),
    /// A `bisim` relating two protocols that are not bisimilar.
    SessionNotEquivalent(Site),
    /// A `sim` relating a protocol that does not simulate its target.
    SessionNotSubtype(Site),
    /// A session statement or flow over something other than a session code.
    SessionCodeExpected(Site),
    /// A ride whose motive uses the moving endpoint other than covariantly.
    NonCovariantMotive(Site),
    /// A ride whose motive the checker cannot move.
    RideUnsupported(Site),
    /// A recorded run the protocol does not admit, with the move that failed.
    RunNotAdmitted
    {
        /// The run.
        at: Site,
        /// How it failed.
        fault: gandr_core_checker::RunFault,
    },
    /// A `forward` whose translator the rule cannot image.
    ForwardUnsupported(Site),
    /// A function flow's boundary that runs against its variance.
    Boundary(Site),
    /// A held value or a view outside its access discipline.
    Access
    {
        /// The node where the defect was found.
        at: Site,
        /// What the discipline refuses.
        defect: gandr_core_checker::access::AccessDefect,
    },
    /// A codata declaration or application refused.
    Codata
    {
        /// The node where the fault was found.
        at: Site,
        /// What is refused.
        fault: gandr_core_checker::codata::CodataFault,
    },
    /// A located judgement broke.
    Located
    {
        /// The node where it broke.
        at: Site,
        /// How.
        defect: Located,
    },
}

/// An item's typing: its verdict, projected.
///
/// # Specification
/// - requires: a projected typing is interpreted against its source judgement.
/// - ensures: projection preserves the four verdict classes, conversion counts
///   and semantic type or refusal content, not arena coordinates.
/// - executable: none — this declaration has no call boundary; the source
///   judgement needed to certify a constructed typing is external.
///
/// # Adequacy
/// - hypothesis: L3 — real checked, synthesised, owed and refused declarations
///   distinguish all four classes; independent integer content and exact
///   refusal payloads distinguish coordinate projection from arena-id copying.
///   The finite cases do not certify arbitrary values of this public enum.
/// - witness: `typing::tests::each_verdict_projects_to_its_typing`
/// - witness: `typing::tests::each_refusal_projects_its_payload`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Typing
{
    /// A nominal declaration whose whole signature formed.
    Data,
    /// The body checked against the signature.
    Checked
    {
        /// The conversions the check made.
        conversions: ConversionCount,
    },
    /// The unsigned body synthesised a type.
    Synthesised
    {
        /// The type produced.
        produced: TypeContent,
        /// The conversions the synthesis made.
        conversions: ConversionCount,
    },
    /// The body is a hole under the signature, owed.
    Owed,
    /// The body waits on owed holes: its type is supplied, nothing defined.
    Suspended,
    /// The item was refused.
    Refused(Refusal),
}

/// What a projection reads beside the verdict: the arena its ids resolve in,
/// the program its positions resolve through, the item's sites, and the
/// pass's encoded types.
///
/// # Specification
/// - requires: arena ids, layout positions and sites refer to the same
///   judgement context; the arena may include nodes minted by checking; the
///   memo belongs to the pass judging in that arena and layout.
/// - ensures: projection reads that context without retaining arena ids or
///   admission positions in its results; absent sites remain unreached.
/// - executable: none — this declaration has no call boundary, and ownership
///   correspondence between its borrowed inputs has no retained proof.
///
/// # Adequacy
/// - hypothesis: L3 — projection over a noisy arena and a fixed item graph
///   distinguishes arena indices, item indices and type-table indices. Actual
///   checking witnesses include types minted after item encoding. These
///   observations assume the inputs share their stated context.
/// - witness: `typing::tests::each_verdict_projects_to_its_typing`
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
pub struct Projection<'arena, 'layout, 'sites, 'types>
{
    /// The arena the verdict's ids resolve in.
    pub arena: &'arena CoreArena,
    /// The program positions resolve through.
    pub layout: &'layout Layout,
    /// The item's table indices of its arena nodes.
    pub sites: &'sites Sites,
    /// The pass's encoded types.
    pub types: &'types TypeMemo,
}

impl Projection<'_, '_, '_, '_>
{
    /// The projected typing of `verdict`.
    ///
    /// # Specification
    /// - requires: `verdict` judged the item whose sites these are, in this
    ///   arena.
    /// - ensures: each verdict maps to its typing, each id to the content or
    ///   site it names, each position to its reference, and nothing else is
    ///   dropped but the origin and the admission positions of an out-of-order
    ///   refusal.
    /// - provides: the coordinate change both runs of the differential pass
    ///   through.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real declarations separate all four verdict classes
    ///   and conversion counts. Six checker refusal classes distinguish named
    ///   coordinates and type content, without claiming all refusal variants or
    ///   all valid arenas have been exercised through this entry.
    /// - witness: `typing::tests::each_verdict_projects_to_its_typing`
    /// - witness: `typing::tests::each_refusal_projects_its_payload`
    #[spec(ensures: |ret| match *verdict {
        Verdict::Data => matches!(ret,Typing::Data),
        | Verdict::Checked { evidence, .. } => {
            matches!(ret, Typing::Checked { conversions } if conversions == evidence.conversions())
        },
        | Verdict::Synthesised { synthesised, .. } => {
            matches!(ret, Typing::Synthesised { conversions, .. } if conversions == synthesised.conversions())
        },
        | Verdict::Owed(_) => matches!(ret, Typing::Owed),
        | Verdict::Suspended(_) => matches!(ret, Typing::Suspended),
        | Verdict::Refused(_) => matches!(ret, Typing::Refused(_)),
    })]
    pub(crate) fn typing(
        &self,
        verdict: &Verdict,
    ) -> Typing
    {
        match *verdict {
            Verdict::Data => Typing::Data,
            Verdict::Checked { evidence, .. } => Typing::Checked {
                conversions: evidence.conversions(),
            },
            Verdict::Synthesised { synthesised, .. } => Typing::Synthesised {
                produced: self.value_type(synthesised.produced().id()),
                conversions: synthesised.conversions(),
            },
            Verdict::Owed(_) => Typing::Owed,
            Verdict::Suspended(_) => Typing::Suspended,
            Verdict::Refused(refusal) => Typing::Refused(self.refusal(refusal)),
        }
    }

    /// The content of a value type.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &self,
        ty: gandr_core_term::ValueTypeId,
    ) -> TypeContent
    {
        self.types
            .content(self.arena, self.layout, ArenaNode::ValueType(ty))
    }

    /// The content of a type node.
    ///
    /// # Specification
    /// trivial.
    fn type_node(
        &self,
        node: TypeNode,
    ) -> TypeContent
    {
        match node {
            TypeNode::Value(ty) => self.value_type(ty),
            TypeNode::Computation(ty) => {
                self.types
                    .content(self.arena, self.layout, ArenaNode::CompType(ty))
            },
        }
    }

    /// The site of an arena node.
    ///
    /// # Specification
    /// - requires: the node is interpreted in this projection's arena.
    /// - ensures: a listed node yields exactly its stored table index;
    ///   otherwise the site is unreached, even if the arena holds the node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fixed item-local sites of four node sorts and one
    ///   same-arena node outside the item walk distinguish absent membership
    ///   from arena validity. No arbitrary-table well-formedness is claimed.
    /// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
    #[spec(ensures: |ret| match self.sites.of(node) {
        Maybe::Present(index) => ret == Site::Node(index),
        Maybe::Absent(_) => ret == Site::Unreached,
    })]
    fn site(
        &self,
        node: ArenaNode,
    ) -> Site
    {
        match self.sites.of(node) {
            Maybe::Present(index) => Site::Node(index),
            Maybe::Absent(_) => Site::Unreached,
        }
    }

    /// The site of a term node.
    ///
    /// # Specification
    /// trivial.
    fn term_site(
        &self,
        node: TermNode,
    ) -> Site
    {
        match node {
            TermNode::Value(id) => self.site(ArenaNode::Value(id)),
            TermNode::Computation(id) => self.site(ArenaNode::Computation(id)),
        }
    }

    /// The site of any core node.
    ///
    /// # Specification
    /// trivial.
    fn core_site(
        &self,
        node: CoreNode,
    ) -> Site
    {
        match node {
            CoreNode::Term(term) => self.term_site(term),
            CoreNode::Type(TypeNode::Value(id)) => self.site(ArenaNode::ValueType(id)),
            CoreNode::Type(TypeNode::Computation(id)) => self.site(ArenaNode::CompType(id)),
        }
    }

    /// The site of an endpoint's fork, beside its side.
    ///
    /// # Specification
    /// trivial.
    fn endpoint(
        &self,
        endpoint: Endpoint,
    ) -> EndpointSite
    {
        EndpointSite {
            fork: self.site(ArenaNode::Computation(endpoint.fork)),
            side: endpoint.side,
        }
    }

    /// The projected linearity defect.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the defect kind and scalar payloads are kept; endpoints and
    ///   arms are item sites and a residue's state its own type table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a residue and an arm disagreement project their
    ///   endpoint, state and arm sites.
    /// - witness: `typing::tests::session_refusals_project_their_endpoints_and_states`
    #[spec(ensures: |ret| core::mem::discriminant(&ret) == match defect {
        | LinearityDefect::Delegated => core::mem::discriminant(&Linearity::Delegated),
        | LinearityDefect::Unrestricted => core::mem::discriminant(&Linearity::Unrestricted),
        | _ => core::mem::discriminant(&ret),
    })]
    fn linearity(
        &self,
        defect: LinearityDefect,
    ) -> Linearity
    {
        match defect {
            LinearityDefect::Residue { endpoint, state } => Linearity::Residue {
                endpoint: self.endpoint(endpoint),
                state: self.value_type(state),
            },
            LinearityDefect::Closed { endpoint } => Linearity::Closed {
                endpoint: self.endpoint(endpoint),
            },
            LinearityDefect::UsedTwice { endpoint } => Linearity::UsedTwice {
                endpoint: self.endpoint(endpoint),
            },
            LinearityDefect::Captured { endpoint, by } => Linearity::Captured {
                endpoint: self.endpoint(endpoint),
                by,
            },
            LinearityDefect::Delegated => Linearity::Delegated,
            LinearityDefect::AsValue { endpoint } => Linearity::AsValue {
                endpoint: self.endpoint(endpoint),
            },
            LinearityDefect::ArmsDisagree {
                endpoint,
                first,
                other,
            } => Linearity::ArmsDisagree {
                endpoint: self.endpoint(endpoint),
                first: self.site(ArenaNode::Computation(first)),
                other: self.site(ArenaNode::Computation(other)),
            },
            LinearityDefect::Unrestricted => Linearity::Unrestricted,
            LinearityDefect::Unbound { index } => Linearity::Unbound { index },
        }
    }

    /// The projected world.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &self,
        world: gandr_core_term::world::World,
    ) -> Place
    {
        match world {
            gandr_core_term::world::World::Host => Place::Host,
            gandr_core_term::world::World::Declared(constant) => {
                Place::Declared(self.layout.resolve(constant))
            },
        }
    }

    /// The projected located defect.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the defect kind and scalar payloads are kept; types are their
    ///   own tables and worlds and positions references.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing capability and an unfounded mark project
    ///   their world, atom and former.
    /// - witness: `typing::tests::a_located_refusal_projects_its_worlds_and_types`
    #[spec(ensures: |ret| matches!(
        (defect, &ret),
        (gandr_core_checker::worlds::LocatedDefect::Unlocated, &Located::Unlocated)
            | (gandr_core_checker::worlds::LocatedDefect::HostWorldUndeclared, &Located::HostWorldUndeclared)
    ) || !matches!(ret, Located::Unlocated | Located::HostWorldUndeclared))]
    fn located(
        &self,
        defect: gandr_core_checker::worlds::LocatedDefect,
    ) -> Located
    {
        use gandr_core_checker::worlds::LocatedDefect;
        match defect {
            LocatedDefect::Immobile {
                crossed,
                ty,
                former,
                predicate,
            } => Located::Immobile {
                crossed,
                ty: self.value_type(ty),
                former: self.value_type(former),
                predicate,
            },
            LocatedDefect::CapabilityMissing { world } => Located::CapabilityMissing {
                world: self.place(world),
            },
            LocatedDefect::CapabilityCaptured { world, by } => Located::CapabilityCaptured {
                world: self.place(world),
                by,
            },
            LocatedDefect::Elsewhere { bound } => Located::Elsewhere {
                bound: self.place(bound),
            },
            LocatedDefect::HoldElsewhere { wanted } => Located::HoldElsewhere {
                wanted: self.place(wanted),
            },
            LocatedDefect::Unlocated => Located::Unlocated,
            LocatedDefect::UndeclaredWorld { world } => Located::UndeclaredWorld {
                world: self.layout.resolve(world),
            },
            LocatedDefect::HostWorldUndeclared => Located::HostWorldUndeclared,
            LocatedDefect::MarkUnfounded {
                atom,
                former,
                predicate,
            } => Located::MarkUnfounded {
                atom: self.layout.resolve(atom),
                former: self.value_type(former),
                predicate,
            },
            LocatedDefect::EntryNamed { constant } => Located::EntryNamed {
                constant: self.layout.resolve(constant),
            },
            LocatedDefect::EntryUngranted { constant } => Located::EntryUngranted {
                constant: self.layout.resolve(constant),
            },
            LocatedDefect::NotAHandle { found } => Located::NotAHandle {
                found: self.value_type(found),
            },
        }
    }

    /// The projected refusal.
    ///
    /// # Specification
    /// - requires: the payload's coordinates are interpreted in this arena and
    ///   layout. The refusal need not be reachable from a checker run.
    /// - ensures: the refusal kind is preserved; node payloads use item sites,
    ///   type payloads use independent type tables, and positions use named
    ///   references. Scalar payloads remain exact; origins and admission-order
    ///   coordinates are intentionally omitted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real checker errors and a finite structural corpus
    ///   separate all four site sorts, unreached nodes, type-content direction,
    ///   checking-form tags, arity direction and classifier positions. The
    ///   corpus does not prove checker reachability; internal admission-order
    ///   and machine-invariant cases are outside the witnessed domain.
    /// - witness: `typing::tests::each_refusal_projects_its_payload`
    /// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body projects each type payload of the refusal once; the check projects each once more and compares it"
        )
    )]
    #[spec(ensures: |ret| { let (matched_left_value, matched_right_value) = (refusal, &ret);
if let CheckRefusal::NotADataType(constant) = matched_left_value && let Refusal::NotADataType(ref projected) = *matched_right_value { *projected == self.layout.resolve(constant) }
 else if let CheckRefusal::DataKindNotUniverse(at) = matched_left_value && let Refusal::DataKindNotUniverse(projected) = *matched_right_value { projected == self.site(ArenaNode::ValueType(at)) }
 else if let CheckRefusal::AbstractKindNotUniverse(at) = matched_left_value && let Refusal::AbstractKindNotUniverse(projected) = *matched_right_value { projected == self.site(ArenaNode::ValueType(at)) }
 else if let CheckRefusal::RepresentationAboveKind {representation,kind} = matched_left_value && let Refusal::RepresentationAboveKind {representation:projected,kind:ref stored} = *matched_right_value { projected == self.site(ArenaNode::ValueType(representation)) && *stored == self.value_type(kind) }
 else if let CheckRefusal::NotAnAbstractType(constant) = matched_left_value && let Refusal::NotAnAbstractType(ref projected) = *matched_right_value { *projected == self.layout.resolve(constant) }
 else if let CheckRefusal::SealSiteRepeated(site) = matched_left_value && let Refusal::SealSiteRepeated(projected) = *matched_right_value { site == projected }
 else if let CheckRefusal::DataArgumentArity(at) = matched_left_value && let Refusal::DataArgumentArity(projected) = *matched_right_value { projected == self.site(ArenaNode::ValueType(at)) }
 else if let CheckRefusal::DataFieldLevel {field,kind} = matched_left_value && let Refusal::DataFieldLevel {field:projected,kind:ref stored} = *matched_right_value { projected == self.site(ArenaNode::ValueType(field)) && *stored == self.value_type(kind) }
 else if let CheckRefusal::RuleNotPresentable {kind,refusal} = matched_left_value && let Refusal::RuleNotPresentable {kind:projected,refusal:stored} = *matched_right_value { projected == self.site(ArenaNode::ValueType(kind)) && stored == refusal }
 else if let CheckRefusal::RuleNotRespected {at,rule, ..} = matched_left_value && let Refusal::RuleNotRespected {at:projected,rule:stored} = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) && stored == rule }
 else if let CheckRefusal::NotApart {at,reason} = matched_left_value && let Refusal::NotApart {at:projected,reason:stored} = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) && stored == reason }
 else if let CheckRefusal::LoopNotRespected {at,cell,reason, ..} = matched_left_value && let Refusal::LoopNotRespected {at:projected,cell:stored,reason:kept} = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) && stored == cell && kept == reason }
 else if let CheckRefusal::LoopUndecided {at,cell} = matched_left_value && let Refusal::LoopUndecided {at:projected,cell:stored} = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) && stored == cell }
 else if let CheckRefusal::UnknownConstructor {at,tag} = matched_left_value && let Refusal::UnknownConstructor {at:projected,tag:stored} = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && stored == tag }
 else if let CheckRefusal::ConstructorArity(at) = matched_left_value && let Refusal::ConstructorArity(projected) = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::IndexedCase(at) = matched_left_value && let Refusal::IndexedCase(projected) = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::NonExhaustiveDataCase(at) = matched_left_value && let Refusal::NonExhaustiveDataCase(projected) = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::UndecidedCoverage(at) = matched_left_value && let Refusal::UndecidedCoverage(projected) = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::AbsentRecordField(at) = matched_left_value && let Refusal::AbsentRecordField(projected) = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::AbsentTupleComponent(at) = matched_left_value && let Refusal::AbsentTupleComponent(projected) = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::MissingRecordField {at,expected} = matched_left_value && let Refusal::MissingRecordField {at:projected,expected:ref stored} = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && *stored == self.value_type(expected) }
 else if let CheckRefusal::DependentStack { at, synthesised } = matched_left_value && let Refusal::DependentStack { at: projected, synthesised: ref actual } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && *actual == self.type_node(TypeNode::Computation(synthesised)) }
 else if let CheckRefusal::EffectSignatureConflict { at, first, second } = matched_left_value && let Refusal::EffectSignatureConflict { at: projected, first: ref actual_first, second: ref actual_second } = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) && *actual_first == self.type_node(TypeNode::Computation(first)) && *actual_second == self.type_node(TypeNode::Computation(second)) }
 else if let CheckRefusal::UnknownOperation { at } = matched_left_value && let Refusal::UnknownOperation { at: projected } = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::HandlerCoverage { at } = matched_left_value && let Refusal::HandlerCoverage { at: projected } = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::ShiftWithoutReset { at } = matched_left_value && let Refusal::ShiftWithoutReset { at: projected } = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::PathCode(at) = matched_left_value && let Refusal::PathCode(projected) = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::EndpointMismatch { at, left, right } = matched_left_value && let Refusal::EndpointMismatch { at: projected, left: projected_left, right: projected_right } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && projected_left == self.site(ArenaNode::Value(left)) && projected_right == self.site(ArenaNode::Value(right)) }
 else if let CheckRefusal::CompoundEndpoint { at, .. } = matched_left_value && let Refusal::CompoundEndpoint { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::FunextUnsupported { at, .. } = matched_left_value && let Refusal::FunextUnsupported { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let (CheckRefusal::PointwiseDistinct { at }, &Refusal::PointwiseDistinct(projected)) = (matched_left_value, matched_right_value) { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::EquivUnsupported { at, .. } = matched_left_value && let Refusal::EquivUnsupported { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::UncertifiedStratum { at, .. } = matched_left_value && let Refusal::UncertifiedStratum { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let (CheckRefusal::RoundTripDistinct { at }, &Refusal::RoundTripDistinct(projected)) = (matched_left_value, matched_right_value) { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::NotOver { at, synthesised, expected } = matched_left_value && let Refusal::NotOver { at: projected, synthesised: ref found, expected: ref wanted } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && *found == self.value_type(synthesised) && *wanted == self.value_type(expected) }
 else if let CheckRefusal::UaUncertified { at, stratum } = matched_left_value && let Refusal::UaUncertified { at: projected, stratum: stored } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && stored == stratum }
 else if let CheckRefusal::UaInequivalent { at, defect } = matched_left_value && let Refusal::UaInequivalent { at: projected, defect: stored } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && stored == defect }
 else if let CheckRefusal::TypeMismatch(Mismatch::Value { at, .. }) = matched_left_value && let Refusal::TypeMismatch { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::SortMismatch { at, .. } = matched_left_value && let Refusal::SortMismatch { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::LevelMismatch { at, .. } = matched_left_value && let Refusal::LevelMismatch { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::Undecided { at } = matched_left_value && let Refusal::Undecided { at: projected } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::StaticLambdaArgument { at } = matched_left_value && let Refusal::StaticLambdaArgument { at: projected } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::TypeMismatch(Mismatch::Computation { at, .. }) = matched_left_value && let Refusal::TypeMismatch { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::DependentBind { at, .. } = matched_left_value && let Refusal::DependentBind { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::ShapeMismatch { at, wanted, .. } = matched_left_value && let Refusal::ShapeMismatch {
                at: projected,
                wanted: returned,
                ..
            } = *matched_right_value { projected == self.term_site(at) && wanted == returned }
 else if let CheckRefusal::NotSynthesisable { form } = matched_left_value && let Refusal::NotSynthesisable { form: projected } = *matched_right_value { match (form, projected) {
            | (CheckingForm::Injection(id), Form::Injection(at))
            | (CheckingForm::List(id), Form::List(at))
            | (CheckingForm::Reify(id), Form::Reify(at))
            | (CheckingForm::Thunk(id), Form::Thunk(at))
            | (CheckingForm::StaticLambda(id), Form::StaticLambda(at))
            | (CheckingForm::Nested(id), Form::Nested(at))
            | (CheckingForm::Run(id), Form::Run(at)) => {
                at == self.site(ArenaNode::Value(id))
            },
            | (CheckingForm::Case(id), Form::Case(at))
            | (CheckingForm::Split(id), Form::Split(at))
            | (CheckingForm::Handle(id), Form::Handle(at))
            | (CheckingForm::Reset(id), Form::Reset(at))
            | (CheckingForm::Shift(id), Form::Shift(at))
            | (CheckingForm::With(id), Form::With(at))
            | (CheckingForm::Lambda(id), Form::Lambda(at))
            | (CheckingForm::Return(id), Form::Return(at))
            | (CheckingForm::Fixpoint(id), Form::Fixpoint(at))
            | (CheckingForm::Offer(id), Form::Offer(at))
            | (CheckingForm::Scope(id), Form::Scope(at)) => {
                at == self.site(ArenaNode::Computation(id))
            },
            | (CheckingForm::Hole(_), Form::Hole) => true,
            | _ => false,
        } }
 else if let CheckRefusal::UnknownConstant { at, constant } = matched_left_value && let Refusal::UnknownConstant {
                at: projected,
                constant: ref returned,
            } = *matched_right_value { {
            projected == self.site(ArenaNode::Value(at))
                && self
                    .layout
                    .items
                    .binary_search_by_key(&constant, |item| item.declaration().constant())
                    .ok()
                    .and_then(|ordinal| self.layout.references.get(ordinal))
                    .map_or_else(
                        || matches!(*returned, Reference::Unoccupied),
                        |expected| returned == expected,
                    )
        } }
 else if let CheckRefusal::OutOfFragment { at, former } = matched_left_value && let Refusal::OutOfFragment {
                at: projected,
                former: returned,
            } = *matched_right_value { projected == self.core_site(at) && former == returned }
 else if let CheckRefusal::UnboundIndex {
                at,
                zone,
                index,
                depth,
            } = matched_left_value && let Refusal::UnboundIndex {
                at: projected,
                zone: returned_zone,
                index: returned_index,
                depth: returned_depth,
            } = *matched_right_value { {
            projected == self.site(ArenaNode::Value(at))
                && zone == returned_zone
                && index == returned_index
                && depth == returned_depth
        } }
 else if let CheckRefusal::BudgetExceeded { budget } = matched_left_value && let Refusal::BudgetExceeded { budget: returned } = *matched_right_value { budget == returned }
 else if let CheckRefusal::DanglingNode { node } = matched_left_value && let Refusal::DanglingNode { at } = *matched_right_value { {
            at == self.core_site(node)
        } }
 else if (matches!(matched_left_value, CheckRefusal::AdmissionOrder { .. }) && matches!(*matched_right_value, Refusal::AdmissionOrder)) || (matches!(matched_left_value, CheckRefusal::MachineInvariant) && matches!(*matched_right_value, Refusal::MachineInvariant)) { true }
 else if let CheckRefusal::FamilyArity {
                at,
                expected,
                actual,
            } = matched_left_value && let Refusal::FamilyArity {
                at: projected,
                expected: returned_expected,
                actual: returned_actual,
            } = *matched_right_value { {
            projected == self.site(ArenaNode::Value(at))
                && expected == returned_expected
                && actual == returned_actual
        } }
 else if let CheckRefusal::FamilyArgumentClassifier { at, position, .. } = matched_left_value && let Refusal::FamilyArgumentClassifier {
                at: projected,
                position: returned,
                ..
            } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && position == returned }
 else if let CheckRefusal::StaticClassifierExpected { at, .. } = matched_left_value && let Refusal::StaticClassifierExpected { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::ValueType(at)) }
 else if let (CheckRefusal::NegativeOccurrence(site), &Refusal::NegativeOccurrence(projected))
     | (CheckRefusal::NestedOccurrence(site), &Refusal::NestedOccurrence(projected))
     | (CheckRefusal::IndexOccurrence(site), &Refusal::IndexOccurrence(projected))
     | (CheckRefusal::NonUniformOccurrence(site), &Refusal::NonUniformOccurrence(projected)) = (matched_left_value, matched_right_value) { site == projected }
 else if let CheckRefusal::CrossBlockReference { site, index } = matched_left_value && let Refusal::CrossBlockReference { site: projected, index: ref returned } = *matched_right_value { site == projected && *returned == self.layout.resolve(index) }
 else if let CheckRefusal::StageNotBelow { at, found, bound } = matched_left_value && let Refusal::StageNotBelow { at: projected, found: stood, bound: wanted } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && stood == found && wanted == bound }
 else if let CheckRefusal::UnenclosedRun { at } = matched_left_value && let Refusal::UnenclosedRun { at: projected } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::SessionMismatch { at, endpoint, state, defect } = matched_left_value && let Refusal::SessionMismatch { at: projected, endpoint: returned, state: ref stored, defect: kept } = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) && returned == self.endpoint(endpoint) && *stored == self.value_type(state) && kept == defect }
 else if let CheckRefusal::Linearity { at, defect } = matched_left_value && let Refusal::Linearity { at: projected, defect: ref stored } = *matched_right_value { projected == self.core_site(at) && *stored == self.linearity(defect) }
 else if let CheckRefusal::CapabilityForged { at, expected } = matched_left_value && let Refusal::CapabilityForged { at: projected, expected: ref stored } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && *stored == self.value_type(expected) }
 else if let CheckRefusal::CapabilityAmplified(Mismatch::Value { at, .. }) = matched_left_value && let Refusal::CapabilityAmplified { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) }
 else if let CheckRefusal::CapabilityAmplified(Mismatch::Computation { at, .. }) = matched_left_value && let Refusal::CapabilityAmplified { at: projected, .. } = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::CapabilityOutsideAuthority { at, capability } = matched_left_value && let Refusal::CapabilityOutsideAuthority { at: projected, capability: ref stored } = *matched_right_value { projected == self.site(ArenaNode::Computation(at)) && *stored == self.value_type(capability) }
 else if let CheckRefusal::CapabilityEscaped { at, found } = matched_left_value && let Refusal::CapabilityEscaped { at: projected, found: ref stored } = *matched_right_value { projected == self.term_site(at) && *stored == self.type_node(found) }
 else if let (CheckRefusal::CapabilityConsumable(at), &Refusal::CapabilityConsumable(projected)) = (matched_left_value, matched_right_value) { projected == self.site(ArenaNode::ValueType(at)) }
 else if let CheckRefusal::CapabilityUngranted { declared, .. } = matched_left_value && let Refusal::CapabilityUngranted(projected) = *matched_right_value { projected == self.site(ArenaNode::ValueType(declared)) }
 else if let (CheckRefusal::SessionNotEquivalent { at }, &Refusal::SessionNotEquivalent(projected)) | (CheckRefusal::SessionNotSubtype { at }, &Refusal::SessionNotSubtype(projected)) | (CheckRefusal::SessionCodeExpected { at }, &Refusal::SessionCodeExpected(projected)) | (CheckRefusal::ForwardUnsupported { at }, &Refusal::ForwardUnsupported(projected)) | (CheckRefusal::Boundary { at }, &Refusal::Boundary(projected)) = (matched_left_value, matched_right_value) { projected == self.site(ArenaNode::Value(at)) }
 else if let (CheckRefusal::NonCovariantMotive { at }, &Refusal::NonCovariantMotive(projected)) | (CheckRefusal::RideUnsupported { at }, &Refusal::RideUnsupported(projected)) = (matched_left_value, matched_right_value) { projected == self.site(ArenaNode::Computation(at)) }
 else if let CheckRefusal::RunNotAdmitted { at, fault } = matched_left_value && let Refusal::RunNotAdmitted { at: projected, fault: stored } = *matched_right_value { projected == self.site(ArenaNode::Value(at)) && stored == fault }
 else if let CheckRefusal::Access { at, defect } = matched_left_value && let Refusal::Access { at: projected, defect: kept } = *matched_right_value { projected == self.core_site(at) && kept == defect }
 else if let CheckRefusal::Codata { at, fault } = matched_left_value && let Refusal::Codata { at: projected, fault: kept } = *matched_right_value { projected == self.core_site(at) && kept == fault }
 else if let CheckRefusal::Located { at, defect } = matched_left_value && let Refusal::Located { at: projected, defect: ref kept } = *matched_right_value { projected == self.core_site(at) && *kept == self.located(defect) }
 else { false }
})]
    fn refusal(
        &self,
        refusal: CheckRefusal,
    ) -> Refusal
    {
        match refusal {
            CheckRefusal::NotADataType(constant) => {
                Refusal::NotADataType(self.layout.resolve(constant))
            },
            CheckRefusal::DataKindNotUniverse(at) => {
                Refusal::DataKindNotUniverse(self.site(ArenaNode::ValueType(at)))
            },
            CheckRefusal::DataFieldLevel { field, kind } => Refusal::DataFieldLevel {
                field: self.site(ArenaNode::ValueType(field)),
                kind: self.value_type(kind),
            },
            CheckRefusal::RuleNotPresentable { kind, refusal } => Refusal::RuleNotPresentable {
                kind: self.site(ArenaNode::ValueType(kind)),
                refusal,
            },
            CheckRefusal::RuleNotRespected { at, rule, .. } => Refusal::RuleNotRespected {
                at: self.site(ArenaNode::Computation(at)),
                rule,
            },
            CheckRefusal::NotApart { at, reason } => Refusal::NotApart {
                at: self.site(ArenaNode::Computation(at)),
                reason,
            },
            CheckRefusal::LoopNotRespected {
                at, cell, reason, ..
            } => Refusal::LoopNotRespected {
                at: self.site(ArenaNode::Computation(at)),
                cell,
                reason,
            },
            CheckRefusal::LoopUndecided { at, cell } => Refusal::LoopUndecided {
                at: self.site(ArenaNode::Computation(at)),
                cell,
            },
            CheckRefusal::AbstractKindNotUniverse(at) => {
                Refusal::AbstractKindNotUniverse(self.site(ArenaNode::ValueType(at)))
            },
            CheckRefusal::RepresentationAboveKind {
                representation,
                kind,
            } => Refusal::RepresentationAboveKind {
                representation: self.site(ArenaNode::ValueType(representation)),
                kind: self.value_type(kind),
            },
            CheckRefusal::NotAnAbstractType(constant) => {
                Refusal::NotAnAbstractType(self.layout.resolve(constant))
            },
            CheckRefusal::SealSiteRepeated(site) => Refusal::SealSiteRepeated(site),
            CheckRefusal::DataArgumentArity(at) => {
                Refusal::DataArgumentArity(self.site(ArenaNode::ValueType(at)))
            },
            CheckRefusal::UnknownConstructor { at, tag } => Refusal::UnknownConstructor {
                at: self.site(ArenaNode::Value(at)),
                tag,
            },
            CheckRefusal::ConstructorArity(at) => {
                Refusal::ConstructorArity(self.site(ArenaNode::Value(at)))
            },
            CheckRefusal::IndexedCase(at) => {
                Refusal::IndexedCase(self.site(ArenaNode::Computation(at)))
            },
            CheckRefusal::NonExhaustiveDataCase(at) => {
                Refusal::NonExhaustiveDataCase(self.site(ArenaNode::Computation(at)))
            },
            CheckRefusal::UndecidedCoverage(at) => {
                Refusal::UndecidedCoverage(self.site(ArenaNode::Computation(at)))
            },
            CheckRefusal::AbsentRecordField(at) => {
                Refusal::AbsentRecordField(self.site(ArenaNode::Computation(at)))
            },
            CheckRefusal::AbsentTupleComponent(at) => {
                Refusal::AbsentTupleComponent(self.site(ArenaNode::Computation(at)))
            },
            CheckRefusal::MissingRecordField { at, expected } => Refusal::MissingRecordField {
                at: self.site(ArenaNode::Value(at)),
                expected: self.value_type(expected),
            },
            CheckRefusal::UnknownOperation { at } => Refusal::UnknownOperation {
                at: self.site(ArenaNode::Computation(at)),
            },
            CheckRefusal::HandlerCoverage { at } => Refusal::HandlerCoverage {
                at: self.site(ArenaNode::Computation(at)),
            },
            CheckRefusal::ShiftWithoutReset { at } => Refusal::ShiftWithoutReset {
                at: self.site(ArenaNode::Computation(at)),
            },
            CheckRefusal::DependentStack { at, synthesised } => Refusal::DependentStack {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.type_node(TypeNode::Computation(synthesised)),
            },
            CheckRefusal::EffectSignatureConflict { at, first, second } => {
                Refusal::EffectSignatureConflict {
                    at: self.site(ArenaNode::Computation(at)),
                    first: self.type_node(TypeNode::Computation(first)),
                    second: self.type_node(TypeNode::Computation(second)),
                }
            },
            CheckRefusal::PathCode(at) => Refusal::PathCode(self.site(ArenaNode::Value(at))),
            CheckRefusal::EndpointMismatch { at, left, right } => Refusal::EndpointMismatch {
                at: self.site(ArenaNode::Value(at)),
                left: self.site(ArenaNode::Value(left)),
                right: self.site(ArenaNode::Value(right)),
            },
            CheckRefusal::CompoundEndpoint { at, synthesised } => Refusal::CompoundEndpoint {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.type_node(TypeNode::Computation(synthesised)),
            },
            CheckRefusal::FunextUnsupported { at, classifier } => Refusal::FunextUnsupported {
                at: self.site(ArenaNode::Value(at)),
                classifier: self.type_node(TypeNode::Value(classifier)),
            },
            CheckRefusal::PointwiseDistinct { at } => {
                Refusal::PointwiseDistinct(self.site(ArenaNode::Value(at)))
            },
            CheckRefusal::EquivUnsupported { at, classifier } => Refusal::EquivUnsupported {
                at: self.site(ArenaNode::Value(at)),
                classifier: self.type_node(TypeNode::Value(classifier)),
            },
            CheckRefusal::UncertifiedStratum { at, code } => Refusal::UncertifiedStratum {
                at: self.site(ArenaNode::Value(at)),
                code: self.type_node(TypeNode::Value(code)),
            },
            CheckRefusal::RoundTripDistinct { at } => {
                Refusal::RoundTripDistinct(self.site(ArenaNode::Value(at)))
            },
            CheckRefusal::NotOver {
                at,
                synthesised,
                expected,
            } => Refusal::NotOver {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            CheckRefusal::UaUncertified { at, stratum } => Refusal::UaUncertified {
                at: self.site(ArenaNode::Value(at)),
                stratum,
            },
            CheckRefusal::UaInequivalent { at, defect } => Refusal::UaInequivalent {
                at: self.site(ArenaNode::Value(at)),
                defect,
            },
            CheckRefusal::TypeMismatch(Mismatch::Value {
                at,
                synthesised,
                expected,
            }) => Refusal::TypeMismatch {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            CheckRefusal::TypeMismatch(Mismatch::Computation {
                at,
                synthesised,
                expected,
            }) => Refusal::TypeMismatch {
                at: self.site(ArenaNode::Computation(at)),
                synthesised: self.type_node(TypeNode::Computation(synthesised)),
                expected: self.type_node(TypeNode::Computation(expected)),
            },
            CheckRefusal::ShapeMismatch { at, wanted, found } => Refusal::ShapeMismatch {
                at: self.term_site(at),
                wanted,
                found: self.type_node(found),
            },
            CheckRefusal::NotSynthesisable { form } => Refusal::NotSynthesisable {
                form: match form {
                    CheckingForm::Reify(id) => Form::Reify(self.site(ArenaNode::Value(id))),
                    CheckingForm::Handle(id) => Form::Handle(self.site(ArenaNode::Computation(id))),
                    CheckingForm::Reset(id) => Form::Reset(self.site(ArenaNode::Computation(id))),
                    CheckingForm::Shift(id) => Form::Shift(self.site(ArenaNode::Computation(id))),
                    CheckingForm::With(id) => Form::With(self.site(ArenaNode::Computation(id))),
                    CheckingForm::List(id) => Form::List(self.site(ArenaNode::Value(id))),
                    CheckingForm::Injection(id) => Form::Injection(self.site(ArenaNode::Value(id))),
                    CheckingForm::Case(id) => Form::Case(self.site(ArenaNode::Computation(id))),
                    CheckingForm::Split(id) => Form::Split(self.site(ArenaNode::Computation(id))),
                    CheckingForm::Thunk(id) => Form::Thunk(self.site(ArenaNode::Value(id))),
                    CheckingForm::Lambda(id) => Form::Lambda(self.site(ArenaNode::Computation(id))),
                    CheckingForm::Return(id) => Form::Return(self.site(ArenaNode::Computation(id))),
                    CheckingForm::Hole(_) => Form::Hole,
                    CheckingForm::StaticLambda(id) => {
                        Form::StaticLambda(self.site(ArenaNode::Value(id)))
                    },
                    CheckingForm::Fixpoint(id) => {
                        Form::Fixpoint(self.site(ArenaNode::Computation(id)))
                    },
                    CheckingForm::Nested(id) => Form::Nested(self.site(ArenaNode::Value(id))),
                    CheckingForm::Run(id) => Form::Run(self.site(ArenaNode::Value(id))),
                    CheckingForm::Offer(id) => Form::Offer(self.site(ArenaNode::Computation(id))),
                    CheckingForm::Scope(id) => Form::Scope(self.site(ArenaNode::Computation(id))),
                },
            },
            CheckRefusal::UnknownConstant { at, constant } => Refusal::UnknownConstant {
                at: self.site(ArenaNode::Value(at)),
                constant: self.layout.resolve(constant),
            },
            CheckRefusal::OutOfFragment { at, former } => Refusal::OutOfFragment {
                at: self.core_site(at),
                former,
            },
            CheckRefusal::UnboundIndex {
                at,
                zone,
                index,
                depth,
            } => Refusal::UnboundIndex {
                at: self.site(ArenaNode::Value(at)),
                zone,
                index,
                depth,
            },
            CheckRefusal::BudgetExceeded { budget } => Refusal::BudgetExceeded { budget },
            CheckRefusal::DanglingNode { node } => Refusal::DanglingNode {
                at: self.core_site(node),
            },
            CheckRefusal::AdmissionOrder { .. } => Refusal::AdmissionOrder,
            CheckRefusal::MachineInvariant => Refusal::MachineInvariant,
            CheckRefusal::SortMismatch {
                at,
                synthesised,
                expected,
            } => Refusal::SortMismatch {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            CheckRefusal::LevelMismatch {
                at,
                synthesised,
                expected,
            } => Refusal::LevelMismatch {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            CheckRefusal::DependentBind { at, synthesised } => Refusal::DependentBind {
                at: self.site(ArenaNode::Computation(at)),
                synthesised: self.type_node(TypeNode::Computation(synthesised)),
            },
            CheckRefusal::Undecided { at } => Refusal::Undecided {
                at: self.site(ArenaNode::Value(at)),
            },
            CheckRefusal::FamilyArity {
                at,
                expected,
                actual,
            } => Refusal::FamilyArity {
                at: self.site(ArenaNode::Value(at)),
                expected,
                actual,
            },
            CheckRefusal::FamilyArgumentClassifier {
                at,
                position,
                synthesised,
                expected,
            } => Refusal::FamilyArgumentClassifier {
                at: self.site(ArenaNode::Value(at)),
                position,
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            CheckRefusal::StaticLambdaArgument { at } => Refusal::StaticLambdaArgument {
                at: self.site(ArenaNode::Value(at)),
            },
            CheckRefusal::StaticClassifierExpected { at, found } => {
                Refusal::StaticClassifierExpected {
                    at: self.site(ArenaNode::ValueType(at)),
                    found: self.value_type(found),
                }
            },
            CheckRefusal::NegativeOccurrence(site) => Refusal::NegativeOccurrence(site),
            CheckRefusal::NestedOccurrence(site) => Refusal::NestedOccurrence(site),
            CheckRefusal::IndexOccurrence(site) => Refusal::IndexOccurrence(site),
            CheckRefusal::NonUniformOccurrence(site) => Refusal::NonUniformOccurrence(site),
            CheckRefusal::CrossBlockReference { site, index } => Refusal::CrossBlockReference {
                site,
                index: self.layout.resolve(index),
            },
            CheckRefusal::StageNotBelow { at, found, bound } => Refusal::StageNotBelow {
                at: self.site(ArenaNode::Value(at)),
                found,
                bound,
            },
            CheckRefusal::UnenclosedRun { at } => Refusal::UnenclosedRun {
                at: self.site(ArenaNode::Value(at)),
            },
            CheckRefusal::SessionMismatch {
                at,
                endpoint,
                state,
                defect,
            } => Refusal::SessionMismatch {
                at: self.site(ArenaNode::Computation(at)),
                endpoint: self.endpoint(endpoint),
                state: self.value_type(state),
                defect,
            },
            CheckRefusal::Linearity { at, defect } => Refusal::Linearity {
                at: self.core_site(at),
                defect: self.linearity(defect),
            },
            CheckRefusal::CapabilityForged { at, expected } => Refusal::CapabilityForged {
                at: self.site(ArenaNode::Value(at)),
                expected: self.value_type(expected),
            },
            CheckRefusal::CapabilityAmplified(Mismatch::Value {
                at,
                synthesised,
                expected,
            }) => Refusal::CapabilityAmplified {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            CheckRefusal::CapabilityAmplified(Mismatch::Computation {
                at,
                synthesised,
                expected,
            }) => Refusal::CapabilityAmplified {
                at: self.site(ArenaNode::Computation(at)),
                synthesised: self.type_node(TypeNode::Computation(synthesised)),
                expected: self.type_node(TypeNode::Computation(expected)),
            },
            CheckRefusal::CapabilityOutsideAuthority { at, capability } => {
                Refusal::CapabilityOutsideAuthority {
                    at: self.site(ArenaNode::Computation(at)),
                    capability: self.value_type(capability),
                }
            },
            CheckRefusal::CapabilityEscaped { at, found } => Refusal::CapabilityEscaped {
                at: self.term_site(at),
                found: self.type_node(found),
            },
            CheckRefusal::CapabilityConsumable(at) => {
                Refusal::CapabilityConsumable(self.site(ArenaNode::ValueType(at)))
            },
            CheckRefusal::CapabilityUngranted { declared, .. } => {
                Refusal::CapabilityUngranted(self.site(ArenaNode::ValueType(declared)))
            },
            CheckRefusal::SessionNotEquivalent { at } => {
                Refusal::SessionNotEquivalent(self.site(ArenaNode::Value(at)))
            },
            CheckRefusal::SessionNotSubtype { at } => {
                Refusal::SessionNotSubtype(self.site(ArenaNode::Value(at)))
            },
            CheckRefusal::SessionCodeExpected { at } => {
                Refusal::SessionCodeExpected(self.site(ArenaNode::Value(at)))
            },
            CheckRefusal::NonCovariantMotive { at } => {
                Refusal::NonCovariantMotive(self.site(ArenaNode::Computation(at)))
            },
            CheckRefusal::RideUnsupported { at } => {
                Refusal::RideUnsupported(self.site(ArenaNode::Computation(at)))
            },
            CheckRefusal::RunNotAdmitted { at, fault } => Refusal::RunNotAdmitted {
                at: self.site(ArenaNode::Value(at)),
                fault,
            },
            CheckRefusal::ForwardUnsupported { at } => {
                Refusal::ForwardUnsupported(self.site(ArenaNode::Value(at)))
            },
            CheckRefusal::Boundary { at } => Refusal::Boundary(self.site(ArenaNode::Value(at))),
            CheckRefusal::Access { at, defect } => Refusal::Access {
                at: self.core_site(at),
                defect,
            },
            CheckRefusal::Codata { at, fault } => Refusal::Codata {
                at: self.core_site(at),
                fault,
            },
            CheckRefusal::Located { at, defect } => Refusal::Located {
                at: self.core_site(at),
                defect: self.located(defect),
            },
        }
    }
}

/// The typing `verdict` projects to, for the item at `ordinal` of `program`,
/// judged in `arena`.
///
/// # Specification
/// - requires: `arena` is `program`'s arena or grew from a copy of it, so every
///   id of the program names the same node in it; `verdict` judged the item at
///   `ordinal` in it.
/// - ensures: the typing an incremental or batch run of this crate records for
///   that verdict.
/// - provides: the coordinate change a caller needs to compare its own batch
///   run — the checker's module entry, say — against this crate's typings.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the generated differential suite compares this public
///   projection against incremental typings over bounded well-formed edits. It
///   does not establish all arena-growth histories or the truth of an arbitrary
///   verdict supplied without its judgement context.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
#[spec(
    requires: usize::from(ordinal) < program.items().len(),
    ensures: |ret| match *verdict {
        Verdict::Data => matches!(ret,Typing::Data),
        | Verdict::Checked { evidence, .. } => {
            matches!(ret, Typing::Checked { conversions } if conversions == evidence.conversions())
        },
        | Verdict::Synthesised { synthesised, .. } => {
            matches!(ret, Typing::Synthesised { conversions, .. } if conversions == synthesised.conversions())
        },
        | Verdict::Owed(_) => matches!(ret, Typing::Owed),
        | Verdict::Suspended(_) => matches!(ret, Typing::Suspended),
        | Verdict::Refused(_) => matches!(ret, Typing::Refused(_)),
    }
)]
#[inline]
#[must_use]
pub fn project(
    program: &Program,
    arena: &CoreArena,
    ordinal: ItemOrdinal,
    verdict: &Verdict,
) -> Typing
{
    let encoded = encode_item(arena, program.layout(), ordinal);
    Projection {
        arena,
        layout: program.layout(),
        sites: &encoded.sites,
        types: &TypeMemo::default(),
    }
    .typing(verdict)
}

#[cfg(test)]
mod tests;
