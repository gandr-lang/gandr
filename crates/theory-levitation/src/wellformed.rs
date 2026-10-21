//! Host-side well-formedness: the checks a [`TheoryDesc`] owes before any typed
//! decoder reads it.
//!
//! No typed decoder runs here, so a description's invariants are checked by
//! this pass, which produces inspectable diagnostics:
//!
//! * the sorting discipline: sort names are distinct, every sort's polarity
//!   agrees with the declaration's, and every result sort and recursive
//!   occurrence names a declared sort;
//! * a π⁺ binder's domain is a declared representable sort: an operation may
//!   bind only variables of a sort that extends a context;
//! * the faces of a signature's shape have distinct names, and each is a
//!   subshape of the shape: its points lie in the shape's carrier;
//! * a rule face may mention only in-signature symbols (constructor and
//!   operation names of this datatype), and its right-hand side may not
//!   introduce a variable absent from its left-hand side;
//! * a circuit rule's wiring must derive the boundary pair its declaration
//!   fixes — the sphere is checked against, never inferred from, the filler;
//! * a bridge arity's three maps must compose;
//! * a symbol may not declare derived metadata: the per-variable variance and
//!   linearity of a rule face are derived ([`derive_cell_var_meta`]), so an
//!   attribute Σ that names them is declined.
//!
//! A higher-order field has no decline here because [`Code`] cannot encode
//! one: that decline lands at elaboration, before a description exists. The π⁺
//! binder of an operation port is object-language binding; the atom
//! abstraction of a constructor code is a separate, nominal former.
//!
//! [`Code`]: crate::Code

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::arity::BridgeArity;
use crate::arity::SortRef;
use crate::boundary::DiagnosticMessage;
use crate::boundary::NameRef;
use crate::boundary::RuleVariableLinearity;
use crate::circuit::CircuitDerivationError;
use crate::circuit::CircuitNode;
use crate::circuit::CircuitRule;
use crate::circuit::derive_boundaries;
use crate::code::Attrs;
use crate::code::Name;
use crate::desc::OperDesc;
use crate::desc::Representability;
use crate::desc::SurfaceSpan;
use crate::desc::TheoryDesc;
use crate::desc::TheoryShape;
use crate::rule::FreeTerm;
use crate::rule::RuleFace;
use crate::rule::RuleVarMeta;
use crate::rule::TermNode;
use crate::rule::TermView;
use crate::rule::Variance;

/// The reserved-derived metadata marker names an attribute Σ may not declare:
/// they name the [`RuleVarMeta`] fields, which are derived from the faces,
/// never declared.
pub const RESERVED_DERIVED_MARKERS: [&str; 3] = ["variance", "linear", "linearity"];

/// The classification of a well-formedness failure, for programmatic
/// matching by consumers and goldens.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum WfKind
{
    /// A rule face mentions a constructor or operation not in this datatype's
    /// signature.
    OutOfSignatureRule,
    /// A rule face's right-hand side introduces a variable absent from its
    /// left-hand side.
    UnboundRhsVariable,
    /// A bridge arity's maps do not compose.
    ArityDoesNotCompose,
    /// A symbol declares derived per-variable metadata (variance or
    /// linearity).
    DeclaresDerivedMetadata,
    /// A circuit rule's wiring derives a boundary its declared sphere does not
    /// fix.
    DerivedBoundaryMismatch,
    /// A circuit rule's wiring reaches a port from itself, so no boundary term
    /// unfolds from it.
    CyclicCircuitWiring,
    /// A circuit rule's redex line applies a rewrite its parameter telescope
    /// does not declare.
    UnknownRewritePort,
    /// A circuit rule's wiring unfolds past the derivation's node ceiling.
    CircuitDerivationBudget,
    /// Two declared sorts share one name, so the sort index is ambiguous.
    DuplicateSortName,
    /// A constructor's result sort names no declared sort of this signature.
    UnknownResultSort,
    /// A recursive occurrence names no declared sort of this signature.
    UnknownVarSort,
    /// A declared sort's polarity disagrees with the declaration's polarity,
    /// outside the polarity-homogeneous fragment this table admits.
    SortPolarityDisagreement,
    /// A results tuple stands somewhere other than the root of a rule's
    /// right-hand side, the one place a many-out operation's results leave.
    MisplacedResults,
    /// A restricted binder's domain is undeclared or not representable.
    NonRepresentableBinder,
    /// A circuit rule's wiring reads one output of a many-out node on its
    /// own, which no term carries.
    SplitCircuitOutputs,
    /// Two faces of the signature's shape share one name.
    DuplicateFaceName,
    /// A face of the signature's shape holds a point the shape lacks.
    FaceOutsideShape,
    /// A rule uses a variable a binding port of its left side binds neither
    /// where a port binds the same variables over the same sort nor applied
    /// to one argument per variable it binds, or applies a variable no binding
    /// port binds.
    UnsortedBinding,
    /// A rule abstracts an atom, `bind a . t`, where no operation's port
    /// abstracts as many atoms.
    MisplacedAbstraction,
    /// An operation's output port sits at an atom sort: an atom is compared
    /// and swapped, never produced.
    AtomResult,
    /// A port's atom abstraction, `bind (a : N) .`, ranges over a sort that is
    /// undeclared or not an atom sort.
    NonAtomAbstraction,
    /// A rule's freshness condition, `where a # q`, names an atom no
    /// abstraction of the rule abstracts, or a variable its left side does not
    /// hold.
    UnknownFreshness,
    /// A rule's variable stands under an atom's abstraction on one side and
    /// outside it on the other with no condition naming the atom fresh for it,
    /// so an instance naming the atom would be captured or escape.
    Capture,
}

quenchant_shape::reason_enum! {
    /// Why a diagnostic carries no surface span.
    pub mod diagnostic_span {
        /// The reason the span is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The failure concerns a declaration-table entry that records no
            /// surface span: a sort, an attribute Σ or an arity.
            Unrecorded,
        }
    }
}

/// One well-formedness diagnostic: an inspectable failure with a message,
/// the declared names it concerns and, when recorded, a surface span.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct WfDiagnostic
{
    /// The failure classification.
    pub kind: WfKind,
    /// The declared names the failure concerns — the sort, port, rule, face,
    /// symbol or variable at fault — in the order its message names them.
    pub subjects: Box<[Name]>,
    /// A human-readable description of the failure.
    pub message: DiagnosticMessage,
    /// The surface span the failure was located at, when recorded.
    pub span: Maybe<SurfaceSpan, diagnostic_span::Absent>,
}

impl WfDiagnostic
{
    /// A diagnostic of the given kind, subjects, message and span.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        kind: WfKind,
        subjects: Box<[Name]>,
        message: DiagnosticMessage,
        span: Maybe<SurfaceSpan, diagnostic_span::Absent>,
    ) -> Self
    {
        Self {
            kind,
            subjects,
            message,
            span,
        }
    }
}

/// The names `names` display as, in order: the subjects of a diagnostic, as
/// its message names them.
///
/// # Specification
/// trivial.
fn named(names: &[&dyn fmt::Display]) -> Box<[Name]>
{
    names
        .iter()
        .map(|name| Name::from(name.to_string()))
        .collect()
}

/// The diagnostic of `kind` about `subjects` with the rendered `message`, at
/// an unrecorded span.
///
/// # Specification
/// trivial.
fn unlocated(
    kind: WfKind,
    subjects: Box<[Name]>,
    message: String,
) -> WfDiagnostic
{
    WfDiagnostic::new(
        kind,
        subjects,
        DiagnosticMessage::from(message),
        Maybe::Absent(diagnostic_span::Absent::Unrecorded),
    )
}

/// The diagnostic of `kind` about `subjects` with the rendered `message`, at
/// `span`.
///
/// # Specification
/// trivial.
fn located(
    kind: WfKind,
    subjects: Box<[Name]>,
    message: String,
    span: SurfaceSpan,
) -> WfDiagnostic
{
    WfDiagnostic::new(
        kind,
        subjects,
        DiagnosticMessage::from(message),
        Maybe::Present(span),
    )
}

/// Check a description, returning one diagnostic per well-formedness failure;
/// an empty vector means well-formed.
///
/// # Specification
/// - ensures: every failure of the rules this module states, in a deterministic
///   order: sorting-discipline checks, then the π⁺ binder check, then the atom
///   abstraction check, then the atom result check, then the shape checks, then
///   attribute declines, then per-face checks, then per-arity checks, then
///   per-circuit-rule checks; an empty result witnesses a well-formed
///   description. The binder check reports one `NonRepresentableBinder` per
///   binder, over every port of every operation, whose domain is not a declared
///   representable sort; the atom abstraction check one `NonAtomAbstraction`
///   per abstraction, over every port of every operation, whose domain is not a
///   declared atom sort; the atom result check one `AtomResult` per output
///   port, over every operation, at a declared atom sort.
/// - panics: none; total on any description, a mis-built one included.
///
/// # Adequacy
/// - hypothesis: L3 — a clean description passes; a duplicate sort name, a
///   foreign result or `var` sort, a sort polarity disagreeing with the
///   declaration's, an ordinary or undeclared π⁺ domain, a face named twice, a
///   face past its shape, an out-of-signature face, a fresh right-hand-side
///   variable, a variable a binding port binds used where no port binds the
///   same variables or instantiated at the wrong count, an abstraction where no
///   port abstracts as many atoms, a non-composing arity, a reserved-derived
///   attribute, a circuit rule whose wiring derives a boundary its sphere does
///   not fix, a cyclic wiring, and a redex applying a rewrite the rule's
///   telescope does not declare each surface exactly their diagnostic.
/// - witness: `wellformed::tests::the_sorting_discipline_indexes_the_description`
/// - witness: `wellformed::tests::a_clean_description_passes`
/// - witness: `wellformed::tests::an_out_of_signature_cell_is_declined`
/// - witness: `wellformed::tests::a_fresh_right_hand_side_variable_is_declined`
/// - witness: `wellformed::tests::a_non_composing_arity_is_declined`
/// - witness: `wellformed::tests::the_congruence_circuit_rule_checks_against_its_sphere`
/// - witness: `wellformed::tests::a_boundary_mismatched_circuit_rule_is_declined`
/// - witness: `wellformed::tests::an_out_of_signature_circuit_frame_is_declined`
/// - witness: `wellformed::tests::diagnostics_preserve_phase_order_multiplicity_and_provenance`
/// - witness: `wellformed::tests::a_cyclic_circuit_wiring_is_declined`
/// - witness: `wellformed::tests::a_declared_telescope_admits_the_redex_heads_it_names`
/// - witness: `wellformed::tests::a_redex_applying_an_undeclared_port_is_declined`
/// - witness: `wellformed::tests::declaring_derived_metadata_is_declined`
/// - witness: `tests::glf::restricted_binding_requires_representability`
/// - witness: `wellformed::tests::an_atom_is_taken_and_never_returned`
/// - witness: `wellformed::tests::a_port_abstracts_atoms_of_an_atom_sort`
/// - witness: `wellformed::tests::a_derivation_budget_failure_prevents_boundary_comparison`
/// - witness: `wellformed::tests::a_results_tuple_stands_only_at_a_right_hand_root`
/// - witness: `wellformed::tests::a_shape_refuses_a_repeated_face_and_a_point_past_it`
/// - witness: `wellformed::tests::a_bound_variable_is_used_under_its_binders_or_instantiated`
/// - witness: `wellformed::tests::an_abstraction_stands_at_a_port_that_abstracts`
#[inline]
#[must_use]
#[spec(ensures: |ref diagnostics| diagnostics.iter().all(|diagnostic| match diagnostic.kind {
    WfKind::OutOfSignatureRule | WfKind::UnboundRhsVariable | WfKind::DerivedBoundaryMismatch
    | WfKind::CyclicCircuitWiring | WfKind::UnknownRewritePort | WfKind::CircuitDerivationBudget
    | WfKind::MisplacedResults | WfKind::SplitCircuitOutputs | WfKind::UnsortedBinding
    | WfKind::MisplacedAbstraction | WfKind::UnknownFreshness
    | WfKind::Capture => matches!(diagnostic.span, Maybe::Present(_)),
    WfKind::ArityDoesNotCompose | WfKind::DeclaresDerivedMetadata | WfKind::DuplicateSortName
    | WfKind::UnknownResultSort | WfKind::UnknownVarSort | WfKind::SortPolarityDisagreement
    | WfKind::NonRepresentableBinder | WfKind::DuplicateFaceName | WfKind::FaceOutsideShape
    | WfKind::AtomResult | WfKind::NonAtomAbstraction => diagnostic.span == Maybe::Absent(diagnostic_span::Absent::Unrecorded),
}) && diagnostics.iter().filter(|diagnostic| diagnostic.kind == WfKind::NonRepresentableBinder).count()
    == desc.opers.iter()
        .flat_map(|op| op.arity.inputs.iter().chain(&op.arity.outputs))
        .flat_map(|port| port.bindings.iter())
        .filter(|binder| !desc.sorts.iter().any(|sort|
            sort.name == binder.sort && sort.representability == Representability::Representable))
        .count()
    && diagnostics.iter().filter(|diagnostic| diagnostic.kind == WfKind::NonAtomAbstraction).count()
        == desc.opers.iter()
            .flat_map(|op| op.arity.inputs.iter().chain(&op.arity.outputs))
            .flat_map(|port| port.abstractions.iter())
            .filter(|atom| !desc.sorts.iter().any(|sort|
                sort.name == atom.sort && sort.representability == Representability::Atom))
            .count()
    && diagnostics.iter().filter(|diagnostic| diagnostic.kind == WfKind::AtomResult).count()
        == desc.opers.iter()
            .flat_map(|op| op.arity.outputs.iter())
            .filter(|port| desc.sorts.iter().any(|sort|
                sort.name == port.sort && sort.representability == Representability::Atom))
            .count())]
pub fn check_desc<G>(desc: &TheoryDesc<G>) -> Vec<WfDiagnostic>
{
    let mut diagnostics = Vec::new();

    // The sorting discipline: the declared sort set is the description's
    // index, and every indexed slot must resolve in it.
    check_sorts(desc, &mut diagnostics);
    for port in desc
        .opers
        .iter()
        .flat_map(|op| op.arity.inputs.iter().chain(&op.arity.outputs))
    {
        for binder in &port.bindings {
            if !desc.sorts.iter().any(|sort| {
                sort.name == binder.sort && sort.representability == Representability::Representable
            }) {
                diagnostics.push(unlocated(
                    WfKind::NonRepresentableBinder,
                    named(&[&binder.sort, &port.name]),
                    format!(
                        "π⁺ domain '{}' of port '{}' is not representable",
                        binder.sort, port.name
                    ),
                ));
            }
        }
        for atom in &port.abstractions {
            if !desc.sorts.iter().any(|sort| {
                sort.name == atom.sort && sort.representability == Representability::Atom
            }) {
                diagnostics.push(unlocated(
                    WfKind::NonAtomAbstraction,
                    named(&[&atom.sort, &port.name]),
                    format!(
                        "atom abstraction over '{}' of port '{}' is not over an atom sort",
                        atom.sort, port.name
                    ),
                ));
            }
        }
    }
    for op in &desc.opers {
        for port in &op.arity.outputs {
            if desc.sorts.iter().any(|sort| {
                sort.name == port.sort && sort.representability == Representability::Atom
            }) {
                diagnostics.push(unlocated(
                    WfKind::AtomResult,
                    named(&[&op.name, &port.sort, &port.name]),
                    format!(
                        "operation '{}' returns atom sort '{}' at port '{}'",
                        op.name, port.sort, port.name
                    ),
                ));
            }
        }
    }
    if let Maybe::Present(ref shape) = desc.shape {
        check_shape(shape, &mut diagnostics);
    }

    // Reserved-derived metadata: no attribute Σ may declare it.
    check_attrs(
        &desc.attrs,
        &desc.id.name,
        AttributeOwner::Datatype,
        &mut diagnostics,
    );
    for ctor in &desc.ctors {
        check_attrs(
            &ctor.attrs,
            &ctor.name,
            AttributeOwner::Constructor,
            &mut diagnostics,
        );
    }
    for param in &desc.params {
        check_attrs(
            &param.attrs,
            &param.name,
            AttributeOwner::Parameter,
            &mut diagnostics,
        );
    }
    for op in &desc.opers {
        check_attrs(
            &op.attrs,
            &op.name,
            AttributeOwner::Operation,
            &mut diagnostics,
        );
    }

    // Rule faces: in-signature symbols, no fresh right-hand-side variable,
    // every variable a binding port binds sorted at its binders, and every
    // variable crossing an abstraction stated fresh for its atom.
    let signature = signature_names(desc);
    let operations: BTreeMap<&Name, &OperDesc> = desc
        .opers
        .iter()
        .map(|operation| (&operation.name, operation))
        .collect();
    for rule in &desc.rules {
        check_rule_face(rule, &signature, &mut diagnostics);
        check_rule_binders(rule, &operations, &mut diagnostics);
        check_abstractions(rule, &operations, &mut diagnostics);
        check_freshness(rule, &mut diagnostics);
    }

    // Bridge arities: the three maps compose.
    for op in &desc.opers {
        check_arity(&op.arity, &op.name, &mut diagnostics);
    }

    // Circuit rules: the wiring derives the sphere the declaration fixes.
    for rule in &desc.circuits {
        check_circuit_rule(rule, &signature, &mut diagnostics);
    }

    diagnostics
}

/// Check a signature's shape parameter: its faces are named apart and each is
/// a subshape of the shape.
///
/// # Specification
/// - ensures: one `DuplicateFaceName` per face whose name an earlier face
///   holds, and one `FaceOutsideShape` per face holding a point the shape
///   lacks, named by its least such point, in face order, each unlocated.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a face named twice and a face holding the first point
///   past its shape are each reported once, in face order, beside a face that
///   passes; skipping either or reporting the first occurrence of a name
///   changes the sequence.
/// - witness: `wellformed::tests::a_shape_refuses_a_repeated_face_and_a_point_past_it`
#[spec(
    captures: [before = diagnostics.len()],
    ensures: diagnostics.len() == before.saturating_add(
        shape.faces.iter().enumerate().filter(|entry| shape.faces.iter().take(entry.0).any(|prior| prior.name() == entry.1.name())).count()
            .saturating_add(shape.faces.iter().filter(|face| matches!(shape.escape(face), Maybe::Present(_))).count())),
)]
fn check_shape(
    shape: &TheoryShape,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    for (at, face) in shape.faces.iter().enumerate() {
        if shape
            .faces
            .iter()
            .take(at)
            .any(|prior| prior.name() == face.name())
        {
            diagnostics.push(unlocated(
                WfKind::DuplicateFaceName,
                named(&[&shape.name, &face.name()]),
                format!("shape '{}' names face '{}' twice", shape.name, face.name()),
            ));
        }
        if let Maybe::Present(point) = shape.escape(face) {
            diagnostics.push(unlocated(
                WfKind::FaceOutsideShape,
                named(&[&face.name(), &shape.name]),
                format!(
                    "face '{}' of shape '{}' holds point {point}, past its {} points",
                    face.name(),
                    shape.name,
                    shape.points
                ),
            ));
        }
    }
}

/// Check the sorting discipline over the declared sort set.
///
/// # Specification
/// - ensures: one diagnostic per repeated sort name (at each later occurrence),
///   per sort whose polarity disagrees with the declaration's, per constructor
///   whose result sort is undeclared, and per recursive occurrence naming an
///   undeclared sort, in that order per entry.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — declared/foreign sorts, a later duplicate, mixed polarity
///   and repeated foreign recursive occurrences are observed as an exact
///   kind/span sequence; skipped duplicates, deduplication and reordering or
///   locating an unlocated diagnostic change that sequence.
/// - witness: `wellformed::tests::the_sorting_discipline_indexes_the_description`
/// - witness: `wellformed::tests::diagnostics_preserve_phase_order_multiplicity_and_provenance`
#[spec(
    captures: [
        before = diagnostics.len(),
        expected = desc.sorts.iter().enumerate().filter(|entry| desc.sorts.iter().take(entry.0).any(|prior| prior.name == entry.1.name)).count()
            .saturating_add(desc.sorts.iter().filter(|sort| sort.polarity != desc.polarity).count())
            .saturating_add(desc.ctors.iter().filter(|ctor| !desc.sorts.iter().any(|sort| sort.name == ctor.result)).count())
            .saturating_add(desc.ctors.iter().map(|ctor| ctor.code.recursive_sorts().filter(|name| !desc.sorts.iter().any(|sort| sort.name == **name)).count()).sum::<usize>()),
    ],
    ensures: diagnostics.len() == before.saturating_add(expected)
        && diagnostics.get(before ..).is_some_and(|added| added.iter().all(|diagnostic| diagnostic.span == Maybe::Absent(diagnostic_span::Absent::Unrecorded)
            && matches!(diagnostic.kind, WfKind::DuplicateSortName | WfKind::SortPolarityDisagreement | WfKind::UnknownResultSort | WfKind::UnknownVarSort))),
)]
fn check_sorts<G>(
    desc: &TheoryDesc<G>,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    for (index, sort) in desc.sorts.iter().enumerate() {
        if desc
            .sorts
            .iter()
            .take(index)
            .any(|earlier| earlier.name == sort.name)
        {
            diagnostics.push(unlocated(
                WfKind::DuplicateSortName,
                named(&[&sort.name]),
                format!("the sort `{}` is declared more than once", sort.name),
            ));
        }
        if sort.polarity != desc.polarity {
            diagnostics.push(unlocated(
                WfKind::SortPolarityDisagreement,
                named(&[&sort.name]),
                format!(
                    "the sort `{}` declares a polarity disagreeing with its declaration's",
                    sort.name
                ),
            ));
        }
    }
    let declares = |name: &Name| desc.sorts.iter().any(|sort| sort.name == *name);
    for ctor in &desc.ctors {
        if !declares(&ctor.result) {
            diagnostics.push(unlocated(
                WfKind::UnknownResultSort,
                named(&[&ctor.name, &ctor.result]),
                format!(
                    "the constructor `{}` targets the undeclared sort `{}`",
                    ctor.name, ctor.result
                ),
            ));
        }
        for sort in ctor.code.recursive_sorts() {
            if !declares(sort) {
                diagnostics.push(unlocated(
                    WfKind::UnknownVarSort,
                    named(&[&ctor.name, &sort]),
                    format!(
                        "the constructor `{}` recurses at the undeclared sort `{sort}`",
                        ctor.name
                    ),
                ));
            }
        }
    }
}

/// Check one circuit rule: the boundary pair its wiring derives is the pair
/// its declared sphere fixes.
///
/// The sphere is the declaration's, and the check runs in that direction
/// only: a derived pair never becomes the sphere, so a mis-glued boundary is
/// a declaration-table failure with the sphere as the diagnostic rather than
/// a silently re-indexed cell downstream.
///
/// The in-signature rule binds here exactly as it does for a written face:
/// the declared sphere's terms and every frame head must name a constructor
/// or operation of this datatype. A redex head is not checked against the
/// signature — it names a rewrite-sorted port of the rule's own telescope,
/// not a signature symbol — and is instead checked against that telescope
/// ([`CircuitRule::ports`]) when the member declares one. An empty telescope
/// means the ports are not declared here rather than that the heads are
/// unknown, so the check bites only on a written telescope.
///
/// The one rule deliberately not re-run is [`WfKind::UnboundRhsVariable`],
/// which reads a rule's variables off its left-hand side: a circuit rule's
/// variables are bound by its port telescope, so a congruence rule's target
/// names the rewrite-sorted ports' endpoints and its source cannot bind them.
/// Port linearity and disjointness are the surface's.
///
/// # Specification
/// - ensures: out-of-signature diagnostics for the sphere's terms and the frame
///   heads, unknown-port diagnostics for redex heads a written telescope omits,
///   then either the derivation's decline or one mismatch diagnostic per
///   boundary side the derived pair does not match.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — matching and mismatching spheres, declared/absent
///   telescope heads, unknown frames, cycles and over-budget bodies are
///   observed as kinds and source spans. Wrong provenance, comparing after a
///   failed derivation, or suppressing one mismatched side changes them.
/// - witness: `wellformed::tests::diagnostics_preserve_phase_order_multiplicity_and_provenance`
/// - witness: `wellformed::tests::a_cyclic_circuit_wiring_is_declined`
/// - witness: `wellformed::tests::a_redex_applying_an_undeclared_port_is_declined`
/// - witness: `wellformed::tests::an_out_of_signature_circuit_frame_is_declined`
/// - witness: `wellformed::tests::the_congruence_circuit_rule_checks_against_its_sphere`
/// - witness: `wellformed::tests::a_derivation_budget_failure_prevents_boundary_comparison`
#[spec(
    captures: before = diagnostics.len(),
    ensures: diagnostics.len() >= before && diagnostics.get(before ..).is_some_and(|added| added.iter().all(|diagnostic|
        diagnostic.span == Maybe::Present(rule.sphere.provenance)
        && matches!(diagnostic.kind, WfKind::OutOfSignatureRule | WfKind::UnknownRewritePort
            | WfKind::CyclicCircuitWiring | WfKind::CircuitDerivationBudget | WfKind::DerivedBoundaryMismatch
            | WfKind::SplitCircuitOutputs))),
)]
fn check_circuit_rule(
    rule: &CircuitRule,
    signature: &BTreeSet<&Name>,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    let span = rule.sphere.provenance;
    check_free_term_symbols(&rule.sphere.lhs, signature, span, diagnostics);
    check_free_term_symbols(&rule.sphere.rhs, signature, span, diagnostics);
    let ports: BTreeSet<&Name> = rule.ports.iter().map(|port| &port.name).collect();
    for node in &rule.body.nodes {
        match *node {
            CircuitNode::Frame(ref frame) => {
                if signature.contains(frame.head.name()) {
                    continue;
                }
                diagnostics.push(located(
                    WfKind::OutOfSignatureRule,
                    named(&[&rule.name, &frame.head.name()]),
                    format!(
                        "circuit rule `{}`'s frame applies symbol `{}` not in the datatype's \
                         signature",
                        rule.name,
                        frame.head.name()
                    ),
                    span,
                ));
            },
            CircuitNode::Redex(ref redex) => {
                // An undeclared telescope means the redex heads are simply not
                // declared here — not that they are unknown. The check bites
                // only where a telescope was written.
                if rule.ports.is_empty() || ports.contains(&redex.rewrite) {
                    continue;
                }
                diagnostics.push(located(
                    WfKind::UnknownRewritePort,
                    named(&[&rule.name, &redex.rewrite]),
                    format!(
                        "circuit rule `{}`'s redex applies rewrite `{}`, which its parameter \
                         telescope does not declare",
                        rule.name, redex.rewrite
                    ),
                    span,
                ));
            },
        }
    }

    let derived = match derive_boundaries(&rule.body) {
        Ok(derived) => derived,
        Err(CircuitDerivationError::CyclicWiring(port)) => {
            diagnostics.push(located(
                WfKind::CyclicCircuitWiring,
                named(&[&rule.name, &port]),
                format!(
                    "circuit rule `{}`'s wiring reaches port `{port}` from itself, so no boundary \
                     term unfolds from it",
                    rule.name
                ),
                span,
            ));
            return;
        },
        Err(CircuitDerivationError::NodeBudget { budget }) => {
            diagnostics.push(located(
                WfKind::CircuitDerivationBudget,
                named(&[&rule.name]),
                format!(
                    "circuit rule `{}`'s wiring unfolds past the derivation's node budget of \
                     {budget}: a wire consumed twice is unfolded twice, so reconvergence is a \
                     shared subterm on the term-shaped store and a body of doubling frames \
                     derives an exponentially large boundary",
                    rule.name
                ),
                span,
            ));
            return;
        },
        Err(CircuitDerivationError::SplitOutputs(port)) => {
            diagnostics.push(located(
                WfKind::SplitCircuitOutputs,
                named(&[&rule.name, &port]),
                format!(
                    "circuit rule `{}`'s wiring reads port `{port}`, one output of a many-out \
                     node, on its own: a term holds a many-out application only whole, as the \
                     results it returns, so the node's outputs must leave the body together as \
                     its declared results, in order",
                    rule.name
                ),
                span,
            ));
            return;
        },
    };
    let sides = [
        ("source", &derived.source, &rule.sphere.lhs),
        ("target", &derived.target, &rule.sphere.rhs),
    ];
    for (side, derived, declared) in sides {
        if derived == declared {
            continue;
        }
        let derived = derived.to_string();
        let declared = declared.to_string();
        // The inspection notation renders a constructor application and an
        // operation application alike, so two unequal terms can render the
        // same; say which axis they differ on rather than printing one term
        // twice.
        let alphabets = if derived == declared {
            ", differing only in whether a head is a constructor or an operation"
        }
        else {
            ""
        };
        diagnostics.push(located(
            WfKind::DerivedBoundaryMismatch,
            named(&[&rule.name]),
            format!(
                "circuit rule `{}`'s wiring derives the {side} boundary `{derived}`, but its \
                 declared sphere fixes `{declared}`{alphabets}",
                rule.name
            ),
            span,
        ));
    }
}

/// The kind of declaration an attribute Σ is attached to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AttributeOwner
{
    /// The datatype's own Σ.
    Datatype,
    /// A constructor's Σ.
    Constructor,
    /// A parameter's Σ.
    Parameter,
    /// An operation's Σ.
    Operation,
}

impl fmt::Display for AttributeOwner
{
    /// Writes the owner as the diagnostic names it (`the constructor`).
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
            Self::Datatype => "the datatype",
            Self::Constructor => "the constructor",
            Self::Parameter => "the parameter",
            Self::Operation => "the operation",
        })
    }
}

/// Append a `DeclaresDerivedMetadata` diagnostic for each reserved-derived
/// marker in `attrs`.
///
/// # Specification
/// - ensures: one diagnostic per reserved marker `attrs` contains, in
///   [`RESERVED_DERIVED_MARKERS`] order, naming the owner and the marker.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and populated attribute sets, repeated reserved
///   markers and reversed declarations are observed by diagnostic count and
///   kind; per-occurrence emission, omission and loss of earlier diagnostics
///   change the complete result.
/// - witness: `wellformed::tests::declaring_derived_metadata_is_declined`
/// - witness: `wellformed::tests::diagnostics_preserve_phase_order_multiplicity_and_provenance`
#[spec(
    captures: before = diagnostics.len(),
    ensures: diagnostics.len() == before.saturating_add(RESERVED_DERIVED_MARKERS.iter().filter(|marker| bool::from(attrs.contains(NameRef::from(**marker)))).count())
        && diagnostics.get(before ..).is_some_and(|added| added.iter().all(|diagnostic| diagnostic.kind == WfKind::DeclaresDerivedMetadata
            && diagnostic.span == Maybe::Absent(diagnostic_span::Absent::Unrecorded))),
)]
fn check_attrs(
    attrs: &Attrs,
    owner: &Name,
    role: AttributeOwner,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    for marker in RESERVED_DERIVED_MARKERS {
        if bool::from(attrs.contains(NameRef::from(marker))) {
            diagnostics.push(unlocated(
                WfKind::DeclaresDerivedMetadata,
                named(&[&owner, &marker]),
                format!(
                    "{role} `{owner}` declares reserved derived metadata `{marker}`: rule \
                     variable variance and linearity are derived from the faces, never declared"
                ),
            ));
        }
    }
}

/// The in-signature symbol names: every constructor and operation of `desc`.
///
/// # Specification
/// trivial.
fn signature_names<G>(desc: &TheoryDesc<G>) -> BTreeSet<&Name>
{
    desc.ctors
        .iter()
        .map(|ctor| &ctor.name)
        .chain(desc.opers.iter().map(|op| &op.name))
        .collect()
}

/// Check one rule face: every applied symbol is in-signature, the right-hand
/// side introduces no fresh variable, and a results tuple stands only at the
/// right-hand root.
///
/// # Specification
/// - ensures: the out-of-signature diagnostics of the left-hand side, then of
///   the right-hand side, then one diagnostic per right-hand-side variable
///   occurrence the left-hand side does not bind, then one per results tuple
///   other than the right-hand root.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — symbols outside the signature on both sides, a repeated
///   fresh right-hand variable, and results tuples at the right-hand root,
///   nested under it and on the left have an exact diagnostic sequence and face
///   span; reversed sides, deduplication, using the wrong span or refusing the
///   root tuple differ.
/// - witness: `wellformed::tests::diagnostics_preserve_phase_order_multiplicity_and_provenance`
/// - witness: `wellformed::tests::a_clean_description_passes`
/// - witness: `wellformed::tests::a_results_tuple_stands_only_at_a_right_hand_root`
#[spec(
    captures: before = diagnostics.len(),
    ensures: diagnostics.len() == before.saturating_add(
        cell.lhs.applied_symbols().chain(cell.rhs.applied_symbols()).filter(|name| !signature.contains(name)).count()
            .saturating_add(cell.rhs.to_node().vars().filter(|name| !cell.lhs.to_node().vars().any(|left| left == *name)).count())
            .saturating_add(cell.lhs.results_widths().count())
            .saturating_add(cell.rhs.results_widths().count().saturating_sub(usize::from(matches!(cell.rhs.view(), TermView::Results { .. }))))
    ) && diagnostics.get(before ..).is_some_and(|added| added.iter().all(|diagnostic| diagnostic.span == Maybe::Present(cell.provenance)
        && matches!(diagnostic.kind, WfKind::OutOfSignatureRule | WfKind::UnboundRhsVariable | WfKind::MisplacedResults))),
)]
fn check_rule_face(
    cell: &RuleFace,
    signature: &BTreeSet<&Name>,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    check_free_term_symbols(&cell.lhs, signature, cell.provenance, diagnostics);
    check_free_term_symbols(&cell.rhs, signature, cell.provenance, diagnostics);

    let lhs_vars: BTreeSet<&Name> = cell.lhs.to_node().vars().collect();
    for var in cell.rhs.collect_vars() {
        if !lhs_vars.contains(&var) {
            diagnostics.push(located(
                WfKind::UnboundRhsVariable,
                named(&[&var]),
                format!(
                    "cell rule's right-hand side introduces variable `{var}` not bound by its \
                     left-hand side"
                ),
                cell.provenance,
            ));
        }
    }

    let rooted = matches!(cell.rhs.view(), TermView::Results { .. });
    let misplaced = cell
        .lhs
        .results_widths()
        .chain(cell.rhs.results_widths().skip(usize::from(rooted)));
    for width in misplaced {
        diagnostics.push(located(
            WfKind::MisplacedResults,
            named(&[]),
            format!(
                "cell rule writes a results tuple of {} components away from its right-hand \
                 root: a tuple is how a many-out operation's rule returns its results, so it \
                 stands only as the whole right-hand side",
                usize::from(width)
            ),
            cell.provenance,
        ));
    }
}

/// Where a rule term node stands: under the input port of an operation the
/// description declares, or anywhere else.
#[derive(Clone, Copy, Debug)]
enum Site<'desc>
{
    /// The argument at a declared operation's input port.
    Port(&'desc SortRef),
    /// The root, or an argument of a constructor, a results tuple, an
    /// instantiation or an undeclared operation.
    Elsewhere,
}

/// Check that `cell` sorts each variable a binding port of its left side binds
/// at that port's binders.
///
/// # Specification
/// - ensures: a variable the left side passes at an input port of a declared
///   operation whose telescope binds variables is bound there, at that port,
///   the first such occurrence deciding. One `UnsortedBinding` diagnostic at
///   the face's span, naming the variable, per right-hand-side occurrence of a
///   bound variable not at a declared input port whose telescope's sorts and
///   own sort are its binding port's, per instantiation of a variable no
///   binding port binds, and per instantiation whose argument count is not the
///   count of variables its binding port binds; in pre-order.
/// - panics: none.
/// - intension: one walk of the left side collecting the bound variables, one
///   of the right side carrying each node's site.
///
/// # Adequacy
/// - hypothesis: L3 — `let`'s body instantiated once per bound variable and β
///   over `lam` pass; `lam`'s body passed bare to `app`, which binds nothing
///   there, an instantiation at two arguments of a one-variable binding and an
///   instantiation of a variable no port binds each refuse naming the variable;
///   reading the site from the parent's constructor, or comparing the count of
///   binders and not their sorts, changes a verdict.
/// - witness: `wellformed::tests::a_bound_variable_is_used_under_its_binders_or_instantiated`
#[spec(
    captures: before = diagnostics.len(),
    ensures: diagnostics.get(before ..).is_some_and(|added| added.iter().all(|diagnostic| diagnostic.span == Maybe::Present(cell.provenance)
        && diagnostic.kind == WfKind::UnsortedBinding)),
)]
fn check_rule_binders(
    cell: &RuleFace,
    operations: &BTreeMap<&Name, &OperDesc>,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    let mut bound: BTreeMap<&Name, &SortRef> = BTreeMap::new();
    let mut pending = vec![cell.lhs.to_node()];
    while let Some(node) = pending.pop() {
        match node.view() {
            TermView::Op { name, args } => {
                let ports = operations
                    .get(name)
                    .map_or(&[][..], |operation| &*operation.arity.inputs);
                for (place, arg) in args.enumerate() {
                    if let (Some(port), TermView::Var(variable)) = (ports.get(place), arg.view())
                        && !port.bindings.is_empty()
                    {
                        let _first = bound.entry(variable).or_insert(port);
                    }
                    pending.push(arg);
                }
            },
            TermView::Ctor { args, .. }
            | TermView::Results { args }
            | TermView::Inst { args, .. }
            | TermView::Abs { args, .. } => {
                pending.extend(args);
            },
            TermView::Var(_) => {},
        }
    }
    let same_binders = |port: &SortRef, binding: &SortRef| {
        port.sort == binding.sort
            && port.bindings.len() == binding.bindings.len()
            && port
                .bindings
                .iter()
                .zip(&binding.bindings)
                .all(|(one, other)| one.sort == other.sort)
    };
    let mut sited = vec![(cell.rhs.to_node(), Site::Elsewhere)];
    while let Some((node, site)) = sited.pop() {
        match node.view() {
            TermView::Var(variable) => {
                let Some(&binding) = bound.get(variable)
                else {
                    continue;
                };
                if !matches!(site, Site::Port(port) if same_binders(port, binding)) {
                    diagnostics.push(located(
                        WfKind::UnsortedBinding,
                        named(&[&variable]),
                        format!(
                            "rule uses `{variable}`, which a binding port of its left side binds, \
                             where no port binds the same variables over the same sort: write it \
                             where one does, or apply it to one argument per variable it binds"
                        ),
                        cell.provenance,
                    ));
                }
            },
            TermView::Inst { name, args } => {
                match bound.get(name) {
                    Some(binding) if binding.bindings.len() == args.len() => {},
                    Some(binding) => diagnostics.push(located(
                        WfKind::UnsortedBinding,
                        named(&[&name]),
                        format!(
                            "rule applies `{name}` to {} arguments, but its binding port binds {} \
                             variables: an instantiation takes one argument per variable",
                            args.len(),
                            binding.bindings.len()
                        ),
                        cell.provenance,
                    )),
                    None => diagnostics.push(located(
                        WfKind::UnsortedBinding,
                        named(&[&name]),
                        format!(
                            "rule applies `{name}`, which no binding port of its left side binds: \
                             only a variable a port binds variables over takes arguments"
                        ),
                        cell.provenance,
                    )),
                }
                sited.extend(args.map(|arg| (arg, Site::Elsewhere)));
            },
            TermView::Op { name, args } => {
                let ports = operations
                    .get(name)
                    .map_or(&[][..], |operation| &*operation.arity.inputs);
                sited.extend(args.enumerate().map(|(place, arg)| {
                    (arg, ports.get(place).map_or(Site::Elsewhere, Site::Port))
                }));
            },
            TermView::Ctor { args, .. }
            | TermView::Results { args }
            | TermView::Abs { args, .. } => {
                sited.extend(args.map(|arg| (arg, Site::Elsewhere)));
            },
        }
    }
}

/// Append a `MisplacedAbstraction` diagnostic for each atom abstraction of
/// `cell` that stands where no port abstracts as many atoms.
///
/// # Specification
/// - ensures: one diagnostic per maximal chain of `bind a . …` that is not an
///   operation's argument at a port abstracting exactly as many atoms as the
///   chain is long, on either side, at the rule's provenance.
/// - panics: none.
/// - intension: one worklist pass over each side, each chain read once.
///
/// # Adequacy
/// - hypothesis: L3 — an abstraction at a `bind` port passes, and one at a port
///   that abstracts nothing, one at the root and one of the wrong length each
///   earn one diagnostic.
/// - witness: `wellformed::tests::an_abstraction_stands_at_a_port_that_abstracts`
#[spec(
    captures: before = diagnostics.len(),
    ensures: diagnostics.get(before ..).is_some_and(|added| added.iter().all(|diagnostic| diagnostic.span == Maybe::Present(cell.provenance)
        && diagnostic.kind == WfKind::MisplacedAbstraction)),
)]
fn check_abstractions(
    cell: &RuleFace,
    operations: &BTreeMap<&Name, &OperDesc>,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    for side in [&cell.lhs, &cell.rhs] {
        let mut pending: Vec<(TermNode<'_>, Option<&SortRef>)> = vec![(side.to_node(), None)];
        while let Some((node, port)) = pending.pop() {
            let mut depth = 0_usize;
            let mut body = node;
            while let TermView::Abs { mut args, .. } = body.view() {
                let Some(next) = args.next()
                else {
                    break;
                };
                depth = depth.saturating_add(1);
                body = next;
            }
            if depth > 0 && port.is_none_or(|port| port.abstractions.len() != depth) {
                diagnostics.push(located(
                    WfKind::MisplacedAbstraction,
                    named(&[]),
                    format!(
                        "rule abstracts {depth} atoms at `{body}` where no port abstracts as many: \
                         write `bind a . t` as an argument at a port written `bind (a : N) . T`",
                        body = body.to_term()
                    ),
                    cell.provenance,
                ));
            }
            match body.view() {
                TermView::Op { name, args } => {
                    let ports = operations
                        .get(name)
                        .map_or(&[][..], |operation| &*operation.arity.inputs);
                    pending.extend(args.enumerate().map(|(place, arg)| (arg, ports.get(place))));
                },
                TermView::Ctor { args, .. }
                | TermView::Results { args }
                | TermView::Inst { args, .. }
                | TermView::Abs { args, .. } => {
                    pending.extend(args.map(|arg| (arg, None)));
                },
                TermView::Var(_) => {},
            }
        }
    }
}

/// Append the diagnostics of `cell`'s freshness conditions: an
/// `UnknownFreshness` for each condition naming an atom no abstraction of the
/// rule abstracts or a variable its left side does not hold, then a `Capture`
/// for each variable and atom whose abstraction encloses some of the
/// variable's occurrences and not others, with no condition naming that atom
/// fresh for it: the variable's instance moves into the abstraction, or out of
/// it, and an occurrence of the atom in it would be captured or escape
/// (Fernández and Gabbay, _Nominal rewriting_, I&C 2007, § 3).
///
/// # Specification
/// - ensures: one `UnknownFreshness` per such condition, in written order, then
///   one `Capture` per such variable and atom, ordered by variable and then
///   atom, each at the rule's provenance; atoms and variables are compared by
///   their written names.
/// - panics: none.
/// - intension: one worklist pass over each side, the abstractions above the
///   node read off a stack cut back to its depth, so each occurrence counts
///   once against each distinct atom above it.
///
/// # Adequacy
/// - hypothesis: L3 — scope extrusion stating `a # q` passes and without it
///   earns one `Capture` for `q`, as does the converse law, where `q` leaves
///   the abstraction; a variable under the same abstractions on both sides
///   passes unstated; a condition naming an atom the rule never abstracts and
///   one naming no variable of the left side each earn one `UnknownFreshness`.
/// - witness: `wellformed::tests::a_metavariable_crossing_an_abstraction_names_its_atom_fresh`
#[spec(
    captures: before = diagnostics.len(),
    ensures: diagnostics.get(before ..).is_some_and(|added| added.iter().all(|diagnostic| diagnostic.span == Maybe::Present(cell.provenance)
        && matches!(diagnostic.kind, WfKind::UnknownFreshness | WfKind::Capture))),
)]
fn check_freshness(
    cell: &RuleFace,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    let mut atoms: BTreeSet<&Name> = BTreeSet::new();
    let mut held: BTreeSet<&Name> = BTreeSet::new();
    // Each variable's occurrences, and how many of them each atom encloses.
    let mut occurrences: BTreeMap<&Name, usize> = BTreeMap::new();
    let mut enclosed: BTreeMap<(&Name, &Name), usize> = BTreeMap::new();
    for (side, left) in [(&cell.lhs, true), (&cell.rhs, false)] {
        let mut stack: Vec<&Name> = Vec::new();
        let mut above: BTreeMap<&Name, usize> = BTreeMap::new();
        let mut pending: Vec<(TermNode<'_>, usize)> = vec![(side.to_node(), 0)];
        while let Some((node, depth)) = pending.pop() {
            while stack.len() > depth {
                if let Some(atom) = stack.pop()
                    && let Some(count) = above.get_mut(atom)
                {
                    *count = count.saturating_sub(1);
                    if *count == 0 {
                        let _left = above.remove(atom);
                    }
                }
            }
            let (variable, args) = match node.view() {
                TermView::Var(name) => (Some(name), None),
                TermView::Inst { name, args } => (Some(name), Some(args)),
                TermView::Abs { atom, args } => {
                    let _new = atoms.insert(atom);
                    stack.push(atom);
                    let count = above.entry(atom).or_insert(0);
                    *count = count.saturating_add(1);
                    pending.extend(args.map(|arg| (arg, depth.saturating_add(1))));
                    continue;
                },
                TermView::Op { args, .. }
                | TermView::Ctor { args, .. }
                | TermView::Results { args } => (None, Some(args)),
            };
            if let Some(variable) = variable {
                if left {
                    let _new = held.insert(variable);
                }
                let count = occurrences.entry(variable).or_insert(0);
                *count = count.saturating_add(1);
                for &atom in above.keys() {
                    let count = enclosed.entry((variable, atom)).or_insert(0);
                    *count = count.saturating_add(1);
                }
            }
            if let Some(args) = args {
                pending.extend(args.map(|arg| (arg, depth)));
            }
        }
    }
    let mut stated: BTreeSet<(&Name, &Name)> = BTreeSet::new();
    for condition in &cell.fresh {
        let _new = stated.insert((&condition.term, &condition.atom));
        let unknown = if !atoms.contains(&condition.atom) {
            Some(format!(
                "names the atom `{}`, which no abstraction of the rule abstracts",
                condition.atom
            ))
        }
        else if !held.contains(&condition.term) {
            Some(format!(
                "names `{}`, which no variable of the rule's left side is",
                condition.term
            ))
        }
        else {
            None
        };
        if let Some(unknown) = unknown {
            diagnostics.push(located(
                WfKind::UnknownFreshness,
                named(&[&condition.atom, &condition.term]),
                format!(
                    "the condition `{} # {}` {unknown}",
                    condition.atom, condition.term
                ),
                cell.provenance,
            ));
        }
    }
    for (&(variable, atom), &count) in &enclosed {
        if occurrences.get(variable).is_some_and(|&all| count < all)
            && !stated.contains(&(variable, atom))
        {
            diagnostics.push(located(
                WfKind::Capture,
                named(&[variable, atom]),
                format!(
                    "`{variable}` stands under `bind {atom}` on one side of the rule and outside \
                     it on the other, so an instance naming `{atom}` would be captured or escape: \
                     state `where {atom} # {variable}`"
                ),
                cell.provenance,
            ));
        }
    }
}

/// Append an `OutOfSignatureRule` diagnostic for each applied symbol of
/// `term` not present in `signature`.
///
/// # Specification
/// - ensures: one diagnostic per out-of-signature application, in pre-order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — known and foreign application heads are observed by
///   diagnostic count, order and the face's span; omitting an occurrence or
///   marking a known head changes the result.
/// - witness: `wellformed::tests::an_out_of_signature_cell_is_declined`
/// - witness: `wellformed::tests::diagnostics_preserve_phase_order_multiplicity_and_provenance`
#[spec(
    captures: before = diagnostics.len(),
    ensures: diagnostics.len() == before.saturating_add(term.applied_symbols().filter(|name| !signature.contains(name)).count())
        && diagnostics.get(before ..).is_some_and(|added| added.iter().all(|diagnostic| diagnostic.kind == WfKind::OutOfSignatureRule && diagnostic.span == Maybe::Present(span))),
)]
fn check_free_term_symbols(
    term: &FreeTerm,
    signature: &BTreeSet<&Name>,
    span: SurfaceSpan,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    for name in term.applied_symbols() {
        if !signature.contains(name) {
            diagnostics.push(located(
                WfKind::OutOfSignatureRule,
                named(&[&name]),
                format!("cell rule mentions symbol `{name}` not in the datatype's signature"),
                span,
            ));
        }
    }
}

/// Check that a bridge arity's three maps compose.
///
/// # Specification
/// - ensures: one diagnostic when `dest` and `factors` disagree on `|I|`, one
///   when `source` and `Σ factors` disagree on `|J|`, and one per `source`
///   entry past the inputs and per `dest` entry past the outputs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — composing maps and simultaneous dimension/range failures,
///   including repeated first-past indices, are observed through exact counts
///   and unlocated kinds; a missed endpoint or per-index deduplication differs.
/// - witness: `wellformed::tests::a_non_composing_arity_is_declined`
/// - witness: `wellformed::tests::diagnostics_preserve_phase_order_multiplicity_and_provenance`
#[spec(
    captures: before = diagnostics.len(),
    ensures: diagnostics.len() == before
        .saturating_add(usize::from(arity.dest.len() != arity.factors.len()))
        .saturating_add(usize::from(arity.source.len() != arity.factors.iter().fold(0_usize, |sum, count| sum.saturating_add(usize::try_from(*count).unwrap_or(usize::MAX)))))
        .saturating_add(arity.source.iter().filter(|index| usize::try_from(**index).unwrap_or(usize::MAX) >= arity.inputs.len()).count())
        .saturating_add(arity.dest.iter().filter(|index| usize::try_from(**index).unwrap_or(usize::MAX) >= arity.outputs.len()).count())
        && diagnostics.get(before ..).is_some_and(|added| added.iter().all(|diagnostic| diagnostic.kind == WfKind::ArityDoesNotCompose
            && diagnostic.span == Maybe::Absent(diagnostic_span::Absent::Unrecorded))),
)]
fn check_arity(
    arity: &BridgeArity,
    owner: &Name,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    let mut fail = |reason: String| {
        diagnostics.push(unlocated(
            WfKind::ArityDoesNotCompose,
            named(&[&owner]),
            format!("operation `{owner}`'s bridge arity does not compose: {reason}"),
        ));
    };

    // `t : I → B` has one entry per monomial, matching `|I| = factors.len()`.
    if arity.dest.len() != arity.factors.len() {
        fail(format!(
            "|I| mismatch: {} monomials by `factors` but {} by `dest`",
            arity.factors.len(),
            arity.dest.len()
        ));
    }
    // `s : J → A` has one entry per factor, matching `Σ factors`.
    let total_factors = arity
        .factors
        .iter()
        .map(|&count| usize::try_from(count).unwrap_or(usize::MAX))
        .fold(0_usize, usize::saturating_add);
    if arity.source.len() != total_factors {
        fail(format!(
            "|J| mismatch: Σ factors = {total_factors} but `source` has {} entries",
            arity.source.len()
        ));
    }
    // `s` lands in `A`, `t` lands in `B`.
    for &input in &arity.source {
        if usize::try_from(input).unwrap_or(usize::MAX) >= arity.inputs.len() {
            fail(format!(
                "`source` reads input {input} but there are only {} inputs",
                arity.inputs.len()
            ));
        }
    }
    for &output in &arity.dest {
        if usize::try_from(output).unwrap_or(usize::MAX) >= arity.outputs.len() {
            fail(format!(
                "`dest` feeds output {output} but there are only {} outputs",
                arity.outputs.len()
            ));
        }
    }
}

/// Derive the per-variable [`RuleVarMeta`] for a face's left-hand-side
/// variables.
///
/// Each variable's variance is the constant [`Variance::Producer`], and its
/// linearity is whether it occurs exactly once in the left-hand side. This is
/// the derivation an elaborator runs to populate [`RuleFace::vars`]; the
/// metadata is derived here, never declared (a surface attempt to declare it
/// is declined by [`check_desc`]).
///
/// # Specification
/// - ensures: one [`RuleVarMeta`] per distinct left-hand-side variable, in
///   first-occurrence order; `linear` is positive exactly when the variable
///   occurs once.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — ground terms, single and repeated variables, and a mixed
///   first-occurrence order have exact metadata records; sorting names,
///   duplicates, inverted linearity and the wrong variance change them.
/// - witness: `wellformed::tests::cell_var_meta_derivation_reads_variance_and_linearity`
/// - witness: `wellformed::tests::variable_metadata_preserves_first_occurrence_order`
#[inline]
#[must_use]
#[spec(ensures: |ref meta| lhs.to_node().vars().all(|name| meta.iter().any(|entry| &entry.var == name))
    && meta.iter().enumerate().all(|(index, entry)| {
        let occurrences = lhs.to_node().vars().filter(|name| **name == entry.var).count();
        occurrences > 0 && bool::from(entry.linear) == (occurrences == 1)
            && entry.variance == Variance::Producer
            && meta.iter().take(index).all(|prior| prior.var != entry.var)
    }) && meta.iter().zip(meta.iter().skip(1)).all(|(first, second)| lhs.to_node().vars().position(|name| *name == first.var)
        .zip(lhs.to_node().vars().position(|name| *name == second.var)).is_some_and(|(first, second)| first < second)))]
pub fn derive_cell_var_meta(lhs: &FreeTerm) -> Vec<RuleVarMeta>
{
    let occurrences = lhs.collect_vars();
    let mut seen: BTreeSet<&Name> = BTreeSet::new();
    let mut meta: Vec<RuleVarMeta> = Vec::new();
    for var in &occurrences {
        if !seen.insert(var) {
            continue;
        }
        let count = occurrences.iter().filter(|&other| other == var).count();
        meta.push(RuleVarMeta::new(
            var.clone(),
            Variance::Producer,
            RuleVariableLinearity::from(count == 1),
        ));
    }
    meta
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use super::*;
    use crate::arity::SortRef;
    use crate::boundary::MonomialCount;
    use crate::boundary::NominalSerial;
    use crate::circuit::CircuitBody;
    use crate::circuit::CircuitFrame;
    use crate::circuit::CircuitRedex;
    use crate::circuit::FrameHead;
    use crate::code::Attr;
    use crate::code::Code;
    use crate::code::ValueTypeRef;
    use crate::desc::CtorDesc;
    use crate::desc::DeclPolarity;
    use crate::desc::NominalId;
    use crate::desc::OperDesc;
    use crate::desc::SortDesc;
    use crate::desc::SortIndex;
    use crate::elaborate::RewritePort;
    use crate::rule::Freshness;
    use crate::test_support::Grade;

    /// The span every test face is read from.
    ///
    /// # Specification
    /// trivial.
    fn span() -> SurfaceSpan
    {
        SurfaceSpan::new(0_usize.into(), 1_usize.into())
    }

    #[test]
    fn the_sorting_discipline_indexes_the_description()
    {
        // A clean two-sorted signature: `Even` and `Odd`, with a constructor
        // targeting `Odd` and recursing at `Even`.
        let two_sorted: TheoryDesc<Grade> = TheoryDesc::new(
            NominalId::new(NominalSerial::from(0_u64), "Parity"),
            Vec::new(),
            [CtorDesc::new(
                "SuccEven",
                Code::var("Even"),
                "Odd",
                Attrs::empty(),
            )],
            Vec::new(),
            Vec::new(),
            DeclPolarity::Data,
            Attrs::empty(),
        )
        .with_sorts([
            SortDesc::family("Even", DeclPolarity::Data, [SortIndex::new("odd", "Odd")]),
            SortDesc::family("Odd", DeclPolarity::Data, []),
        ]);
        assert!(
            check_desc(&two_sorted).is_empty(),
            "a constructor may target and recurse at any declared sort"
        );

        // A duplicate sort name is ambiguous.
        let duplicated = two_sorted.clone().with_sorts([
            SortDesc::new("Even", DeclPolarity::Data),
            SortDesc::new("Even", DeclPolarity::Data),
        ]);
        let diagnostics = check_desc(&duplicated);
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::DuplicateSortName),
            "a duplicate sort name is declined"
        );

        // A result sort outside the declared set is foreign.
        let foreign_result = two_sorted
            .clone()
            .with_sorts([SortDesc::new("Even", DeclPolarity::Data)]);
        let diagnostics = check_desc(&foreign_result);
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::UnknownResultSort),
            "an undeclared result sort is declined"
        );

        // A recursive occurrence outside the declared set is foreign.
        let foreign_var = two_sorted
            .clone()
            .with_sorts([SortDesc::new("Odd", DeclPolarity::Data)]);
        let diagnostics = check_desc(&foreign_var);
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::UnknownVarSort),
            "an undeclared var sort is declined"
        );

        // A sort polarity disagreeing with the declaration's is outside the
        // polarity-homogeneous fragment.
        let disagreeing = two_sorted.with_sorts([
            SortDesc::family("Even", DeclPolarity::Codata, [SortIndex::new("odd", "Odd")]),
            SortDesc::family("Odd", DeclPolarity::Data, []),
        ]);
        let diagnostics = check_desc(&disagreeing);
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::SortPolarityDisagreement),
            "a heterogeneous sort polarity is declined"
        );
    }

    #[test]
    fn the_constructor_layer_agrees_with_the_bridge_shape()
    {
        // `Cons = a × var List : List` reads as the single-output arity
        // `(a, List) --> List` — the container view under which the
        // constructor layer and `BridgeArity` carry one shape.
        let cons = CtorDesc::new(
            "Cons",
            Code::prod(
                Code::field(ValueTypeRef::param("a"), Grade::One, Attrs::empty()),
                Code::var("List"),
            ),
            "List",
            Attrs::empty(),
        );
        let arity = cons.arity();
        assert_eq!(
            MonomialCount::from(1_usize),
            arity.monomials(),
            "a product payload is one monomial"
        );
        assert_eq!(&[2_u32], &*arity.factors, "the monomial has two factors");
        assert_eq!(
            &[0_u32, 1_u32],
            &*arity.source,
            "factors read ports in order"
        );
        assert_eq!(&[0_u32], &*arity.dest, "the monomial feeds the sole output");
        assert_eq!(
            Some("List"),
            arity.outputs.first().map(|port| port.sort.as_ref()),
            "the output port reads at the result sort"
        );
        let input_sorts: Vec<&str> = arity.inputs.iter().map(|port| port.sort.as_ref()).collect();
        assert_eq!(
            vec!["a", "List"],
            input_sorts,
            "input ports read at the leaf sorts in order"
        );
        let mut diagnostics = Vec::new();
        check_arity(&arity, &Name::from("Cons"), &mut diagnostics);
        assert!(diagnostics.is_empty(), "the product arity composes");

        // An inline sum contributes one monomial per summand, both feeding
        // the one output.
        let mk: CtorDesc<Grade> = CtorDesc::new(
            "MkBool",
            Code::sum(Code::unit(), Code::unit()),
            "BoolSum",
            Attrs::empty(),
        );
        let arity = mk.arity();
        assert_eq!(
            MonomialCount::from(2_usize),
            arity.monomials(),
            "an inline sum is one monomial per summand"
        );
        assert_eq!(
            &[0_u32, 0_u32],
            &*arity.dest,
            "both monomials feed the output"
        );
        let mut diagnostics = Vec::new();
        check_arity(&arity, &Name::from("MkBool"), &mut diagnostics);
        assert!(
            diagnostics.is_empty(),
            "the derived constructor arity composes"
        );
    }

    #[test]
    fn a_clean_description_passes()
    {
        let face = RuleFace::new(
            FreeTerm::op("id", [FreeTerm::ctor("Zero", [])]),
            FreeTerm::ctor("Zero", []),
            Vec::new(),
            span(),
        );
        let op = OperDesc::new(
            "id",
            BridgeArity::single_output([SortRef::new("m", "Nat")], SortRef::new("q", "Nat")),
            Attrs::empty(),
        );
        assert!(
            check_desc(&nat_with(vec![face], vec![op], Attrs::empty())).is_empty(),
            "a well-formed description has no diagnostics"
        );
    }

    #[test]
    fn a_shape_refuses_a_repeated_face_and_a_point_past_it()
    {
        use crate::boundary::ShapePoint;
        use crate::boundary::ShapeSize;
        use crate::desc::ShapeFace;

        let points = |raw: &[usize]| {
            raw.iter()
                .copied()
                .map(ShapePoint::from)
                .collect::<Vec<_>>()
        };
        let shaped = |faces: Vec<ShapeFace>| {
            nat_with(Vec::new(), Vec::new(), Attrs::empty()).with_shape(TheoryShape::new(
                "Square",
                ShapeSize::from(4_usize),
                faces,
            ))
        };
        let left = ShapeFace::new("left", points(&[0, 2]));
        let right = ShapeFace::new("right", points(&[1, 3]));
        assert!(
            check_desc(&shaped(vec![left.clone(), right.clone()])).is_empty(),
            "two faces of the square named apart pass"
        );
        let kinds = |faces: Vec<ShapeFace>| {
            check_desc(&shaped(faces))
                .into_iter()
                .map(|diagnostic| (diagnostic.kind, diagnostic.span))
                .collect::<Vec<_>>()
        };
        let absent = Maybe::Absent(diagnostic_span::Absent::Unrecorded);
        assert_eq!(
            kinds(vec![
                left.clone(),
                ShapeFace::new("far", points(&[1, 4])),
                right,
                ShapeFace::new("left", points(&[3])),
            ]),
            [
                (WfKind::FaceOutsideShape, absent),
                (WfKind::DuplicateFaceName, absent)
            ],
            "the point past the square and the second `left` are each reported once, in face order"
        );
        assert_eq!(
            kinds(vec![left, ShapeFace::new("left", points(&[5]))]),
            [
                (WfKind::DuplicateFaceName, absent),
                (WfKind::FaceOutsideShape, absent)
            ],
            "one face both repeated and past the shape earns both, the name first"
        );
    }

    #[test]
    fn an_atom_is_taken_and_never_returned()
    {
        let named = |ops: Vec<OperDesc>| {
            nat_with(Vec::new(), ops, Attrs::empty()).with_sorts([
                SortDesc::new("Nat", DeclPolarity::Data),
                SortDesc {
                    representability: Representability::Atom,
                    ..SortDesc::new("Name", DeclPolarity::Data)
                },
            ])
        };
        let operation = |name: &str, inputs: Vec<SortRef>, outputs: Vec<SortRef>| {
            OperDesc::new(name, BridgeArity::tupled(inputs, outputs), Attrs::empty())
        };
        let rename = operation(
            "rename",
            vec![SortRef::new("a", "Name"), SortRef::new("t", "Nat")],
            vec![SortRef::new("u", "Nat")],
        );
        assert!(
            check_desc(&named(vec![rename.clone()])).is_empty(),
            "an operation taking an atom and returning a term passes"
        );
        let kinds = |ops: Vec<OperDesc>| {
            check_desc(&named(ops))
                .into_iter()
                .map(|diagnostic| (diagnostic.kind, diagnostic.span))
                .collect::<Vec<_>>()
        };
        let absent = Maybe::Absent(diagnostic_span::Absent::Unrecorded);
        assert_eq!(
            kinds(vec![
                rename,
                operation("fresh", vec![SortRef::new("t", "Nat")], vec![SortRef::new(
                    "a", "Name"
                )]),
                operation("split", vec![SortRef::new("t", "Nat")], vec![
                    SortRef::new("u", "Nat"),
                    SortRef::new("b", "Name"),
                ]),
            ]),
            [(WfKind::AtomResult, absent), (WfKind::AtomResult, absent)],
            "each output at the atom sort is refused once, a term output beside it not"
        );
        assert!(
            check_desc(
                &nat_with(
                    Vec::new(),
                    vec![operation("fresh", vec![SortRef::new("t", "Nat")], vec![
                        SortRef::new("a", "Name")
                    ])],
                    Attrs::empty()
                )
                .with_sorts([
                    SortDesc::new("Nat", DeclPolarity::Data),
                    SortDesc::new("Name", DeclPolarity::Data),
                ])
            )
            .is_empty(),
            "the same output at an ordinary sort passes: the refusal reads the atom sort"
        );
    }

    #[test]
    fn a_port_abstracts_atoms_of_an_atom_sort()
    {
        let named = |name: Representability, ops: Vec<OperDesc>| {
            nat_with(Vec::new(), ops, Attrs::empty()).with_sorts([
                SortDesc::new("Nat", DeclPolarity::Data),
                SortDesc {
                    representability: name,
                    ..SortDesc::new("Name", DeclPolarity::Data)
                },
            ])
        };
        let nu = |over: &str| {
            OperDesc::new(
                "nu",
                BridgeArity::tupled(
                    [SortRef::new("p", "Nat").abstracting([SortIndex::new("a", over)])],
                    [SortRef::new("q", "Nat")],
                ),
                Attrs::empty(),
            )
        };
        assert!(
            check_desc(&named(Representability::Atom, vec![nu("Name")])).is_empty(),
            "a port abstracting an atom of an atom sort passes"
        );
        let kinds = |desc: &TheoryDesc<Grade>| {
            check_desc(desc)
                .into_iter()
                .map(|diagnostic| diagnostic.kind)
                .collect::<Vec<_>>()
        };
        assert_eq!(
            kinds(&named(Representability::Ordinary, vec![nu("Name")])),
            [WfKind::NonAtomAbstraction],
            "an abstraction over an ordinary sort is refused by name"
        );
        assert_eq!(
            kinds(&named(Representability::Atom, vec![nu("Absent")])),
            [WfKind::NonAtomAbstraction],
            "an abstraction over an undeclared sort is refused by the same name"
        );
        assert_eq!(
            kinds(&named(Representability::Representable, vec![nu("Name")])),
            [WfKind::NonAtomAbstraction],
            "a representable sort is bound by `pi+`, never abstracted"
        );
    }

    #[test]
    fn an_abstraction_stands_at_a_port_that_abstracts()
    {
        let atoms = |count: usize| {
            ["a0", "a1"]
                .into_iter()
                .take(count)
                .map(|name| SortIndex::new(name, "Name"))
                .collect::<Vec<_>>()
        };
        let op = |name: &str, inputs: Vec<SortRef>| {
            OperDesc::new(
                name,
                BridgeArity::single_output(inputs, SortRef::new("r", "Nat")),
                Attrs::empty(),
            )
        };
        let ops = || {
            vec![
                op("nu", vec![SortRef::new("p", "Nat").abstracting(atoms(1))]),
                op("nu2", vec![SortRef::new("p", "Nat").abstracting(atoms(2))]),
                op("par", vec![
                    SortRef::new("p", "Nat"),
                    SortRef::new("q", "Nat"),
                ]),
            ]
        };
        let desc = |lhs: FreeTerm, rhs: FreeTerm| {
            nat_with(
                vec![RuleFace::new(lhs, rhs, Vec::new(), span())],
                ops(),
                Attrs::empty(),
            )
            .with_sorts([SortDesc::new("Nat", DeclPolarity::Data), SortDesc {
                representability: Representability::Atom,
                ..SortDesc::new("Name", DeclPolarity::Data)
            }])
        };
        let misplaced = |lhs: FreeTerm, rhs: FreeTerm| {
            check_desc(&desc(lhs, rhs))
                .into_iter()
                .filter(|diagnostic| diagnostic.kind == WfKind::MisplacedAbstraction)
                .count()
        };
        let var = FreeTerm::var;
        let abs = |body: FreeTerm| FreeTerm::abs("a", body);
        let scope = || FreeTerm::op("par", [FreeTerm::op("nu", [abs(var("p"))]), var("q")]);
        let extruded = || FreeTerm::op("nu", [abs(FreeTerm::op("par", [var("p"), var("q")]))]);
        assert_eq!(
            0,
            misplaced(scope(), extruded()),
            "scope extrusion abstracts at `nu`"
        );
        assert_eq!(
            0,
            misplaced(FreeTerm::op("nu2", [abs(abs(var("p")))]), var("p")),
            "two abstractions at a port abstracting two atoms"
        );
        assert_eq!(
            1,
            misplaced(FreeTerm::op("par", [abs(var("p")), var("q")]), var("q")),
            "`par` abstracts nothing"
        );
        assert_eq!(
            1,
            misplaced(scope(), abs(var("q"))),
            "an abstraction at the root"
        );
        assert_eq!(
            1,
            misplaced(FreeTerm::op("nu2", [abs(var("p"))]), var("p")),
            "one abstraction where the port abstracts two"
        );
    }

    #[test]
    fn a_metavariable_crossing_an_abstraction_names_its_atom_fresh()
    {
        let op = |name: &str, inputs: Vec<SortRef>| {
            OperDesc::new(
                name,
                BridgeArity::single_output(inputs, SortRef::new("r", "Nat")),
                Attrs::empty(),
            )
        };
        let ops = || {
            vec![
                op("nu", vec![
                    SortRef::new("p", "Nat").abstracting([SortIndex::new("a", "Name")]),
                ]),
                op("par", vec![
                    SortRef::new("p", "Nat"),
                    SortRef::new("q", "Nat"),
                ]),
            ]
        };
        let found = |lhs: FreeTerm, rhs: FreeTerm, fresh: &[(&str, &str)]| {
            let face = RuleFace::new(lhs, rhs, Vec::new(), span()).with_fresh(
                fresh
                    .iter()
                    .map(|&(atom, term)| Freshness::new(atom, term))
                    .collect::<Vec<_>>(),
            );
            let desc = nat_with(vec![face], ops(), Attrs::empty()).with_sorts([
                SortDesc::new("Nat", DeclPolarity::Data),
                SortDesc {
                    representability: Representability::Atom,
                    ..SortDesc::new("Name", DeclPolarity::Data)
                },
            ]);
            check_desc(&desc)
                .into_iter()
                .filter(|diagnostic| {
                    matches!(diagnostic.kind, WfKind::Capture | WfKind::UnknownFreshness)
                })
                .map(|diagnostic| (diagnostic.kind, diagnostic.span))
                .collect::<Vec<_>>()
        };
        let var = FreeTerm::var;
        let nu = |body: FreeTerm| FreeTerm::op("nu", [FreeTerm::abs("a", body)]);
        let par = |left: FreeTerm, right: FreeTerm| FreeTerm::op("par", [left, right]);
        let scope = || par(nu(var("p")), var("q"));
        let extruded = || nu(par(var("p"), var("q")));
        let at = |kind: WfKind| (kind, Maybe::Present(span()));
        assert_eq!(
            found(scope(), extruded(), &[("a", "q")]),
            [],
            "`q` enters the abstraction fresh for `a`, `p` stays under it"
        );
        assert_eq!(
            found(scope(), extruded(), &[]),
            [at(WfKind::Capture)],
            "`q` enters the abstraction unstated"
        );
        assert_eq!(
            found(extruded(), scope(), &[]),
            [at(WfKind::Capture)],
            "`q` leaves the abstraction unstated"
        );
        assert_eq!(
            found(scope(), extruded(), &[("b", "q"), ("a", "r")]),
            [
                at(WfKind::UnknownFreshness),
                at(WfKind::UnknownFreshness),
                at(WfKind::Capture),
            ],
            "an atom no abstraction names, then a variable the left side lacks"
        );
    }

    #[test]
    fn a_results_tuple_stands_only_at_a_right_hand_root()
    {
        let divmod = || {
            OperDesc::new(
                "divmod",
                BridgeArity::tupled([SortRef::new("m", "Nat"), SortRef::new("n", "Nat")], [
                    SortRef::new("q", "Nat"),
                    SortRef::new("r", "Nat"),
                ]),
                Attrs::empty(),
            )
        };
        let lhs = || FreeTerm::op("divmod", [FreeTerm::var("m"), FreeTerm::var("n")]);
        let pair = || FreeTerm::results([FreeTerm::var("n"), FreeTerm::var("m")]);
        for (face, misplaced) in [
            (RuleFace::new(lhs(), pair(), Vec::new(), span()), 0_usize),
            (
                RuleFace::new(lhs(), FreeTerm::ctor("Succ", [pair()]), Vec::new(), span()),
                1,
            ),
            (
                RuleFace::new(
                    FreeTerm::op("divmod", [pair(), FreeTerm::var("n")]),
                    FreeTerm::results([pair(), FreeTerm::var("m")]),
                    Vec::new(),
                    span(),
                ),
                2,
            ),
        ] {
            let diagnostics = check_desc(&nat_with(vec![face], vec![divmod()], Attrs::empty()));
            assert_eq!(
                misplaced,
                diagnostics
                    .iter()
                    .filter(|diagnostic| diagnostic.kind == WfKind::MisplacedResults)
                    .count()
            );
            assert_eq!(misplaced, diagnostics.len(), "{diagnostics:?}");
        }
    }

    #[test]
    fn an_out_of_signature_cell_is_declined()
    {
        // `bogus(x) ==> x`: `bogus` is not a constructor or op of `Nat`.
        let face = RuleFace::new(
            FreeTerm::op("bogus", [FreeTerm::var("x")]),
            FreeTerm::var("x"),
            Vec::new(),
            span(),
        );
        let diagnostics = check_desc(&nat_with(vec![face], Vec::new(), Attrs::empty()));
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::OutOfSignatureRule
                    && diag.message.as_ref().contains("bogus")),
            "an out-of-signature symbol is declined"
        );
    }

    #[test]
    fn a_fresh_right_hand_side_variable_is_declined()
    {
        // `Succ(x) ==> y`: `y` is unbound.
        let face = RuleFace::new(
            FreeTerm::ctor("Succ", [FreeTerm::var("x")]),
            FreeTerm::var("y"),
            Vec::new(),
            span(),
        );
        let diagnostics = check_desc(&nat_with(vec![face], Vec::new(), Attrs::empty()));
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::UnboundRhsVariable
                    && diag.message.as_ref().contains('y')),
            "a fresh right-hand-side variable is declined"
        );
    }

    #[test]
    fn a_bound_variable_is_used_under_its_binders_or_instantiated()
    {
        let op = |name: &str, inputs: Vec<SortRef>| {
            OperDesc::new(
                name,
                BridgeArity::single_output(inputs, SortRef::new("r", "Nat")),
                Attrs::empty(),
            )
        };
        let over = |binder: &str| SortRef::new("t", "Nat").pi_plus([SortIndex::new("x", binder)]);
        let ops = || {
            vec![
                op("let", vec![SortRef::new("u", "Nat"), over("Nat")]),
                op("lam", vec![over("Nat")]),
                op("lamZ", vec![over("Zed")]),
                op("app", vec![
                    SortRef::new("f", "Nat"),
                    SortRef::new("u", "Nat"),
                ]),
            ]
        };
        let var = FreeTerm::var;
        let bind = || FreeTerm::op("let", [var("u"), var("t")]);
        let redex = || FreeTerm::op("app", [FreeTerm::op("lam", [var("t")]), var("u")]);
        let refusals = |lhs: FreeTerm, rhs: FreeTerm| {
            check_desc(&nat_with(
                vec![RuleFace::new(lhs, rhs, Vec::new(), span())],
                ops(),
                Attrs::empty(),
            ))
            .into_iter()
            .filter(|diagnostic| diagnostic.kind == WfKind::UnsortedBinding)
            .map(|diagnostic| String::from(diagnostic.message.as_ref()))
            .collect::<Vec<_>>()
        };
        for (lhs, rhs, what) in [
            (
                bind(),
                FreeTerm::inst("t", [var("u")]),
                "ζ instantiates `let`'s body",
            ),
            (
                redex(),
                FreeTerm::inst("t", [var("u")]),
                "β instantiates `lam`'s body",
            ),
            (
                redex(),
                FreeTerm::op("lam", [var("t")]),
                "`lam`'s body stands where `lam` binds it again",
            ),
        ] {
            assert_eq!(refusals(lhs, rhs), Vec::<String>::new(), "{what}");
        }
        for (lhs, rhs, named, what) in [
            (
                redex(),
                FreeTerm::op("app", [var("t"), var("u")]),
                "`t`",
                "`app` binds nothing at its first port",
            ),
            (
                bind(),
                FreeTerm::ctor("Succ", [var("t")]),
                "`t`",
                "a constructor's field binds nothing",
            ),
            (
                redex(),
                FreeTerm::op("lamZ", [var("t")]),
                "`t`",
                "`lamZ` binds as many variables over another sort",
            ),
            (
                bind(),
                FreeTerm::inst("t", [var("u"), var("u")]),
                "`t` to 2 arguments",
                "one variable bound, two arguments",
            ),
            (
                bind(),
                FreeTerm::inst("u", [var("u")]),
                "`u`, which no binding port",
                "no port binds over `u`",
            ),
        ] {
            let messages = refusals(lhs, rhs);
            assert!(
                messages.len() == 1 && messages.iter().all(|message| message.contains(named)),
                "{what}: {messages:?}"
            );
        }
    }

    #[test]
    fn a_non_composing_arity_is_declined()
    {
        // `dest` feeds output 5 but there are no outputs.
        let arity = BridgeArity::new(
            [SortRef::new("m", "Nat")],
            [1_u32],
            [0_u32],
            [5_u32],
            Vec::new(),
        );
        let op = OperDesc::new("bad", arity, Attrs::empty());
        let diagnostics = check_desc(&nat_with(Vec::new(), vec![op], Attrs::empty()));
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::ArityDoesNotCompose),
            "a non-composing arity is declined"
        );
    }

    #[test]
    fn the_congruence_circuit_rule_checks_against_its_sphere()
    {
        // The `cong2` block: `add(x, y)` derived as the source, `add(x′, y′)`
        // as the target, against the sphere its declaration fixes.
        let rule = CircuitRule::new(
            "cong2",
            congruence_sphere(FreeTerm::op("add", [
                FreeTerm::var("x\u{2032}"),
                FreeTerm::var("y\u{2032}"),
            ])),
            congruence_body(),
        );
        let desc = nat_with(Vec::new(), vec![add_op()], Attrs::empty()).with_circuits([rule]);
        assert!(
            check_desc(&desc).is_empty(),
            "the derived pair is the pair the declared sphere fixes"
        );
    }

    #[test]
    fn a_boundary_mismatched_circuit_rule_is_declined()
    {
        // The same wiring under a sphere whose target is `add(x′, y)`: the
        // second redex is glued in the declaration but not in the body.
        let rule = CircuitRule::new(
            "cong2",
            congruence_sphere(FreeTerm::op("add", [
                FreeTerm::var("x\u{2032}"),
                FreeTerm::var("y"),
            ])),
            congruence_body(),
        );
        let desc = nat_with(Vec::new(), vec![add_op()], Attrs::empty()).with_circuits([rule]);
        let diagnostics = check_desc(&desc);
        let mismatch = diagnostics
            .iter()
            .find(|diag| diag.kind == WfKind::DerivedBoundaryMismatch)
            .expect("the mismatched target is declined");
        let message = mismatch.message.as_ref();
        assert!(
            message.contains("cong2") && message.contains("target"),
            "the diagnostic names the rule and the mismatched side: {message}"
        );
        assert!(
            message.contains("add(x\u{2032}, y\u{2032})") && message.contains("add(x\u{2032}, y)"),
            "the diagnostic names both the derived and the declared boundary: {message}"
        );
        assert_eq!(
            1,
            diagnostics
                .iter()
                .filter(|diag| diag.kind == WfKind::DerivedBoundaryMismatch)
                .count(),
            "the matching source boundary raises nothing"
        );
    }

    #[test]
    fn an_out_of_signature_circuit_frame_is_declined()
    {
        // The frame applies `frobnicate`, which `Nat` does not declare; the
        // redex heads `p` and `q` are ports and are not signature symbols.
        let body = CircuitBody::new(
            [CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Op("frobnicate".into()),
                [FreeTerm::var("x")],
                "z",
            ))],
            "z",
        );
        let rule = CircuitRule::new(
            "bogus",
            RuleFace::new(
                FreeTerm::op("frobnicate", [FreeTerm::var("x")]),
                FreeTerm::op("frobnicate", [FreeTerm::var("x")]),
                Vec::new(),
                span(),
            ),
            body,
        );
        let desc = nat_with(Vec::new(), Vec::new(), Attrs::empty()).with_circuits([rule]);
        let diagnostics = check_desc(&desc);
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::OutOfSignatureRule
                    && diag
                        .message
                        .as_ref()
                        .contains("frame applies symbol `frobnicate`")),
            "an out-of-signature frame head is declined"
        );
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::OutOfSignatureRule
                    && diag.message.as_ref().contains("cell rule mentions symbol")),
            "and so is the declared sphere that names it"
        );
        assert!(
            !diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::DerivedBoundaryMismatch),
            "the wiring still derives the sphere it was declared at"
        );
    }

    #[test]
    fn a_cyclic_circuit_wiring_is_declined()
    {
        // `node : add(b, b) --> (a); node : add(a, a) --> (b);` — no boundary
        // term unfolds, so the rule is refused before any comparison.
        let body = CircuitBody::new(
            [
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("b"), FreeTerm::var("b")],
                    "a",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("a"), FreeTerm::var("a")],
                    "b",
                )),
            ],
            "a",
        );
        let rule = CircuitRule::new("loop", congruence_sphere(FreeTerm::var("a")), body);
        let desc = nat_with(Vec::new(), vec![add_op()], Attrs::empty()).with_circuits([rule]);
        let diagnostics = check_desc(&desc);
        let cyclic = diagnostics
            .iter()
            .find(|diag| diag.kind == WfKind::CyclicCircuitWiring)
            .expect("a cyclic wiring is declined");
        assert!(
            cyclic.message.as_ref().contains('a'),
            "the diagnostic names the port reached from itself"
        );
        assert!(
            !diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::DerivedBoundaryMismatch),
            "no boundary comparison is reported for a wiring that derives nothing"
        );
    }

    #[test]
    fn a_declared_telescope_admits_the_redex_heads_it_names()
    {
        // `rule cong2 : (rule p : Nat ==> Nat, rule q : Nat ==> Nat, …)`: both
        // redex heads are ports of the rule's own telescope, and neither is a
        // signature symbol.
        let rule = CircuitRule::new(
            "cong2",
            congruence_sphere(FreeTerm::op("add", [
                FreeTerm::var("x\u{2032}"),
                FreeTerm::var("y\u{2032}"),
            ])),
            congruence_body(),
        )
        .with_ports([
            RewritePort::sorted("p", "Nat"),
            RewritePort::sorted("q", "Nat"),
        ]);
        let desc = nat_with(Vec::new(), vec![add_op()], Attrs::empty()).with_circuits([rule]);
        assert!(
            check_desc(&desc).is_empty(),
            "a redex head the telescope declares is not an out-of-signature symbol"
        );
    }

    #[test]
    fn a_redex_applying_an_undeclared_port_is_declined()
    {
        // The same wiring with only `p` in the telescope: `q` is applied by a
        // redex line but bound nowhere.
        let rule = CircuitRule::new(
            "cong2",
            congruence_sphere(FreeTerm::op("add", [
                FreeTerm::var("x\u{2032}"),
                FreeTerm::var("y\u{2032}"),
            ])),
            congruence_body(),
        )
        .with_ports([RewritePort::sorted("p", "Nat")]);
        let desc = nat_with(Vec::new(), vec![add_op()], Attrs::empty()).with_circuits([rule]);
        let diagnostics = check_desc(&desc);
        let unknown = diagnostics
            .iter()
            .find(|diag| diag.kind == WfKind::UnknownRewritePort)
            .expect("an undeclared redex head is declined");
        assert!(
            unknown.message.as_ref().contains('q'),
            "the diagnostic names the rewrite the telescope does not declare"
        );
        assert_eq!(
            1,
            diagnostics.len(),
            "and the declared port is not reported alongside it"
        );
    }

    /// The `cong2` wiring: two disjoint redexes whiskered into one `add`
    /// frame.
    ///
    /// # Specification
    /// trivial.
    fn congruence_body() -> CircuitBody
    {
        CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::var("x\u{2032}"),
                    "x\u{2032}",
                )),
                CircuitNode::Redex(CircuitRedex::new(
                    "q",
                    FreeTerm::var("y"),
                    FreeTerm::var("y\u{2032}"),
                    "y\u{2032}",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("x\u{2032}"), FreeTerm::var("y\u{2032}")],
                    "z",
                )),
            ],
            "z",
        )
    }

    /// A sphere whose source is `add(x, y)` and whose target is `target`.
    ///
    /// # Specification
    /// trivial.
    fn congruence_sphere(target: FreeTerm) -> RuleFace
    {
        RuleFace::new(
            FreeTerm::op("add", [FreeTerm::var("x"), FreeTerm::var("y")]),
            target,
            Vec::new(),
            span(),
        )
    }

    /// The `add : (Nat, Nat) --> Nat` operation the congruence frame applies.
    ///
    /// # Specification
    /// trivial.
    fn add_op() -> OperDesc
    {
        OperDesc::new(
            "add",
            BridgeArity::single_output(
                [SortRef::new("m", "Nat"), SortRef::new("n", "Nat")],
                SortRef::new("q", "Nat"),
            ),
            Attrs::empty(),
        )
    }

    #[test]
    fn declaring_derived_metadata_is_declined()
    {
        // The declined-declaration golden: a constructor declares the
        // reserved-derived marker `variance`.
        let attrs = Attrs::new([Attr::marker("variance")]);
        let diagnostics = check_desc(&nat_with(Vec::new(), Vec::new(), attrs));
        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.kind == WfKind::DeclaresDerivedMetadata
                    && diag.message.as_ref().contains("variance")),
            "declaring derived variance metadata is declined"
        );
    }

    /// A minimal `Nat`-like description with the given faces, operations and
    /// `Succ` attributes.
    ///
    /// # Specification
    /// trivial.
    fn nat_with(
        cells: Vec<RuleFace>,
        ops: Vec<OperDesc>,
        attrs: Attrs,
    ) -> TheoryDesc<Grade>
    {
        TheoryDesc::new(
            NominalId::new(NominalSerial::from(0_u64), "Nat"),
            Vec::new(),
            [
                CtorDesc::new("Zero", Code::unit(), "Nat", Attrs::empty()),
                CtorDesc::new("Succ", Code::var("Nat"), "Nat", attrs),
            ],
            ops,
            cells,
            DeclPolarity::Data,
            Attrs::empty(),
        )
    }

    #[test]
    fn cell_var_meta_derivation_reads_variance_and_linearity()
    {
        // `f(x, g(x))`: `x` occurs twice (non-linear), variance constant
        // Producer.
        let lhs = FreeTerm::op("f", [
            FreeTerm::var("x"),
            FreeTerm::ctor("g", [FreeTerm::var("x")]),
        ]);
        let meta = derive_cell_var_meta(&lhs);
        assert_eq!(1, meta.len(), "one distinct variable");
        assert_eq!("x", meta[0].var.as_ref(), "the variable is `x`");
        assert_eq!(
            Variance::Producer,
            meta[0].variance,
            "variance is the constant"
        );
        assert!(
            !bool::from(meta[0].linear),
            "a twice-occurring variable is non-linear"
        );

        // `Succ(n)`: `n` occurs once (linear).
        let linear = derive_cell_var_meta(&FreeTerm::ctor("Succ", [FreeTerm::var("n")]));
        assert!(
            bool::from(linear[0].linear),
            "a once-occurring variable is linear"
        );
    }

    #[test]
    fn diagnostics_preserve_phase_order_multiplicity_and_provenance()
    {
        let face_span = SurfaceSpan::new(11_usize.into(), 17_usize.into());
        let circuit_span = SurfaceSpan::new(21_usize.into(), 27_usize.into());
        let face = RuleFace::new(
            FreeTerm::op("outside", [FreeTerm::var("x")]),
            FreeTerm::op("elsewhere", [FreeTerm::var("y"), FreeTerm::var("y")]),
            [],
            face_span,
        );
        let malformed = OperDesc::new(
            "broken",
            BridgeArity::new([SortRef::new("x", "Nat")], [2, 0], [1, 1, 0], [1], [
                SortRef::new("y", "Nat"),
            ]),
            Attrs::empty(),
        );
        let mut desc = nat_with(
            vec![face],
            vec![malformed],
            Attrs::new([
                Attr::marker("linearity"),
                Attr::marker("variance"),
                Attr::marker("linear"),
                Attr::marker("variance"),
            ]),
        );
        desc.sorts = alloc::boxed::Box::from([
            SortDesc::new("Nat", DeclPolarity::Data),
            SortDesc::new("Nat", DeclPolarity::Codata),
        ]);
        desc.ctors[1].result = Name::from("Foreign");
        desc.ctors[1].code = Code::prod(Code::var("Foreign"), Code::var("Foreign"));
        let sphere = RuleFace::new(FreeTerm::var("q"), FreeTerm::var("r"), [], circuit_span);
        desc = desc.with_circuits([CircuitRule::new(
            "boundary",
            sphere,
            CircuitBody::new([], "x"),
        )]);
        let absent = Maybe::Absent(diagnostic_span::Absent::Unrecorded);
        let mut expected = vec![
            (WfKind::DuplicateSortName, absent),
            (WfKind::SortPolarityDisagreement, absent),
            (WfKind::UnknownResultSort, absent),
            (WfKind::UnknownVarSort, absent),
            (WfKind::UnknownVarSort, absent),
            (WfKind::DeclaresDerivedMetadata, absent),
            (WfKind::DeclaresDerivedMetadata, absent),
            (WfKind::DeclaresDerivedMetadata, absent),
            (WfKind::OutOfSignatureRule, Maybe::Present(face_span)),
            (WfKind::OutOfSignatureRule, Maybe::Present(face_span)),
            (WfKind::UnboundRhsVariable, Maybe::Present(face_span)),
            (WfKind::UnboundRhsVariable, Maybe::Present(face_span)),
        ];
        expected.extend([(WfKind::ArityDoesNotCompose, absent); 5]);
        expected.extend(
            [(
                WfKind::DerivedBoundaryMismatch,
                Maybe::Present(circuit_span),
            ); 2],
        );
        assert_eq!(
            check_desc(&desc)
                .iter()
                .map(|diagnostic| (diagnostic.kind, diagnostic.span))
                .collect::<Vec<_>>(),
            expected
        );
    }

    #[test]
    fn a_derivation_budget_failure_prevents_boundary_comparison()
    {
        let mut nodes = Vec::new();
        let mut previous = Name::from("x");
        for level in 0 .. 20_usize {
            let out = Name::from(format!("w{level}"));
            nodes.push(CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Op("add".into()),
                [FreeTerm::var(previous.clone()), FreeTerm::var(previous)],
                out.clone(),
            )));
            previous = out;
        }
        let sphere = RuleFace::new(FreeTerm::var("x"), FreeTerm::var("x"), [], span());
        let desc =
            nat_with(vec![], vec![add_op()], Attrs::empty()).with_circuits([CircuitRule::new(
                "large",
                sphere,
                CircuitBody::new(nodes, previous),
            )]);
        assert_eq!(
            check_desc(&desc)
                .iter()
                .map(|diagnostic| (diagnostic.kind, diagnostic.span))
                .collect::<Vec<_>>(),
            [(WfKind::CircuitDerivationBudget, Maybe::Present(span()))]
        );
    }

    #[test]
    fn variable_metadata_preserves_first_occurrence_order()
    {
        assert_eq!(derive_cell_var_meta(&FreeTerm::ctor("Zero", [])), []);
        let lhs = FreeTerm::op("f", [
            FreeTerm::var("z"),
            FreeTerm::var("a"),
            FreeTerm::var("z"),
            FreeTerm::var("b"),
        ]);
        assert_eq!(derive_cell_var_meta(&lhs), [
            RuleVarMeta::new("z", Variance::Producer, RuleVariableLinearity::from(false)),
            RuleVarMeta::new("a", Variance::Producer, RuleVariableLinearity::from(true)),
            RuleVarMeta::new("b", Variance::Producer, RuleVariableLinearity::from(true)),
        ]);
    }
}
