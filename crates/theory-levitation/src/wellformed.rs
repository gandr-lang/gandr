//! Host-side well-formedness: the checks a [`SignDesc`] owes before any typed
//! decoder reads it.
//!
//! No typed decoder runs here, so a description's invariants are checked by
//! this pass, which produces inspectable diagnostics:
//!
//! * the sorting discipline: sort names are distinct, every sort's polarity
//!   agrees with the declaration's, and every result sort and recursive
//!   occurrence names a declared sort;
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
//! Restricted π⁺ ports require representable domain sorts; nominal
//! atom abstraction in constructor codes remains a separate former.
//!
//! [`Code`]: crate::Code

use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::arity::BridgeArity;
use crate::boundary::DiagnosticMessage;
use crate::boundary::NameRef;
use crate::boundary::RuleVariableLinearity;
use crate::circuit::CircuitDerivationError;
use crate::circuit::CircuitNode;
use crate::circuit::CircuitRule;
use crate::circuit::derive_boundaries;
use crate::code::Attrs;
use crate::code::Name;
use crate::desc::SignDesc;
use crate::desc::SurfaceSpan;
use crate::rule::FreeTerm;
use crate::rule::RuleFace;
use crate::rule::RuleVarMeta;
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
    /// A restricted binder's domain is undeclared or not representable.
    NonRepresentableBinder,
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

/// One well-formedness diagnostic: an inspectable failure with a message and,
/// when recorded, a surface span.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct WfDiagnostic
{
    /// The failure classification.
    pub kind: WfKind,
    /// A human-readable description of the failure.
    pub message: DiagnosticMessage,
    /// The surface span the failure was located at, when recorded.
    pub span: Maybe<SurfaceSpan, diagnostic_span::Absent>,
}

impl WfDiagnostic
{
    /// A diagnostic of the given kind, message and span.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        kind: WfKind,
        message: DiagnosticMessage,
        span: Maybe<SurfaceSpan, diagnostic_span::Absent>,
    ) -> Self
    {
        Self {
            kind,
            message,
            span,
        }
    }
}

/// The diagnostic of `kind` with the rendered `message`, at an unrecorded
/// span.
///
/// # Specification
/// trivial.
fn unlocated(
    kind: WfKind,
    message: String,
) -> WfDiagnostic
{
    WfDiagnostic::new(
        kind,
        DiagnosticMessage::from(message),
        Maybe::Absent(diagnostic_span::Absent::Unrecorded),
    )
}

/// The diagnostic of `kind` with the rendered `message`, at `span`.
///
/// # Specification
/// trivial.
fn located(
    kind: WfKind,
    message: String,
    span: SurfaceSpan,
) -> WfDiagnostic
{
    WfDiagnostic::new(kind, DiagnosticMessage::from(message), Maybe::Present(span))
}

/// Check a description, returning one diagnostic per well-formedness failure;
/// an empty vector means well-formed.
///
/// # Specification
/// - ensures: every failure of the rules this module states, in a deterministic
///   order: sorting-discipline checks, then attribute declines, then per-face
///   checks, then per-arity checks, then per-circuit-rule checks; an empty
///   result witnesses a well-formed description.
/// - panics: none; total on any description, a mis-built one included.
///
/// # Adequacy
/// - hypothesis: L3 — a clean description passes; a duplicate sort name, a
///   foreign result or `var` sort, a sort polarity disagreeing with the
///   declaration's, an out-of-signature face, a fresh right-hand-side variable,
///   a non-composing arity, a reserved-derived attribute, a circuit rule whose
///   wiring derives a boundary its sphere does not fix, a cyclic wiring, and a
///   redex applying a rewrite the rule's telescope does not declare each
///   surface exactly their diagnostic.
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
/// - witness: `wellformed::tests::a_derivation_budget_failure_prevents_boundary_comparison`
#[inline]
#[must_use]
#[spec(ensures: |ref diagnostics| diagnostics.iter().all(|diagnostic| match diagnostic.kind {
    | WfKind::OutOfSignatureRule | WfKind::UnboundRhsVariable | WfKind::DerivedBoundaryMismatch
    | WfKind::CyclicCircuitWiring | WfKind::UnknownRewritePort | WfKind::CircuitDerivationBudget => matches!(diagnostic.span, Maybe::Present(_)),
    | WfKind::ArityDoesNotCompose | WfKind::DeclaresDerivedMetadata | WfKind::DuplicateSortName
    | WfKind::UnknownResultSort | WfKind::UnknownVarSort | WfKind::SortPolarityDisagreement | WfKind::NonRepresentableBinder => diagnostic.span == Maybe::Absent(diagnostic_span::Absent::Unrecorded),
}))]
pub fn check_desc<G>(desc: &SignDesc<G>) -> Vec<WfDiagnostic>
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
                sort.name == binder.sort
                    && sort.representability == crate::desc::Representability::Representable
            }) {
                diagnostics.push(unlocated(
                    WfKind::NonRepresentableBinder,
                    format!(
                        "π⁺ domain '{}' of port '{}' is not representable",
                        binder.sort, port.name
                    ),
                ));
            }
        }
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

    // Rule faces: in-signature symbols and no fresh right-hand-side variable.
    let signature = signature_names(desc);
    for rule in &desc.rules {
        check_rule_face(rule, &signature, &mut diagnostics);
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
        && diagnostics.iter().skip(before).all(|diagnostic| diagnostic.span == Maybe::Absent(diagnostic_span::Absent::Unrecorded)
            && matches!(diagnostic.kind, WfKind::DuplicateSortName | WfKind::SortPolarityDisagreement | WfKind::UnknownResultSort | WfKind::UnknownVarSort)),
)]
fn check_sorts<G>(
    desc: &SignDesc<G>,
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
                format!("the sort `{}` is declared more than once", sort.name),
            ));
        }
        if sort.polarity != desc.polarity {
            diagnostics.push(unlocated(
                WfKind::SortPolarityDisagreement,
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
    ensures: diagnostics.len() >= before && diagnostics.iter().skip(before).all(|diagnostic|
        diagnostic.span == Maybe::Present(rule.sphere.provenance)
        && matches!(diagnostic.kind, WfKind::OutOfSignatureRule | WfKind::UnknownRewritePort
            | WfKind::CyclicCircuitWiring | WfKind::CircuitDerivationBudget | WfKind::DerivedBoundaryMismatch)),
)]
fn check_circuit_rule(
    rule: &CircuitRule,
    signature: &[Name],
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    let span = rule.sphere.provenance;
    check_free_term_symbols(&rule.sphere.lhs, signature, span, diagnostics);
    check_free_term_symbols(&rule.sphere.rhs, signature, span, diagnostics);
    for node in &rule.body.nodes {
        match *node {
            | CircuitNode::Frame(ref frame) => {
                if signature.contains(frame.head.name()) {
                    continue;
                }
                diagnostics.push(located(
                    WfKind::OutOfSignatureRule,
                    format!(
                        "circuit rule `{}`'s frame applies symbol `{}` not in the datatype's \
                         signature",
                        rule.name,
                        frame.head.name()
                    ),
                    span,
                ));
            },
            | CircuitNode::Redex(ref redex) => {
                // An undeclared telescope means the redex heads are simply not
                // declared here — not that they are unknown. The check bites
                // only where a telescope was written.
                if rule.ports.is_empty() || rule.ports.iter().any(|port| port.name == redex.rewrite)
                {
                    continue;
                }
                diagnostics.push(located(
                    WfKind::UnknownRewritePort,
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
        | Ok(derived) => derived,
        | Err(CircuitDerivationError::CyclicWiring(port)) => {
            diagnostics.push(located(
                WfKind::CyclicCircuitWiring,
                format!(
                    "circuit rule `{}`'s wiring reaches port `{port}` from itself, so no boundary \
                     term unfolds from it",
                    rule.name
                ),
                span,
            ));
            return;
        },
        | Err(CircuitDerivationError::NodeBudget { budget }) => {
            diagnostics.push(located(
                WfKind::CircuitDerivationBudget,
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
            | Self::Datatype => "the datatype",
            | Self::Constructor => "the constructor",
            | Self::Parameter => "the parameter",
            | Self::Operation => "the operation",
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
        && diagnostics.iter().skip(before).all(|diagnostic| diagnostic.kind == WfKind::DeclaresDerivedMetadata
            && diagnostic.span == Maybe::Absent(diagnostic_span::Absent::Unrecorded)),
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
fn signature_names<G>(desc: &SignDesc<G>) -> Vec<Name>
{
    desc.ctors
        .iter()
        .map(|ctor| ctor.name.clone())
        .chain(desc.opers.iter().map(|op| op.name.clone()))
        .collect()
}

/// Check one rule face: every applied symbol is in-signature and the
/// right-hand side introduces no fresh variable.
///
/// # Specification
/// - ensures: the out-of-signature diagnostics of the left-hand side, then of
///   the right-hand side, then one diagnostic per right-hand-side variable
///   occurrence the left-hand side does not bind.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — symbols outside the signature on both sides and a
///   repeated fresh right-hand variable have an exact diagnostic sequence and
///   face span; reversed sides, deduplication and using the wrong span differ.
/// - witness: `wellformed::tests::diagnostics_preserve_phase_order_multiplicity_and_provenance`
/// - witness: `wellformed::tests::a_clean_description_passes`
#[spec(
    captures: before = diagnostics.len(),
    ensures: diagnostics.len() == before.saturating_add(
        cell.lhs.applied_symbols().chain(cell.rhs.applied_symbols()).filter(|name| !signature.contains(name)).count()
            .saturating_add(cell.rhs.to_node().vars().filter(|name| !cell.lhs.to_node().vars().any(|left| left == *name)).count())
    ) && diagnostics.iter().skip(before).all(|diagnostic| diagnostic.span == Maybe::Present(cell.provenance)
        && matches!(diagnostic.kind, WfKind::OutOfSignatureRule | WfKind::UnboundRhsVariable)),
)]
fn check_rule_face(
    cell: &RuleFace,
    signature: &[Name],
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    check_free_term_symbols(&cell.lhs, signature, cell.provenance, diagnostics);
    check_free_term_symbols(&cell.rhs, signature, cell.provenance, diagnostics);

    let lhs_vars = cell.lhs.collect_vars();
    for var in cell.rhs.collect_vars() {
        if !lhs_vars.contains(&var) {
            diagnostics.push(located(
                WfKind::UnboundRhsVariable,
                format!(
                    "cell rule's right-hand side introduces variable `{var}` not bound by its \
                     left-hand side"
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
        && diagnostics.iter().skip(before).all(|diagnostic| diagnostic.kind == WfKind::OutOfSignatureRule && diagnostic.span == Maybe::Present(span)),
)]
fn check_free_term_symbols(
    term: &FreeTerm,
    signature: &[Name],
    span: SurfaceSpan,
    diagnostics: &mut Vec<WfDiagnostic>,
)
{
    for name in term.applied_symbols() {
        if !signature.contains(name) {
            diagnostics.push(located(
                WfKind::OutOfSignatureRule,
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
        && diagnostics.iter().skip(before).all(|diagnostic| diagnostic.kind == WfKind::ArityDoesNotCompose
            && diagnostic.span == Maybe::Absent(diagnostic_span::Absent::Unrecorded)),
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
    let mut meta: Vec<RuleVarMeta> = Vec::new();
    for var in &occurrences {
        if meta.iter().any(|existing| existing.var == *var) {
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
        let two_sorted: SignDesc<Grade> = SignDesc::new(
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
    ) -> SignDesc<Grade>
    {
        SignDesc::new(
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
