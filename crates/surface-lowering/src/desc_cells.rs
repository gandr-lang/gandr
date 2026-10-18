//! Description members elaborated into checked cells with source-local
//! refusals.
//!
//! # Cells and circuit wiring
//!
//! `desc_cells::elaborate_desc_cells` turns each description into one
//! declaration-local cell store, retaining operation frames, circuit composites
//! and typed refusals. Ordinary `lower_module` collection executes this route
//! and exposes the result through `LoweredModule::cells`; cell refusals become
//! held declarations at their own operation or rule spans. A many-output
//! operation elaborates to one frame with a return continuation per output
//! port, and its rules elaborate over that frame; a rule returning a different
//! number of results is refused at its own span. A face reads its left-hand
//! side as a cut of a value against an operation frame, so a family's rule
//! whose left-hand side applies an operation where that value stands,
//! `add(add(m, n), k)`, has no cell: it is refused at its span as a shape the
//! elaboration does not read. A `theory` block's law of that shape over
//! unindexed sorts, `turn(unturn(x)) ==> x`, compiles to no operation body, and
//! is read over terms (`elaborate_theory_desc`): a presentation's laws are
//! elaborated under the shape reading, a family's rules under the generative
//! one. Over an indexed sort, `comp(id(a), f) ==> f`, the law stays refused at
//! its span: its indices are fixed by types a term does not carry. A face whose
//! left-hand side is a constructor application — a presented type's rule,
//! `Loop(Unloop(x)) ==> x` — is no operation redex and has no sequent cell
//! either; it is read over terms too (`DeclarationCells::presented`), where it
//! rewrites a value wherever the value stands. A `data` operation whose rules
//! compile runs as a declaration of the module, returning its results as one
//! tuple (`operation`). Identical faces share one cell identity.
//! Witnesses:
//! `desc_cells::tests::ordinary_lowering_executes_the_cell_gate_and_preserves_later_values`,
//! `desc_cells::tests::a_face_declared_twice_is_one_cell`,
//! `desc_cells::tests::a_single_redex_block_reaches_the_cell_layer_behind_the_gate`,
//! `desc_cells::tests::a_many_out_operation_rule_becomes_a_cell_with_a_continuation_per_output`,
//! `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`,
//! `description::theory::tests::the_cat_shape_laws_are_written_faces`.
//!
//! `circuit::embed` reads literal port wiring into the circuit-algebra matcher.
//! Equal spelling in different generator roles remains distinct, and an
//! exhausted search budget is a refusal rather than an empty match set. This
//! uses the shared diagram checker and embedding certificates instead of an
//! independent adjacency matcher. Witnesses:
//! `circuit::embed::tests::one_spelling_in_two_roles_is_two_boxes`,
//! `circuit::embed::tests::an_exhausted_budget_declines_rather_than_reporting_no_match`.
//!
//! Every declaration's rules are then decided as one rewriting system
//! (`coincide`): a block whose rules may not terminate, or two of whose rules
//! rewrite one term to two normal forms, is refused as a family at the rule
//! that shows it, and an admitted block keeps one certificate per critical
//! pair. Witness:
//! `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`.

use alloc::borrow::Cow;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_computads::AdmittedFaceIndex;
use gandr_theory_computads::CircuitElaboration;
use gandr_theory_computads::DeclinedFaceIndex;
use gandr_theory_computads::DescElaboration;
use gandr_theory_computads::ElaborateError;
use gandr_theory_computads::EtaElaboration;
use gandr_theory_computads::OpElaborateError;
use gandr_theory_computads::OpFrame;
use gandr_theory_computads::PresentedRules;
use gandr_theory_computads::elaborate_data_desc;
use gandr_theory_computads::elaborate_theory_desc;
use gandr_theory_computads::presented_reading;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SurfaceSpan;
use gandr_theory_levitation::WhiskeredCell;
use quenchant_shape::shape::Maybe;

use crate::coincide::CoherenceFault;
use crate::coincide::Coincidence;
use crate::coincide::decide;
use crate::coincide::orient_block;
use crate::coincide::rewriting_store;
use crate::description::DescribedDeclaration;
use crate::description::written::RuleDirection;
use crate::form::Placed;

/// An index into a cell report's located diagnostic vector.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CellDiagnosticIndex(pub usize);

/// Why a readable description member has no cell-layer interpretation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CellFault
{
    /// The operation's arity has no cell-alphabet frame: it has no output, or
    /// aggregates several monomials into one output port.
    Operation(OpElaborateError),
    /// The written face or circuit composite did not pass the cell gate.
    Rule(ElaborateError),
    /// The declaration's rules are no one rewriting system: the fault stands
    /// at the rule that shows it.
    Coherence(CoherenceFault),
}

/// A cell-layer refusal at its own source member.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellDiagnostic
{
    /// The member's written interval.
    pub span: ByteSpan,
    /// The cell gate's structured cause.
    pub fault: CellFault,
}

impl CellDiagnostic
{
    /// Present the diagnostic as a refusal: a cell-language boundary as a
    /// held, unrepresentable declaration, a coherence fault by its own name.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn lowering_refusal(&self) -> crate::LoweringRefusal<'static>
    {
        match self.fault {
            CellFault::Coherence(ref fault) => fault.lowering_refusal(self.span),
            CellFault::Operation(_) | CellFault::Rule(_) => crate::LoweringRefusal::OutOfFragment {
                span: self.span,
                form: crate::FormName::DECLARATION,
                sort: crate::FragmentSort::Declaration,
                boundary: crate::FragmentBoundary::Unadmitted,
            },
        }
    }
}

/// A circuit member's admitted cell or its retained diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitCell
{
    /// Both the cell and its whiskered composite passed the gate.
    Admitted
    {
        /// The admitted identity in this declaration's store.
        cell: CellId,
        /// The composite denoted by the source body.
        composite: WhiskeredCell,
    },
    /// The reason is owned once by the enclosing report.
    Refused(CellDiagnosticIndex),
}

/// The cells and operation alphabet of one description declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationCells
{
    /// The source declaration owning this store.
    pub at: Placed,
    /// The checked frame, face, circuit and eta cells, owned once.
    pub store: CellStore,
    /// Admitted operations in declaration order.
    pub operations: Vec<OpFrame>,
    /// The written faces the cell gate declined, by their position among the
    /// description's rules; the cause is owned by the report's diagnostics.
    pub declined_faces: Vec<DeclinedFaceIndex>,
    /// The written faces the cell gate admitted to the sequent reading, by
    /// their position among the description's rules, each with its cell.
    pub faces: Vec<(AdmittedFaceIndex, CellId)>,
    /// The rules read over terms, when a face calls for them: a presented
    /// type's constructor rules, or a presentation's laws nesting an operation.
    pub presented: Maybe<PresentedRules, presented_reading::Absent>,
    /// One result per circuit rule, in declaration order.
    pub circuits: Vec<CircuitCell>,
    /// The declaration's eta cells or their explicit absence.
    pub eta: EtaElaboration,
    /// The kernel-facing rules, left above right, parallel to the description's
    /// rules. Empty when the block did not orient.
    pub oriented: Vec<RuleFace>,
    /// The direction the order chose for each oriented rule.
    pub directions: Vec<RuleDirection>,
    /// The written span of each oriented rule, parallel to `directions`.
    pub rule_spans: Vec<ByteSpan>,
    /// How the declaration's rules stand as one rewriting system.
    pub coincidence: Coincidence,
}

impl DeclarationCells
{
    /// The cells a rewrite reads: the store less its circuit cells, which are
    /// congruences over a rewrite rather than rewrites of their own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rewriting(&self) -> Cow<'_, CellStore>
    {
        rewriting_store(&self.store, &self.faces, &self.circuits)
    }
}

/// Cell stores in declaration order and every member-local refusal.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CellReport
{
    /// One store per readable description declaration.
    pub declarations: Vec<DeclarationCells>,
    /// Refused members; circuit refusals refer here without copying their
    /// cause.
    pub diagnostics: Vec<CellDiagnostic>,
}

/// Elaborate descriptions through the cell gate, preserving every refusal.
///
/// # Specification
/// - requires: operation provenance corresponds to the supplied descriptions.
/// - ensures: each declaration owns one store; a declined face never enters it;
///   readable siblings are elaborated independently in source order; a
///   declaration the gate declined nothing of has its rules decided as one
///   rewriting system (`coincide::decide`), a refusal among the diagnostics at
///   the rule that shows it, and every other declaration is unexamined.
/// - panics: none.
///
/// Missing external provenance is located at its owning declaration, rather
/// than inventing a member interval. Parser-produced descriptions retain every
/// operation's exact interval and every face carries its own provenance.
///
/// # Adequacy
/// - hypothesis: L3 — a two-output operation with a results-tuple rule, a rule
///   returning too few results and a later declaration separate an admitted
///   many-out member, a refused rule and an untouched sibling, and two
///   declarations in swapped order separate store order from source order; a
///   declaration with a declined rule or a declined circuit is unexamined, and
///   two rules rewriting one term apart refuse their declaration.
/// - witness: `desc_cells::tests::a_many_out_operation_rule_becomes_a_cell_with_a_continuation_per_output`
/// - witness: `desc_cells::tests::a_rule_returning_fewer_results_than_outputs_is_refused_rather_than_narrowed`
/// - witness: `desc_cells::tests::a_two_redex_body_declines_with_both_occurrences`
/// - witness: `desc_cells::tests::declaration_order_is_the_cell_order`
/// - witness: `desc_cells::tests::ordinary_lowering_executes_the_cell_gate_and_preserves_later_values`
/// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
#[spec(ensures: |report| report.declarations.len() == declarations.len()
    && report.declarations.iter().zip(declarations).all(|(cells, declaration)| cells.at == declaration.at
        && (cells.declined_faces.is_empty() || cells.coincidence == Coincidence::Unexamined)))]
#[inline]
#[must_use]
pub fn elaborate_desc_cells(declarations: &[DescribedDeclaration]) -> CellReport
{
    let mut report = CellReport {
        declarations: Vec::with_capacity(declarations.len()),
        diagnostics: Vec::new(),
    };
    for declaration in declarations {
        let orientations: Vec<_> = declaration
            .written
            .faces
            .iter()
            .map(|face| face.orientation)
            .collect();
        let oriented = orient_block(&declaration.description, &orientations).ok();
        let reading = oriented
            .as_ref()
            .map_or(&declaration.description, |block| &block.description);
        let DescElaboration {
            store,
            opers,
            declined_opers,
            admitted_faces,
            declined_faces,
            presented,
            circuits,
            eta,
        } = match declaration.presentation {
            Maybe::Present(_) => elaborate_theory_desc(reading),
            Maybe::Absent(_) => elaborate_data_desc(reading),
        };
        let examined = declined_opers.is_empty()
            && declined_faces.is_empty()
            && circuits
                .iter()
                .all(|circuit| matches!(circuit, CircuitElaboration::Admitted { .. }));
        for (index, error) in declined_opers {
            let span = declaration
                .operation_spans
                .get(usize::from(index))
                .copied()
                .unwrap_or(declaration.at.span);
            report.diagnostics.push(CellDiagnostic {
                span,
                fault: CellFault::Operation(error),
            });
        }
        let mut declined = Vec::with_capacity(declined_faces.len());
        for (index, error) in declined_faces {
            let span = declaration
                .description
                .rules
                .get(usize::from(index))
                .map_or(declaration.at.span, |face| {
                    located(face.provenance, declaration.at.span)
                });
            report.diagnostics.push(CellDiagnostic {
                span,
                fault: CellFault::Rule(error),
            });
            declined.push(index);
        }
        let mut outcomes = Vec::with_capacity(circuits.len());
        for (index, circuit) in circuits.into_iter().enumerate() {
            let outcome = match circuit {
                CircuitElaboration::Admitted { cell, composite } => {
                    CircuitCell::Admitted { cell, composite }
                },
                CircuitElaboration::Declined(error) => {
                    let span = declaration
                        .description
                        .circuits
                        .get(index)
                        .map_or(declaration.at.span, |rule| {
                            located(rule.sphere.provenance, declaration.at.span)
                        });
                    let diagnostic = CellDiagnosticIndex(report.diagnostics.len());
                    report.diagnostics.push(CellDiagnostic {
                        span,
                        fault: CellFault::Rule(error),
                    });
                    CircuitCell::Refused(diagnostic)
                },
            };
            outcomes.push(outcome);
        }
        let coincidence = if !examined {
            Coincidence::Unexamined
        }
        else if declaration.description.rules.is_empty() && outcomes.is_empty() {
            Coincidence::Orthogonal
        }
        else {
            match decide(
                reading,
                declaration.at.span,
                &store,
                &admitted_faces,
                &presented,
                &outcomes,
            ) {
                Ok(coincidence) => coincidence,
                Err((span, fault)) => {
                    let diagnostic = CellDiagnosticIndex(report.diagnostics.len());
                    report.diagnostics.push(CellDiagnostic {
                        span,
                        fault: CellFault::Coherence(fault),
                    });
                    Coincidence::Refused(diagnostic)
                },
            }
        };
        let (oriented_rules, directions) = match oriented {
            Some(block) => (block.description.rules.to_vec(), block.directions),
            None => (Vec::new(), Vec::new()),
        };
        let rule_spans = if directions.is_empty() {
            Vec::new()
        }
        else {
            declaration
                .written
                .faces
                .iter()
                .map(|face| face.arrow)
                .collect()
        };
        report.declarations.push(DeclarationCells {
            at: declaration.at,
            store,
            operations: opers,
            declined_faces: declined,
            faces: admitted_faces,
            presented,
            circuits: outcomes,
            eta,
            oriented: oriented_rules,
            directions,
            rule_spans,
            coincidence,
        });
    }
    report
}

/// Convert a retained description interval without clamping its endpoints.
///
/// # Specification
/// trivial.
pub(crate) fn located(
    span: SurfaceSpan,
    owner: ByteSpan,
) -> ByteSpan
{
    ByteSpan::new(usize::from(span.start).into(), usize::from(span.end).into()).unwrap_or(owner)
}

#[cfg(test)]
mod tests;
