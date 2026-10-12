//! Description members elaborated into checked cells with source-local
//! refusals.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_computads::CircuitElaboration;
use gandr_theory_computads::DeclinedFaceIndex;
use gandr_theory_computads::DescElaboration;
use gandr_theory_computads::ElaborateError;
use gandr_theory_computads::EtaElaboration;
use gandr_theory_computads::OpElaborateError;
use gandr_theory_computads::OpFrame;
use gandr_theory_computads::elaborate_data_desc;
use gandr_theory_levitation::SurfaceSpan;
use gandr_theory_levitation::WhiskeredCell;

use crate::description::DescribedDeclaration;
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
    /// Present a cell-language boundary as a held, unrepresentable declaration.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn lowering_refusal(&self) -> crate::LoweringRefusal<'static>
    {
        crate::LoweringRefusal::OutOfFragment {
            span: self.span,
            form: crate::FormName::DECLARATION,
            sort: crate::FragmentSort::Declaration,
            boundary: crate::FragmentBoundary::Unadmitted,
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
    /// One result per circuit rule, in declaration order.
    pub circuits: Vec<CircuitCell>,
    /// The declaration's eta cells or their explicit absence.
    pub eta: EtaElaboration,
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
///   readable siblings are elaborated independently in source order.
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
///   declarations in swapped order separate store order from source order.
/// - witness: `desc_cells::tests::a_many_out_operation_rule_becomes_a_cell_with_a_continuation_per_output`
/// - witness: `desc_cells::tests::a_rule_returning_fewer_results_than_outputs_is_refused_rather_than_narrowed`
/// - witness: `desc_cells::tests::declaration_order_is_the_cell_order`
/// - witness: `desc_cells::tests::ordinary_lowering_executes_the_cell_gate_and_preserves_later_values`
#[spec(ensures: |report| report.declarations.len() == declarations.len() && report.declarations.iter().zip(declarations).all(|(cells, declaration)| cells.at == declaration.at))]
#[inline]
#[must_use]
pub fn elaborate_desc_cells(declarations: &[DescribedDeclaration]) -> CellReport
{
    let mut report = CellReport {
        declarations: Vec::with_capacity(declarations.len()),
        diagnostics: Vec::new(),
    };
    for declaration in declarations {
        let DescElaboration {
            store,
            opers,
            declined_opers,
            declined_faces,
            circuits,
            eta,
        } = elaborate_data_desc(&declaration.description);
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
                | CircuitElaboration::Admitted { cell, composite } => {
                    CircuitCell::Admitted { cell, composite }
                },
                | CircuitElaboration::Declined(error) => {
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
        report.declarations.push(DeclarationCells {
            at: declaration.at,
            store,
            operations: opers,
            declined_faces: declined,
            circuits: outcomes,
            eta,
        });
    }
    report
}

/// Convert a retained description interval without clamping its endpoints.
///
/// # Specification
/// trivial.
fn located(
    span: SurfaceSpan,
    owner: ByteSpan,
) -> ByteSpan
{
    ByteSpan::new(usize::from(span.start).into(), usize::from(span.end).into()).unwrap_or(owner)
}

#[cfg(test)]
mod tests;
