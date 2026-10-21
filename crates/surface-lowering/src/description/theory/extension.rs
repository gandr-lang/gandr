//! The `ext` member: an extension type stated as the signature the face theory
//! generates for it.
//!
//! `ext Cell = Val on left is zero` over a `shape` of `n` points declares the
//! sort `Cell` of cells of `Val` fixed to `zero` on the face `left`, and
//! generates its operations and laws (Tesla Zhang, _Three non-cubical
//! applications of extension types_, arXiv:2311.05658):
//!
//! - `inCell`, one input `yq : Val` per point `q` off the face, in ascending
//!   order, and one output at `Cell`: a cell is introduced by its values off
//!   the face;
//! - `outCellp : (e : Cell) --> Val` for every point `p`: a cell read at `p`;
//! - `boundaryCellp : outCellp(e) ==> zero()` for every point `p` of the face;
//! - `betaCellq : outCellq(inCell(yq₁, …)) ==> yq` for every point `q` off it;
//! - `etaCell : inCell(outCellq₁(e), …) ==> e`.
//!
//! The laws join the block's rules, so each holds by the conversion the
//! block's rules already have, on a neutral cell as on an introduced one, and
//! a rule that fixes a cell to another value on the face diverges from the
//! boundary law and is refused by name.
//!
//! # Witnesses
//!
//! - `description::theory::tests::an_extension_generates_its_signature`
//! - `description::theory::tests::an_extension_is_refused_by_name`

use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::OperationKind;
use gandr_theory_levitation::Representability;
use gandr_theory_levitation::ShapePoint;
use gandr_theory_levitation::TheoryOperation;
use gandr_theory_levitation::TheoryParts;
use gandr_theory_levitation::TheoryPort;
use gandr_theory_levitation::TheoryRule;
use gandr_theory_levitation::TheorySort;
use quenchant_shape::shape::Maybe;

use super::super::DescriptionDiagnostic;
use super::super::DescriptionFault;
use super::super::Reader;
use super::super::Run;
use super::super::Spelling;
use super::super::Written;
use super::super::written::RuleDirection;
use super::super::written::RuleOrientation;
use super::super::written::WrittenFace;
use super::super::written::WrittenOperation;
use super::super::written::WrittenPort;
use super::super::written::WrittenSort;
use super::super::written::WrittenSortMember;
use super::super::written::WrittenTerm;
use super::super::written::WrittenUse;
use super::super::written::arrow;
use super::super::written::member_name;
use super::super::written::port_name;
use crate::circuit::ExtensionFault;
use crate::circuit::SignatureFault;
use crate::form::Placed;

/// An `ext` member as written: its keyword, the cell sort it declares, the
/// type it extends, the face and the boundary constant.
#[derive(Clone, Copy)]
pub(super) struct Extension
{
    /// The `ext` keyword.
    keyword: Placed,
    /// The cell sort's name tile.
    cell: Placed,
    /// The extended type's name tile.
    carrier: Placed,
    /// The face's name tile.
    face: Placed,
    /// The boundary constant's name tile.
    boundary: Placed,
    /// The whole member.
    span: ByteSpan,
}

/// The members an `ext` member generates, each with its tile and where it
/// stands written, and the names the member writes for others.
pub(super) struct Generated
{
    /// The introduction and the readings, each with its tile and ports.
    pub operations: Vec<(TheoryOperation, Placed, WrittenOperation)>,
    /// The boundary, β and η laws, each with its tile and sides.
    pub laws: Vec<(TheoryRule, Placed, WrittenFace)>,
    /// The face's and the boundary constant's names, as uses.
    pub uses: Vec<WrittenUse>,
}

impl Extension
{
    /// The cell sort's name tile.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn cell(&self) -> Placed
    {
        self.cell
    }

    /// The whole member.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn span(&self) -> ByteSpan
    {
        self.span
    }
}

impl Reader<'_, '_>
{
    /// Read an `ext` member, `ext Cell = Val on left is zero`, and the sort of
    /// cells it declares.
    ///
    /// # Specification
    /// - requires: `run` stands at the member's `ext` keyword.
    /// - ensures: the member's tiles, and the cell sort it declares: unindexed,
    ///   ordinary, named by the cell tile and classified where the extended
    ///   type is written.
    /// - fails: a missing tile, `=`, `on` or `is`, or a trailing piece, is a
    ///   member-local refusal.
    /// - panics: none.
    /// - executable: none — the written member is source syntax the sort does
    ///   not retain.
    ///
    /// # Errors
    /// Returns malformed syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written member declares its cell sort beside the
    ///   block's own, and a member missing its face is malformed.
    /// - witness: `description::theory::tests::an_extension_generates_its_signature`
    /// - witness: `description::theory::tests::an_extension_is_refused_by_name`
    pub(super) fn extension_member(
        &self,
        run: &mut Run<'_>,
    ) -> Result<(Extension, TheorySort, WrittenSortMember), DescriptionDiagnostic>
    {
        let keyword = run.take()?;
        let cell = run.take()?;
        if !run.eat(Spelling("=")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let carrier = run.take()?;
        if !run.eat(Spelling("on")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let face = run.take()?;
        if !run.eat(Spelling("is")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let boundary = run.take()?;
        run.end()?;
        Ok((
            Extension {
                keyword,
                cell,
                carrier,
                face,
                boundary,
                span: run.span,
            },
            TheorySort {
                name: self.text(cell).0.into(),
                indices: Vec::new(),
                representability: Representability::Ordinary,
            },
            WrittenSortMember {
                named: cell.span,
                classifier: carrier.span,
                indices: Vec::new(),
            },
        ))
    }

    /// The operations and laws the face theory generates for `extension`
    /// over the block's members `parts`, and the uses its face and boundary
    /// names are.
    ///
    /// # Specification
    /// - requires: `parts` holds the block's shape, sorts and operations, the
    ///   cell sort among them; `tiles` holds the name tile of each of `parts`'
    ///   operations, in order, and `faces` the name tile of each of its shape's
    ///   faces the block writes, in order.
    /// - ensures: `inCell` over the points off the face, ascending; one
    ///   `outCellp` per point of the shape; one boundary law per point of the
    ///   face, one β law per point off it, and the η law — each named for the
    ///   cell sort and the point, as the module states, none with a written
    ///   name or arrow; and the face's and the boundary's names as uses of the
    ///   face's and the constant's name tiles, each where its tile is held.
    /// - fails: a block with no shape, a face the shape does not name, a face
    ///   holding every point, an extended type that is not an unindexed sort of
    ///   the block other than the cell sort, and a boundary that is not a
    ///   constant at the extended type, each refused by name at the member.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the member's [`ExtensionFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over two points with one on the face, the block holds
    ///   the two readings, the introduction and the three laws the hand-written
    ///   signature states; each fault is refused apart from the others.
    /// - witness: `description::theory::tests::an_extension_generates_its_signature`
    /// - witness: `description::theory::tests::an_extension_is_refused_by_name`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |generated| generated.operations.len() >= 2 && generated.laws.len() >= 2))]
    pub(super) fn extended(
        &self,
        extension: &Extension,
        parts: &TheoryParts,
        tiles: &[Placed],
        faces: &[Placed],
    ) -> Result<Generated, DescriptionDiagnostic>
    {
        let refused = |fault: ExtensionFault| DescriptionDiagnostic {
            span: extension.span,
            fault: DescriptionFault::Signature(SignatureFault::Extension(fault)),
        };
        let Maybe::Present(ref shape) = parts.shape
        else {
            return Err(refused(ExtensionFault::Unshaped));
        };
        let Written(face_name) = self.text(extension.face);
        let Some((face_at, face)) = shape
            .faces
            .iter()
            .enumerate()
            .find(|&(_, face)| face.name().as_ref() == face_name)
        else {
            return Err(refused(ExtensionFault::UnknownFace(Name::from(face_name))));
        };
        let Written(cell) = self.text(extension.cell);
        let Written(carrier) = self.text(extension.carrier);
        let extended = parts
            .sorts
            .iter()
            .any(|sort| sort.name.as_ref() == carrier && sort.indices.is_empty());
        if carrier == cell || !extended {
            return Err(refused(ExtensionFault::Carrier(Name::from(carrier))));
        }
        let Written(boundary) = self.text(extension.boundary);
        let Some(constant) = parts.operations.iter().position(|operation| {
            operation.name.as_ref() == boundary
                && matches!(
                    operation.kind,
                    OperationKind::Operation | OperationKind::Constant
                )
                && operation.inputs.is_empty()
                && matches!(operation.outputs.as_slice(), [port]
                    if port.sort.as_ref() == carrier && port.indices.is_empty())
        })
        else {
            return Err(refused(ExtensionFault::Boundary(Name::from(boundary))));
        };
        let points: Vec<ShapePoint> = (0 .. usize::from(shape.points))
            .map(ShapePoint::from)
            .collect();
        let on_face: BTreeSet<ShapePoint> = face.points().iter().copied().collect();
        let off: Vec<ShapePoint> = points
            .iter()
            .copied()
            .filter(|point| !on_face.contains(point))
            .collect();
        if off.is_empty() {
            return Err(refused(ExtensionFault::CoveringFace(Name::from(face_name))));
        }
        let introduce = Name::from(format!("in{cell}"));
        let read = |point: ShapePoint| Name::from(format!("out{cell}{}", usize::from(point)));
        let value = |point: ShapePoint| Name::from(format!("y{}", usize::from(point)));
        let port = |name: Name, sort: &str| TheoryPort {
            name,
            sort: Name::from(sort),
            indices: Vec::new(),
            bindings: Vec::new(),
        };
        let written_port = |at: Placed| WrittenPort {
            named: Maybe::Absent(port_name::Absent::Generated),
            binders: Vec::new(),
            sort: WrittenSort {
                span: at.span,
                indices: Vec::new(),
            },
        };
        let mut operations = Vec::with_capacity(points.len().saturating_add(1));
        operations.push((
            TheoryOperation {
                name: introduce.clone(),
                kind: OperationKind::Operation,
                inputs: off
                    .iter()
                    .map(|&point| port(value(point), carrier))
                    .collect(),
                outputs: vec![port(Name::from(""), cell)],
            },
            extension.keyword,
            WrittenOperation {
                named: Maybe::Absent(member_name::Absent::Generated),
                inputs: off
                    .iter()
                    .map(|_| written_port(extension.carrier))
                    .collect(),
                outputs: vec![written_port(extension.cell)],
            },
        ));
        for &point in &points {
            operations.push((
                TheoryOperation {
                    name: read(point),
                    kind: OperationKind::Operation,
                    inputs: vec![port(Name::from("e"), cell)],
                    outputs: vec![port(Name::from(""), carrier)],
                },
                extension.keyword,
                WrittenOperation {
                    named: Maybe::Absent(member_name::Absent::Generated),
                    inputs: vec![written_port(extension.cell)],
                    outputs: vec![written_port(extension.carrier)],
                },
            ));
        }
        let cell_variable = || FreeTerm::var("e");
        let introduced = FreeTerm::op(
            introduce.clone(),
            off.iter().map(|&point| FreeTerm::var(value(point))),
        );
        let law = |name: Name, left: FreeTerm, right: FreeTerm| {
            (
                TheoryRule { name, left, right },
                extension.keyword,
                WrittenFace {
                    named: Maybe::Absent(member_name::Absent::Generated),
                    left: WrittenTerm::default(),
                    right: WrittenTerm::default(),
                    arrow: Maybe::Absent(arrow::Absent::Generated),
                    orientation: RuleOrientation::Pinned(RuleDirection::LeftToRight),
                },
            )
        };
        let mut laws = Vec::with_capacity(points.len().saturating_add(1));
        for &point in face.points() {
            laws.push(law(
                Name::from(format!("boundary{cell}{}", usize::from(point))),
                FreeTerm::op(read(point), [cell_variable()]),
                FreeTerm::op(boundary, []),
            ));
        }
        for &point in &off {
            laws.push(law(
                Name::from(format!("beta{cell}{}", usize::from(point))),
                FreeTerm::op(read(point), [introduced.clone()]),
                FreeTerm::var(value(point)),
            ));
        }
        laws.push(law(
            Name::from(format!("eta{cell}")),
            FreeTerm::op(
                introduce,
                off.iter()
                    .map(|&point| FreeTerm::op(read(point), [cell_variable()])),
            ),
            cell_variable(),
        ));
        let mut uses = Vec::with_capacity(2);
        if let Some(&named) = faces.get(face_at) {
            uses.push(WrittenUse {
                span: extension.face.span,
                named: named.span,
            });
        }
        if let Some(&named) = tiles.get(constant) {
            uses.push(WrittenUse {
                span: extension.boundary.span,
                named: named.span,
            });
        }
        Ok(Generated {
            operations,
            laws,
            uses,
        })
    }
}
