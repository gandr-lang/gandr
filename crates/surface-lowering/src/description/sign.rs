//! Ruled signature members and their literal circuit bodies.
//!
//! # Signature blocks
//!
//! A `sign` block is a description judgment, not an ordinary native value
//! family: it has no family classifier and creates no placeholder core value.
//! It retains declared sorts and their index telescopes, operation boundaries
//! with every output port, written faces and circuit rules. An operation
//! `f : (m : N, n : N) --> (q : N, r : N)` is one monomial per output, as a
//! `data` member's is (Spivak, Garner and Fairbanks, _Functorial Aggregation_,
//! arXiv:2111.10968); a port name written twice on one boundary is two ports
//! rather than one wire, and is refused by name. A rule member whose first side
//! is a term is the face `rule name : lhs ==> rhs` it writes; one whose first
//! side is a port group is a circuit rule. A rewrite port is instantiated at
//! its written wiring, a frame binds one port per output of its head, and a
//! body rooted at several outputs derives its sphere root by root, a many-out
//! frame's application standing for its whole result tuple when its ports
//! leave together in order. A cycle or a derivation ceiling refuses that
//! derivation rather than fabricating a boundary. A feed back-edge is a wheel
//! refusal, a bodiless cell between composites of cells a higher-cell refusal,
//! an operation filler, in a block or as a top-level `oper`, a filler refusal,
//! and the reversible glyphs `<->` and `<=>` are reserved; each is a fragment
//! boundary rather than malformed source. Witnesses:
//! `description::sign::tests::a_ruled_sign_block_lowers_its_members_into_a_description`,
//! `description::sign::tests::a_many_out_frame_binds_every_port_and_roots_the_body`,
//! `description::sign::tests::the_cat_shape_laws_are_written_faces`,
//! `description::sign::tests::a_port_name_on_both_sides_is_two_ports`,
//! `description::sign::tests::a_feed_statement_declines_naming_the_wheel_obligation`,
//! `description::sign::tests::sign_declines_and_malformed_wiring_are_refused_apart`.
//!
//! **Choice.** A `sign` block or a top-level `oper` declares no core constant,
//! so one that refuses nothing is no declaration. Each refusal raised inside it
//! is a held declaration at its member's span whose signature half is the
//! block, so the attribute blocks written before the block state it,
//! `@[ refuses("OutOfFragment") ] sign …`, and every refusal of one block reads
//! that expectation; its name enters no namespace. The alternatives were a
//! declaration per block with an outcome of its own, which every consumer of a
//! declaration outcome would have to learn before a block has anything to
//! check, and refusals with no half, which no expectation can state and which
//! kept every refused block's source pending. A decoration on a block that
//! refuses nothing decorates no declaration and refuses the source as a stray
//! block. A sign's models are checked against `Model(S)`, which the lowering
//! derives from the block's presentation where a module names it, so the block
//! still takes no slot (the decision is in `module::model`). The choice
//! reverses when the derived signature becomes a core declaration: the block
//! then takes its slot whether or not a member refuses.
//! Witnesses:
//! `description::sign::tests::a_refused_sign_block_states_its_refusal`,
//! `description::sign::tests::a_top_level_operation_declines_its_filler_by_name`.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::vec::Vec;

use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::BridgeArity;
use gandr_theory_levitation::CircuitBody;
use gandr_theory_levitation::CircuitFrame;
use gandr_theory_levitation::CircuitNode;
use gandr_theory_levitation::CircuitRule;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::FrameHead;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::RewritePort;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::SortDesc;
use gandr_theory_levitation::SortIndex;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::SurfaceSpan;
use gandr_theory_levitation::derive_boundaries;
use gandr_theory_levitation::derive_cell_var_meta;
use quenchant_shape::shape::Maybe;

use super::DescribedDeclaration;
use super::DescriptionDiagnostic;
use super::DescriptionFault;
use super::Reader;
use super::Run;
use super::Spelling;
use super::TileSeen;
use super::Written;
use super::family_classifier;
use super::split_members;
use super::written::WrittenCircuit;
use super::written::WrittenCircuitPort;
use super::written::WrittenFace;
use super::written::WrittenFrame;
use super::written::WrittenMembers;
use super::written::WrittenOperation;
use super::written::WrittenPort;
use super::written::WrittenRewrite;
use super::written::WrittenSort;
use super::written::WrittenSortMember;
use super::written::WrittenWire;
use super::written::port_name;
use crate::circuit::ArrowRow;
use crate::circuit::OutputCount;
use crate::circuit::SignatureFault;
use crate::form::Piece;
use crate::form::Placed;
use crate::model::Port;
use crate::model::Presentation;
use crate::model::PresentedCircuit;
use crate::model::PresentedLaw;
use crate::model::PresentedOperation;
use crate::model::PresentedSort;
use crate::model::SortTerm;
use crate::model::presentation;

/// The two sides of a signature and its rewrite-sorted binders.
struct Boundary
{
    /// Ordinary value ports supplied by the interface.
    inputs: Vec<SortRef>,
    /// Ports at which the interface returns its result.
    outputs: Vec<SortRef>,
    /// Each input port's written sort, in order.
    input_sorts: Vec<Placed>,
    /// Each output port's written sort, in order.
    output_sorts: Vec<Placed>,
    /// Each input port's name tile, in order.
    input_names: Vec<Maybe<ByteSpan, port_name::Absent>>,
    /// Each output port's name tile, in order.
    output_names: Vec<Maybe<ByteSpan, port_name::Absent>>,
    /// The rewrite heads in scope in the body.
    rewrites: Vec<RewritePort>,
    /// Where each rewrite head is written, in the same order.
    written_rewrites: Vec<WrittenRewrite>,
}

/// One side of a signature: its ports, each port's written sort and name
/// tile, in order.
struct Side
{
    /// The ports.
    ports: Vec<SortRef>,
    /// Each port's written sort.
    sorts: Vec<Placed>,
    /// Each port's name tile.
    names: Vec<Maybe<ByteSpan, port_name::Absent>>,
}

/// A declared head determines a node arrow before any body is read.
#[derive(Clone, Copy)]
enum HeadKind
{
    /// A constructor frame.
    Constructor,
    /// An operation frame.
    Operation,
    /// A rewrite head.
    Rewrite,
}

impl HeadKind
{
    /// The arrow row fixed by the declaration kind.
    ///
    /// # Specification
    /// trivial.
    const fn row(self) -> ArrowRow
    {
        match self {
            | Self::Constructor | Self::Operation => ArrowRow::Mapping,
            | Self::Rewrite => ArrowRow::Face,
        }
    }
}

/// A sign block's rule member: a face it writes or a circuit it wires, each
/// with what it presents to the model signature and where it is written.
enum RuleMember
{
    /// A written face `rule name : lhs ==> rhs`.
    Face(RuleFace, PresentedLaw, WrittenFace),
    /// A circuit rule whose sphere its wiring derives.
    Circuit(CircuitRule, PresentedCircuit, WrittenCircuit),
}

impl Reader<'_, '_>
{
    /// Read each sign member independently, preserving its declared sort set.
    ///
    /// # Specification
    /// - ensures: an unreadable member does not consume a following member.
    /// - fails: a malformed signature head refuses the whole declaration.
    /// - panics: none.
    /// - executable: none — a member's independence is a relation between the
    ///   source's members and the report, which the call does not retain.
    ///
    /// # Errors
    /// Returns a located malformed-head diagnostic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declined rule member between readable ones leaves
    ///   both neighbours read, and an unreadable member keeps its own report.
    /// - witness: `description::sign::tests::a_declined_rule_member_leaves_the_members_after_it_intact`
    /// - witness: `description::sign::tests::an_unreadable_member_keeps_its_own_report`
    pub(super) fn signature(
        &self,
        at: Placed,
        run: &mut Run<'_>,
        serial: NominalSerial,
        diagnostics: &mut Vec<DescriptionDiagnostic>,
    ) -> Result<DescribedDeclaration, DescriptionDiagnostic>
    {
        let named = run.take()?;
        if !run.eat(Spelling("{")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let members = split_members(run.remaining());
        let mut sorts = Vec::new();
        let mut scope = BTreeMap::new();
        let mut presentation = Presentation::default();
        let mut written = WrittenMembers::default();
        for member in &members {
            let span = member_span(member, at.span);
            let mut reading = Run::new(member, span);
            let kind = if reading.eat(Spelling("oper")).0 {
                Some(HeadKind::Operation)
            }
            else if reading.eat(Spelling("rule")).0 {
                Some(HeadKind::Rewrite)
            }
            else if reading.eat(Spelling("data")).0 {
                Some(HeadKind::Constructor)
            }
            else {
                None
            };
            if let Some(kind) = kind {
                if let Ok(name) = reading.take() {
                    scope.insert(self.text(name), kind);
                }
                continue;
            }
            if !reading.eat(Spelling("sort")).0 {
                continue;
            }
            match self.signature_sort(&mut reading) {
                | Ok((sort, presented, member)) => {
                    sorts.push(sort);
                    presentation.sorts.push(presented);
                    written.sorts.push(member);
                },
                | Err(diagnostic) => diagnostics.push(diagnostic),
            }
        }
        let mut operations = Vec::new();
        let mut operation_spans = Vec::new();
        let mut circuits = Vec::new();
        let mut faces = Vec::new();
        for member in members {
            let span = member_span(member, at.span);
            let mut reading = Run::new(member, span);
            let result = if reading.eat(Spelling("sort")).0 {
                continue;
            }
            else if reading.eat(Spelling("data")).0 {
                Err(reading.signature_fault(SignatureFault::RetiredDataMember))
            }
            else if reading.eat(Spelling("oper")).0 {
                self.signature_operation(&mut reading, &sorts).map(
                    |(operation, presented, ports)| {
                        operations.push(operation);
                        operation_spans.push(span);
                        presentation.operations.push(presented);
                        written.operations.push(ports);
                    },
                )
            }
            else if reading.eat(Spelling("rule")).0 {
                self.signature_rule(&mut reading, &sorts, &scope)
                    .map(|member| match member {
                        | RuleMember::Circuit(rule, presented, wired) => {
                            circuits.push(rule);
                            presentation.circuits.push(presented);
                            written.circuits.push(wired);
                        },
                        | RuleMember::Face(face, presented, sides) => {
                            faces.push(face);
                            presentation.laws.push(presented);
                            written.faces.push(sides);
                        },
                    })
            }
            else {
                Err(reading.signature_fault(SignatureFault::MissingJudgment))
            };
            if let Err(diagnostic) = result {
                diagnostics.push(diagnostic);
            }
        }
        let mut description = SignDesc::new(
            NominalId::new(serial, self.text(named).0),
            [],
            [],
            operations,
            faces,
            DeclPolarity::Data,
            Attrs::empty(),
        )
        .with_circuits(circuits);
        if !sorts.is_empty() {
            description = description.with_sorts(sorts);
        }
        Ok(DescribedDeclaration {
            at,
            named,
            description,
            operation_spans,
            parameters: Vec::new(),
            classifier: Maybe::Absent(family_classifier::Absent::Signature),
            presentation: Maybe::Present(presentation),
            written,
        })
    }

    /// Read a top-level `oper` declaration as the one operation it declares,
    /// in a description of its own: its boundary through the sign route, and
    /// its filler declined as an operation filler is inside a sign block.
    ///
    /// # Specification
    /// - ensures: the description holds the operation when its boundary reads
    ///   and it has no filler, and nothing else; the declaration is named by
    ///   the operation.
    /// - fails: a missing name refuses the declaration; a filler or an
    ///   unreadable boundary is the operation's own diagnostic, appended.
    /// - panics: none.
    /// - executable: none — which diagnostic the operation earned is source
    ///   syntax the description does not retain.
    ///
    /// # Errors
    /// Returns a located malformed-name diagnostic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a top-level operation with a filler keeps its name
    ///   and declines the filler at the declaration, where a stray form would
    ///   refuse the whole module.
    /// - witness: `description::sign::tests::a_top_level_operation_declines_its_filler_by_name`
    pub(super) fn circuit_declaration(
        &self,
        at: Placed,
        run: &mut Run<'_>,
        serial: NominalSerial,
        diagnostics: &mut Vec<DescriptionDiagnostic>,
    ) -> Result<DescribedDeclaration, DescriptionDiagnostic>
    {
        let Some(&first) = run.remaining().first()
        else {
            return Err(run.fault(DescriptionFault::Malformed));
        };
        let named = first.placed();
        let mut operations = Vec::new();
        let mut operation_spans = Vec::new();
        match self.signature_operation(run, &[]) {
            | Ok((operation, _presented, _written)) => {
                operations.push(operation);
                operation_spans.push(at.span);
            },
            | Err(diagnostic) => diagnostics.push(diagnostic),
        }
        Ok(DescribedDeclaration {
            at,
            named,
            description: SignDesc::new(
                NominalId::new(serial, self.text(named).0),
                [],
                [],
                operations,
                [],
                DeclPolarity::Data,
                Attrs::empty(),
            ),
            operation_spans,
            parameters: Vec::new(),
            classifier: Maybe::Absent(family_classifier::Absent::Circuit),
            presentation: Maybe::Absent(presentation::Absent::Circuit),
            written: WrittenMembers::default(),
        })
    }

    /// Read an indexed or unindexed sort without erasing its telescope.
    ///
    /// # Specification
    /// - ensures: indices retain their written order and sort names, beside the
    ///   sort as it presents itself to a model signature: its name tile and
    ///   each index's sort read as a sort over index terms; and where its name,
    ///   its classifier and each index are written.
    /// - fails: an incomplete judgment earns a member-local refusal.
    /// - panics: none.
    /// - executable: none — the written telescope is source syntax the result
    ///   does not retain beside the sort.
    ///
    /// # Errors
    /// Returns malformed syntax or an unreadable port.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an indexed sort beside a plain one is read whole, and
    ///   two unseparated sorts are declined rather than read as one.
    /// - witness: `description::sign::tests::a_terminated_block_is_not_told_it_lacks_terminators`
    /// - witness: `description::sign::tests::unseparated_members_are_declined_rather_than_dropped`
    /// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
    /// - witness: `described::tests::a_sign_answers_at_every_member`
    fn signature_sort(
        &self,
        run: &mut Run<'_>,
    ) -> Result<(SortDesc, PresentedSort, WrittenSortMember), DescriptionDiagnostic>
    {
        let name = run.take()?;
        let mut indices = Vec::new();
        let mut presented = Vec::new();
        let mut written = Vec::new();
        if run.eat(Spelling("(")).0 {
            while !run.eat(Spelling(")")).0 {
                let index = run.take()?;
                if !run.eat(Spelling(":")).0 {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
                let sort = run.take()?;
                indices.push(SortIndex::new(self.text(index).0, self.text(sort).0));
                let (term, at) = self.sort_term(sort)?;
                presented.push(Port {
                    name: self.text(index).0.into(),
                    sort: term,
                });
                written.push(WrittenPort {
                    named: Maybe::Present(index.span),
                    sort: at,
                });
                if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
            }
        }
        if !run.eat(Spelling(":")).0 {
            return Err(run.signature_fault(SignatureFault::MissingJudgment));
        }
        let classifier = run.take()?;
        if self.text(classifier).0 != "Type" {
            return Err(run.fault(DescriptionFault::TypeShape));
        }
        run.end()?;
        Ok((
            SortDesc::family(self.text(name).0, DeclPolarity::Data, indices),
            PresentedSort {
                name: self.text(name).0.into(),
                named: name,
                indices: presented,
            },
            WrittenSortMember {
                named: name.span,
                classifier: classifier.span,
                indices: written,
            },
        ))
    }

    /// Read a boundary-only operation; never discard its filler or a port.
    ///
    /// # Specification
    /// - ensures: admitted operations retain every input and every output, in
    ///   order, one monomial per output, beside the operation as it presents
    ///   itself to a model signature: its name tile and each port's sort read
    ///   as a sort over index terms; and where its name and each port are
    ///   written.
    /// - fails: a filler is an explicit decline; a port name written twice on
    ///   the boundary is two ports, not one wire, and is refused by name.
    /// - panics: none.
    /// - executable: none — the written boundary is source syntax the operation
    ///   does not retain.
    ///
    /// # Errors
    /// Returns the precise signature boundary or malformed syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a filler, a data-spelled operation, a shared port
    ///   name and a two-output operation separate the declines from admission,
    ///   and the admitted outputs keep their order.
    /// - witness: `description::sign::tests::an_oper_filler_stays_declined_and_names_its_own_rung`
    /// - witness: `description::sign::tests::a_data_spelled_sign_oper_declines_before_no_output_can_be_fabricated`
    /// - witness: `description::sign::tests::a_two_output_operation_keeps_both_ports_in_order`
    /// - witness: `description::sign::tests::a_port_name_on_both_sides_is_two_ports`
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `described::tests::a_sign_answers_at_every_member`
    fn signature_operation(
        &self,
        run: &mut Run<'_>,
        sorts: &[SortDesc],
    ) -> Result<(OperDesc, PresentedOperation, WrittenOperation), DescriptionDiagnostic>
    {
        let name = run.take()?;
        if !run.eat(Spelling(":")).0 {
            return Err(run.signature_fault(SignatureFault::MissingJudgment));
        }
        let boundary = self.boundary(run, sorts, ArrowRow::Mapping)?;
        if run.at(Spelling("{")).0 {
            return Err(run.signature_fault(SignatureFault::OperationFiller));
        }
        run.end()?;
        let ports: Vec<&SortRef> = boundary.inputs.iter().chain(&boundary.outputs).collect();
        if let Some(&shared) = ports
            .iter()
            .enumerate()
            .find(|&(at, port)| {
                ports
                    .iter()
                    .take(at)
                    .any(|earlier| earlier.name == port.name)
            })
            .map(|(_, port)| port)
        {
            return Err(run.signature_fault(SignatureFault::SharedPort(shared.name.clone())));
        }
        let (inputs, written_inputs) = self.presented_ports(
            &boundary.inputs,
            &boundary.input_sorts,
            &boundary.input_names,
        )?;
        let (outputs, written_outputs) = self.presented_ports(
            &boundary.outputs,
            &boundary.output_sorts,
            &boundary.output_names,
        )?;
        let presented = PresentedOperation {
            name: self.text(name).0.into(),
            named: name,
            inputs,
            outputs,
        };
        let arity = BridgeArity::tupled(boundary.inputs, boundary.outputs);
        Ok((
            OperDesc::new(self.text(name).0, arity, Attrs::empty()),
            presented,
            WrittenOperation {
                named: name.span,
                inputs: written_inputs,
                outputs: written_outputs,
            },
        ))
    }

    /// Each port of one side with its written sort read as a sort over index
    /// terms, and where it is written.
    ///
    /// # Specification
    /// - ensures: one port per entry of `ports`, in order, under its name, and
    ///   one written port per port, its name tile from `names` and its sort's
    ///   bytes and index terms.
    /// - fails: as [`Self::sort_term`].
    /// - panics: none.
    /// - executable: none — the sorts read are source syntax.
    ///
    /// # Errors
    /// Returns `Malformed` for a sort that is neither a name nor an
    /// application.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::signature_operation`].
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `described::tests::a_sign_answers_at_every_member`
    fn presented_ports(
        &self,
        ports: &[SortRef],
        sorts: &[Placed],
        names: &[Maybe<ByteSpan, port_name::Absent>],
    ) -> Result<(Vec<Port>, Vec<WrittenPort>), DescriptionDiagnostic>
    {
        let mut presented = Vec::with_capacity(ports.len());
        let mut written = Vec::with_capacity(ports.len());
        for ((port, &sort), &named) in ports.iter().zip(sorts).zip(names) {
            let (term, at) = self.sort_term(sort)?;
            presented.push(Port {
                name: port.name.clone(),
                sort: term,
            });
            written.push(WrittenPort { named, sort: at });
        }
        Ok((presented, written))
    }

    /// Read a written sort as a sort name over index terms: `Ob` with none,
    /// `Hom(a, b)` with two; and where it and each index term are written.
    ///
    /// # Specification
    /// - ensures: a single name tile is its sort with no indices; an
    ///   application is its head's spelling over each argument read as a free
    ///   term, in order, each argument's nodes written where they stand.
    /// - fails: a form that is neither is malformed.
    /// - panics: none.
    /// - executable: none — the sort read is source syntax.
    ///
    /// # Errors
    /// Returns `Malformed` for a sort that is neither a name nor an
    /// application.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `CatShape` ports read their indexed and unindexed
    ///   sorts.
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    fn sort_term(
        &self,
        at: Placed,
    ) -> Result<(SortTerm, WrittenSort), DescriptionDiagnostic>
    {
        let pieces = self.pieces(at)?;
        if let [Piece::Tile { .. }] = *pieces.as_slice() {
            return Ok((
                SortTerm {
                    sort: self.text(at).0.into(),
                    indices: Vec::new(),
                },
                WrittenSort {
                    span: at.span,
                    indices: Vec::new(),
                },
            ));
        }
        let mut run = Run::new(&pieces, at.span);
        let head = run.take()?;
        if !run.eat(Spelling("(")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let mut indices = Vec::new();
        let mut written = Vec::new();
        while !run.eat(Spelling(")")).0 {
            let (index, nodes) = self.free_term(run.take()?)?;
            indices.push(index);
            written.push(nodes);
            if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        run.end()?;
        Ok((
            SortTerm {
                sort: self.text(head).0.into(),
                indices,
            },
            WrittenSort {
                span: at.span,
                indices: written,
            },
        ))
    }

    /// Read a rule member: a written face between two terms, or a circuit
    /// body whose sphere is derived from the written wiring.
    ///
    /// # Specification
    /// - ensures: a member whose first side is a term is the face `lhs ==> rhs`
    ///   it writes; a member whose first side is a port group is a circuit rule
    ///   whose source and target are derived, never fabricated for a failed
    ///   body, with one root per declared output and one port per output of
    ///   each frame.
    /// - fails: malformed, cyclic, oversized and unrepresentable bodies are
    ///   located; a redex binds exactly one port; a member with no body whose
    ///   first side is a parenthesized composite, a cell between composites of
    ///   cells, is a fillerless higher cell.
    /// - panics: none.
    /// - executable: none — the derived sphere is checked by the derivation it
    ///   comes from; restating it would derive it again.
    ///
    /// # Errors
    /// Returns syntax, interface, instantiation or boundary-derivation
    /// failures.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a readable body, a cycle, a body past the node
    ///   ceiling, a written face and a two-rooted body over a many-out frame
    ///   separate a derived sphere, a written one and the two refusals.
    /// - witness: `description::sign::tests::a_ruled_sign_block_lowers_its_members_into_a_description`
    /// - witness: `description::sign::tests::a_wiring_that_closes_a_cycle_earns_the_declaration_tables_refusal`
    /// - witness: `description::sign::tests::a_doubling_body_declines_on_the_derivation_node_budget`
    /// - witness: `description::sign::tests::the_cat_shape_laws_are_written_faces`
    /// - witness: `description::sign::tests::a_many_out_frame_binds_every_port_and_roots_the_body`
    /// - witness: `description::sign::tests::a_coherence_between_composites_is_a_higher_cell`
    fn signature_rule(
        &self,
        run: &mut Run<'_>,
        sorts: &[SortDesc],
        scope: &BTreeMap<Written<'_>, HeadKind>,
    ) -> Result<RuleMember, DescriptionDiagnostic>
    {
        let name = run.take()?;
        if !run.eat(Spelling(":")).0 {
            return Err(run.signature_fault(SignatureFault::WrittenFace));
        }
        let parenthesized = !run.at(Spelling("(")).0
            && run
                .remaining()
                .first()
                .is_some_and(|piece| self.text(piece.placed()).0.starts_with('('));
        let bodied = run
            .remaining()
            .iter()
            .any(|piece| matches!(*piece, Piece::Tile { ref label, .. } if label.as_ref() == "{"));
        if parenthesized && !bodied {
            return Err(run.signature_fault(SignatureFault::HigherCell));
        }
        if !run.at(Spelling("(")).0 && !parenthesized {
            let lhs = run.take()?;
            run.arrow(Some(ArrowRow::Face))?;
            let rhs = run.take()?;
            run.end()?;
            let (lhs, left) = self.free_term(lhs)?;
            let (rhs, right) = self.free_term(rhs)?;
            let variables = derive_cell_var_meta(&lhs);
            let presented = PresentedLaw {
                name: self.text(name).0.into(),
                named: name,
                left: lhs.clone(),
                right: rhs.clone(),
            };
            return Ok(RuleMember::Face(
                RuleFace::new(lhs, rhs, variables, surface_span(run.span)),
                presented,
                WrittenFace {
                    named: Maybe::Present(name.span),
                    left,
                    right,
                },
            ));
        }
        let boundary = self.boundary(run, sorts, ArrowRow::Face)?;
        if boundary.outputs.is_empty() {
            return Err(run.signature_fault(SignatureFault::MissingOutput));
        }
        if !run.eat(Spelling("{")).0 {
            return Err(run.signature_fault(SignatureFault::HigherCell));
        }
        let mut nodes = Vec::new();
        let mut frames = Vec::new();
        while !run.eat(Spelling("}")).0 {
            if run.at(Spelling("feed")).0 {
                return Err(run.signature_fault(SignatureFault::Wheel));
            }
            if !run.eat(Spelling("node")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
            if !run.at(Spelling(":")).0 {
                let _label = run.take()?;
            }
            if !run.eat(Spelling(":")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
            let head = run.take()?;
            let arguments = self.wire_tuple(run)?;
            let rewrite = boundary
                .rewrites
                .iter()
                .find(|port| port.name.as_ref() == self.text(head).0);
            let kind = scope.get(&self.text(head)).copied();
            let expected = if rewrite.is_some() {
                Some(ArrowRow::Face)
            }
            else {
                kind.map(HeadKind::row)
            };
            let actual = run.arrow(expected)?;
            if actual == ArrowRow::Face && rewrite.is_none() {
                return Err(run
                    .signature_fault(SignatureFault::UndeclaredRewrite(self.text(head).0.into())));
            }
            let written_outputs = self.wire_tuple(run)?;
            if written_outputs.is_empty() {
                return Err(run.signature_fault(SignatureFault::MissingOutput));
            }
            let outputs: Vec<Name> = written_outputs
                .iter()
                .map(|wire| wire.name.clone())
                .collect();
            let terms: Vec<_> = arguments
                .iter()
                .map(|wire| FreeTerm::var(wire.name.clone()))
                .collect();
            frames.push(WrittenFrame {
                head: WrittenWire {
                    name: self.text(head).0.into(),
                    span: head.span,
                },
                arguments,
                outputs: written_outputs,
            });
            let arguments = terms;
            let node =
                if let Some(port) = rewrite {
                    let out = match <[Name; 1]>::try_from(outputs) {
                        | Ok([out]) => out,
                        | Err(several) => {
                            return Err(run.signature_fault(SignatureFault::MultipleOutputs(
                                OutputCount(several.len()),
                            )));
                        },
                    };
                    CircuitNode::Redex(port.interface().instantiate(arguments, out).map_err(
                        |error| run.signature_fault(SignatureFault::Instantiation(error)),
                    )?)
                }
                else {
                    let head = match kind {
                        | Some(HeadKind::Constructor) => FrameHead::Ctor(self.text(head).0.into()),
                        | Some(HeadKind::Operation | HeadKind::Rewrite) | None => {
                            FrameHead::Op(self.text(head).0.into())
                        },
                    };
                    CircuitNode::Frame(CircuitFrame::binding(head, arguments, outputs))
                };
            nodes.push(node);
            if !run.eat(Spelling(";")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        run.end()?;
        let roots: Vec<Name> = boundary
            .outputs
            .iter()
            .map(|output| output.name.clone())
            .collect();
        let body = CircuitBody::rooted(nodes, roots);
        let derived = derive_boundaries(&body)
            .map_err(|error| run.signature_fault(SignatureFault::Derivation(error)))?;
        let vars = derive_cell_var_meta(&derived.source);
        let sphere = RuleFace::new(derived.source, derived.target, vars, surface_span(run.span));
        let ports = boundary
            .inputs
            .iter()
            .zip(&boundary.input_sorts)
            .zip(&boundary.input_names)
            .chain(
                boundary
                    .outputs
                    .iter()
                    .zip(&boundary.output_sorts)
                    .zip(&boundary.output_names),
            )
            .map(|((port, sort), &named)| WrittenCircuitPort {
                name: port.name.clone(),
                sort: port.sort.clone(),
                written: WrittenPort {
                    named,
                    sort: WrittenSort {
                        span: sort.span,
                        indices: Vec::new(),
                    },
                },
            })
            .collect();
        Ok(RuleMember::Circuit(
            CircuitRule::new(self.text(name).0, sphere, body).with_ports(boundary.rewrites),
            PresentedCircuit {
                name: self.text(name).0.into(),
                named: name,
            },
            WrittenCircuit {
                named: name.span,
                ports,
                rewrites: boundary.written_rewrites,
                frames,
            },
        ))
    }

    /// Read both signature sides and rewrite binders before the optional
    /// filler.
    ///
    /// # Specification
    /// - ensures: only a written arrow makes the first side an input interface.
    /// - fails: expression endpoints and mismatched arrows remain
    ///   distinguishable.
    /// - panics: none.
    /// - executable: none — whether an arrow was written is source syntax the
    ///   boundary does not retain.
    ///
    /// # Errors
    /// Returns a located signature reading failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an expression endpoint and a node whose arrow
    ///   disagrees with its head are refused apart.
    /// - witness: `description::sign::tests::an_expression_kind_signature_endpoint_is_refused_by_the_description_route`
    /// - witness: `description::sign::tests::node_arrow_resolution_distinguishes_declared_and_unknown_heads`
    fn boundary(
        &self,
        run: &mut Run<'_>,
        sorts: &[SortDesc],
        row: ArrowRow,
    ) -> Result<Boundary, DescriptionDiagnostic>
    {
        let mut rewrites = Vec::new();
        let mut written_rewrites = Vec::new();
        let first = self.port_side(run, sorts, &mut rewrites, &mut written_rewrites)?;
        let (inputs, outputs) = if run.has_arrow().0 {
            run.arrow(Some(row))?;
            let second = self.port_side(run, sorts, &mut rewrites, &mut written_rewrites)?;
            (first, second)
        }
        else {
            (
                Side {
                    ports: Vec::new(),
                    sorts: Vec::new(),
                    names: Vec::new(),
                },
                first,
            )
        };
        Ok(Boundary {
            inputs: inputs.ports,
            outputs: outputs.ports,
            input_sorts: inputs.sorts,
            output_sorts: outputs.sorts,
            input_names: inputs.names,
            output_names: outputs.names,
            rewrites,
            written_rewrites,
        })
    }

    /// Read direct port syntax, retaining unnamed ports as distinct fresh
    /// wires.
    ///
    /// # Specification
    /// - ensures: typed ports and rewrite binders retain source order and
    ///   names, each port its written sort and name tile, and each rewrite
    ///   binder where its name and sides are written.
    /// - fails: a parenthesized expression is not coerced to a circuit
    ///   interface.
    /// - panics: none.
    /// - executable: none — source order of the written ports is syntax the
    ///   result does not retain beside them.
    ///
    /// # Errors
    /// Returns malformed binders, arrows or expression endpoints.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a rewrite binder beside data ports keeps its name and
    ///   face, and a parenthesized expression is refused as an endpoint.
    /// - witness: `description::sign::tests::a_ruled_sign_block_lowers_its_members_into_a_description`
    /// - witness: `description::sign::tests::an_expression_kind_signature_endpoint_is_refused_by_the_description_route`
    fn port_side(
        &self,
        run: &mut Run<'_>,
        sorts: &[SortDesc],
        rewrites: &mut Vec<RewritePort>,
        written_rewrites: &mut Vec<WrittenRewrite>,
    ) -> Result<Side, DescriptionDiagnostic>
    {
        let grouped = run.eat(Spelling("(")).0;
        let mut side = Side {
            ports: Vec::new(),
            sorts: Vec::new(),
            names: Vec::new(),
        };
        let wire = |at: Placed| WrittenWire {
            name: self.text(at).0.into(),
            span: at.span,
        };
        loop {
            if grouped && run.eat(Spelling(")")).0 {
                break;
            }
            if run.eat(Spelling("rule")).0 {
                let name = run.take()?;
                if !run.eat(Spelling(":")).0 {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
                let lhs = run.take()?;
                run.arrow(Some(ArrowRow::Face))?;
                let rhs = run.take()?;
                let port = if self.text(lhs).0 == self.text(rhs).0
                    && sorts
                        .iter()
                        .any(|sort| sort.name.as_ref() == self.text(lhs).0)
                {
                    RewritePort::sorted(self.text(name).0, self.text(lhs).0)
                }
                else {
                    let (left, _) = self.free_term(lhs)?;
                    let (right, _) = self.free_term(rhs)?;
                    RewritePort::pinned(self.text(name).0, left, right)
                };
                rewrites.push(port);
                written_rewrites.push(WrittenRewrite {
                    named: wire(name),
                    left: wire(lhs),
                    right: wire(rhs),
                });
            }
            else {
                let _data = run.eat(Spelling("data")).0;
                let first = run.take()?;
                if self.text(first).0.starts_with('(') {
                    return Err(DescriptionDiagnostic {
                        span: first.span,
                        fault: DescriptionFault::Signature(SignatureFault::ExpressionEndpoint),
                    });
                }
                let (name, sort, named) = if run.eat(Spelling(":")).0 {
                    (
                        self.port_name(first),
                        run.take()?,
                        Maybe::Present(first.span),
                    )
                }
                else {
                    (
                        fresh_port(first),
                        first,
                        Maybe::Absent(port_name::Absent::Unnamed),
                    )
                };
                side.ports.push(SortRef::new(name, self.text(sort).0));
                side.sorts.push(sort);
                side.names.push(named);
            }
            if !grouped {
                break;
            }
            if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        Ok(side)
    }

    /// Read a node's literal tuple of port names, each where it is written.
    ///
    /// # Specification
    /// - ensures: argument order is preserved and anonymous ports do not
    ///   collide; each wire keeps its bytes.
    /// - fails: an incomplete tuple is refused at its member.
    /// - panics: none.
    /// - executable: none — argument order is source syntax the names do not
    ///   retain.
    ///
    /// # Errors
    /// Returns malformed tuple syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-argument node keeps its arguments in order, and
    ///   a repeated argument reaches the cell layer's linearity refusal.
    /// - witness: `description::sign::tests::a_ruled_sign_block_lowers_its_members_into_a_description`
    /// - witness: `description::sign::tests::a_repeated_argument_name_reaches_the_linearity_refusal`
    fn wire_tuple(
        &self,
        run: &mut Run<'_>,
    ) -> Result<Vec<WrittenWire>, DescriptionDiagnostic>
    {
        if !run.eat(Spelling("(")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let mut ports = Vec::new();
        while !run.eat(Spelling(")")).0 {
            let at = run.take()?;
            ports.push(WrittenWire {
                name: self.port_name(at),
                span: at.span,
            });
            if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        Ok(ports)
    }

    /// Preserve a written wire name or mint the anonymous port's private name.
    ///
    /// # Specification
    /// trivial.
    fn port_name(
        &self,
        at: Placed,
    ) -> Name
    {
        if self.text(at).0 == "_" {
            fresh_port(at)
        }
        else {
            self.text(at).0.into()
        }
    }
}

impl Run<'_>
{
    /// Locate a typed signature refusal at its written member.
    ///
    /// # Specification
    /// trivial.
    fn signature_fault(
        &self,
        fault: SignatureFault,
    ) -> DescriptionDiagnostic
    {
        self.fault(DescriptionFault::Signature(fault))
    }

    /// Whether the next tile belongs to the ruled arrow grid.
    ///
    /// # Specification
    /// trivial.
    fn has_arrow(&self) -> TileSeen
    {
        TileSeen(
            ["-->", "<->", "==>", "<=>"]
                .into_iter()
                .any(|glyph| self.at(Spelling(glyph)).0),
        )
    }

    /// Confirm an arrow's row without interpreting an unresolved head.
    ///
    /// # Specification
    /// - ensures: mismatches and the reserved reversible glyphs, `<->` and
    ///   `<=>`, retain their own span.
    /// - fails: a missing arrow is malformed syntax.
    /// - panics: none.
    /// - executable: none — the glyph consumed is source syntax the row does
    ///   not retain.
    ///
    /// # Errors
    /// Returns a malformed, reversible or wrong-row diagnostic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declared head under the wrong arrow, an unknown
    ///   head under any arrow and a reversible map are refused apart.
    /// - witness: `description::sign::tests::node_arrow_resolution_distinguishes_declared_and_unknown_heads`
    /// - witness: `description::sign::tests::both_reversible_glyphs_are_reserved`
    fn arrow(
        &mut self,
        expected: Option<ArrowRow>,
    ) -> Result<ArrowRow, DescriptionDiagnostic>
    {
        let at = self.cursor.here();
        let actual = if self.eat(Spelling("<=>")).0 || self.eat(Spelling("<->")).0 {
            return Err(DescriptionDiagnostic {
                span: at,
                fault: DescriptionFault::Signature(SignatureFault::Reversible),
            });
        }
        else if self.eat(Spelling("-->")).0 {
            ArrowRow::Mapping
        }
        else if self.eat(Spelling("==>")).0 {
            ArrowRow::Face
        }
        else {
            return Err(self.fault(DescriptionFault::Malformed));
        };
        if let Some(expected) = expected
            && actual != expected
        {
            return Err(DescriptionDiagnostic {
                span: at,
                fault: DescriptionFault::Signature(SignatureFault::ArrowMismatch {
                    expected,
                    actual,
                }),
            });
        }
        Ok(actual)
    }
}

/// A member's precise written interval, excluding its separator.
///
/// # Specification
/// trivial.
fn member_span(
    member: &[Piece],
    fallback: ByteSpan,
) -> ByteSpan
{
    match (member.first(), member.last()) {
        | (Some(first), Some(last)) => {
            ByteSpan::new(first.placed().span.start(), last.placed().span.end()).unwrap_or(fallback)
        },
        | _ => fallback,
    }
}

/// The description's provenance for a written member span.
///
/// # Specification
/// trivial.
fn surface_span(span: ByteSpan) -> SurfaceSpan
{
    SurfaceSpan::new(
        usize::from(span.start()).into(),
        usize::from(span.end()).into(),
    )
}

/// An anonymous port's collision-free, source-stable internal name.
///
/// # Specification
/// trivial.
fn fresh_port(at: Placed) -> Name
{
    format!("$port:{}", usize::from(at.span.start())).into()
}

#[cfg(test)]
mod tests;
