//! Ruled signature members and their literal circuit bodies.

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
use crate::circuit::ArrowRow;
use crate::circuit::OutputCount;
use crate::circuit::SignatureFault;
use crate::form::Piece;
use crate::form::Placed;

/// The two sides of a signature and its rewrite-sorted binders.
struct Boundary
{
    /// Ordinary value ports supplied by the interface.
    inputs: Vec<SortRef>,
    /// Ports at which the interface returns its result.
    outputs: Vec<SortRef>,
    /// The rewrite heads in scope in the body.
    rewrites: Vec<RewritePort>,
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
                | Ok(sort) => sorts.push(sort),
                | Err(diagnostic) => diagnostics.push(diagnostic),
            }
        }
        let mut operations = Vec::new();
        let mut operation_spans = Vec::new();
        let mut circuits = Vec::new();
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
                self.signature_operation(&mut reading, &sorts)
                    .map(|operation| {
                        operations.push(operation);
                        operation_spans.push(span);
                    })
            }
            else if reading.eat(Spelling("rule")).0 {
                self.signature_rule(&mut reading, &sorts, &scope)
                    .map(|rule| circuits.push(rule))
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
            [],
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
        })
    }

    /// Read an indexed or unindexed sort without erasing its telescope.
    ///
    /// # Specification
    /// - ensures: indices retain their written order and sort names.
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
    fn signature_sort(
        &self,
        run: &mut Run<'_>,
    ) -> Result<SortDesc, DescriptionDiagnostic>
    {
        let name = run.take()?;
        let indices = if run.eat(Spelling("(")).0 {
            self.ports(run)?
                .into_iter()
                .map(|port| SortIndex::new(port.name, port.sort))
                .collect()
        }
        else {
            Vec::new()
        };
        if !run.eat(Spelling(":")).0 {
            return Err(run.signature_fault(SignatureFault::MissingJudgment));
        }
        let classifier = run.take()?;
        if self.text(classifier).0 != "Type" {
            return Err(run.fault(DescriptionFault::TypeShape));
        }
        run.end()?;
        Ok(SortDesc::family(
            self.text(name).0,
            DeclPolarity::Data,
            indices,
        ))
    }

    /// Read a boundary-only operation; never discard its filler or extra
    /// outputs.
    ///
    /// # Specification
    /// - ensures: admitted operations retain every input and their one output.
    /// - fails: a filler or a many-output boundary is an explicit decline.
    /// - panics: none.
    /// - executable: none — the written boundary is source syntax the operation
    ///   does not retain.
    ///
    /// # Errors
    /// Returns the precise signature boundary or malformed syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a filler, a data-spelled operation and a readable one
    ///   separate the two declines from admission.
    /// - witness: `description::sign::tests::an_oper_filler_stays_declined_and_names_its_own_rung`
    /// - witness: `description::sign::tests::a_data_spelled_sign_oper_declines_before_no_output_can_be_fabricated`
    fn signature_operation(
        &self,
        run: &mut Run<'_>,
        sorts: &[SortDesc],
    ) -> Result<OperDesc, DescriptionDiagnostic>
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
        let arity = match *boundary.outputs.as_slice() {
            | [] => BridgeArity::new(boundary.inputs, [], [], [], []),
            | [ref output] => BridgeArity::single_output(boundary.inputs, output.clone()),
            | ref outputs => {
                return Err(run
                    .signature_fault(SignatureFault::MultipleOutputs(OutputCount(outputs.len()))));
            },
        };
        Ok(OperDesc::new(self.text(name).0, arity, Attrs::empty()))
    }

    /// Read a rule body and derive its sphere from the written wiring.
    ///
    /// # Specification
    /// - ensures: source and target are derived, never fabricated for a failed
    ///   body.
    /// - fails: malformed, cyclic, oversized and unrepresentable bodies are
    ///   located.
    /// - panics: none.
    /// - executable: none — the derived sphere is checked by the derivation it
    ///   comes from; restating it would derive it again.
    ///
    /// # Errors
    /// Returns syntax, interface, instantiation or boundary-derivation
    /// failures.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a readable body, a cycle and a body past the node
    ///   ceiling separate a derived sphere from the two refusals.
    /// - witness: `description::sign::tests::a_ruled_sign_block_lowers_its_members_into_a_description`
    /// - witness: `description::sign::tests::a_wiring_that_closes_a_cycle_earns_the_declaration_tables_refusal`
    /// - witness: `description::sign::tests::a_doubling_body_declines_on_the_derivation_node_budget`
    fn signature_rule(
        &self,
        run: &mut Run<'_>,
        sorts: &[SortDesc],
        scope: &BTreeMap<Written<'_>, HeadKind>,
    ) -> Result<CircuitRule, DescriptionDiagnostic>
    {
        let name = run.take()?;
        if !run.eat(Spelling(":")).0 {
            return Err(run.signature_fault(SignatureFault::WrittenFace));
        }
        let boundary = self.boundary(run, sorts, ArrowRow::Face)?;
        let output = match *boundary.outputs.as_slice() {
            | [ref output] => output.name.clone(),
            | [] => return Err(run.signature_fault(SignatureFault::MissingOutput)),
            | ref outputs => {
                return Err(run
                    .signature_fault(SignatureFault::MultipleOutputs(OutputCount(outputs.len()))));
            },
        };
        if !run.eat(Spelling("{")).0 {
            return Err(run.signature_fault(SignatureFault::HigherCell));
        }
        let mut nodes = Vec::new();
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
            let mut outputs = self.wire_tuple(run)?;
            if outputs.len() != 1 {
                return Err(run
                    .signature_fault(SignatureFault::MultipleOutputs(OutputCount(outputs.len()))));
            }
            let out = outputs
                .pop()
                .ok_or_else(|| run.signature_fault(SignatureFault::MissingOutput))?;
            let arguments: Vec<_> = arguments.into_iter().map(FreeTerm::var).collect();
            let node =
                if let Some(port) = rewrite {
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
                    CircuitNode::Frame(CircuitFrame::new(head, arguments, out))
                };
            nodes.push(node);
            if !run.eat(Spelling(";")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        run.end()?;
        let body = CircuitBody::new(nodes, output);
        let derived = derive_boundaries(&body)
            .map_err(|error| run.signature_fault(SignatureFault::Derivation(error)))?;
        let vars = derive_cell_var_meta(&derived.source);
        let span = SurfaceSpan::new(
            usize::from(run.span.start()).into(),
            usize::from(run.span.end()).into(),
        );
        let sphere = RuleFace::new(derived.source, derived.target, vars, span);
        Ok(CircuitRule::new(self.text(name).0, sphere, body).with_ports(boundary.rewrites))
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
        let first = self.port_side(run, sorts, &mut rewrites)?;
        let (inputs, outputs) = if run.has_arrow().0 {
            run.arrow(Some(row))?;
            (first, self.port_side(run, sorts, &mut rewrites)?)
        }
        else {
            (Vec::new(), first)
        };
        Ok(Boundary {
            inputs,
            outputs,
            rewrites,
        })
    }

    /// Read direct port syntax, retaining unnamed ports as distinct fresh
    /// wires.
    ///
    /// # Specification
    /// - ensures: typed ports and rewrite binders retain source order and
    ///   names.
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
    ) -> Result<Vec<SortRef>, DescriptionDiagnostic>
    {
        let grouped = run.eat(Spelling("(")).0;
        let mut ports = Vec::new();
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
                    RewritePort::pinned(
                        self.text(name).0,
                        self.free_term(lhs)?,
                        self.free_term(rhs)?,
                    )
                };
                rewrites.push(port);
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
                let (name, sort) = if run.eat(Spelling(":")).0 {
                    (self.port_name(first), run.take()?)
                }
                else {
                    (fresh_port(first), first)
                };
                ports.push(SortRef::new(name, self.text(sort).0));
            }
            if !grouped {
                break;
            }
            if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        Ok(ports)
    }

    /// Read a node's literal tuple of port names.
    ///
    /// # Specification
    /// - ensures: argument order is preserved and anonymous ports do not
    ///   collide.
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
    ) -> Result<Vec<Name>, DescriptionDiagnostic>
    {
        if !run.eat(Spelling("(")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let mut ports = Vec::new();
        while !run.eat(Spelling(")")).0 {
            ports.push(self.port_name(run.take()?));
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
    /// - ensures: mismatches and the reserved reversible glyph retain their own
    ///   span.
    /// - fails: a missing arrow is malformed syntax.
    /// - panics: none.
    /// - executable: none — the glyph consumed is source syntax the row does
    ///   not retain.
    ///
    /// # Errors
    /// Returns a malformed, reversible or wrong-row diagnostic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declared head under the wrong arrow and an unknown
    ///   head under any arrow are refused apart.
    /// - witness: `description::sign::tests::node_arrow_resolution_distinguishes_declared_and_unknown_heads`
    fn arrow(
        &mut self,
        expected: Option<ArrowRow>,
    ) -> Result<ArrowRow, DescriptionDiagnostic>
    {
        let at = self.cursor.here();
        let actual = if self.eat(Spelling("<=>")).0 {
            return Err(DescriptionDiagnostic {
                span: at,
                fault: DescriptionFault::Signature(SignatureFault::Reversible),
            });
        }
        else if self.eat(Spelling("-->")).0 || self.eat(Spelling("<->")).0 {
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
