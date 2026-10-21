//! Ruled signature members and their literal circuit bodies.
//!
//! # Signature blocks
//!
//! A `theory` block is a description judgment, not an ordinary native value
//! family: it has no family classifier, and it defines its name as a value of
//! `Theory`, the presentation code (§ A presentation is a value). It retains
//! declared sorts and their index telescopes, operation boundaries
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
//! derivation rather than fabricating a boundary. A bodiless cell between
//! composites of cells is a higher-cell refusal, an operation filler, in a
//! block or as a top-level `oper`, a filler refusal, and the reversible map
//! `<->` is reserved. `<=>` is the equation: a face arrow whose direction the
//! order chooses. Each refusal is a fragment boundary rather than malformed
//! source. Witnesses:
//! `description::theory::tests::a_ruled_theory_block_lowers_its_members_into_a_description`,
//! `description::theory::tests::a_many_out_frame_binds_every_port_and_roots_the_body`,
//! `description::theory::tests::the_cat_shape_laws_are_written_faces`,
//! `description::theory::tests::a_port_name_on_both_sides_is_two_ports`,
//! `description::theory::tests::theory_declines_and_malformed_wiring_are_refused_apart`.
//!
//! # Wheels
//!
//! An `obs` member declares an observation of a sort, written as an
//! operation's boundary is and kept in the value as an `Obs` member. A rule
//! body's `feed : (out) --> (state);` carries the wire `out` back, one step
//! later, as the port `state` its nodes read (Katis, Sabadini and Walters,
//! _Feedback, Trace and Fixed-Point Semantics_, RAIRO-ITA 36(2), 2002). The
//! nodes stay the body's cut-open wiring, where `state` is a boundary
//! variable, and the rule keeps its feeds beside them. A fed port is read
//! under an observation, one tick, or the rule is refused `BareFeedback` at
//! its bare occurrence: the guard of the feedback rule of Di Lavore, de Felice
//! and Román (_Monoidal Streams for Dataflow Programming_, LICS 2022).
//! Witnesses:
//! `description::theory::tests::an_observed_feed_is_kept_beside_its_cut_open_wiring`,
//! `description::theory::tests::a_refused_theory_block_states_its_refusal`,
//! `description::theory::tests::a_fed_port_no_node_reads_is_refused_at_the_feed`.
//!
//! # Second-order members
//!
//! A sort member classified `Type+` is representable, and an operation's
//! input port may write its sort under restricted binders, `t : pi+ (x : S) .
//! T`, each binding a variable of a representable sort `S` over `T`, outermost
//! first (Kaposi and Xie, _Second-Order Generalised Algebraic Theories_, FSCD
//! 2024, Definition 3). The reader codes both in the value — a sort at
//! `Representable`, a port at `Bound` with its binder chain — so a block
//! written as the description's rendering reads back to that description. A
//! binder over an ordinary sort is the description check's
//! `NonRepresentableBinder`; a sort's index is a plain variable and is refused
//! as malformed under a binder; a binder's domain and a result do not parse
//! under one. `Model(S)` refuses an operation that binds by name: its models
//! are those of its first-order translation.
//!
//! **Choice.** The binder is a form of the input port, not a type former: `pi+`
//! is a marked tile, read only where a parameter list writes a named port. The
//! alternative was a type rule at every type slot, refused by the lowering
//! outside a port; its parenthesis, name, colon and dot molds then competed in
//! every damaged type the parser repairs, and the one-token-drop records
//! recovered worse at dozens of corpus tokens, where the port form leaves
//! every record no worse. The choice reverses when a binder is admitted as a
//! type elsewhere, where a type rule is what reads it. `Type+` stays a type
//! atom: one tile no other form shares. Witnesses:
//! `description::theory::tests::a_rendered_signature_reparses_to_itself`,
//! `description::theory::tests::a_binder_over_an_ordinary_sort_is_refused_by_name`,
//! `model::tests::an_underivable_component_keeps_its_fault`.
//!
//! # The shape parameter
//!
//! A `shape` member states the finite shape the signature's cells are stated
//! over and its named faces: `shape Square : 4 { left = {0, 2}; right = {1,
//! 3}; }` is a shape of four points and two faces of it, each the subshape of
//! the points it lists (Schönlank, Nuyts and Devriese, _Towards `FaceTT`_,
//! TYPES 2026: the shape parameter `ft`). The reader codes it in the value at
//! the head of the sort chain, so the block's rendering reads back to its
//! description; a face with a point past the shape and a face named twice are
//! the description check's `FaceOutsideShape` and `DuplicateFaceName`, and a
//! second `shape` member is malformed. The extension type reads a face as the
//! subshape a cell is fixed on. The spelling is provisional: the keyword, the
//! size after the colon and the braces around each face's points are the
//! first that read, not a settled surface. Witnesses:
//! `description::theory::tests::a_rendered_signature_reparses_to_itself`,
//! `description::theory::tests::a_face_past_its_shape_is_refused_by_name`.
//!
//! # A presentation is a value
//!
//! The reader reads a block's members once, into the parts of a presentation
//! (`TheoryParts`): each sort with its index ports, each operation with its
//! input and output ports, each face as its two terms. Those parts are encoded
//! once, as a `TheoryValue`, and everything after reads the value: the block's
//! description is decoded from it, `Model(S)` derives from it, and the core
//! definition `S : Theory` is it, node for node. Beside the value the reader
//! keeps only provenance — the name tile of each member and the span of each
//! face — and the circuit rules `Theory` does not code yet. An unnamed port
//! carries the empty name in the value, so where it was written leaves the
//! presentation's identity unchanged; every reading names it by its position,
//! `_1` for the second port of an operation. A port's sort is spelled from the
//! value, so `Hom(a,a)` and `Hom(a, a)` are one sort.
//!
//! **Choice.** The description is a view of the value rather than replaced by
//! it: the cell gate, the rules check and coincidence read a `TheoryDesc`, and
//! a view decoded from the value keeps them one consumer of one table while the
//! block is read once. The alternative was the value replacing the table in
//! every consumer, which moves the cell gate and coincidence onto `Theory`
//! before `Theory` codes what they read — circuit rules among them. The choice
//! reverses when `Theory` codes everything a description holds: the consumers
//! then read the value and the view retires. Witness:
//! `description::theory::tests::the_description_is_read_off_the_value`.
//!
//! **Choice.** A `theory` block takes a declared slot under its name whose
//! definition is the block's value at `Theory`, whether or not a member
//! refuses: a refused block's slot carries its first refusal, at that member's
//! span, and each further refusal is a held declaration at its own member's
//! span whose signature half is the block, so the attribute blocks written
//! before the block state every one of them, `@[ refuses("OutOfFragment") ]
//! theory …`. A top-level `oper` declares no core constant: each refusal raised
//! inside it is such a held declaration and its name enters no namespace. The
//! alternatives were a refused block taking no slot, which leaves `S` naming
//! nothing a module or a program can reach, and a block's refusals with no
//! half, which no expectation can state. `Model(S)` derives from the value of
//! a refused block too, as it never inherited the cell gate (the decision is
//! in `module::model`). Witnesses:
//! `description::theory::tests::a_theory_block_defines_its_presentation`,
//! `description::theory::tests::a_refused_theory_block_states_its_refusal`,
//! `description::theory::tests::a_refused_top_level_operation_states_its_refusal`,
//! `description::theory::tests::a_top_level_operation_declines_its_filler_by_name`.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::ToString as _;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::BridgeArity;
use gandr_theory_levitation::CircuitBody;
use gandr_theory_levitation::CircuitFeed;
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
use gandr_theory_levitation::OperationKind;
use gandr_theory_levitation::Representability;
use gandr_theory_levitation::RewritePort;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::ShapeFace;
use gandr_theory_levitation::ShapePoint;
use gandr_theory_levitation::ShapeSize;
use gandr_theory_levitation::SortDesc;
use gandr_theory_levitation::SortIndex;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::SurfaceSpan;
use gandr_theory_levitation::TheoryBinder;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::TheoryOperation;
use gandr_theory_levitation::TheoryParts;
use gandr_theory_levitation::TheoryPort;
use gandr_theory_levitation::TheoryRule;
use gandr_theory_levitation::TheoryShape;
use gandr_theory_levitation::TheorySort;
use gandr_theory_levitation::TheoryValue;
use gandr_theory_levitation::derive_boundaries;
use gandr_theory_levitation::derive_cell_var_meta;
use gandr_theory_levitation::shape_parameter;
use quenchant_shape::shape::Maybe;

use super::DescribedDeclaration;
use super::DescriptionDiagnostic;
use super::DescriptionFault;
use super::DescriptionGrade;
use super::Reader;
use super::Run;
use super::Spelling;
use super::TileSeen;
use super::Written;
use super::family_classifier;
use super::split_members;
use super::written::RuleDirection;
use super::written::RuleOrientation;
use super::written::WrittenBound;
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
use crate::description::DescribedDeclaration as Earlier;
use crate::description::Visible;
use crate::form::Piece;
use crate::form::Placed;
use crate::model::Included;
use crate::model::Placement;
use crate::model::Presentation;
use crate::model::PresentationFault;
use crate::model::PresentedCircuit;
use crate::model::SortTerm;
use crate::model::presentation;
use crate::model::presented_names;
use crate::unit::SourceIndex;

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
    /// Each input port's restricted binders, outermost first, in order.
    input_binders: Vec<Vec<WrittenBinder>>,
    /// Each output port's restricted binders, outermost first, in order.
    output_binders: Vec<Vec<WrittenBinder>>,
    /// Each input port's name tile, in order.
    input_names: Vec<Maybe<ByteSpan, port_name::Absent>>,
    /// Each output port's name tile, in order.
    output_names: Vec<Maybe<ByteSpan, port_name::Absent>>,
    /// The rewrite heads in scope in the body.
    rewrites: Vec<RewritePort>,
    /// Where each rewrite head is written, in the same order.
    written_rewrites: Vec<WrittenRewrite>,
}

/// One side of a signature: its ports, each port's written sort, binders and
/// name tile, in order.
struct Side
{
    /// The ports.
    ports: Vec<SortRef>,
    /// Each port's written sort.
    sorts: Vec<Placed>,
    /// Each port's restricted binders, outermost first.
    binders: Vec<Vec<WrittenBinder>>,
    /// Each port's name tile.
    names: Vec<Maybe<ByteSpan, port_name::Absent>>,
}

/// A restricted binder as a port writes it, `pi+ (name : domain) .`.
#[derive(Clone, Copy)]
struct WrittenBinder
{
    /// The bound variable's name tile.
    name: Placed,
    /// The bound variable's written sort.
    domain: Placed,
}

/// A declared head determines a node arrow before any body is read.
#[derive(Clone, Copy)]
enum HeadKind
{
    /// A constructor frame.
    Constructor,
    /// An operation frame.
    Operation,
    /// An observation frame: it reads its input under an observation of the
    /// input's sort.
    Observation,
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
            Self::Constructor | Self::Operation | Self::Observation => ArrowRow::Mapping,
            Self::Rewrite => ArrowRow::Face,
        }
    }
}

/// How many members of each kind a presentation held before an inclusion
/// extended it.
#[derive(Clone, Copy)]
struct Held
{
    /// The sorts held.
    sorts: usize,
    /// The operations held.
    operations: usize,
    /// The rules held.
    rules: usize,
}

/// A theory block's rule member: a face it writes or a circuit it wires, each
/// with what it presents and where it is written.
enum RuleMember
{
    /// A written face `rule name : lhs ==> rhs`, its name tile and its whole
    /// member.
    Face(TheoryRule, Placed, ByteSpan, WrittenFace),
    /// A circuit rule whose sphere its wiring derives.
    Circuit(CircuitRule, PresentedCircuit, WrittenCircuit),
}

impl Reader<'_, '_>
{
    /// Read each theory member independently, preserving its declared sort set,
    /// into the block's `Theory` value and the description that value reads as.
    /// Each `include` member first extends the presentation by the members of
    /// the block it names among those `visible` holds; each `ext`
    /// member declares its cell sort among the block's sorts and generates its
    /// operations and laws after the written ones.
    ///
    /// # Specification
    /// - ensures: an unreadable member does not consume a following member;
    ///   every member read enters the presentation's value, its circuits beside
    ///   it, and the description is [`described`] of that value with the
    ///   circuits added. The included presentations come first, in written
    ///   order, each by [`TheoryParts::include`], with the inclusion kept
    ///   beside the value and each included member's provenance its own
    ///   block's. An `ext` member's generated operations and laws follow the
    ///   written ones, each placed at the member's keyword.
    /// - fails: a malformed signature head refuses the whole declaration; an
    ///   `include` that names no visible block, names two, or whose members
    ///   clash with the presentation's, and an `ext` member the block cannot
    ///   generate, is that member's own diagnostic.
    /// - panics: none.
    /// - executable: none — a member's independence is a relation between the
    ///   source's members and the report, which the call does not retain.
    ///
    /// # Errors
    /// Returns a located malformed-head diagnostic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declined rule member between readable ones leaves
    ///   both neighbours read, and an unreadable member keeps its own report; a
    ///   block that includes another restricts along the inclusion to it, and
    ///   an include of an unknown or clashing block is refused at the member;
    ///   an extension generates the signature a hand-written block states.
    /// - witness: `description::theory::tests::a_declined_rule_member_leaves_the_members_after_it_intact`
    /// - witness: `description::theory::tests::an_unreadable_member_keeps_its_own_report`
    /// - witness: `description::theory::tests::the_description_is_read_off_the_value`
    /// - witness: `description::theory::tests::an_included_theory_is_the_extension_restricted`
    /// - witness: `description::theory::tests::an_include_is_refused_at_its_member`
    /// - witness: `description::theory::tests::an_extension_generates_its_signature`
    pub(super) fn signature(
        &self,
        at: Placed,
        run: &mut Run<'_>,
        serial: NominalSerial,
        visible: &Visible<'_>,
        diagnostics: &mut Vec<DescriptionDiagnostic>,
    ) -> Result<DescribedDeclaration, DescriptionDiagnostic>
    {
        let named = run.take()?;
        if !run.eat(Spelling("{")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let members = split_members(run.remaining());
        let mut parts = TheoryParts::default();
        let mut placement = Placement::default();
        let mut scope = BTreeMap::new();
        let mut written = WrittenMembers::default();
        let mut operation_spans = Vec::new();
        let mut circuits = Vec::new();
        let mut presented_circuits = Vec::new();
        let mut inclusions = Vec::new();
        let mut included_circuits = BTreeSet::new();
        let mut extensions = Vec::new();
        let mut face_tiles = Vec::new();
        for member in &members {
            let span = member_span(member, at.span);
            let mut reading = Run::new(member, span);
            if !reading.eat(Spelling("include")).0 {
                continue;
            }
            let (declaration, presented, included, include_tile) =
                match self.included(&mut reading, visible) {
                    Ok(found) => found,
                    Err(diagnostic) => {
                        diagnostics.push(diagnostic);
                        continue;
                    },
                };
            let read = Held {
                sorts: parts.sorts.len(),
                operations: parts.operations.len(),
                rules: parts.rules.len(),
            };
            let inclusion = match parts.include(&included) {
                Ok(inclusion) => inclusion,
                Err(clash) => {
                    diagnostics.push(reading.signature_fault(SignatureFault::IncludeClash(clash)));
                    continue;
                },
            };
            for ((position, &tile), member) in inclusion
                .sorts
                .iter()
                .zip(&presented.placement.sorts)
                .zip(&declaration.written.sorts)
            {
                if usize::from(*position) >= read.sorts {
                    placement.sorts.push(tile);
                    written.sorts.push(member.clone());
                }
            }
            for (((position, &tile), &whole), member) in inclusion
                .operations
                .iter()
                .zip(&presented.placement.operations)
                .zip(&declaration.operation_spans)
                .zip(&declaration.written.operations)
            {
                if usize::from(*position) >= read.operations {
                    scope.insert(self.text(tile), HeadKind::Operation);
                    placement.operations.push(tile);
                    operation_spans.push(whole);
                    written.operations.push(member.clone());
                }
            }
            for (((position, &tile), &whole), sides) in inclusion
                .rules
                .iter()
                .zip(&presented.placement.laws)
                .zip(&presented.placement.faces)
                .zip(&declaration.written.faces)
            {
                if usize::from(*position) >= read.rules {
                    scope.insert(self.text(tile), HeadKind::Rewrite);
                    placement.laws.push(tile);
                    placement.faces.push(whole);
                    written.faces.push(sides.clone());
                }
            }
            for ((presented_circuit, rule), wired) in presented
                .circuits
                .iter()
                .zip(&declaration.description.circuits)
                .zip(&declaration.written.circuits)
            {
                if included_circuits.insert(&presented_circuit.name) {
                    presented_circuits.push(presented_circuit.clone());
                    circuits.push(rule.clone());
                    written.circuits.push(wired.clone());
                }
            }
            inclusions.push(Included {
                theory: declaration.description.id.clone(),
                inclusion,
                named: include_tile,
                block: declaration.at,
            });
        }
        for member in &members {
            let span = member_span(member, at.span);
            let mut reading = Run::new(member, span);
            let kind = if reading.eat(Spelling("oper")).0 {
                Some(HeadKind::Operation)
            }
            else if reading.eat(Spelling("obs")).0 {
                Some(HeadKind::Observation)
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
            if reading.eat(Spelling("shape")).0 {
                match self.signature_shape(&mut reading) {
                    Ok(_) if matches!(parts.shape, Maybe::Present(_)) => {
                        diagnostics.push(reading.fault(DescriptionFault::Malformed));
                    },
                    Ok((shape, tiles)) => {
                        parts.shape = Maybe::Present(shape);
                        face_tiles = tiles;
                    },
                    Err(diagnostic) => diagnostics.push(diagnostic),
                }
                continue;
            }
            if reading.at(Spelling("ext")).0 {
                match self.extension_member(&mut reading) {
                    Ok((extension, sort, member)) => {
                        parts.sorts.push(sort);
                        placement.sorts.push(extension.cell());
                        written.sorts.push(member);
                        extensions.push(extension);
                    },
                    Err(diagnostic) => diagnostics.push(diagnostic),
                }
                continue;
            }
            if !reading.eat(Spelling("sort")).0 {
                continue;
            }
            match self.signature_sort(&mut reading) {
                Ok((sort, tile, member)) => {
                    parts.sorts.push(sort);
                    placement.sorts.push(tile);
                    written.sorts.push(member);
                },
                Err(diagnostic) => diagnostics.push(diagnostic),
            }
        }
        for member in members {
            let span = member_span(member, at.span);
            let mut reading = Run::new(member, span);
            let result = if reading.eat(Spelling("sort")).0 || reading.eat(Spelling("shape")).0 {
                continue;
            }
            else if reading.eat(Spelling("data")).0 {
                Err(reading.signature_fault(SignatureFault::RetiredDataMember))
            }
            else if reading.eat(Spelling("oper")).0 || reading.at(Spelling("obs")).0 {
                let kind = if reading.eat(Spelling("obs")).0 {
                    OperationKind::Observation
                }
                else {
                    OperationKind::Operation
                };
                self.signature_operation(&mut reading, &parts.sorts, kind)
                    .map(|(operation, tile, ports)| {
                        parts.operations.push(operation);
                        placement.operations.push(tile);
                        operation_spans.push(span);
                        written.operations.push(ports);
                    })
            }
            else if reading.eat(Spelling("rule")).0 {
                self.signature_rule(&mut reading, &parts.sorts, &scope)
                    .map(|member| match member {
                        RuleMember::Circuit(rule, presented, wired) => {
                            circuits.push(rule);
                            presented_circuits.push(presented);
                            written.circuits.push(wired);
                        },
                        RuleMember::Face(face, tile, whole, sides) => {
                            parts.rules.push(face);
                            placement.laws.push(tile);
                            placement.faces.push(whole);
                            written.faces.push(sides);
                        },
                    })
            }
            else if reading.eat(Spelling("include")).0 || reading.eat(Spelling("ext")).0 {
                continue;
            }
            else {
                Err(reading.signature_fault(SignatureFault::MissingJudgment))
            };
            if let Err(diagnostic) = result {
                diagnostics.push(diagnostic);
            }
        }
        for extension in &extensions {
            match self.extended(extension, &parts, &placement.operations, &face_tiles) {
                Ok(generated) => {
                    for (operation, tile, ports) in generated.operations {
                        parts.operations.push(operation);
                        placement.operations.push(tile);
                        operation_spans.push(extension.span());
                        written.operations.push(ports);
                    }
                    for (law, tile, sides) in generated.laws {
                        parts.rules.push(law);
                        placement.laws.push(tile);
                        placement.faces.push(extension.span());
                        written.faces.push(sides);
                    }
                    written.uses.extend(generated.uses);
                },
                Err(diagnostic) => diagnostics.push(diagnostic),
            }
        }
        let presentation = Presentation {
            value: TheoryValue::encode(&parts),
            placement,
            circuits: presented_circuits,
            inclusions,
        };
        let description = described(&presentation, NominalId::new(serial, self.text(named).0))
            .map_err(|_unread| DescriptionDiagnostic {
                span: at.span,
                fault: DescriptionFault::Malformed,
            })?;
        Ok(DescribedDeclaration {
            at,
            named,
            description: description.with_circuits(circuits),
            operation_spans,
            parameters: Vec::new(),
            classifier: Maybe::Absent(family_classifier::Absent::Signature),
            presentation: Maybe::Present(presentation),
            written,
        })
    }

    /// The `theory` block an `include` member names, its presentation's
    /// members, and the member's name tile: the last block of its own source
    /// under that name, or else the one block of the sources it imports
    /// unqualified.
    ///
    /// # Specification
    /// - requires: `run` stands just past the member's `include` keyword.
    /// - ensures: the block, its presentation, the parts its value decodes to,
    ///   and the tile naming it; a block of the including source shadows the
    ///   imported ones, and a later block of one imported source an earlier.
    /// - fails: a missing name is malformed; a name no block of `visible`
    ///   presents is [`SignatureFault::UnknownInclude`]; a name blocks of two
    ///   imported sources present, and none of its own, is
    ///   [`SignatureFault::AmbiguousInclude`]; a value that does not decode is
    ///   malformed.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the located diagnostic of the first failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::signature`]; one name presented by two
    ///   imported sources is refused where one presented by one is read.
    /// - witness: `description::theory::tests::an_include_is_refused_at_its_member`
    /// - witness: `description::theory::tests::an_included_theory_is_the_extension_restricted`
    /// - witness: `tests::namespace::an_include_reads_the_theories_its_source_imports_1224`
    #[spec(ensures: |ret| match ret {
        | Ok((found, presented, _, _)) => {
            matches!(found.presentation, Maybe::Present(ref own) if own == presented)
        },
        | Err(_) => true,
    })]
    fn included<'earlier>(
        &self,
        run: &mut Run<'_>,
        visible: &Visible<'earlier>,
    ) -> Result<
        (
            &'earlier Earlier,
            &'earlier Presentation,
            TheoryParts,
            Placed,
        ),
        DescriptionDiagnostic,
    >
    {
        let named = run.take()?;
        let Written(name) = self.text(named);
        let presents = |declaration: &'earlier Earlier| match declaration.presentation {
            Maybe::Present(ref presented) if declaration.description.id.name.as_ref() == name => {
                Some((declaration, presented))
            },
            Maybe::Present(_) | Maybe::Absent(_) => None,
        };
        let mut found = visible
            .own
            .iter()
            .rev()
            .find_map(|&declaration| presents(declaration));
        if found.is_none() {
            let mut answered: Option<SourceIndex> = None;
            for &(source, declaration) in visible.imported.iter().rev() {
                let Some(presented) = presents(declaration)
                else {
                    continue;
                };
                match answered {
                    Some(held) if held != source => {
                        return Err(
                            run.signature_fault(SignatureFault::AmbiguousInclude(Name::from(name)))
                        );
                    },
                    Some(_) => {},
                    None => {
                        answered = Some(source);
                        found = Some(presented);
                    },
                }
            }
        }
        let Some((declaration, presented)) = found
        else {
            return Err(run.signature_fault(SignatureFault::UnknownInclude(Name::from(name))));
        };
        let parts = presented
            .value
            .decode()
            .map_err(|_fault| run.fault(DescriptionFault::Malformed))?;
        Ok((declaration, presented, parts, named))
    }

    /// Read a top-level `oper` declaration as the one operation it declares,
    /// in a description of its own: its boundary through the theory route, and
    /// its filler declined as an operation filler is inside a theory block.
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
    /// - witness: `description::theory::tests::a_top_level_operation_declines_its_filler_by_name`
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
        match self.signature_operation(run, &[], OperationKind::Operation) {
            Ok((operation, _tile, _written)) => {
                operations.push(operation_desc(&operation));
                operation_spans.push(at.span);
            },
            Err(diagnostic) => diagnostics.push(diagnostic),
        }
        Ok(DescribedDeclaration {
            at,
            named,
            description: TheoryDesc::new(
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
    /// - ensures: the sort as `Theory` codes it — its index ports in written
    ///   order, each port's sort read as a sort over index terms, and its
    ///   representability, `Type+` representable and `Type` ordinary — beside
    ///   its name tile and where its name, its classifier and each index are
    ///   written.
    /// - fails: an incomplete judgment earns a member-local refusal; a
    ///   classifier other than the two universes is a type-shape refusal.
    /// - panics: none.
    /// - executable: none — the written telescope is source syntax the result
    ///   does not retain beside the sort.
    ///
    /// # Errors
    /// Returns malformed syntax or an unreadable port.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an indexed sort beside a plain one is read whole, two
    ///   unseparated sorts are declined rather than read as one, and a
    ///   representable sort is read apart from an ordinary one.
    /// - witness: `description::theory::tests::a_terminated_block_is_not_told_it_lacks_terminators`
    /// - witness: `description::theory::tests::unseparated_members_are_declined_rather_than_dropped`
    /// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
    /// - witness: `described::tests::a_theory_answers_at_every_member`
    /// - witness: `description::theory::tests::a_rendered_signature_reparses_to_itself`
    fn signature_sort(
        &self,
        run: &mut Run<'_>,
    ) -> Result<(TheorySort, Placed, WrittenSortMember), DescriptionDiagnostic>
    {
        let name = run.take()?;
        let mut indices = Vec::new();
        let mut written = Vec::new();
        if run.eat(Spelling("(")).0 {
            while !run.eat(Spelling(")")).0 {
                let index = run.take()?;
                if !run.eat(Spelling(":")).0 {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
                let sort = run.take()?;
                let (term, at) = self.sort_term(sort)?;
                indices.push(TheoryPort {
                    name: self.text(index).0.into(),
                    sort: term.sort,
                    indices: term.indices,
                    bindings: Vec::new(),
                });
                written.push(WrittenPort {
                    named: Maybe::Present(index.span),
                    binders: Vec::new(),
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
        let representability = match self.text(classifier).0 {
            "Type" => Representability::Ordinary,
            "Type+" => Representability::Representable,
            _ => return Err(run.fault(DescriptionFault::TypeShape)),
        };
        run.end()?;
        Ok((
            TheorySort {
                name: self.text(name).0.into(),
                indices,
                representability,
            },
            name,
            WrittenSortMember {
                named: name.span,
                classifier: classifier.span,
                indices: written,
            },
        ))
    }

    /// Read a shape member: the finite shape the signature's cells are stated
    /// over, its named faces, and each face's name tile.
    ///
    /// # Specification
    /// - ensures: the shape of the written name and size, one face per written
    ///   face in order, each holding the points it lists, and beside it the
    ///   faces' name tiles in the same order; a point past the shape is kept
    ///   for the description check to refuse by name.
    /// - fails: a size or a point that is not a decimal numeral, and a member
    ///   missing its colon, a brace, an equals sign or a separator, is a
    ///   member-local refusal.
    /// - panics: none.
    /// - executable: none — the written member is source syntax the shape does
    ///   not retain.
    ///
    /// # Errors
    /// Returns malformed syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shape with two faces and an empty one reads back
    ///   from its rendering, and a face past its shape is refused by the
    ///   description check rather than by the reader.
    /// - witness: `description::theory::tests::a_rendered_signature_reparses_to_itself`
    /// - witness: `description::theory::tests::a_face_past_its_shape_is_refused_by_name`
    fn signature_shape(
        &self,
        run: &mut Run<'_>,
    ) -> Result<(TheoryShape, Vec<Placed>), DescriptionDiagnostic>
    {
        let name = run.take()?;
        if !run.eat(Spelling(":")).0 {
            return Err(run.signature_fault(SignatureFault::MissingJudgment));
        }
        let size = run.take()?;
        let size: ShapeSize = self.numeral(size, run)?;
        if !run.eat(Spelling("{")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let mut faces = Vec::new();
        let mut tiles = Vec::new();
        while !run.eat(Spelling("}")).0 {
            let face = run.take()?;
            if !run.eat(Spelling("=")).0 || !run.eat(Spelling("{")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
            let mut points: Vec<ShapePoint> = Vec::new();
            while !run.eat(Spelling("}")).0 {
                let point = run.take()?;
                points.push(self.numeral(point, run)?);
                if !run.eat(Spelling(",")).0 && !run.at(Spelling("}")).0 {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
            }
            if !run.eat(Spelling(";")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
            faces.push(ShapeFace::new(self.text(face).0, points));
            tiles.push(face);
        }
        run.end()?;
        Ok((TheoryShape::new(self.text(name).0, size, faces), tiles))
    }

    /// The count a numeral tile writes, as the wrapper `Count` that holds it.
    ///
    /// # Specification
    /// - ensures: the decimal value of the tile's text.
    /// - fails: text that is not a decimal numeral within the machine word is a
    ///   member-local refusal.
    /// - panics: none.
    /// - executable: none — the numeral's text is source syntax the count does
    ///   not retain.
    ///
    /// # Errors
    /// Returns malformed syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::signature_shape`].
    /// - witness: `description::theory::tests::a_rendered_signature_reparses_to_itself`
    fn numeral<Count>(
        &self,
        at: Placed,
        run: &Run<'_>,
    ) -> Result<Count, DescriptionDiagnostic>
    where
        Count: From<usize>,
    {
        let written = self.text(at).0;
        if written.is_empty() || !written.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        written
            .parse::<usize>()
            .map(Count::from)
            .map_err(|_overflow| run.fault(DescriptionFault::Malformed))
    }

    /// Read a boundary-only operation; never discard its filler or a port.
    ///
    /// # Specification
    /// - ensures: admitted operations retain every input and every output, in
    ///   order, as `Theory` codes them — each port's sort read as a sort over
    ///   index terms, an unnamed port at the empty name — beside the
    ///   operation's name tile and where its name and each port are written.
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
    /// - witness: `description::theory::tests::an_oper_filler_stays_declined_and_names_its_own_rung`
    /// - witness: `description::theory::tests::a_data_spelled_theory_oper_declines_before_no_output_can_be_fabricated`
    /// - witness: `description::theory::tests::a_two_output_operation_keeps_both_ports_in_order`
    /// - witness: `description::theory::tests::a_port_name_on_both_sides_is_two_ports`
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `described::tests::a_theory_answers_at_every_member`
    fn signature_operation(
        &self,
        run: &mut Run<'_>,
        sorts: &[TheorySort],
        kind: OperationKind,
    ) -> Result<(TheoryOperation, Placed, WrittenOperation), DescriptionDiagnostic>
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
            &boundary.input_binders,
        )?;
        let (outputs, written_outputs) = self.presented_ports(
            &boundary.outputs,
            &boundary.output_sorts,
            &boundary.output_names,
            &boundary.output_binders,
        )?;
        Ok((
            TheoryOperation {
                name: self.text(name).0.into(),
                kind,
                inputs,
                outputs,
            },
            name,
            WrittenOperation {
                named: Maybe::Present(name.span),
                inputs: written_inputs,
                outputs: written_outputs,
            },
        ))
    }

    /// Each port of one side as `Theory` codes it, its written sort and each of
    /// its binders' domains read as a sort over index terms, and where it is
    /// written.
    ///
    /// # Specification
    /// - ensures: one port per entry of `ports`, in order, under its written
    ///   name or, unnamed, the empty one, with one binder per written binder,
    ///   outermost first, each under its written name over its domain's sort;
    ///   and one written port per port, its name tile from `names` and its
    ///   sort's bytes and index terms.
    /// - fails: a sort or a binder's domain [`Self::sort_term`] cannot read.
    /// - panics: none.
    /// - executable: none — the sorts read are source syntax.
    ///
    /// # Errors
    /// Returns `Malformed` for a sort or a domain that is neither a name nor
    /// an application.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::signature_operation`]; an unnamed port
    ///   leaves the value unchanged wherever it is written; the λ-calculus
    ///   `lam` port and the identity-return `lam` port, whose binder's domain
    ///   is an indexed sort, read back their binder and their sort.
    /// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
    /// - witness: `described::tests::a_theory_answers_at_every_member`
    /// - witness: `description::theory::tests::the_description_is_read_off_the_value`
    /// - witness: `description::theory::tests::a_rendered_signature_reparses_to_itself`
    fn presented_ports(
        &self,
        ports: &[SortRef],
        sorts: &[Placed],
        names: &[Maybe<ByteSpan, port_name::Absent>],
        binders: &[Vec<WrittenBinder>],
    ) -> Result<(Vec<TheoryPort>, Vec<WrittenPort>), DescriptionDiagnostic>
    {
        let mut presented = Vec::with_capacity(ports.len());
        let mut written = Vec::with_capacity(ports.len());
        for (((port, &sort), &named), bound) in ports.iter().zip(sorts).zip(names).zip(binders) {
            let (term, at) = self.sort_term(sort)?;
            let mut bindings = Vec::with_capacity(bound.len());
            let mut binders_at = Vec::with_capacity(bound.len());
            for binder in bound {
                let (domain, domain_at) = self.sort_term(binder.domain)?;
                bindings.push(TheoryBinder {
                    name: self.text(binder.name).0.into(),
                    sort: domain.sort,
                    indices: domain.indices,
                });
                binders_at.push(WrittenBound {
                    named: binder.name.span,
                    sort: domain_at,
                });
            }
            presented.push(TheoryPort {
                name: if port.name.as_ref().starts_with(FRESH_PORT) {
                    Name::from("")
                }
                else {
                    port.name.clone()
                },
                sort: term.sort,
                indices: term.indices,
                bindings,
            });
            written.push(WrittenPort {
                named,
                binders: binders_at,
                sort: at,
            });
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
    /// - witness: `description::theory::tests::a_ruled_theory_block_lowers_its_members_into_a_description`
    /// - witness: `description::theory::tests::a_wiring_that_closes_a_cycle_earns_the_declaration_tables_refusal`
    /// - witness: `description::theory::tests::a_doubling_body_declines_on_the_derivation_node_budget`
    /// - witness: `description::theory::tests::the_cat_shape_laws_are_written_faces`
    /// - witness: `description::theory::tests::a_many_out_frame_binds_every_port_and_roots_the_body`
    /// - witness: `description::theory::tests::a_coherence_between_composites_is_a_higher_cell`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `boundary.rewrites` holds the rewrite ports one rule's boundary writes"
        )
    )]
    fn signature_rule(
        &self,
        run: &mut Run<'_>,
        sorts: &[TheorySort],
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
            let arrow = run.here();
            let orientation = if run.at(Spelling("<=>")).0 {
                RuleOrientation::Unpinned
            }
            else {
                RuleOrientation::Pinned(RuleDirection::LeftToRight)
            };
            run.arrow(Some(ArrowRow::Face))?;
            let rhs = run.take()?;
            run.end()?;
            let (lhs, left) = self.free_term(lhs)?;
            let (rhs, right) = self.free_term(rhs)?;
            return Ok(RuleMember::Face(
                TheoryRule {
                    name: self.text(name).0.into(),
                    left: lhs,
                    right: rhs,
                },
                name,
                run.span,
                WrittenFace {
                    named: Maybe::Present(name.span),
                    left,
                    right,
                    arrow: Maybe::Present(arrow),
                    orientation,
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
        let mut kinds = Vec::new();
        let mut feeds = Vec::new();
        let mut fed = Vec::new();
        while !run.eat(Spelling("}")).0 {
            if run.eat(Spelling("feed")).0 {
                if !run.eat(Spelling(":")).0 {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
                let sources = self.wire_tuple(run)?;
                run.arrow(Some(ArrowRow::Mapping))?;
                let ports = self.wire_tuple(run)?;
                if sources.is_empty() || sources.len() != ports.len() {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
                for (source, port) in sources.into_iter().zip(ports) {
                    feeds.push(CircuitFeed {
                        source: source.name,
                        port: port.name.clone(),
                    });
                    fed.push(port);
                }
                if !run.eat(Spelling(";")).0 {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
                continue;
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
            kinds.push(kind);
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
                        Ok([out]) => out,
                        Err(several) => {
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
                        Some(HeadKind::Constructor) => FrameHead::Ctor(self.text(head).0.into()),
                        Some(HeadKind::Operation | HeadKind::Observation | HeadKind::Rewrite)
                        | None => FrameHead::Op(self.text(head).0.into()),
                    };
                    CircuitNode::Frame(CircuitFrame::binding(head, arguments, outputs))
                };
            nodes.push(node);
            if !run.eat(Spelling(";")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        run.end()?;
        for port in &fed {
            let mut reads = frames.iter().zip(&kinds).flat_map(|(frame, &kind)| {
                frame
                    .arguments
                    .iter()
                    .filter(|wire| wire.name == port.name)
                    .map(move |wire| (wire.span, kind))
            });
            if !reads
                .clone()
                .any(|(_, kind)| matches!(kind, Some(HeadKind::Observation)))
            {
                return Err(DescriptionDiagnostic {
                    span: reads.next().map_or(port.span, |(span, _)| span),
                    fault: DescriptionFault::Signature(SignatureFault::BareFeedback {
                        rule: name.span,
                    }),
                });
            }
        }
        let roots: Vec<Name> = boundary
            .outputs
            .iter()
            .map(|output| output.name.clone())
            .collect();
        let body = CircuitBody::rooted(nodes, roots).with_feeds(feeds);
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
                    binders: Vec::new(),
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
    /// - witness: `description::theory::tests::an_expression_kind_signature_endpoint_is_refused_by_the_description_route`
    /// - witness: `description::theory::tests::node_arrow_resolution_distinguishes_declared_and_unknown_heads`
    fn boundary(
        &self,
        run: &mut Run<'_>,
        sorts: &[TheorySort],
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
                    binders: Vec::new(),
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
            input_binders: inputs.binders,
            output_binders: outputs.binders,
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
    ///   names, each port its written sort, its restricted binders outermost
    ///   first and its name tile, and each rewrite binder where its name and
    ///   sides are written.
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
    ///   face, a parenthesized expression is refused as an endpoint, an
    ///   endpoint written twice is a variable unless a sort carries its name,
    ///   and a port under a binder keeps it.
    /// - witness: `description::theory::tests::a_ruled_theory_block_lowers_its_members_into_a_description`
    /// - witness: `description::theory::tests::an_expression_kind_signature_endpoint_is_refused_by_the_description_route`
    /// - witness: `description::theory::tests::a_pinned_rewrite_endpoint_reads_as_a_variable`
    /// - witness: `description::theory::tests::a_rendered_signature_reparses_to_itself`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `sorts` holds the sorts one signature declares, searched once per written rule"
        )
    )]
    fn port_side(
        &self,
        run: &mut Run<'_>,
        sorts: &[TheorySort],
        rewrites: &mut Vec<RewritePort>,
        written_rewrites: &mut Vec<WrittenRewrite>,
    ) -> Result<Side, DescriptionDiagnostic>
    {
        let grouped = run.eat(Spelling("(")).0;
        let mut side = Side {
            ports: Vec::new(),
            sorts: Vec::new(),
            binders: Vec::new(),
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
                let (name, sort, named, binders) = if run.eat(Spelling(":")).0 {
                    let binders = run.binders()?;
                    (
                        self.port_name(first),
                        run.take()?,
                        Maybe::Present(first.span),
                        binders,
                    )
                }
                else {
                    (
                        fresh_port(first),
                        first,
                        Maybe::Absent(port_name::Absent::Unnamed),
                        Vec::new(),
                    )
                };
                side.ports.push(SortRef::new(name, self.text(sort).0));
                side.sorts.push(sort);
                side.binders.push(binders);
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
    /// - witness: `description::theory::tests::a_ruled_theory_block_lowers_its_members_into_a_description`
    /// - witness: `description::theory::tests::a_repeated_argument_name_reaches_the_linearity_refusal`
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
    /// Read the restricted binders a port's sort is written under, `pi+ (x :
    /// S) .` each, outermost first.
    ///
    /// # Specification
    /// - ensures: one binder per `pi+` the run continues with, in order, each
    ///   its name tile and its written domain; a run that continues with none
    ///   reads none and is left where it was.
    /// - fails: a binder short of its opening parenthesis, name, colon, domain,
    ///   closing parenthesis or dot is malformed.
    /// - panics: none.
    /// - executable: none — the binders read are source syntax.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the λ-calculus `lam` port and the identity-return
    ///   `lam` port read back their one binder, and a port with none reads
    ///   none.
    /// - witness: `description::theory::tests::a_rendered_signature_reparses_to_itself`
    fn binders(&mut self) -> Result<Vec<WrittenBinder>, DescriptionDiagnostic>
    {
        let mut binders = Vec::new();
        while self.eat(Spelling("pi+")).0 {
            if !self.eat(Spelling("(")).0 {
                return Err(self.fault(DescriptionFault::Malformed));
            }
            let name = self.take()?;
            if !self.eat(Spelling(":")).0 {
                return Err(self.fault(DescriptionFault::Malformed));
            }
            let domain = self.take()?;
            if !self.eat(Spelling(")")).0 || !self.eat(Spelling(".")).0 {
                return Err(self.fault(DescriptionFault::Malformed));
            }
            binders.push(WrittenBinder { name, domain });
        }
        Ok(binders)
    }

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
    /// - ensures: mismatches and the reserved reversible map `<->` retain their
    ///   own span. `<=>` is a face arrow, the equation.
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
    ///   head under any arrow and a reversible map are refused apart; an
    ///   equation is a face arrow.
    /// - witness: `description::theory::tests::node_arrow_resolution_distinguishes_declared_and_unknown_heads`
    /// - witness: `description::theory::tests::a_reversible_map_is_reserved_and_an_equation_is_a_face`
    fn arrow(
        &mut self,
        expected: Option<ArrowRow>,
    ) -> Result<ArrowRow, DescriptionDiagnostic>
    {
        let at = self.cursor.here();
        let actual = if self.eat(Spelling("<->")).0 {
            return Err(DescriptionDiagnostic {
                span: at,
                fault: DescriptionFault::Signature(SignatureFault::Reversible),
            });
        }
        else if self.eat(Spelling("-->")).0 {
            ArrowRow::Mapping
        }
        else if self.eat(Spelling("==>")).0 || self.eat(Spelling("<=>")).0 {
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
        (Some(first), Some(last)) => {
            ByteSpan::new(first.placed().span.start(), last.placed().span.end()).unwrap_or(fallback)
        },
        _ => fallback,
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

/// The prefix of the private name the reader mints for an anonymous port,
/// which a written name cannot begin with.
const FRESH_PORT: &str = "$port:";

/// An anonymous port's collision-free, source-stable internal name.
///
/// # Specification
/// trivial.
fn fresh_port(at: Placed) -> Name
{
    format!("{FRESH_PORT}{}", usize::from(at.span.start())).into()
}

/// The description a presentation's value reads as, under `id`: the
/// declaration table the cell gate, the rules check and coincidence read.
///
/// # Specification
/// - ensures: the shape parameter the value codes, when it codes one; one data
///   sort per sort the value codes, its index telescope each index port's name
///   over its sort's spelling, representable when the value codes it so; one
///   operation per operation, its arity the ports in order, an unnamed one at
///   its placeholder, each port under its binders, each binder's domain its
///   sort's name over its index terms; one face per rule, its variables derived
///   from its left side and its provenance the whole member the placement
///   records; no parameter, constructor or circuit.
/// - fails: as [`Presentation::members`]: a value that codes no presentation,
///   or a rule no member places.
/// - panics: none.
/// - executable: none — the table is a reading of the value; a predicate would
///   decode the value a second time.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — a block's description agrees with the value it defines,
///   member for member, an unnamed port at its placeholder and a face at its
///   member's span; a rule the placement does not place is refused; a rendered
///   second-order signature's representable sorts and binders read back, and a
///   rendered shaped signature's shape and faces.
/// - witness: `description::theory::tests::the_description_is_read_off_the_value`
/// - witness: `description::theory::tests::the_cat_shape_laws_are_written_faces`
/// - witness: `description::theory::tests::a_rendered_signature_reparses_to_itself`
fn described(
    presentation: &Presentation,
    id: NominalId,
) -> Result<TheoryDesc<DescriptionGrade>, PresentationFault>
{
    let parts = presentation
        .value
        .decode()
        .map_err(PresentationFault::Value)?;
    if parts.rules.len() > presentation.placement.faces.len() {
        return Err(PresentationFault::Unplaced);
    }
    let sorts: Vec<SortDesc> = parts
        .sorts
        .iter()
        .map(|sort| {
            let family = SortDesc::family(
                sort.name.clone(),
                DeclPolarity::Data,
                sort.indices
                    .iter()
                    .map(|index| SortIndex::new(index.name.clone(), spelled(index)))
                    .collect::<Vec<_>>(),
            );
            match sort.representability {
                Representability::Ordinary => family,
                Representability::Representable => family.representable(),
            }
        })
        .collect();
    let operations: Vec<OperDesc> = parts.operations.iter().map(operation_desc).collect();
    let faces: Vec<RuleFace> = parts
        .rules
        .into_iter()
        .zip(&presentation.placement.faces)
        .map(|(rule, &span)| {
            let variables = derive_cell_var_meta(&rule.left);
            RuleFace::new(rule.left, rule.right, variables, surface_span(span))
        })
        .collect();
    let description = TheoryDesc::new(
        id,
        [],
        [],
        operations,
        faces,
        DeclPolarity::Data,
        Attrs::empty(),
    );
    let description = if sorts.is_empty() {
        description
    }
    else {
        description.with_sorts(sorts)
    };
    Ok(match parts.shape {
        Maybe::Present(shape) => description.with_shape(shape),
        Maybe::Absent(shape_parameter::Absent::Unshaped) => description,
    })
}

/// The operation `operation` codes, its arity its ports in order, an unnamed
/// one at its placeholder, each under its binders.
///
/// # Specification
/// trivial.
fn operation_desc(operation: &TheoryOperation) -> OperDesc
{
    let mut names = presented_names(&operation.inputs, &operation.outputs).into_iter();
    let inputs: Vec<SortRef> = operation
        .inputs
        .iter()
        .zip(names.by_ref())
        .map(|(port, name)| port_ref(port, name))
        .collect();
    let outputs: Vec<SortRef> = operation
        .outputs
        .iter()
        .zip(names)
        .map(|(port, name)| port_ref(port, name))
        .collect();
    let arity = BridgeArity::tupled(inputs, outputs);
    OperDesc::new(operation.name.clone(), arity, Attrs::empty())
}

/// The port `port` codes, under `name`: its sort spelled, and each binder as
/// its name over its domain, the domain's sort name applied to its index
/// terms, which is how `check_desc` resolves a binder's representability.
///
/// # Specification
/// trivial.
fn port_ref(
    port: &TheoryPort,
    name: Name,
) -> SortRef
{
    let reference = SortRef::new(name, spelled(port));
    if port.bindings.is_empty() {
        return reference;
    }
    reference.pi_plus(
        port.bindings
            .iter()
            .map(|binder| {
                SortIndex::new(binder.name.clone(), binder.sort.clone())
                    .applied(binder.indices.clone())
            })
            .collect::<Vec<_>>(),
    )
}

/// A port's sort as the description spells it: its name, applied to its
/// index terms when it has any.
///
/// # Specification
/// trivial.
fn spelled(port: &TheoryPort) -> Name
{
    Name::from(FreeTerm::op(port.sort.clone(), port.indices.iter().cloned()).to_string())
}

mod extension;

#[cfg(test)]
mod tests;
