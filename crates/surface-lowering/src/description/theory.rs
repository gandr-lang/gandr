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
//! under one. `Model(S)` states such an operation's port as the thunked
//! function from its variables, `+U ((x : S) -> -F T)`, and refuses a law
//! relating a term at the port by name.
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
//! # Atom sorts
//!
//! A sort member classified `Atom` is an atom sort: orbit-infinite, with
//! equality and swapping its only structure (Pitts, _Nominal Sets_, CUP 2013).
//! The reader codes it at `Atom` in the value. An operation's port may sit at
//! it; an output at it is the description check's `AtomResult`, and a `pi+`
//! binder over it its `NonRepresentableBinder`.
//!
//! An operation's port abstracts atoms of it under `bind`, `p : bind (a :
//! Name) . Proc`: swapping renames the atom, and it may escape, where `pi+`
//! binds a variable that substitution instantiates. The abstractions stand
//! outside the port's `pi+` binders, so a `bind` after a `pi+` is malformed;
//! the reader codes such a port at `Abstracted`, and an abstraction over a
//! sort that is not an atom sort is the description check's
//! `NonAtomAbstraction`. Witnesses:
//! `description::theory::tests::a_rendered_signature_reparses_to_itself`,
//! `description::theory::tests::a_binder_over_an_ordinary_sort_is_refused_by_name`,
//! `description::theory::tests::an_abstraction_stands_outside_the_binders`.
//!
//! A rule between terms may close on a `where` clause of freshness
//! conditions, `rule scope : par(nu(bind a . p), q) <=> nu(bind a . par(p,
//! q)) where a # q;`: the atom `a` stands outside the support of the term `q`
//! stands for (Fernández and Gabbay, _Nominal rewriting_, I&C 2007). The
//! reader keeps each condition on its rule, in written order, and the value
//! codes it in a `Fresh` member after the rule; a condition naming an atom no
//! abstraction of the rule names or a variable its left side does not bind,
//! and a rule whose variable moves into or out of an abstraction with no
//! condition naming that atom fresh for it, are the description check's
//! `UnknownFreshness` and `Capture`. Witnesses:
//! `description::theory::tests::a_where_clause_states_each_condition_on_its_rule`,
//! `wellformed::tests::a_metavariable_crossing_an_abstraction_names_its_atom_fresh`.
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
//! description is `TheoryValue::description` of it at the faces' spans,
//! `Model(S)` derives from it, and the core definition `S : Theory` is it, node
//! for node. Beside the value the reader
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
//! before the block state every one of them,
//! `@[ refuses("UndescribedMember.NestedOperation") ] theory …`, and a block
//! whose members refuse two features is two sources. A top-level `oper`
//! declares no core constant: each refusal raised
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

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::CircuitBody;
use gandr_theory_levitation::CircuitFeed;
use gandr_theory_levitation::CircuitFrame;
use gandr_theory_levitation::CircuitNode;
use gandr_theory_levitation::CircuitRule;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::DiagnosticMessage;
use gandr_theory_levitation::FrameHead;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Freshness;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::OperationKind;
use gandr_theory_levitation::Representability;
use gandr_theory_levitation::RewritePort;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::ShapeFace;
use gandr_theory_levitation::ShapePoint;
use gandr_theory_levitation::ShapeSize;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::SurfaceSpan;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TheoryBinder;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::TheoryOperation;
use gandr_theory_levitation::TheoryParts;
use gandr_theory_levitation::TheoryPort;
use gandr_theory_levitation::TheoryRule;
use gandr_theory_levitation::TheoryShape;
use gandr_theory_levitation::TheorySort;
use gandr_theory_levitation::TheoryValue;
use gandr_theory_levitation::WfDiagnostic;
use gandr_theory_levitation::WfKind;
use gandr_theory_levitation::derive_boundaries;
use gandr_theory_levitation::derive_cell_var_meta;
use quenchant_shape::shape::Maybe;

use super::DescribedDeclaration;
use super::DescriptionDiagnostic;
use super::DescriptionFault;
use super::MemberEnd;
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
use super::written::WrittenLaw;
use super::written::WrittenMembers;
use super::written::WrittenNode;
use super::written::WrittenOperation;
use super::written::WrittenPath;
use super::written::WrittenPort;
use super::written::WrittenRewrite;
use super::written::WrittenSort;
use super::written::WrittenSortMember;
use super::written::WrittenTerm;
use super::written::WrittenWire;
use super::written::head;
use super::written::port_name;
use crate::SurfaceName;
use crate::circuit::ArrowRow;
use crate::circuit::OutputCount;
use crate::circuit::SignatureFault;
use crate::description::DescribedDeclaration as Earlier;
use crate::description::Visible;
use crate::form::Piece;
use crate::form::Placed;
use crate::model::Binder;
use crate::model::Hypothesis;
use crate::model::Included;
use crate::model::Placement;
use crate::model::Presentation;
use crate::model::PresentedCircuit;
use crate::model::SortTerm;
use crate::model::StatedLaw;
use crate::model::presentation;
use crate::resolve::type_atom;
use crate::unit::SourceIndex;

quenchant_shape::reason_enum! {
    /// Why a type a law writes states no path.
    pub mod stated_path {
        /// The reason no path is read.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The type is of another former than `Path`.
            OtherFormer,
        }
    }
}

/// A path a law writes, `Path(C, l, r)`, as read: its carrier, its two
/// sides, and where each is written.
///
/// # Specification
/// trivial.
struct LawPath
{
    /// The carrier.
    carrier: SortTerm,
    /// The side the path starts at.
    left: FreeTerm,
    /// The side it ends at.
    right: FreeTerm,
    /// Where the path and its parts are written.
    written: WrittenPath,
}

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

/// A binder as a port writes it: a restricted binder, `pi+ (name : domain)
/// .`, or an atom abstraction, `bind (name : domain) .`.
#[derive(Clone, Copy)]
struct WrittenBinder
{
    /// The bound variable's name tile.
    name: Placed,
    /// The bound variable's written sort.
    domain: Placed,
    /// Whether the binder is an atom abstraction, `bind`.
    abstracts: bool,
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
    /// operations and laws after the written ones; each `law` member is kept
    /// beside the value, which the rule decision reads.
    ///
    /// # Specification
    /// - ensures: an unreadable member does not consume a following member;
    ///   every member read enters the presentation's value, its circuits beside
    ///   it, and the description is the value's [`TheoryValue::description`] at
    ///   its faces' spans, with the circuits added. The included presentations
    ///   come first, in written order, each by [`TheoryParts::include`], with
    ///   the inclusion kept beside the value and each included member's
    ///   provenance its own block's. An `ext` member's generated operations and
    ///   laws follow the written ones, each placed at the member's keyword. The
    ///   stated laws are the included presentations' then the block's own, in
    ///   written order.
    /// - fails: a malformed signature head refuses the whole declaration; an
    ///   `include` that names no visible block, names two, or whose members
    ///   clash with the presentation's, an `ext` member the block cannot
    ///   generate, and a `law` member [`Self::signature_law`] refuses or named
    ///   as another member is, is that member's own diagnostic; so is each
    ///   operation's port at a sort nothing declares ([`undeclared_ports`]),
    ///   unless an `include` was not read, whose refusal stands for the sorts
    ///   it would bring.
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
    /// - witness: `description::theory::tests::a_port_at_a_sort_nothing_declares_is_refused_2410`
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
        let members = split_members(run.remaining(), MemberEnd::Semicolon);
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
        let mut laws: Vec<StatedLaw> = Vec::new();
        // Each stated law's name, at its place among `laws`.
        let mut stated: BTreeMap<Name, usize> = BTreeMap::new();
        // An include not read leaves the sorts it would bring unknown: its own
        // refusal stands for them, and no port is refused at one (#2410).
        let mut unread_include = false;
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
                        unread_include = true;
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
                    unread_include = true;
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
            // A law two includes reach through one theory is held once; a
            // different law under a held name clashes.
            for (law, sides) in presented.laws.iter().zip(&declaration.written.laws) {
                match stated.get(&law.name).and_then(|&at| laws.get(at)) {
                    Some(held) if held == law => {},
                    Some(_) => diagnostics.push(DescriptionDiagnostic {
                        span: include_tile.span,
                        fault: DescriptionFault::Signature(SignatureFault::LawName(
                            law.name.clone(),
                        )),
                    }),
                    None => {
                        let _first = stated.insert(law.name.clone(), laws.len());
                        laws.push(law.clone());
                        written.laws.push(sides.clone());
                    },
                }
            }
            inclusions.push(Included {
                theory: declaration.description.id.clone(),
                inclusion,
                named: include_tile,
                block: declaration.at,
            });
        }
        let direct: Vec<&NominalId> = inclusions.iter().map(|included| &included.theory).collect();
        if let Some(fault) = super::joins::ambiguous_join(
            &NominalId::new(serial, self.text(named).0),
            &direct,
            visible,
        ) {
            diagnostics.push(run.signature_fault(SignatureFault::AmbiguousJoin(fault)));
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
                        if !unread_include {
                            diagnostics.extend(undeclared_ports(&operation, &ports, &parts.sorts));
                        }
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
            else if reading.eat(Spelling("law")).0 {
                self.signature_law(&mut reading).and_then(|(law, sides)| {
                    let spelled = Name::from(self.text(law.named).0);
                    if scope.contains_key(&self.text(law.named)) || stated.contains_key(&spelled) {
                        return Err(DescriptionDiagnostic {
                            span: law.named.span,
                            fault: DescriptionFault::Signature(SignatureFault::LawName(spelled)),
                        });
                    }
                    let _first = stated.insert(spelled, laws.len());
                    laws.push(law);
                    written.laws.push(sides);
                    Ok(())
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
        // An abstraction a rule writes at a `pi+` port is the binding field
        // that port binds, read against every operation the parts hold.
        parts.bind_fields();
        let presentation = Presentation {
            value: TheoryValue::encode(&parts),
            placement,
            circuits: presented_circuits,
            inclusions,
            laws,
        };
        let faces: Vec<SurfaceSpan> = presentation
            .placement
            .faces
            .iter()
            .map(|&span| surface_span(span))
            .collect();
        let description = presentation
            .value
            .description(NominalId::new(serial, self.text(named).0), &faces)
            .map_err(|_unread| DescriptionDiagnostic {
                span: at.span,
                fault: DescriptionFault::Malformed,
            })?;
        Ok(DescribedDeclaration {
            at,
            named,
            description: description.with_circuits(circuits),
            ill_formed: false,
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
                operations.push(operation.description());
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
            ill_formed: false,
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
    ///   representability, `Type+` representable, `Atom` an atom sort and
    ///   `Type` ordinary — beside its name tile and where its name, its
    ///   classifier and each index are written.
    /// - fails: an incomplete judgment earns a member-local refusal; a
    ///   classifier other than the two universes and `Atom` is a type-shape
    ///   refusal.
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
                    abstractions: Vec::new(),
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
            "Atom" => Representability::Atom,
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
    ///   operation's name tile and where its name and each port are written; an
    ///   `oper` written as a type alone, with no port group and no arrow, is a
    ///   constant of that type; and one written at a model type, `Model(T)`, a
    ///   nested model of the theory `T`, its one unnamed output port at `T`.
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
    /// - witness: `description::theory::tests::a_rule_bearing_theory_defines_its_presentation_with_its_laws`
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
        // `oper next : +U[ω] (T -> -F T)`, a thunk of curried arrows, is the
        // operation of those inputs and that output, as is the value-function
        // alias standing for it, `oper next : T => T`; `oper inner : Model(T)`
        // a model of the theory `T` nested in this one; `oper zero : T`, a type
        // alone with no arrow and no port group, a constant of `T`; and `oper
        // zero : () --> T` an operation of no inputs. A listed domain opens
        // the judgment's own port group, so the operation of two inputs the
        // alias `(T, T) => T` stands for is written `(T, T) --> T` here.
        let thunked = self.thunked(run)?;
        let modeled = match kind {
            OperationKind::Operation if thunked.is_none() => self.modeled(run)?,
            OperationKind::Operation
            | OperationKind::Observation
            | OperationKind::Constant
            | OperationKind::Nested => None,
        };
        let kind = match kind {
            OperationKind::Operation if modeled.is_some() => OperationKind::Nested,
            OperationKind::Operation
                if thunked.is_none() && !run.at(Spelling("(")).0 && !run.has_arrow().0 =>
            {
                OperationKind::Constant
            },
            OperationKind::Operation
            | OperationKind::Observation
            | OperationKind::Constant
            | OperationKind::Nested => kind,
        };
        let (boundary, formers) = match (thunked, modeled) {
            (Some(thunk), _) => {
                let _thunk = run.take()?;
                self.thunk_boundary(thunk)?
            },
            (None, Some(theory)) => {
                let model = run.take()?;
                (self.model_boundary(theory), vec![(
                    model.span,
                    GroundSort::Value,
                )])
            },
            (None, None) => (self.boundary(run, sorts, ArrowRow::Mapping)?, Vec::new()),
        };
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
                formers,
            },
        ))
    }

    /// The thunk type an operation's judgment writes whole, when it writes one,
    /// as a thunk or as the value-function alias that stands for one.
    ///
    /// # Specification
    /// - ensures: the one piece left in `run` when it is a type whose first
    ///   tile is `+U`, or whose own tile is `=>`, and nothing otherwise; `run`
    ///   is not advanced.
    /// - fails: the piece's reading refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The piece's reading refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk, an alias, a sort alone and a port group
    ///   separate the operation, the constant and the boundary readings.
    /// - witness: `description::theory::tests::a_thunk_type_reads_as_the_operation_it_curries_1226`
    /// - witness: `description::theory::tests::the_value_function_alias_reads_as_its_thunk_1329`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.is_none_or(|at| matches!(*run.remaining(), [Piece::Operand(only)] if only.span == at.span))))]
    fn thunked(
        &self,
        run: &Run<'_>,
    ) -> Result<Option<Placed>, DescriptionDiagnostic>
    {
        let [Piece::Operand(at)] = *run.remaining()
        else {
            return Ok(None);
        };
        let pieces = self.pieces(at)?;
        let thunk = match *pieces.as_slice() {
            [
                Piece::Operand(_),
                Piece::Tile { ref label, .. },
                Piece::Operand(_),
            ] => label.as_ref() == "=>",
            [Piece::Tile { ref label, .. }, ..] => label.as_ref() == "+U",
            _ => false,
        };
        Ok(thunk.then_some(at))
    }

    /// The theory a model type, `Model(T)`, written as the whole of an
    /// operation's judgment names, when it writes one.
    ///
    /// # Specification
    /// - ensures: the name `T` when the one piece left in `run` reads `Model`,
    ///   `(`, one name and `)`, and nothing otherwise; `run` is not advanced.
    /// - fails: the piece's reading refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The piece's reading refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a model type, a sort over an index and a sort alone
    ///   separate the nested model from the constant readings.
    /// - witness: `description::theory::tests::a_model_type_reads_as_a_nested_model_1226`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.is_none_or(|_| matches!(*run.remaining(), [Piece::Operand(_)]))))]
    fn modeled(
        &self,
        run: &Run<'_>,
    ) -> Result<Option<Placed>, DescriptionDiagnostic>
    {
        let [Piece::Operand(at)] = *run.remaining()
        else {
            return Ok(None);
        };
        let pieces = self.pieces(at)?;
        let [
            Piece::Tile { at: former, .. },
            Piece::Tile {
                label: ref open, ..
            },
            Piece::Operand(theory) | Piece::Tile { at: theory, .. },
            Piece::Tile {
                label: ref close, ..
            },
        ] = *pieces.as_slice()
        else {
            return Ok(None);
        };
        let named = self.text(former).0 == "Model"
            && open.as_ref() == "("
            && close.as_ref() == ")"
            && self.pieces(theory)?.len() <= 1;
        Ok(named.then_some(theory))
    }

    /// The boundary of a nested model of the theory `theory` names: no inputs
    /// and one unnamed output at `theory`.
    ///
    /// # Specification
    /// - requires: `theory` is the name a model type `Model(T)` applies.
    /// - ensures: no input port and one unnamed output port whose sort is the
    ///   name, written at `theory`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::modeled`].
    /// - witness: `description::theory::tests::a_model_type_reads_as_a_nested_model_1226`
    #[spec(ensures: |ret| ret.inputs.is_empty() && ret.outputs.len() == 1 && ret.output_sorts == [theory])]
    fn model_boundary(
        &self,
        theory: Placed,
    ) -> Boundary
    {
        Boundary {
            inputs: Vec::new(),
            outputs: vec![SortRef::new(fresh_port(theory), self.text(theory).0)],
            input_names: Vec::new(),
            output_names: vec![Maybe::Absent(port_name::Absent::Unnamed)],
            input_binders: Vec::new(),
            output_binders: vec![Vec::new()],
            input_sorts: Vec::new(),
            output_sorts: vec![theory],
            rewrites: Vec::new(),
            written_rewrites: Vec::new(),
        }
    }

    /// Read a thunk of curried arrows, `+U[ω] (A1 -> … -> An -> -F R)`, or the
    /// value-function alias `A => R` over one bare domain, as the boundary
    /// `(_ : A1, …, _ : An) --> R`, beside the type formers written: the
    /// thunk, each arrow and the returner, or the alias alone.
    ///
    /// # Specification
    /// - requires: `thunk` is a type whose first tile is `+U`, or the alias.
    /// - ensures: one unnamed input per arrow's domain, in written order, and
    ///   the one output the returner returns, each at its written sort;
    ///   parentheses around the body or a codomain are read through; the grade
    ///   is `ω` or unwritten; the formers are the thunk's node at the value
    ///   sort, then each arrow's and the returner's at the computation sort.
    ///   The alias reads as its thunk `+U (A -> -F R)`: its domain the one
    ///   unnamed input, its result the one output, its node the one former, at
    ///   the value sort.
    /// - fails: any other grade, and a body that is not arrows ending in a
    ///   returner, are malformed.
    /// - panics: none.
    /// - executable: none — the written type is source syntax the boundary does
    ///   not retain.
    ///
    /// # Errors
    /// Returns `Malformed` at the part out of shape.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one and two arrows, a builtin result and a grade
    ///   other than `ω` separate the inputs read, the output read and the
    ///   refusal; the alias and its thunk read as the same operation.
    /// - witness: `description::theory::tests::a_thunk_type_reads_as_the_operation_it_curries_1226`
    /// - witness: `description::theory::tests::the_value_function_alias_reads_as_its_thunk_1329`
    fn thunk_boundary(
        &self,
        thunk: Placed,
    ) -> Result<(Boundary, Vec<(ByteSpan, GroundSort)>), DescriptionDiagnostic>
    {
        let pieces = self.pieces(thunk)?;
        if let [
            Piece::Operand(domain),
            Piece::Tile { ref label, .. },
            Piece::Operand(result),
        ] = *pieces.as_slice()
            && label.as_ref() == "=>"
        {
            return Ok((
                Self::curried(&[domain], result, |sort| self.text(sort).0),
                Vec::from([(thunk.span, GroundSort::Value)]),
            ));
        }
        let mut run = Run::new(&pieces, thunk.span);
        let _former = run.eat(Spelling("+U"));
        if run.eat(Spelling("[")).0 && !(run.eat(Spelling("ω")).0 && run.eat(Spelling("]")).0) {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let mut body = run.take()?;
        run.end()?;
        let mut formers = Vec::from([(thunk.span, GroundSort::Value)]);
        let mut inputs = Vec::new();
        let result = loop {
            let pieces = self.pieces(body)?;
            let mut run = Run::new(&pieces, body.span);
            if run.eat(Spelling("(")).0 {
                body = run.take()?;
                if !run.eat(Spelling(")")).0 {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
                run.end()?;
                continue;
            }
            if run.eat(Spelling("-F")).0 {
                let result = run.take()?;
                run.end()?;
                formers.push((body.span, GroundSort::Computation));
                break result;
            }
            let domain = run.take()?;
            if !run.eat(Spelling("->")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
            formers.push((body.span, GroundSort::Computation));
            body = run.take()?;
            run.end()?;
            inputs.push(domain);
        };
        Ok((
            Self::curried(&inputs, result, |sort| self.text(sort).0),
            formers,
        ))
    }

    /// The boundary of an operation whose unnamed inputs are at the sorts
    /// `inputs` and whose one unnamed output is at the sort `result`, each
    /// spelled by `text`.
    ///
    /// # Specification
    /// trivial.
    fn curried<'text>(
        inputs: &[Placed],
        result: Placed,
        text: impl Fn(Placed) -> &'text str,
    ) -> Boundary
    {
        let port = |sort: Placed| SortRef::new(fresh_port(sort), text(sort));
        let unnamed = |_| Maybe::Absent(port_name::Absent::Unnamed);
        Boundary {
            inputs: inputs.iter().copied().map(port).collect(),
            outputs: vec![port(result)],
            input_names: inputs.iter().map(unnamed).collect(),
            output_names: vec![Maybe::Absent(port_name::Absent::Unnamed)],
            input_binders: inputs.iter().map(|_| Vec::new()).collect(),
            output_binders: vec![Vec::new()],
            input_sorts: inputs.to_vec(),
            output_sorts: vec![result],
            rewrites: Vec::new(),
            written_rewrites: Vec::new(),
        }
    }

    /// Each port of one side as `Theory` codes it, its written sort and each of
    /// its binders' and abstractions' domains read as a sort over index terms,
    /// and where it is written.
    ///
    /// # Specification
    /// - ensures: one port per entry of `ports`, in order, under its written
    ///   name or, unnamed, the empty one, with one abstraction per written
    ///   `bind` and one binder per written `pi+`, each list outermost first,
    ///   each entry under its written name over its domain's sort; and one
    ///   written port per port, its name tile from `names`, its abstractions
    ///   then its binders where they are written, and its sort's bytes and
    ///   index terms.
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
    ///   is an indexed sort, read back their binder and their sort, and a
    ///   restriction's `nu` port its abstraction.
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
            let mut abstractions = Vec::new();
            let mut binders_at = Vec::with_capacity(bound.len());
            for binder in bound {
                let (domain, domain_at) = self.sort_term(binder.domain)?;
                let into = if binder.abstracts {
                    &mut abstractions
                }
                else {
                    &mut bindings
                };
                into.push(TheoryBinder {
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
                abstractions,
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
            let (index, nodes) = self.free_term(run.take()?, &BTreeSet::new())?;
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

    /// Read a law member, `law name : (binders) => Path(C, l, r)`: the
    /// equation a model proves at the path type its statement writes, and
    /// where each of its parts is written.
    ///
    /// # Specification
    /// - requires: `run` stands just past the member's `law` keyword.
    /// - ensures: the law's name and tile, its sort binders in written order,
    ///   then its path hypotheses, and the path its statement ends in; each
    ///   sort read as [`Self::sort_term`] reads one, each side as
    ///   [`Self::law_side`] reads one; beside it, the bytes of its name, its
    ///   statement, each binder, each hypothesis and each node of every side.
    /// - fails: [`SignatureFault::LawStatement`] for a statement that is not a
    ///   value function type from named binders to a path, or a sort binder
    ///   after a hypothesis; a malformed sort or side as its reader refuses it.
    /// - panics: none.
    /// - executable: none — the law read is source syntax.
    ///
    /// # Errors
    /// Returns the located diagnostic of the first failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `refl`, `sym` and `trans` read their binders,
    ///   hypotheses and paths, and a statement that is no path is refused at
    ///   its member.
    /// - witness: `description::theory::tests::a_law_member_reads_its_statement_2356`
    fn signature_law(
        &self,
        run: &mut Run<'_>,
    ) -> Result<(StatedLaw, WrittenLaw), DescriptionDiagnostic>
    {
        let named = run.take()?;
        if !run.eat(Spelling(":")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let statement = run.take()?;
        run.end()?;
        let refused = |at: Placed| DescriptionDiagnostic {
            span: at.span,
            fault: DescriptionFault::Signature(SignatureFault::LawStatement),
        };
        let pieces = self.pieces(statement)?;
        let mut arrow = Run::new(&pieces, statement.span);
        let domain = arrow.take()?;
        if !arrow.eat(Spelling("=>")).0 {
            return Err(refused(statement));
        }
        let concluded = arrow.take()?;
        arrow.end()?;
        let entries = self.pieces(domain)?;
        let mut entry = Run::new(&entries, domain.span);
        if !entry.eat(Spelling("(")).0 {
            return Err(refused(domain));
        }
        let mut binders = Vec::new();
        let mut hypotheses = Vec::new();
        let mut written_binders = Vec::new();
        let mut written_hypotheses = Vec::new();
        while !entry.eat(Spelling(")")).0 {
            let key = entry.take()?;
            if !entry.eat(Spelling(":")).0 {
                return Err(refused(key));
            }
            let typed = entry.take()?;
            let name = Name::from(self.text(key).0);
            match self.law_path(typed)? {
                Maybe::Present(path) => {
                    hypotheses.push(Hypothesis {
                        name,
                        carrier: path.carrier,
                        left: path.left,
                        right: path.right,
                    });
                    written_hypotheses.push((key.span, path.written));
                },
                Maybe::Absent(_) if hypotheses.is_empty() => {
                    let (sort, written) = self.sort_term(typed)?;
                    binders.push(Binder {
                        name,
                        over: Vec::new(),
                        sort,
                    });
                    written_binders.push(WrittenPort {
                        named: Maybe::Present(key.span),
                        binders: Vec::new(),
                        sort: written,
                    });
                },
                Maybe::Absent(_) => return Err(refused(typed)),
            }
            if !entry.eat(Spelling(",")).0 && !entry.at(Spelling(")")).0 {
                return Err(entry.fault(DescriptionFault::Malformed));
            }
        }
        entry.end()?;
        let Maybe::Present(path) = self.law_path(concluded)?
        else {
            return Err(refused(concluded));
        };
        Ok((
            StatedLaw {
                name: Name::from(self.text(named).0),
                named,
                binders,
                hypotheses,
                carrier: path.carrier,
                left: path.left,
                right: path.right,
            },
            WrittenLaw {
                named: named.span,
                statement: statement.span,
                binders: written_binders,
                hypotheses: written_hypotheses,
                path: path.written,
            },
        ))
    }

    /// The path a law's type writes, `Path(C, l, r)`: its carrier and its two
    /// sides, and where each is written; none for a type of another former.
    ///
    /// # Specification
    /// - ensures: for an application headed `Path` of three arguments, the
    ///   first read as [`Self::sort_term`] reads a sort and the others as
    ///   [`Self::law_side`] reads a side, with the bytes of the whole type;
    ///   [`Maybe::Absent`] for any other type.
    /// - fails: a malformed carrier or side as its reader refuses it.
    /// - panics: none.
    /// - executable: none — the path read is source syntax.
    ///
    /// # Errors
    /// Returns the located diagnostic of the first failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::signature_law`].
    /// - witness: `description::theory::tests::a_law_member_reads_its_statement_2356`
    fn law_path(
        &self,
        at: Placed,
    ) -> Result<Maybe<LawPath, stated_path::Absent>, DescriptionDiagnostic>
    {
        let unpathed = Maybe::Absent(stated_path::Absent::OtherFormer);
        let pieces = self.pieces(at)?;
        if let [Piece::Tile { .. }] = *pieces.as_slice() {
            return Ok(unpathed);
        }
        let mut run = Run::new(&pieces, at.span);
        let head = run.take()?;
        if self.text(head).0 != "Path" || !run.eat(Spelling("(")).0 {
            return Ok(unpathed);
        }
        let mut arguments = Vec::with_capacity(3);
        while !run.eat(Spelling(")")).0 {
            arguments.push(run.take()?);
            if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        run.end()?;
        let [carrier, left, right] =
            <[Placed; 3]>::try_from(arguments).map_err(|_count| DescriptionDiagnostic {
                span: at.span,
                fault: DescriptionFault::Signature(SignatureFault::LawStatement),
            })?;
        let (carrier, carried) = self.sort_term(carrier)?;
        let (left, from) = self.law_side(left)?;
        let (right, to) = self.law_side(right)?;
        Ok(Maybe::Present(LawPath {
            carrier,
            left,
            right,
            written: WrittenPath {
                span: at.span,
                carrier: carried,
                left: from,
                right: to,
            },
        }))
    }

    /// One side of a law's path: a `Bool` literal, or a term of the theory,
    /// with where each of its nodes is written.
    ///
    /// # Specification
    /// - ensures: `true` and `false` are the nullary constructor terms of their
    ///   spelling, one leaf node at their bytes; any other side is the term and
    ///   nodes [`Self::free_term`] reads.
    /// - fails: as [`Self::free_term`].
    /// - panics: none.
    /// - executable: none — the side read is source syntax.
    ///
    /// # Errors
    /// Returns `Malformed` for an unreadable term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `refl`'s `true` and `sym`'s applications read as the
    ///   literal and the terms they are.
    /// - witness: `description::theory::tests::a_law_member_reads_its_statement_2356`
    fn law_side(
        &self,
        at: Placed,
    ) -> Result<(FreeTerm, WrittenTerm), DescriptionDiagnostic>
    {
        let pieces = self.pieces(at)?;
        if let [Piece::Tile { label, .. }] = *pieces.as_slice()
            && matches!(label.as_ref(), "true" | "false")
        {
            let leaf = WrittenNode {
                span: at.span,
                head: Maybe::Absent(head::Absent::Leaf),
            };
            return Ok((FreeTerm::ctor(self.text(at).0, []), WrittenTerm {
                nodes: vec![leaf],
            }));
        }
        self.free_term(at, &BTreeSet::new())
    }

    /// Read a rule member: a written face between two terms, with the
    /// freshness conditions its `where` clause states, or a circuit body
    /// whose sphere is derived from the written wiring.
    ///
    /// # Specification
    /// - ensures: a member whose first side is a term is the face `lhs ==> rhs`
    ///   it writes, each `a # q` of its `where` clause a condition on it in
    ///   written order; a member whose first side is a port group is a circuit
    ///   rule whose source and target are derived, never fabricated for a
    ///   failed body, with one root per declared output and one port per output
    ///   of each frame.
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
    ///   ceiling, a written face, a face with two conditions and a two-rooted
    ///   body over a many-out frame separate a derived sphere, a written one,
    ///   its conditions and the two refusals.
    /// - witness: `description::theory::tests::a_ruled_theory_block_lowers_its_members_into_a_description`
    /// - witness: `description::theory::tests::a_wiring_that_closes_a_cycle_earns_the_declaration_tables_refusal`
    /// - witness: `description::theory::tests::a_doubling_body_declines_on_the_derivation_node_budget`
    /// - witness: `description::theory::tests::the_cat_shape_laws_are_written_faces`
    /// - witness: `description::theory::tests::a_many_out_frame_binds_every_port_and_roots_the_body`
    /// - witness: `description::theory::tests::a_coherence_between_composites_is_a_higher_cell`
    /// - witness: `description::theory::tests::a_where_clause_states_each_condition_on_its_rule`
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
            let mut fresh = Vec::new();
            if run.eat(Spelling("where")).0 {
                loop {
                    let atom = run.take()?;
                    if !run.eat(Spelling("#")).0 {
                        return Err(run.fault(DescriptionFault::Malformed));
                    }
                    let term = run.take()?;
                    fresh.push(Freshness::new(self.text(atom).0, self.text(term).0));
                    if !run.eat(Spelling(",")).0 {
                        break;
                    }
                }
            }
            run.end()?;
            let (lhs, left) = self.free_term(lhs, &BTreeSet::new())?;
            let lhs = patterned(&lhs, |name| {
                matches!(
                    scope.get(&Written(name.as_ref())),
                    Some(HeadKind::Operation | HeadKind::Observation | HeadKind::Rewrite)
                )
            });
            let instantiable: BTreeSet<&Name> =
                lhs.to_node().vars().chain(patterns(&lhs)).collect();
            let (rhs, right) = self.free_term(rhs, &instantiable)?;
            return Ok(RuleMember::Face(
                TheoryRule {
                    name: self.text(name).0.into(),
                    left: lhs,
                    right: rhs,
                    fresh,
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
                    let (left, _) = self.free_term(lhs, &BTreeSet::new())?;
                    let (right, _) = self.free_term(rhs, &BTreeSet::new())?;
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
    /// - witness: `desc_cells::tests::a_copied_variable_is_refused_at_its_second_occurrence`
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
    /// Read the binders a port's sort is written under, outermost first: the
    /// atom abstractions, `bind (a : N) .` each, then the restricted binders,
    /// `pi+ (x : S) .` each.
    ///
    /// # Specification
    /// - ensures: one binder per `bind` or `pi+` the run continues with, in
    ///   order, each its name tile, its written domain and whether it is an
    ///   abstraction; a run that continues with neither reads none and is left
    ///   where it was.
    /// - fails: a binder short of its opening parenthesis, name, colon, domain,
    ///   closing parenthesis or dot is malformed, and so is a `bind` after a
    ///   `pi+`: the abstractions stand outside the binders.
    /// - panics: none.
    /// - executable: none — the binders read are source syntax.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the λ-calculus `lam` port and the identity-return
    ///   `lam` port read back their one binder, a restriction's `nu` port its
    ///   one abstraction, and a port with none reads none; a `bind` inside a
    ///   `pi+` is refused.
    /// - witness: `description::theory::tests::a_rendered_signature_reparses_to_itself`
    /// - witness: `description::theory::tests::an_abstraction_stands_outside_the_binders`
    fn binders(&mut self) -> Result<Vec<WrittenBinder>, DescriptionDiagnostic>
    {
        let mut binders: Vec<WrittenBinder> = Vec::new();
        loop {
            let abstracts = if self.eat(Spelling("bind")).0 {
                if binders.last().is_some_and(|binder| !binder.abstracts) {
                    return Err(self.fault(DescriptionFault::Malformed));
                }
                true
            }
            else if self.eat(Spelling("pi+")).0 {
                false
            }
            else {
                break;
            };
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
            binders.push(WrittenBinder {
                name,
                domain,
                abstracts,
            });
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

/// The refusal of each port of `operation`, written at `written`, that sits
/// at a sort none of `sorts` names and that no builtin type spells (#2410).
///
/// A port's sort names a sort of the signature, one an `include` or an `ext`
/// member brought in among them, or, written bare, a builtin type such as
/// `Void`: a model interprets every other sort, and a name no sort declares
/// has nothing to interpret it by. A nested model's one port is at the theory
/// it nests, not at a sort, and is not read here.
///
/// # Specification
/// - requires: `written` is where `operation`'s ports are written, in order.
/// - ensures: one [`WfKind::UnknownPortSort`] refusal per input then output
///   port, in order, whose sort is neither the name of one of `sorts` nor a
///   builtin type written with no index, located at the port's sort and naming
///   the operation then the sort; none for a nested model.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a result naming nothing is refused at its bytes, while a
///   declared sort, an included one and a builtin type are read.
/// - witness: `description::theory::tests::a_port_at_a_sort_nothing_declares_is_refused_2410`
#[spec(ensures: |ref refused| refused.iter().all(|refusal| matches!(refusal.fault,
    DescriptionFault::IllFormed(ref diagnostic) if diagnostic.kind == WfKind::UnknownPortSort))
    && (operation.kind != OperationKind::Nested || refused.is_empty()))]
fn undeclared_ports(
    operation: &TheoryOperation,
    written: &WrittenOperation,
    sorts: &[TheorySort],
) -> Vec<DescriptionDiagnostic>
{
    if operation.kind == OperationKind::Nested {
        return Vec::new();
    }
    let declared: BTreeSet<&Name> = sorts.iter().map(|sort| &sort.name).collect();
    operation
        .inputs
        .iter()
        .chain(&operation.outputs)
        .zip(written.inputs.iter().chain(&written.outputs))
        .filter(|&(port, _)| {
            !declared.contains(&port.sort)
                && (!port.indices.is_empty()
                    || matches!(
                        type_atom(SurfaceName::from(port.sort.as_ref())),
                        Maybe::Absent(_)
                    ))
        })
        .map(|(port, at)| DescriptionDiagnostic {
            span: at.sort.span,
            fault: DescriptionFault::IllFormed(WfDiagnostic::new(
                WfKind::UnknownPortSort,
                Box::from([operation.name.clone(), port.sort.clone()]),
                DiagnosticMessage::from(format!(
                    "the operation `{}` has a port at `{}`, which no sort declares",
                    operation.name, port.sort
                )),
                Maybe::Present(surface_span(at.sort.span)),
            )),
        })
        .collect()
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
mod extension;

/// `term` with each application of a name no operation of the theory is, to
/// distinct names its enclosing abstractions bind, read as that name's
/// instantiation: a metavariable written as a pattern in Miller's sense,
/// `k(s, t)` under `bind s .` and `bind t .`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the term node for node, each operation node whose head `declared`
///   refuses and whose arguments are one or more pairwise distinct bound names
///   read as an instantiation of the same head and arguments; every other node
///   as it was.
/// - fails: never.
/// - panics: none.
/// - executable: none — the ensures clause is the rebuild itself; a predicate
///   restating it would walk the term again.
///
/// # Termination
/// Each node of the finite term is read once and rebuilt once.
///
/// # Adequacy
/// - hypothesis: L3 — `k(s, t)` under two abstractions reads as `k`'s
///   instantiation; an operation the theory declares, applied to the same
///   names, stays an operation, and an undeclared name applied to one name
///   twice or to a variable stays an operation the description check refuses.
/// - witness: `description::theory::tests::an_applied_bound_name_reads_as_a_pattern_2115`
fn patterned(
    term: &FreeTerm,
    declared: impl Fn(&Name) -> bool,
) -> FreeTerm
{
    /// A step of the rebuild: a node to read, or a head to apply to the
    /// terms its arguments built.
    enum Step<'term>
    {
        /// A node to read.
        Read(TermNode<'term>),
        /// An operation over its arguments, or a pattern when `true`.
        Op(&'term Name, usize, bool),
        /// A constructor over its arguments.
        Ctor(&'term Name, usize),
        /// A results tuple.
        Results(usize),
        /// An instantiation.
        Inst(&'term Name, usize),
        /// An abstraction over its body.
        Abs(&'term Name),
        /// A binding field over its body.
        Lam(&'term Name),
    }
    let mut pending = vec![Step::Read(term.to_node())];
    let mut built: Vec<FreeTerm> = Vec::new();
    let mut names: Vec<&Name> = Vec::new();
    let take = |built: &mut Vec<FreeTerm>, count: usize| {
        built.split_off(built.len().saturating_sub(count))
    };
    while let Some(step) = pending.pop() {
        match step {
            Step::Read(node) => match node.view() {
                TermView::Var(name) => built.push(FreeTerm::var(name.clone())),
                TermView::Atom(name) => built.push(FreeTerm::atom(name.clone())),
                TermView::Bound(name) => built.push(FreeTerm::bound(name.clone())),
                TermView::Op { name, args } => {
                    let args: Vec<TermNode<'_>> = args.collect();
                    names.clear();
                    names.extend(args.iter().filter_map(|arg| bound_name(*arg)));
                    names.sort_unstable();
                    names.dedup();
                    let pattern = !declared(name) && !args.is_empty() && names.len() == args.len();
                    pending.push(Step::Op(name, args.len(), pattern));
                    pending.extend(args.into_iter().rev().map(Step::Read));
                },
                TermView::Ctor { name, args } => {
                    let args: Vec<TermNode<'_>> = args.collect();
                    pending.push(Step::Ctor(name, args.len()));
                    pending.extend(args.into_iter().rev().map(Step::Read));
                },
                TermView::Results { args } => {
                    let args: Vec<TermNode<'_>> = args.collect();
                    pending.push(Step::Results(args.len()));
                    pending.extend(args.into_iter().rev().map(Step::Read));
                },
                TermView::Inst { name, args } => {
                    let args: Vec<TermNode<'_>> = args.collect();
                    pending.push(Step::Inst(name, args.len()));
                    pending.extend(args.into_iter().rev().map(Step::Read));
                },
                TermView::Abs { atom, args } => {
                    pending.push(Step::Abs(atom));
                    pending.extend(args.map(Step::Read));
                },
                TermView::Lam { var, args } => {
                    pending.push(Step::Lam(var));
                    pending.extend(args.map(Step::Read));
                },
            },
            Step::Op(name, count, pattern) => {
                let args = take(&mut built, count);
                built.push(if pattern {
                    FreeTerm::inst(name.clone(), args)
                }
                else {
                    FreeTerm::op(name.clone(), args)
                });
            },
            Step::Ctor(name, count) => {
                let args = take(&mut built, count);
                built.push(FreeTerm::ctor(name.clone(), args));
            },
            Step::Results(count) => {
                let args = take(&mut built, count);
                built.push(FreeTerm::results(args));
            },
            Step::Inst(name, count) => {
                let args = take(&mut built, count);
                built.push(FreeTerm::inst(name.clone(), args));
            },
            Step::Abs(atom) => {
                let body = built.pop().unwrap_or_else(|| FreeTerm::results([]));
                built.push(FreeTerm::abs(atom.clone(), body));
            },
            Step::Lam(var) => {
                let body = built.pop().unwrap_or_else(|| FreeTerm::results([]));
                built.push(FreeTerm::lam(var.clone(), body));
            },
        }
    }
    built.pop().unwrap_or_else(|| term.clone())
}

/// The name `node` is when it is a name an enclosing binder binds.
///
/// # Specification
/// trivial.
fn bound_name(node: TermNode<'_>) -> Option<&Name>
{
    match node.view() {
        TermView::Atom(name) | TermView::Bound(name) => Some(name),
        TermView::Var(_)
        | TermView::Ctor { .. }
        | TermView::Op { .. }
        | TermView::Results { .. }
        | TermView::Inst { .. }
        | TermView::Abs { .. }
        | TermView::Lam { .. } => None,
    }
}

/// The metavariables `term` writes as patterns: the heads of its
/// instantiations, in pre-order with repeats.
///
/// # Specification
/// - ensures: one name per instantiation node of `term`, its head.
/// - panics: none.
/// - executable: none — the ensures clause is the walk itself; a predicate
///   restating it would walk the term again.
///
/// # Adequacy
/// - hypothesis: L3 — as [`patterned`]: a right side may instantiate the
///   metavariable its left side writes as a pattern.
/// - witness: `description::theory::tests::an_applied_bound_name_reads_as_a_pattern_2115`
fn patterns(term: &FreeTerm) -> Vec<&Name>
{
    let mut heads = Vec::new();
    let mut pending = vec![term.to_node()];
    while let Some(node) = pending.pop() {
        match node.view() {
            TermView::Inst { name, args } => {
                heads.push(name);
                pending.extend(args);
            },
            TermView::Ctor { args, .. }
            | TermView::Op { args, .. }
            | TermView::Results { args }
            | TermView::Abs { args, .. }
            | TermView::Lam { args, .. } => pending.extend(args),
            TermView::Var(_) | TermView::Atom(_) | TermView::Bound(_) => {},
        }
    }
    heads
}

#[cfg(test)]
mod tests;
