//! Elaboration of a levitated description into command cells: the seam where
//! a description's rules enter a cell store.
//!
//! A [`RuleFace`] is a rewrite `lhs ==> rhs` over free terms.
//! [`elaborate_rule`] turns it into an oriented [`Cell`] whose left-hand side
//! is a cut between the matched producer and an operation frame: an operation
//! application `f(head, rest…)` becomes `⟨head | f(rest…; $ret)⟩`, and the
//! right-hand side sends the result term to the same return continuation
//! `$ret`, flattening a constructor that wraps an operation into a return-side
//! constructor frame `K⁻`. The supported fragment is the direct one — a matched
//! producer, an operation frame, and result terms that are variables,
//! constructors of producers, tail operations, or a constructor wrapping an
//! operation through single-argument constructors. A shape outside it is
//! declined with an [`ElaborateError`], never mis-elaborated.
//!
//! # The declaration's polarity
//!
//! Every cell a description contributes cuts at the polarity its declaration
//! fixes: a `data` declaration's at a positive cut, a `codata` declaration's at
//! a negative one, which is the polarity its η law requires
//! ([`EtaKind::required_polarity`]). Rule, frame and η cells read that polarity
//! from one mapping, so they cannot disagree. The frame-defining cells follow
//! it too: a negative rule cell hands its result to a return-side constructor
//! frame at a negative cut, which only a negative frame cell reduces, so a
//! `codata` declaration's η critical pair joins the way a `data` one's does.
//!
//! # The operation alphabet a description supplies
//!
//! A description declares operations, each with a multi-output arity, and the
//! arity decides what the cell layer can hold. [`elaborate_data_desc`] reads
//! the operations before the faces: an operation whose arity is the
//! one-monomial, one-output shape is admitted, because an operation frame
//! `f(p̄; c)` carries exactly one return continuation; every other arity is
//! declined with an [`OpElaborateError`], and a face applying a declined
//! operation is declined with it rather than elaborated into a frame that
//! silently drops the operation's other outputs.
//!
//! Whether a face's symbols belong to the declaration at all, and whether an
//! arity's maps compose, are [`check_desc`]'s questions; a caller wanting both
//! verdicts runs both passes.
//!
//! # The admission seam
//!
//! [`elaborate_data_desc`] is where cells enter a store from a description, so
//! it is where admission binds, and it refuses two hole faults apart. A rule
//! whose left-hand side copies a hole is refused with the cell layer's
//! linearity diagnostic ([`ElaborateError::NonLinear`]). A cell that wears one
//! hole name at both polarities is refused with its own diagnostic
//! ([`ElaborateError::MixedPolarity`]): the cell layer reads such a hole as the
//! dinaturality seam its composition gate needs, and that reading is right for
//! the cells completion derives, but a description's rule binds its pattern
//! variables as producers and its result to one reserved continuation, so a
//! face reaches the seam only by spelling a variable with a reserved name.
//! Neither refusal lives deeper than this seam, because non-linear and
//! mixed-polarity command patterns are legitimate internal shapes.
//!
//! [`check_desc`]: gandr_theory_levitation::check_desc

use alloc::vec::Vec;
use core::fmt;

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CellVariance;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::EtaKind;
use gandr_theory_cell_complexes::HoleName;
use gandr_theory_cell_complexes::NonLinearPattern;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Sym;
use gandr_theory_cell_complexes::admit_linear_cell;
use gandr_theory_cell_complexes::frame_defining_cell;
use gandr_theory_levitation::CircuitElaborationError;
use gandr_theory_levitation::CircuitRule;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::TermArgs;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::WhiskeredCell;
use gandr_theory_levitation::elaborate_body;

use crate::boundary::ConstructorCount;
use crate::boundary::DeclinedFaceIndex;
use crate::boundary::DeclinedOpIndex;
use crate::boundary::InverseFacePresence;
use crate::boundary::OperationInputCount;

/// The reserved return-continuation hole a rule's cut binds; the `$` prefix
/// keeps it apart from every conventionally spelled pattern variable.
const RETURN_CONT: &str = "$ret";

/// The reserved producer hole an η cell observes and hands back.
const ETA_OBSERVED: &str = "$eta";

/// Why a face could not be elaborated into a command cell, or could not be
/// admitted once elaborated.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ElaborateError
{
    /// The rule's left-hand side is not an operation application; a rule
    /// rewrites an operation redex `f(…)`.
    LhsNotOperation,
    /// An operation application carries no arguments, so there is no matched
    /// producer to cut against.
    EmptyOperation,
    /// A term shape outside the supported fragment: an operation in producer
    /// position, or a several-argument constructor wrapping an operation.
    UnsupportedShape,
    /// The face applies an operation whose declared arity the
    /// single-continuation command-pattern grammar cannot hold.
    UnrepresentableOperation,
    /// The face elaborated, but its left-hand side copies a hole: refused at
    /// the admission seam, because cell patterns are linear.
    NonLinear(NonLinearPattern),
    /// The face elaborated, but one hole name is worn by a producer and by a
    /// consumer: refused at the admission seam, because no rule a description
    /// states writes that seam.
    MixedPolarity(MixedPolarityHole),
    /// A circuit rule's wiring denotes no single whiskered composite, so the
    /// boundary-language object the member stands for does not exist and its
    /// derived pair is not admitted on its own strength.
    NoCircuitComposite(CircuitElaborationError),
}

impl From<NonLinearPattern> for ElaborateError
{
    /// Wraps the copy refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: NonLinearPattern) -> Self
    {
        Self::NonLinear(refusal)
    }
}

impl From<MixedPolarityHole> for ElaborateError
{
    /// Wraps the mixed-polarity refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: MixedPolarityHole) -> Self
    {
        Self::MixedPolarity(refusal)
    }
}

/// A refused cell that wears one hole name at both polarities: the admission
/// diagnostic, naming the hole.
///
/// The hole is the first of the cell's holes whose occurrences include both a
/// producer and a consumer, across both faces. Its rendering names the hole and
/// the respelling, as the copy diagnostic does.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct MixedPolarityHole
{
    /// The hole worn at both polarities.
    hole: HoleName,
}

impl MixedPolarityHole
{
    /// The hole worn at both polarities.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn hole(&self) -> &HoleName
    {
        &self.hole
    }
}

impl fmt::Display for MixedPolarityHole
{
    /// Names the hole and the respelling.
    ///
    /// # Specification
    /// - ensures: the rendering names the hole, states that it joins a pattern
    ///   variable to a continuation, names the reserved spellings that reach
    ///   the seam, and says to rename the variable.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the rendering of one refused seam is asserted to name
    ///   the hole and the respelling, and to differ from the copy diagnostic.
    /// - witness: `elaborate::tests::a_repeated_hole_and_a_mixed_polarity_hole_earn_distinct_refusals`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "mixed-polarity hole: `{hole}` is worn by a producer and by a consumer of one cell, \
             which joins a pattern variable to a continuation. A description's rule binds its \
             pattern variables as producers and sends its result to one reserved continuation, so \
             a face reaches this seam only by spelling a variable with a name the elaboration \
             reserves (`{RETURN_CONT}`, `{ETA_OBSERVED}`). Give the variable a name of its own.",
            hole = self.hole,
        )
    }
}

impl core::error::Error for MixedPolarityHole
{
}

/// Why a declared operation gets no operation frame in the cell layer.
///
/// Each variant names a way the operation's arity leaves the shape an
/// operation frame expresses: one frame carries exactly one producer-argument
/// list and exactly one return continuation, so the only arity it holds is the
/// one-monomial, one-output shape.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OpElaborateError
{
    /// The operation declares no output port, so its frame's return
    /// continuation would carry nothing.
    NoOutput,
    /// The operation declares more than one output port, which needs one
    /// continuation per port and so a wider consumer grammar.
    ManyOutput,
    /// The operation's one output port is fed by zero or several monomials;
    /// several is the sum-layer aggregation that needs a commutative monoid on
    /// the target, and zero feeds the port nothing.
    AggregatedOutput,
}

/// A declared operation the cell layer admits: the symbol its applications
/// cut against, and how many input ports it reads.
///
/// The elaborated operation frame carries one fewer producer argument than
/// `inputs`, because a rule's first argument is the matched producer the cut is
/// against.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct OpFrame
{
    /// The operation symbol.
    pub op: Sym,
    /// The operation's declared input ports.
    pub inputs: OperationInputCount,
}

/// One circuit rule member's elaboration, in declaration order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitElaboration
{
    /// The member entered the store: the cell its derived pair became, beside
    /// the whiskered composite its body denotes.
    Admitted
    {
        /// The cell the member's declared sphere elaborated to.
        cell: CellId,
        /// The boundary-language composite the member's filler denotes.
        composite: WhiskeredCell,
    },
    /// The member was declined, and why.
    Declined(ElaborateError),
}

/// Why a declaration licenses no η cell.
///
/// An η law says a destructor and the constructor it inverts cancel. A
/// declaration licenses one only when it states both halves, so each variant
/// names a missing half rather than a failure to elaborate.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum EtaElaborateError
{
    /// The declaration has zero or several constructors, so `K(f(w)) ~> w`
    /// would be false at every constructor but one.
    NotSingleConstructor(ConstructorCount),
    /// No admitted operation of the declaration carries the inverse face
    /// `f(K(x)) ==> x`, so nothing states that an operation destructs the
    /// constructor.
    NoInverseFace,
}

impl fmt::Display for EtaElaborateError
{
    /// Names the missing half of the η licence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::NotSingleConstructor(count) => write!(
                f,
                "no η cell: the declaration has {count} constructors, and an η law cancels a \
                 destructor against the one constructor it inverts. Write the declaration with \
                 one constructor, or state the per-constructor laws as ordinary `rule` members."
            ),
            | Self::NoInverseFace => f.write_str(
                "no η cell: no operation of the declaration carries the face `f(K(x)) ==> x`, so \
                 nothing in the declaration says that an operation destructs the constructor. An \
                 η law is licensed by the inverse face, never assumed from an operation's \
                 presence.",
            ),
        }
    }
}

impl core::error::Error for EtaElaborateError
{
}

/// The η cells a declaration minted, or why it minted none.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum EtaElaboration
{
    /// The η cells, by their identifiers in the store; never empty.
    Minted(Vec<CellId>),
    /// Why the declaration licenses no η cell.
    Declined(EtaElaborateError),
}

/// The cell-layer elaboration of one whole description: what reached the
/// store, and everything that did not.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DescElaboration
{
    /// The elaborated cells: a frame-defining cell per declared constructor,
    /// every admitted rule and circuit cell, and the η cells.
    pub store: CellStore,
    /// The operations the cell layer admits, in declaration order.
    pub opers: Vec<OpFrame>,
    /// Each declined operation, by index into the description's operations,
    /// with its reason.
    pub declined_opers: Vec<(DeclinedOpIndex, OpElaborateError)>,
    /// Each declined face, by index into the description's rules, with its
    /// reason.
    pub declined_faces: Vec<(DeclinedFaceIndex, ElaborateError)>,
    /// One entry per circuit rule member, in declaration order.
    pub circuits: Vec<CircuitElaboration>,
    /// The η cells the declaration licensed, or why it licensed none.
    pub eta: EtaElaboration,
}

/// Elaborate a whole description's operations, rules, circuit rules and η
/// laws into one store.
///
/// The grade a description's fields carry is never read: elaboration reads
/// names, arities, faces and the declaration's polarity.
///
/// # Specification
/// - ensures: `store` holds one frame-defining cell per declared constructor,
///   then every rule cell that passed the operation gate, elaborated, and
///   passed the admission seam, then every admitted circuit cell, then the η
///   cells; every one of them cuts at the declaration's polarity — positive for
///   `data`, negative for `codata`.
/// - ensures: `opers` holds one [`OpFrame`] per admitted operation and
///   `declined_opers` the rest, both in declaration order; `declined_faces`
///   pairs each declined face with its [`ElaborateError`], and a face applying
///   a declined operation is declined with
///   [`ElaborateError::UnrepresentableOperation`] and never reaches the store.
/// - ensures: `circuits` holds one [`CircuitElaboration`] per circuit rule, in
///   declaration order; a rule whose body denotes no single composite is
///   declined with [`ElaborateError::NoCircuitComposite`] before its derived
///   pair is offered anywhere, and otherwise passes the same gate a face does.
/// - ensures: `eta` holds one η cell per admitted operation carrying the
///   inverse face `f(K(x)) ==> x` of the declaration's one constructor, or the
///   missing half of that licence.
/// - provides: the single admission point for a description's cells: a face
///   passes the operation gate before it is shaped and the admission seam —
///   copy first, then polarity — before it enters the store.
/// - panics: none.
/// - intension: frame-defining and η cells are generated rather than read from
///   the description, and carry only reserved holes each used once, so they
///   bypass the admission seam.
///
/// # Adequacy
/// - hypothesis: L3 — the operation pass is separated from the face pass by a
///   description whose only operation is admitted and one whose only operation
///   is many-out; the face refusals are separated pointwise (fragment shape,
///   operation gate, copy, mixed polarity, circuit composite); the polarity
///   clause by a `codata` declaration whose every cell cuts negative and whose
///   η critical pair joins.
/// - witness: `elaborate::tests::a_whole_description_elaborates_frame_and_rule_cells`
/// - witness: `elaborate::tests::a_many_out_operation_is_declined_and_declines_its_faces`
/// - witness: `elaborate::tests::an_admitted_operation_reports_its_declared_inputs`
/// - witness: `elaborate::tests::a_description_whose_rule_copies_a_hole_is_refused`
/// - witness: `elaborate::tests::a_repeated_hole_and_a_mixed_polarity_hole_earn_distinct_refusals`
/// - witness: `elaborate::tests::a_codata_declarations_cells_all_cut_at_its_eta_polarity`
/// - witness: `elaborate::tests::a_single_redex_circuit_rule_reaches_the_store`
/// - witness: `elaborate::tests::a_two_redex_circuit_rule_is_declined_its_composite`
/// - witness: `tests::eta::a_codata_eta_cell_joins_the_projection_route_at_its_negative_cut`
#[inline]
#[must_use]
pub fn elaborate_data_desc<G>(desc: &SignDesc<G>) -> DescElaboration
{
    let polarity = cut_polarity(desc.polarity);
    let mut store = CellStore::new();
    for ctor in &desc.ctors {
        store.insert(frame_cell(&sym(&ctor.name), polarity));
    }
    let mut opers = Vec::with_capacity(desc.opers.len());
    let mut declined_opers = Vec::new();
    // The names no cell may mention, gathered while the operation pass runs so
    // the face pass can consult them.
    let mut unrepresentable: Vec<&Name> = Vec::new();
    for (index, op) in desc.opers.iter().enumerate() {
        match admit_op(op) {
            | Ok(frame) => opers.push(frame),
            | Err(error) => {
                unrepresentable.push(&op.name);
                declined_opers.push((DeclinedOpIndex::from(index), error));
            },
        }
    }
    let mut declined_faces = Vec::new();
    for (index, face) in desc.rules.iter().enumerate() {
        if let Err(error) = admit_face(&mut store, face, desc.polarity, &unrepresentable) {
            declined_faces.push((DeclinedFaceIndex::from(index), error));
        }
    }
    let circuits = desc
        .circuits
        .iter()
        .map(|rule| admit_circuit_rule(&mut store, rule, desc.polarity, &unrepresentable))
        .collect();
    let eta = mint_eta_cells(&mut store, desc, &unrepresentable);
    DescElaboration {
        store,
        opers,
        declined_opers,
        declined_faces,
        circuits,
        eta,
    }
}

/// Admit one written face: the operation gate, the elaboration, then the
/// admission seam.
///
/// # Specification
/// - ensures: the face's cell is in `store` when it mentions no declined
///   operation, elaborates, and passes the admission seam; otherwise `store` is
///   unchanged.
/// - fails: [`ElaborateError::UnrepresentableOperation`] first, then as
///   [`elaborate_rule`] fails, then as the admission seam refuses.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn admit_face(
    store: &mut CellStore,
    face: &RuleFace,
    polarity: DeclPolarity,
    unrepresentable: &[&Name],
) -> Result<(), ElaborateError>
{
    declined_operation(face, unrepresentable)?;
    let cell = elaborate_rule(face, polarity)?;
    admit_cell(store, cell)?;
    Ok(())
}

/// Admit one circuit rule: its composite, then its cell, through the gate a
/// written face passes.
///
/// # Specification
/// - ensures: [`CircuitElaboration::Admitted`] with the rule's declared sphere
///   inserted as a cell when the body denotes one whiskered composite and the
///   sphere passes the gate a written face passes; otherwise `store` is
///   unchanged.
/// - ensures: [`CircuitElaboration::Declined`] with
///   [`ElaborateError::NoCircuitComposite`] when the body denotes no single
///   composite, decided before the sphere is read; then as a written face is
///   declined.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the composite condition is decided before the face
///   conditions, so a two-redex body whose sphere would elaborate and a
///   frames-only body whose sphere copies a hole separate the two halves, and a
///   body over a declined operation reaches the operation gate.
/// - witness: `elaborate::tests::a_single_redex_circuit_rule_reaches_the_store`
/// - witness: `elaborate::tests::a_two_redex_circuit_rule_is_declined_its_composite`
/// - witness: `elaborate::tests::a_circuit_rule_whose_boundary_copies_a_hole_is_refused`
/// - witness: `elaborate::tests::a_circuit_rule_applying_a_declined_operation_is_declined_at_the_gate`
fn admit_circuit_rule(
    store: &mut CellStore,
    rule: &CircuitRule,
    polarity: DeclPolarity,
    unrepresentable: &[&Name],
) -> CircuitElaboration
{
    let composite = match elaborate_body(&rule.body) {
        | Ok(composite) => composite,
        | Err(error) => {
            return CircuitElaboration::Declined(ElaborateError::NoCircuitComposite(error));
        },
    };
    let admitted = declined_operation(&rule.sphere, unrepresentable)
        .and_then(|()| elaborate_rule(&rule.sphere, polarity))
        .and_then(|cell| admit_cell(store, cell));
    match admitted {
        | Ok(cell) => CircuitElaboration::Admitted { cell, composite },
        | Err(error) => CircuitElaboration::Declined(error),
    }
}

/// Mint the η cells a declaration licenses into `store`.
///
/// An η law says a destructor and the constructor it inverts cancel. It is
/// written in the contracting direction,
///
/// ```text
/// ⟨w |ε f(; K⁻(β))⟩  ~>  ⟨w |ε β⟩
/// ```
///
/// destruct `w` with `f`, rebuild with `K`, and you are back where you started.
/// The left-hand side is headed by an operation frame, so it is a
/// consumer-driven redex like every other cell the route admits; the mirror is
/// headed by a bare hole, matches every cut of its polarity, and is not
/// minted. The declaration licenses the law by stating both halves: exactly
/// one constructor `K`, and an admitted operation `f` carrying the inverse
/// face `f(K(x)) ==> x`. The cut is the declaration's — data η positive, codata
/// η negative — and the cell's provenance carries the kind, so the alphabet
/// refuses it at the other polarity however well it matches.
///
/// # Specification
/// - ensures: one η cell per admitted operation carrying the inverse face, when
///   the declaration has exactly one constructor, in operation order.
/// - fails: [`EtaElaborateError::NotSingleConstructor`] with the constructor
///   count when it is not one; [`EtaElaborateError::NoInverseFace`] when no
///   admitted operation carries the face.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the two declines are separated by a description with two
///   constructors and one with a single constructor whose operation carries no
///   inverse face; minting by a single-constructor description whose operation
///   carries it, at both polarities, whose cell is shown joinable with the
///   projection route at each.
/// - witness: `elaborate::tests::a_wrapper_description_mints_its_eta_cell`
/// - witness: `elaborate::tests::a_codata_declaration_mints_its_eta_cell_at_a_negative_cut`
/// - witness: `elaborate::tests::a_multi_constructor_description_declines_its_eta_cell`
/// - witness: `elaborate::tests::an_operation_with_no_inverse_face_licenses_no_eta_cell`
/// - witness: `tests::eta::the_two_routes_out_of_the_eta_redex_agree`
fn mint_eta_cells<G>(
    store: &mut CellStore,
    desc: &SignDesc<G>,
    unrepresentable: &[&Name],
) -> EtaElaboration
{
    let [ref ctor] = *desc.ctors
    else {
        return EtaElaboration::Declined(EtaElaborateError::NotSingleConstructor(
            ConstructorCount::from(desc.ctors.len()),
        ));
    };
    let kind = eta_kind(desc.polarity);
    let constructor = sym(&ctor.name);
    let mut minted = Vec::new();
    for op in &desc.opers {
        if unrepresentable.contains(&&op.name) {
            continue;
        }
        if !bool::from(inverts(desc, &op.name, &ctor.name)) {
            continue;
        }
        minted.push(store.insert(eta_cell(&sym(&op.name), &constructor, kind)));
    }
    if minted.is_empty() {
        return EtaElaboration::Declined(EtaElaborateError::NoInverseFace);
    }
    EtaElaboration::Minted(minted)
}

/// Whether some face of `desc` states `op(ctor(x)) ==> x`: the declaration's
/// own statement that `op` destructs `ctor`.
///
/// # Specification
/// - ensures: positive exactly when some face is the inverse face
///   ([`is_inverse_face`]).
/// - panics: none.
fn inverts<G>(
    desc: &SignDesc<G>,
    op: &Name,
    ctor: &Name,
) -> InverseFacePresence
{
    InverseFacePresence::from(
        desc.rules
            .iter()
            .any(|face| bool::from(is_inverse_face(face, op, ctor))),
    )
}

/// Whether `face` is `op(ctor(x)) ==> x`.
///
/// # Specification
/// - ensures: positive exactly when the left-hand side is `op` applied to one
///   argument, that argument is `ctor` applied to one variable, and the
///   right-hand side is that same variable.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the licence is a shape, so each way a face can miss it is
///   separated pointwise: another operation, a variable or another constructor
///   as the argument, a non-variable field, another or a non-variable result, a
///   second operation argument, and a second constructor field.
/// - witness: `elaborate::tests::the_inverse_face_is_recognized_by_its_shape_and_nothing_looser`
fn is_inverse_face(
    face: &RuleFace,
    op: &Name,
    ctor: &Name,
) -> InverseFacePresence
{
    let TermView::Op {
        name: applied,
        args: mut operands,
    } = face.lhs.view()
    else {
        return InverseFacePresence::from(false);
    };
    let (Some(argument), None) = (operands.next(), operands.next())
    else {
        return InverseFacePresence::from(false);
    };
    let TermView::Ctor {
        name: built,
        args: mut fields,
    } = argument.view()
    else {
        return InverseFacePresence::from(false);
    };
    let (Some(field), None) = (fields.next(), fields.next())
    else {
        return InverseFacePresence::from(false);
    };
    let (TermView::Var(field), TermView::Var(result)) = (field.view(), face.rhs.view())
    else {
        return InverseFacePresence::from(false);
    };
    InverseFacePresence::from(applied == op && built == ctor && field == result)
}

/// The η cell `⟨$eta |ε op(; ctor⁻($ret))⟩ ~> ⟨$eta |ε $ret⟩` at `kind`'s
/// polarity.
///
/// # Specification
/// - ensures: a cell whose left-hand side cuts a fresh producer hole against
///   the operation frame wrapping the constructor's return-side frame, whose
///   right-hand side drops both, whose cut is `kind`'s required polarity, and
///   whose provenance is [`CellProvenance::Eta`] at `kind`.
/// - panics: none.
fn eta_cell(
    op: &Sym,
    ctor: &Sym,
    kind: EtaKind,
) -> Cell
{
    let polarity = kind.required_polarity();
    let lhs = CmdPat::cut(
        polarity,
        ProdPat::meta(ETA_OBSERVED),
        ConsPat::op(
            op.clone(),
            [],
            ConsPat::frame(ctor.clone(), ConsPat::meta(RETURN_CONT)),
        ),
    );
    let rhs = CmdPat::cut(
        polarity,
        ProdPat::meta(ETA_OBSERVED),
        ConsPat::meta(RETURN_CONT),
    );
    Cell::new(
        lhs,
        rhs,
        Orientation::PolarityDerived,
        CellProvenance::Eta(kind),
    )
}

/// The defining cell of the return-side frame `ctor⁻`, cut at `polarity`.
///
/// # Specification
/// - ensures: [`frame_defining_cell`]'s faces, orientation and provenance, with
///   both faces cut at `polarity`; at [`Polarity::Positive`] it is exactly
///   [`frame_defining_cell`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the positive cell is compared whole against the cell
///   layer's own, and a `codata` declaration's negative frame cell is what
///   joins its η critical pair.
/// - witness: `elaborate::tests::the_positive_frame_cell_is_the_frame_defining_cell`
/// - witness: `tests::eta::a_codata_eta_cell_joins_the_projection_route_at_its_negative_cut`
fn frame_cell(
    ctor: &Sym,
    polarity: Polarity,
) -> Cell
{
    let defining = frame_defining_cell(ctor);
    let cut =
        |face: &CmdPat| CmdPat::cut(polarity, face.producer().clone(), face.consumer().clone());
    Cell::new(
        cut(defining.lhs()),
        cut(defining.rhs()),
        defining.orient(),
        defining.provenance(),
    )
}

/// The η law a declaration of `polarity` states: the one mapping every cell's
/// cut polarity is read from.
///
/// # Specification
/// trivial.
const fn eta_kind(polarity: DeclPolarity) -> EtaKind
{
    match polarity {
        | DeclPolarity::Data => EtaKind::Data,
        | DeclPolarity::Codata => EtaKind::Codata,
    }
}

/// The cut polarity a declaration of `polarity` elaborates its cells at: the
/// polarity its η law requires.
///
/// # Specification
/// trivial.
const fn cut_polarity(polarity: DeclPolarity) -> Polarity
{
    eta_kind(polarity).required_polarity()
}

/// Admit one declared operation into the cell layer's operation alphabet.
///
/// # Specification
/// - ensures: the frame exactly when the arity has one output port fed by one
///   monomial; it carries the operation's symbol and declared input count.
/// - fails: [`OpElaborateError::NoOutput`] with no output port,
///   [`OpElaborateError::ManyOutput`] with several, then
///   [`OpElaborateError::AggregatedOutput`] when the one port is fed by zero or
///   several monomials.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — an admitted operation, a many-out one, an aggregating one
///   and an outputless one separate the three refusals and the admission.
/// - witness: `elaborate::tests::an_admitted_operation_reports_its_declared_inputs`
/// - witness: `elaborate::tests::a_many_out_operation_is_declined_and_declines_its_faces`
/// - witness: `elaborate::tests::an_aggregating_arity_and_an_outputless_one_are_declined_apart`
fn admit_op(op: &OperDesc) -> Result<OpFrame, OpElaborateError>
{
    match *op.arity.outputs {
        | [_] => {},
        | [] => return Err(OpElaborateError::NoOutput),
        | [_, _, ..] => return Err(OpElaborateError::ManyOutput),
    }
    if usize::from(op.arity.monomials()) != 1 {
        return Err(OpElaborateError::AggregatedOutput);
    }
    Ok(OpFrame {
        op: sym(&op.name),
        inputs: OperationInputCount::from(op.arity.inputs.len()),
    })
}

/// The decline a face earns for applying an operation the cell layer refused.
///
/// # Specification
/// - ensures: success exactly when no operation application in either face
///   names an operation in `declined`.
/// - fails: [`ElaborateError::UnrepresentableOperation`] otherwise.
/// - panics: none.
/// - intension: an explicit worklist over both faces, so face depth costs no
///   stack.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a face over a declined operation is declined and a face
///   over an admitted operation beside a declined one survives.
/// - witness: `elaborate::tests::a_many_out_operation_is_declined_and_declines_its_faces`
/// - witness: `elaborate::tests::a_face_over_an_admitted_operation_survives_the_gate`
fn declined_operation(
    face: &RuleFace,
    declined: &[&Name],
) -> Result<(), ElaborateError>
{
    let mut stack: Vec<TermNode<'_>> = alloc::vec![face.lhs.to_node(), face.rhs.to_node()];
    while let Some(node) = stack.pop() {
        match node.view() {
            | TermView::Var(_) => {},
            | TermView::Op { name, args } => {
                if declined.contains(&name) {
                    return Err(ElaborateError::UnrepresentableOperation);
                }
                stack.extend(args);
            },
            | TermView::Ctor { args, .. } => stack.extend(args),
        }
    }
    Ok(())
}

/// Admit one elaborated cell into `store` through the admission seam.
///
/// # Specification
/// - ensures: `cell` inserted (deduplicated as [`CellStore::insert`] specifies)
///   and its identifier, when its left-hand side copies no hole and no hole
///   name is worn at both polarities; otherwise `store` is unchanged.
/// - fails: [`ElaborateError::NonLinear`] naming the copied hole;
///   [`ElaborateError::MixedPolarity`] naming the hole worn at both polarities.
/// - panics: none.
/// - intension: the copy is decided first, so a cell with both faults is
///   refused for the copy.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a copying face, a face whose variable spells the reserved
///   continuation, and a face with both faults separate the two refusals and
///   their order; a linear neighbour still lands.
/// - witness: `elaborate::tests::a_repeated_hole_and_a_mixed_polarity_hole_earn_distinct_refusals`
/// - witness: `tests::linearity::a_refused_face_does_not_stop_its_linear_neighbours`
fn admit_cell(
    store: &mut CellStore,
    cell: Cell,
) -> Result<CellId, ElaborateError>
{
    admit_linear_cell(&cell)?;
    single_polarity_holes(&cell)?;
    Ok(store.insert(cell))
}

/// Refuse a cell that wears one hole name at both polarities.
///
/// # Specification
/// - ensures: success exactly when no hole of the cell's derived metadata is
///   [`CellVariance::Mixed`].
/// - fails: [`MixedPolarityHole`] naming the first such hole, in
///   first-occurrence order.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn single_polarity_holes(cell: &Cell) -> Result<(), MixedPolarityHole>
{
    for var in cell.meta().vars() {
        if var.variance() == CellVariance::Mixed {
            return Err(MixedPolarityHole {
                hole: var.var().hole().clone(),
            });
        }
    }
    Ok(())
}

/// Elaborate one rule face into an oriented command cell at the declaration's
/// polarity.
///
/// # Specification
/// - ensures: for a face whose left-hand side is an operation `f(head, rest…)`
///   and whose result term is in the supported fragment, the cell `⟨head |ε
///   f(rest…; $ret)⟩ ~> 𝓡⟦rhs⟧$ret`, with `ε` positive for `data` and negative
///   for `codata`, provenance [`CellProvenance::SurfaceRule`], and derived
///   metadata.
/// - fails: [`ElaborateError::LhsNotOperation`] when the left-hand side is not
///   an operation, [`ElaborateError::EmptyOperation`] on an operation with no
///   argument, [`ElaborateError::UnsupportedShape`] on a term outside the
///   fragment.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the direct case, the flattening case and a non-operation
///   left-hand side separate the arms; a `codata` declaration's rule cell is
///   pinned at the negative cut its η cell sits at.
/// - witness: `elaborate::tests::add_zero_elaborates_to_a_cut_against_the_operation_frame`
/// - witness: `elaborate::tests::add_succ_flattens_the_wrapping_constructor_into_a_frame`
/// - witness: `elaborate::tests::a_non_operation_lhs_is_declined`
/// - witness: `elaborate::tests::a_codata_declarations_cells_all_cut_at_its_eta_polarity`
#[inline]
pub fn elaborate_rule(
    face: &RuleFace,
    polarity: DeclPolarity,
) -> Result<Cell, ElaborateError>
{
    let polarity = cut_polarity(polarity);
    let TermView::Op { name, args } = face.lhs.view()
    else {
        return Err(ElaborateError::LhsNotOperation);
    };
    let lhs = operation_cut(name, args, ConsPat::meta(RETURN_CONT), polarity)?;
    let rhs = elaborate_result(face.rhs.to_node(), ConsPat::meta(RETURN_CONT), polarity)?;
    Ok(Cell::new(
        lhs,
        rhs,
        Orientation::PolarityDerived,
        CellProvenance::SurfaceRule,
    ))
}

/// The cut of an operation application `name(head, rest…)` against `cont`.
///
/// # Specification
/// - ensures: `⟨head |ε name(rest…; cont)⟩` when `head` and every `rest` term
///   is a producer.
/// - fails: [`ElaborateError::EmptyOperation`] with no argument;
///   [`ElaborateError::UnsupportedShape`] when an argument is not a producer.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn operation_cut(
    name: &Name,
    mut args: TermArgs<'_>,
    cont: ConsPat,
    polarity: Polarity,
) -> Result<CmdPat, ElaborateError>
{
    let Some(head) = args.next()
    else {
        return Err(ElaborateError::EmptyOperation);
    };
    let producer = elaborate_producer(head)?;
    let frame_args = elaborate_producers(args)?;
    Ok(CmdPat::cut(
        polarity,
        producer,
        ConsPat::op(sym(name), frame_args, cont),
    ))
}

/// Elaborate a result term, sending its value to the continuation `cont`.
///
/// # Specification
/// - ensures: `⟨x |ε cont⟩` for a variable, `⟨K(p̄) |ε cont⟩` for a constructor
///   of producers, `⟨head |ε g(rest…; cont)⟩` for a tail operation, and a
///   single-argument constructor wrapping anything else flattened into a
///   return-side frame `K⁻(cont)` around its argument's elaboration.
/// - fails: [`ElaborateError::UnsupportedShape`] for a several-argument
///   constructor wrapping an operation, and as [`operation_cut`] fails.
/// - panics: none.
/// - intension: a loop that descends one constructor per turn, so nesting costs
///   no stack.
///
/// # Errors
/// As the failure clause states.
fn elaborate_result(
    term: TermNode<'_>,
    cont: ConsPat,
    polarity: Polarity,
) -> Result<CmdPat, ElaborateError>
{
    let mut current = term;
    let mut cont = cont;
    loop {
        match current.view() {
            | TermView::Var(name) => {
                return Ok(CmdPat::cut(polarity, ProdPat::meta(hole(name)), cont));
            },
            | TermView::Op { name, args } => return operation_cut(name, args, cont, polarity),
            | TermView::Ctor { name, args } => {
                if let Ok(producers) = elaborate_producers(args.clone()) {
                    return Ok(CmdPat::cut(
                        polarity,
                        ProdPat::ctor(sym(name), producers),
                        cont,
                    ));
                }
                let mut args = args;
                let (Some(inner), None) = (args.next(), args.next())
                else {
                    return Err(ElaborateError::UnsupportedShape);
                };
                cont = ConsPat::frame(sym(name), cont);
                current = inner;
            },
        }
    }
}

/// Elaborate a term as a producer pattern: a variable or a constructor of
/// producers.
///
/// # Specification
/// - ensures: the producer pattern of a variable or of a constructor whose
///   arguments are all producers, argument order kept.
/// - fails: [`ElaborateError::UnsupportedShape`] when the term holds an
///   operation application.
/// - panics: none.
/// - intension: an explicit stack of constructors awaiting their arguments, so
///   nesting costs no call stack.
///
/// # Errors
/// As the failure clause states.
fn elaborate_producer(term: TermNode<'_>) -> Result<ProdPat, ElaborateError>
{
    /// A constructor whose arguments are being elaborated.
    struct Pending<'term>
    {
        /// The constructor's name.
        name: &'term Name,
        /// The arguments not yet elaborated.
        rest: TermArgs<'term>,
        /// The arguments elaborated so far, in order.
        built: Vec<ProdPat>,
    }

    let mut pending: Vec<Pending<'_>> = Vec::new();
    let mut current = term;
    loop {
        let mut value = match current.view() {
            | TermView::Var(name) => ProdPat::meta(hole(name)),
            | TermView::Op { .. } => return Err(ElaborateError::UnsupportedShape),
            | TermView::Ctor { name, mut args } => match args.next() {
                | Some(first) => {
                    let built = Vec::with_capacity(args.len().saturating_add(1));
                    pending.push(Pending {
                        name,
                        rest: args,
                        built,
                    });
                    current = first;
                    continue;
                },
                | None => ProdPat::ctor(sym(name), []),
            },
        };
        // Hand the finished value up until a constructor still awaits an
        // argument, which becomes the next term to descend into.
        loop {
            let Some(mut top) = pending.pop()
            else {
                return Ok(value);
            };
            top.built.push(value);
            if let Some(next) = top.rest.next() {
                pending.push(top);
                current = next;
                break;
            }
            value = ProdPat::ctor(sym(top.name), top.built);
        }
    }
}

/// Elaborate every term of `terms` as a producer pattern.
///
/// # Specification
/// - ensures: one producer per term, in order, when every term is a producer.
/// - fails: [`ElaborateError::UnsupportedShape`] at the first term that is not.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn elaborate_producers(terms: TermArgs<'_>) -> Result<Vec<ProdPat>, ElaborateError>
{
    let mut out = Vec::with_capacity(terms.len());
    for term in terms {
        let producer = elaborate_producer(term)?;
        out.push(producer);
    }
    Ok(out)
}

/// The cell-layer symbol a description name spells.
///
/// # Specification
/// trivial.
fn sym(name: &Name) -> Sym
{
    Sym::from(name.as_ref())
}

/// The cell-layer hole a pattern variable spells.
///
/// # Specification
/// trivial.
fn hole(name: &Name) -> HoleName
{
    HoleName::from(name.as_ref())
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;
    use alloc::string::ToString as _;
    use alloc::vec;

    use gandr_theory_cell_complexes::CellContractumUse;
    use gandr_theory_cell_complexes::CellCount;
    use gandr_theory_cell_complexes::MetaVar;
    use gandr_theory_cell_complexes::StepGrowth;
    use gandr_theory_levitation::Attrs;
    use gandr_theory_levitation::BridgeArity;
    use gandr_theory_levitation::CircuitBody;
    use gandr_theory_levitation::CircuitFrame;
    use gandr_theory_levitation::CircuitNode;
    use gandr_theory_levitation::CircuitRedex;
    use gandr_theory_levitation::Code;
    use gandr_theory_levitation::CtorDesc;
    use gandr_theory_levitation::FrameHead;
    use gandr_theory_levitation::FreeTerm;
    use gandr_theory_levitation::NominalId;
    use gandr_theory_levitation::NominalSerial;
    use gandr_theory_levitation::SortRef;
    use gandr_theory_levitation::SurfaceSpan;
    use gandr_theory_levitation::TermPositionIndex;
    use gandr_theory_levitation::derive_boundaries;
    use quenchant_shape::shape::Maybe;

    use super::*;

    /// The grade a test description's fields would carry; no field here is
    /// graded.
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    enum Ungraded {}

    #[test]
    fn add_zero_elaborates_to_a_cut_against_the_operation_frame()
    {
        // rule add(Zero, n) ==> n.
        let f = face(
            FreeTerm::op("add", [FreeTerm::ctor("Zero", []), FreeTerm::var("n")]),
            FreeTerm::var("n"),
        );
        let cell = elaborate_rule(&f, DeclPolarity::Data).expect("the direct case elaborates");
        assert_eq!(
            &CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Zero", []),
                ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta(RETURN_CONT)),
            ),
            cell.lhs(),
            "⟨Zero | add(n; $ret)⟩"
        );
        assert_eq!(
            &CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("n"),
                ConsPat::meta(RETURN_CONT)
            ),
            cell.rhs(),
            "⟨n | $ret⟩"
        );
    }

    #[test]
    fn add_succ_flattens_the_wrapping_constructor_into_a_frame()
    {
        // rule add(Succ(m), n) ==> Succ(add(m, n)).
        let f = face(
            FreeTerm::op("add", [
                FreeTerm::ctor("Succ", [FreeTerm::var("m")]),
                FreeTerm::var("n"),
            ]),
            FreeTerm::ctor("Succ", [FreeTerm::op("add", [
                FreeTerm::var("m"),
                FreeTerm::var("n"),
            ])]),
        );
        let cell = elaborate_rule(&f, DeclPolarity::Data).expect("the flattening case elaborates");
        assert_eq!(
            &CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::op(
                    "add",
                    [ProdPat::meta("n")],
                    ConsPat::frame("Succ", ConsPat::meta(RETURN_CONT)),
                ),
            ),
            cell.rhs(),
            "⟨m | add(n; Succ⁻($ret))⟩"
        );
    }

    #[test]
    fn a_non_operation_lhs_is_declined()
    {
        let f = face(FreeTerm::var("x"), FreeTerm::var("x"));
        assert_eq!(
            Err(ElaborateError::LhsNotOperation),
            elaborate_rule(&f, DeclPolarity::Data),
            "a rule rewrites an operation"
        );
    }

    #[test]
    fn a_whole_description_elaborates_frame_and_rule_cells()
    {
        let desc = nat_with([add_op()], [add_zero_face(), add_succ_face()]);
        let elaborated = elaborate_data_desc(&desc);
        assert!(
            elaborated.declined_faces.is_empty(),
            "both rules are in the supported fragment: {:?}",
            elaborated.declined_faces
        );
        assert!(
            elaborated.declined_opers.is_empty(),
            "a single-output `add` is admitted"
        );
        assert_eq!(
            CellCount::from(4_usize),
            elaborated.store.len(),
            "two frame cells (Zero⁻, Succ⁻) and two rule cells"
        );
    }

    #[test]
    fn a_description_whose_rule_copies_a_hole_is_refused()
    {
        // `rule and(x, x) ==> x`, the idempotence law written with a repeated
        // hole: ⟨x | and(x; $ret)⟩ ~> ⟨x | $ret⟩ copies the producer hole `x`.
        let desc = bit_with([face(
            FreeTerm::op("and", [FreeTerm::var("x"), FreeTerm::var("x")]),
            FreeTerm::var("x"),
        )]);
        let elaborated = elaborate_data_desc(&desc);
        assert_eq!(
            CellCount::from(1_usize),
            elaborated.store.len(),
            "only the Off frame cell is admitted"
        );
        let [(index, ElaborateError::NonLinear(ref refusal))] = *elaborated.declined_faces
        else {
            panic!(
                "the one decline is the copy refusal: {:?}",
                elaborated.declined_faces
            );
        };
        assert_eq!(
            DeclinedFaceIndex::from(0_usize),
            index,
            "the decline is reported against the face's index"
        );
        assert_eq!(
            &MetaVar::producer("x"),
            refusal.copied(),
            "the diagnostic names the copied hole"
        );
    }

    #[test]
    fn a_repeated_hole_and_a_mixed_polarity_hole_earn_distinct_refusals()
    {
        // Face 0 copies `x`. Face 1 spells its variable `$ret`, so the
        // elaborated cell ⟨$ret | seam($ret)⟩ wears one name as a producer and
        // as its continuation: linear per hole and category, so the copy check
        // admits it, and the polarity check refuses it. Face 2 has both faults
        // and is refused for the copy, which is decided first.
        let desc = bit_with([
            face(
                FreeTerm::op("and", [FreeTerm::var("x"), FreeTerm::var("x")]),
                FreeTerm::var("x"),
            ),
            face(
                FreeTerm::op("seam", [FreeTerm::var(RETURN_CONT)]),
                FreeTerm::ctor("Off", []),
            ),
            face(
                FreeTerm::op("both", [
                    FreeTerm::var(RETURN_CONT),
                    FreeTerm::var(RETURN_CONT),
                ]),
                FreeTerm::ctor("Off", []),
            ),
        ]);
        let elaborated = elaborate_data_desc(&desc);
        let [
            (copy_index, ElaborateError::NonLinear(ref copy)),
            (seam_index, ElaborateError::MixedPolarity(ref seam)),
            (both_index, ElaborateError::NonLinear(ref both)),
        ] = *elaborated.declined_faces
        else {
            panic!(
                "a copy, a mixed-polarity hole, and the copy again: {:?}",
                elaborated.declined_faces
            );
        };
        assert_eq!(
            [0_usize, 1_usize, 2_usize].map(DeclinedFaceIndex::from),
            [copy_index, seam_index, both_index],
            "each refusal is reported against its own face"
        );
        assert_eq!(&MetaVar::producer("x"), copy.copied(), "the copy is named");
        assert_eq!(
            &HoleName::from(RETURN_CONT),
            seam.hole(),
            "the hole worn at both polarities is named"
        );
        assert_eq!(
            &MetaVar::producer(RETURN_CONT),
            both.copied(),
            "a cell with both faults is refused for the copy"
        );
        let copy_text = copy.to_string();
        let seam_text = seam.to_string();
        assert!(
            seam_text.contains("mixed-polarity hole: `$ret`")
                && seam_text.contains("Give the variable a name of its own"),
            "the seam diagnostic names the hole and the respelling: {seam_text}"
        );
        assert!(
            copy_text.contains("non-linear cell pattern") && !seam_text.contains("non-linear"),
            "and the two diagnostics are distinct: {copy_text} / {seam_text}"
        );
        assert_eq!(
            CellCount::from(1_usize),
            elaborated.store.len(),
            "no refused face reaches the store"
        );
    }

    #[test]
    fn a_codata_declarations_cells_all_cut_at_its_eta_polarity()
    {
        // The wrapper declaration with a circuit rule beside its inverse face,
        // at both polarities: every cell the declaration contributes cuts at
        // the polarity its η cell requires.
        for (polarity, expected) in [
            (DeclPolarity::Data, Polarity::Positive),
            (DeclPolarity::Codata, Polarity::Negative),
        ] {
            let desc = wrapper(polarity).with_circuits([unwrap_cong_rule()]);
            let elaborated = elaborate_data_desc(&desc);
            assert!(
                elaborated.declined_faces.is_empty(),
                "{polarity:?}: the inverse face is admitted"
            );
            let [CircuitElaboration::Admitted { .. }] = *elaborated.circuits
            else {
                panic!(
                    "{polarity:?}: the circuit rule is admitted: {:?}",
                    elaborated.circuits
                );
            };
            let EtaElaboration::Minted(ref eta) = elaborated.eta
            else {
                panic!("{polarity:?}: the η cell is minted: {:?}", elaborated.eta);
            };
            let mut provenances = Vec::new();
            for (id, cell) in elaborated.store.iter() {
                assert_eq!(
                    expected,
                    cell.polarity(),
                    "{polarity:?}: cell {id:?} ({:?}) cuts at the declaration's polarity",
                    cell.provenance()
                );
                assert_eq!(
                    cell.polarity(),
                    cell.rhs().polarity(),
                    "{polarity:?}: and both of its faces do"
                );
                provenances.push(cell.provenance());
            }
            assert_eq!(
                vec![
                    CellProvenance::FrameDefining,
                    CellProvenance::SurfaceRule,
                    CellProvenance::SurfaceRule,
                    CellProvenance::Eta(eta_kind(polarity)),
                ],
                provenances,
                "{polarity:?}: the frame, rule, circuit and η cells are all checked"
            );
            assert_eq!(1, eta.len(), "{polarity:?}: one η cell");
        }
    }

    #[test]
    fn the_positive_frame_cell_is_the_frame_defining_cell()
    {
        let ctor = Sym::from("Succ");
        assert_eq!(
            frame_defining_cell(&ctor),
            frame_cell(&ctor, Polarity::Positive),
            "a data declaration's frame cell is the cell layer's own"
        );
        let negative = frame_cell(&ctor, Polarity::Negative);
        assert_eq!(
            (Polarity::Negative, Polarity::Negative),
            (negative.polarity(), negative.rhs().polarity()),
            "a codata declaration's is the same cell cut negative"
        );
    }

    #[test]
    fn a_single_redex_circuit_rule_reaches_the_store()
    {
        let desc = nat_with([add_op()], []).with_circuits([cong1_rule()]);
        let elaborated = elaborate_data_desc(&desc);
        let [
            CircuitElaboration::Admitted {
                cell,
                ref composite,
            },
        ] = *elaborated.circuits
        else {
            panic!("the gate admits the rule: {:?}", elaborated.circuits);
        };
        assert_eq!(
            CellCount::from(3_usize),
            elaborated.store.len(),
            "the rule's cell joins the two constructor frame cells"
        );
        assert!(
            matches!(elaborated.store.get(cell), Maybe::Present(_)),
            "the reported identifier addresses the rule's cell"
        );
        assert_eq!(
            Maybe::Present(vec![TermPositionIndex::from(0_usize)]),
            composite.active_position(),
            "the redex sits at `add`'s first argument"
        );
    }

    #[test]
    fn a_two_redex_circuit_rule_is_declined_its_composite()
    {
        let body = CircuitBody::new(
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
        );
        let desc = nat_with([add_op()], []).with_circuits([rule_over("cong2", body)]);
        let elaborated = elaborate_data_desc(&desc);
        assert_eq!(
            CellCount::from(2_usize),
            elaborated.store.len(),
            "the rule's cell never enters the store"
        );
        let [
            CircuitElaboration::Declined(ElaborateError::NoCircuitComposite(
                CircuitElaborationError::ManyRedexOccurrences { ref occurrences },
            )),
        ] = *elaborated.circuits
        else {
            panic!(
                "the decline is the composite refusal, not a face decline: {:?}",
                elaborated.circuits
            );
        };
        assert_eq!(2, occurrences.len(), "both occurrences are carried");
    }

    #[test]
    fn a_circuit_rule_whose_boundary_copies_a_hole_is_refused()
    {
        // One interface wire feeding both arguments of one frame: the derived
        // source is `add(x, x)`, refused at the admission seam for copying a
        // hole. The body is frames-only on purpose: a reconvergent redex is two
        // occurrences of one rewrite, declined a composite before the seam.
        let body = CircuitBody::new(
            [CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Op("add".into()),
                [FreeTerm::var("x"), FreeTerm::var("x")],
                "z",
            ))],
            "z",
        );
        let desc = nat_with([add_op()], []).with_circuits([rule_over("dup", body)]);
        let elaborated = elaborate_data_desc(&desc);
        assert_eq!(
            CellCount::from(2_usize),
            elaborated.store.len(),
            "the copying rule never enters the store"
        );
        let [CircuitElaboration::Declined(ElaborateError::NonLinear(ref refusal))] =
            *elaborated.circuits
        else {
            panic!("the decline is the copy refusal: {:?}", elaborated.circuits);
        };
        assert_eq!(
            &MetaVar::producer("x"),
            refusal.copied(),
            "the diagnostic names the copied hole"
        );
    }

    #[test]
    fn a_circuit_rule_applying_a_declined_operation_is_declined_at_the_gate()
    {
        let body = CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::var("w"),
                    "w",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("divmod".into()),
                    [FreeTerm::var("w"), FreeTerm::var("y")],
                    "z",
                )),
            ],
            "z",
        );
        let desc = nat_with([divmod_op()], []).with_circuits([rule_over("over", body)]);
        let elaborated = elaborate_data_desc(&desc);
        assert_eq!(
            vec![CircuitElaboration::Declined(
                ElaborateError::UnrepresentableOperation
            )],
            elaborated.circuits,
            "the operation gate binds where the block applies a declined operation"
        );
    }

    #[test]
    fn an_admitted_operation_reports_its_declared_inputs()
    {
        let elaborated = elaborate_data_desc(&nat_with([add_op()], []));
        assert_eq!(
            vec![OpFrame {
                op: Sym::from("add"),
                inputs: OperationInputCount::from(2_usize),
            }],
            elaborated.opers,
            "the admitted operation carries its symbol and its declared input count"
        );
    }

    #[test]
    fn a_many_out_operation_is_declined_and_declines_its_faces()
    {
        // `op divmod(m, n) -> (q, r)`: two output ports, and an operation frame
        // has exactly one return continuation.
        let desc = nat_with([divmod_op()], [face(
            FreeTerm::op("divmod", [FreeTerm::ctor("Zero", []), FreeTerm::var("n")]),
            FreeTerm::ctor("Zero", []),
        )]);
        let elaborated = elaborate_data_desc(&desc);
        assert_eq!(
            vec![(DeclinedOpIndex::from(0_usize), OpElaborateError::ManyOutput)],
            elaborated.declined_opers,
            "a many-out arity has no operation frame in this grammar"
        );
        assert!(elaborated.opers.is_empty(), "nothing was admitted");
        assert_eq!(
            vec![(
                DeclinedFaceIndex::from(0_usize),
                ElaborateError::UnrepresentableOperation
            )],
            elaborated.declined_faces,
            "a face over a declined operation is declined, not silently narrowed"
        );
        assert_eq!(
            CellCount::from(2_usize),
            elaborated.store.len(),
            "only the two constructor frame cells reached the store"
        );
    }

    #[test]
    fn an_aggregating_arity_and_an_outputless_one_are_declined_apart()
    {
        // One output port fed by two monomials, and an operation with no
        // output port at all.
        let aggregated = OperDesc::new(
            "merge",
            BridgeArity::new(
                [SortRef::new("p", "Nat"), SortRef::new("q", "Nat")],
                [1_u32, 1_u32],
                [0_u32, 1_u32],
                [0_u32, 0_u32],
                [SortRef::new("r", "Nat")],
            ),
            Attrs::empty(),
        );
        let outputless = OperDesc::new(
            "sink",
            BridgeArity::new([SortRef::new("p", "Nat")], [], [], [], []),
            Attrs::empty(),
        );
        let elaborated = elaborate_data_desc(&nat_with([aggregated, outputless], []));
        assert_eq!(
            vec![
                (
                    DeclinedOpIndex::from(0_usize),
                    OpElaborateError::AggregatedOutput
                ),
                (DeclinedOpIndex::from(1_usize), OpElaborateError::NoOutput),
            ],
            elaborated.declined_opers,
            "the aggregating and the outputless arity decline for their own reasons"
        );
    }

    #[test]
    fn a_face_over_an_admitted_operation_survives_the_gate()
    {
        // The declined operation is not the one this face applies.
        let desc = nat_with(
            [
                op("id", [SortRef::new("x", "Nat")]),
                OperDesc::new(
                    "divmod",
                    BridgeArity::new(
                        [SortRef::new("m", "Nat")],
                        [1_u32, 1_u32],
                        [0_u32, 0_u32],
                        [0_u32, 1_u32],
                        [SortRef::new("q", "Nat"), SortRef::new("r", "Nat")],
                    ),
                    Attrs::empty(),
                ),
            ],
            [face(
                FreeTerm::op("id", [FreeTerm::ctor("Zero", [])]),
                FreeTerm::ctor("Zero", []),
            )],
        );
        let elaborated = elaborate_data_desc(&desc);
        assert!(
            elaborated.declined_faces.is_empty(),
            "the face applies `id`, which is admitted"
        );
        assert_eq!(
            CellCount::from(3_usize),
            elaborated.store.len(),
            "two frame cells and the one rule cell"
        );
    }

    #[test]
    fn a_duplicating_contractum_is_admitted_and_reported()
    {
        // The admission seam governs the redex side alone, so a rule whose
        // right-hand side duplicates one hole and drops another is admitted,
        // and its growth is reported by the cell's derived metadata.
        let desc = nat_with(
            [
                op("f", [SortRef::new("x", "Nat"), SortRef::new("y", "Nat")]),
                op("h", [SortRef::new("u", "Nat"), SortRef::new("v", "Nat")]),
            ],
            [face(
                FreeTerm::op("f", [FreeTerm::var("x"), FreeTerm::var("y")]),
                FreeTerm::op("h", [FreeTerm::var("x"), FreeTerm::var("x")]),
            )],
        );
        let elaborated = elaborate_data_desc(&desc);
        assert!(
            elaborated.declined_faces.is_empty(),
            "the duplicating rule is admitted"
        );
        let rule_cell = elaborated
            .store
            .iter()
            .map(|(_, cell)| cell)
            .find(|cell| cell.provenance() == CellProvenance::SurfaceRule)
            .expect("the rule cell is in the store");
        assert_eq!(
            StepGrowth::Duplicating,
            rule_cell.meta().step_growth(),
            "and its growth is reported"
        );
        let use_of = |name: &str| {
            rule_cell
                .meta()
                .vars()
                .iter()
                .find(|var| *var.var() == MetaVar::producer(name))
                .map(gandr_theory_cell_complexes::CellVarMeta::contractum)
        };
        assert_eq!(
            Some(CellContractumUse::Repeated),
            use_of("x"),
            "the duplicated hole is named"
        );
        assert_eq!(
            Some(CellContractumUse::Erased),
            use_of("y"),
            "and the dropped hole beside it"
        );
    }

    #[test]
    fn a_wrapper_description_mints_its_eta_cell()
    {
        let elaborated = elaborate_data_desc(&wrapper(DeclPolarity::Data));
        let EtaElaboration::Minted(ref minted) = elaborated.eta
        else {
            panic!(
                "the declaration states both halves of the law: {:?}",
                elaborated.eta
            );
        };
        let [id] = **minted
        else {
            panic!("exactly one η cell is minted: {minted:?}");
        };
        let Maybe::Present(cell) = elaborated.store.get(id)
        else {
            panic!("the η cell is in the store");
        };
        assert_eq!(
            CellProvenance::Eta(EtaKind::Data),
            cell.provenance(),
            "a `data` declaration's η law is the data one"
        );
        assert_eq!(
            &CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta(ETA_OBSERVED),
                ConsPat::op(
                    "unwrap",
                    [],
                    ConsPat::frame("MkWrap", ConsPat::meta(RETURN_CONT))
                ),
            ),
            cell.lhs(),
            "a positive cut against the destructor's frame wrapping the constructor's"
        );
        assert_eq!(
            &CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta(ETA_OBSERVED),
                ConsPat::meta(RETURN_CONT)
            ),
            cell.rhs(),
            "and the contractum drops the whole pair, which is what cancelling means"
        );
    }

    #[test]
    fn a_codata_declaration_mints_its_eta_cell_at_a_negative_cut()
    {
        let elaborated = elaborate_data_desc(&wrapper(DeclPolarity::Codata));
        let EtaElaboration::Minted(ref minted) = elaborated.eta
        else {
            panic!(
                "the codata declaration mints its η cell: {:?}",
                elaborated.eta
            );
        };
        let [id] = **minted
        else {
            panic!("exactly one η cell is minted: {minted:?}");
        };
        let Maybe::Present(cell) = elaborated.store.get(id)
        else {
            panic!("the η cell is in the store");
        };
        assert_eq!(
            CellProvenance::Eta(EtaKind::Codata),
            cell.provenance(),
            "a `codata` declaration's η law is the codata one"
        );
        assert_eq!(
            Polarity::Negative,
            cell.polarity(),
            "and codata η is valid only at a negative cut"
        );
    }

    #[test]
    fn a_multi_constructor_description_declines_its_eta_cell()
    {
        let desc = nat_with([op("pred", [SortRef::new("n", "Nat")])], [face(
            FreeTerm::op("pred", [FreeTerm::ctor("Succ", [FreeTerm::var("m")])]),
            FreeTerm::var("m"),
        )]);
        let elaborated = elaborate_data_desc(&desc);
        assert_eq!(
            EtaElaboration::Declined(EtaElaborateError::NotSingleConstructor(
                ConstructorCount::from(2_usize)
            )),
            elaborated.eta,
            "the decline names the missing half, with the count that decides it"
        );
    }

    #[test]
    fn an_operation_with_no_inverse_face_licenses_no_eta_cell()
    {
        // One constructor and one operation, but no face says the operation
        // destructs the constructor.
        let desc = wrapper_with(
            "twice",
            FreeTerm::op("twice", [FreeTerm::ctor("MkWrap", [FreeTerm::var("x")])]),
            FreeTerm::ctor("MkWrap", [FreeTerm::var("x")]),
        );
        let elaborated = elaborate_data_desc(&desc);
        assert_eq!(
            EtaElaboration::Declined(EtaElaborateError::NoInverseFace),
            elaborated.eta,
            "an operation's presence is not the licence; the inverse face is"
        );
    }

    #[test]
    fn the_inverse_face_is_recognized_by_its_shape_and_nothing_looser()
    {
        let unwrap_of = |inner: FreeTerm| FreeTerm::op("unwrap", [inner]);
        let mk = |inner: FreeTerm| FreeTerm::ctor("MkWrap", [inner]);
        for (label, lhs, rhs) in [
            (
                "the face applies a different operation",
                FreeTerm::op("other", [mk(FreeTerm::var("x"))]),
                FreeTerm::var("x"),
            ),
            (
                "the operation is applied to a variable rather than a constructor",
                unwrap_of(FreeTerm::var("x")),
                FreeTerm::var("x"),
            ),
            (
                "the face's left-hand side is not an operation application at all",
                mk(FreeTerm::var("x")),
                FreeTerm::var("x"),
            ),
            (
                "the operation is applied to a different constructor",
                unwrap_of(FreeTerm::ctor("Other", [FreeTerm::var("x")])),
                FreeTerm::var("x"),
            ),
            (
                "the constructor's field is not a variable",
                unwrap_of(mk(FreeTerm::ctor("Zero", []))),
                FreeTerm::var("x"),
            ),
            (
                "the result is a different variable",
                unwrap_of(mk(FreeTerm::var("x"))),
                FreeTerm::var("y"),
            ),
            (
                "the result is not a variable at all",
                unwrap_of(mk(FreeTerm::var("x"))),
                mk(FreeTerm::var("x")),
            ),
            (
                "the operation takes more than the constructed argument",
                FreeTerm::op("unwrap", [mk(FreeTerm::var("x")), FreeTerm::var("y")]),
                FreeTerm::var("x"),
            ),
            (
                "the constructor takes more than one field",
                unwrap_of(FreeTerm::ctor("MkWrap", [
                    FreeTerm::var("x"),
                    FreeTerm::var("y"),
                ])),
                FreeTerm::var("x"),
            ),
        ] {
            let elaborated = elaborate_data_desc(&wrapper_with("unwrap", lhs, rhs));
            assert_eq!(
                EtaElaboration::Declined(EtaElaborateError::NoInverseFace),
                elaborated.eta,
                "{label}: no η cell, because the licence is the inverse face's shape"
            );
        }

        // A left-hand side that is not an operation is outside the fragment
        // too, so the face is declined as well: the η licence and the
        // elaboration gate are separate verdicts on one shape.
        let elaborated = elaborate_data_desc(&wrapper_with(
            "unwrap",
            mk(FreeTerm::var("x")),
            FreeTerm::var("x"),
        ));
        assert_eq!(
            vec![(
                DeclinedFaceIndex::from(0_usize),
                ElaborateError::LhsNotOperation
            )],
            elaborated.declined_faces,
            "the face is declined against its own index, naming the shape"
        );
    }

    /// A face over two terms, with no derived metadata and an empty span.
    ///
    /// # Specification
    /// trivial.
    fn face(
        lhs: FreeTerm,
        rhs: FreeTerm,
    ) -> RuleFace
    {
        RuleFace::new(lhs, rhs, Vec::new(), SurfaceSpan::default())
    }

    /// A single-output operation over the given input ports.
    ///
    /// # Specification
    /// trivial.
    fn op<N, I>(
        name: N,
        inputs: I,
    ) -> OperDesc
    where
        N: Into<Name>,
        I: Into<Box<[SortRef]>>,
    {
        OperDesc::new(
            name,
            BridgeArity::single_output(inputs, SortRef::new("out", "Nat")),
            Attrs::empty(),
        )
    }

    /// `op add(m, n) -> Nat`.
    ///
    /// # Specification
    /// trivial.
    fn add_op() -> OperDesc
    {
        op("add", [SortRef::new("m", "Nat"), SortRef::new("n", "Nat")])
    }

    /// `op divmod(m, n) -> (q, r)`: two output ports, two monomials.
    ///
    /// # Specification
    /// trivial.
    fn divmod_op() -> OperDesc
    {
        OperDesc::new(
            "divmod",
            BridgeArity::new(
                [SortRef::new("m", "Nat"), SortRef::new("n", "Nat")],
                [2_u32, 2_u32],
                [0_u32, 1_u32, 0_u32, 1_u32],
                [0_u32, 1_u32],
                [SortRef::new("q", "Nat"), SortRef::new("r", "Nat")],
            ),
            Attrs::empty(),
        )
    }

    /// `rule add(Zero, n) ==> n`.
    ///
    /// # Specification
    /// trivial.
    fn add_zero_face() -> RuleFace
    {
        face(
            FreeTerm::op("add", [FreeTerm::ctor("Zero", []), FreeTerm::var("n")]),
            FreeTerm::var("n"),
        )
    }

    /// `rule add(Succ(m), n) ==> Succ(add(m, n))`.
    ///
    /// # Specification
    /// trivial.
    fn add_succ_face() -> RuleFace
    {
        face(
            FreeTerm::op("add", [
                FreeTerm::ctor("Succ", [FreeTerm::var("m")]),
                FreeTerm::var("n"),
            ]),
            FreeTerm::ctor("Succ", [FreeTerm::op("add", [
                FreeTerm::var("m"),
                FreeTerm::var("n"),
            ])]),
        )
    }

    /// A circuit rule over `body`, declared at the sphere its wiring derives,
    /// as the surface route supplies it.
    ///
    /// # Specification
    /// - panics: when the body derives no boundary pair, which is a fixture
    ///   defect.
    fn rule_over<N>(
        name: N,
        body: CircuitBody,
    ) -> CircuitRule
    where
        N: Into<Name>,
    {
        let derived = derive_boundaries(&body).expect("the fixture bodies derive their boundaries");
        CircuitRule::new(name, face(derived.source, derived.target), body)
    }

    /// The single-redex congruence body `*p(-x, +x′); *add(-x′, -y, +z);`.
    ///
    /// # Specification
    /// trivial.
    fn cong1_rule() -> CircuitRule
    {
        rule_over(
            "cong1",
            CircuitBody::new(
                [
                    CircuitNode::Redex(CircuitRedex::new(
                        "p",
                        FreeTerm::var("x"),
                        FreeTerm::var("x\u{2032}"),
                        "x\u{2032}",
                    )),
                    CircuitNode::Frame(CircuitFrame::new(
                        FrameHead::Op("add".into()),
                        [FreeTerm::var("x\u{2032}"), FreeTerm::var("y")],
                        "z",
                    )),
                ],
                "z",
            ),
        )
    }

    /// The single-redex congruence body under `unwrap`:
    /// `*p(-w, +w′); *unwrap(-w′, +z);`.
    ///
    /// # Specification
    /// trivial.
    fn unwrap_cong_rule() -> CircuitRule
    {
        rule_over(
            "under",
            CircuitBody::new(
                [
                    CircuitNode::Redex(CircuitRedex::new(
                        "p",
                        FreeTerm::var("w"),
                        FreeTerm::var("w\u{2032}"),
                        "w\u{2032}",
                    )),
                    CircuitNode::Frame(CircuitFrame::new(
                        FrameHead::Op("unwrap".into()),
                        [FreeTerm::var("w\u{2032}")],
                        "z",
                    )),
                ],
                "z",
            ),
        )
    }

    /// A one-constructor `Bit` description carrying the given rules.
    ///
    /// # Specification
    /// trivial.
    fn bit_with<C>(rules: C) -> SignDesc<Ungraded>
    where
        C: Into<Box<[RuleFace]>>,
    {
        SignDesc::new(
            NominalId::new(NominalSerial::from(0_u64), "Bit"),
            Vec::new(),
            [CtorDesc::new("Off", Code::unit(), "Bit", Attrs::empty())],
            Vec::new(),
            rules,
            DeclPolarity::Data,
            Attrs::empty(),
        )
    }

    /// A `Nat` description with two constructors plus the given operations
    /// and faces.
    ///
    /// # Specification
    /// trivial.
    fn nat_with<O, C>(
        opers: O,
        rules: C,
    ) -> SignDesc<Ungraded>
    where
        O: Into<Box<[OperDesc]>>,
        C: Into<Box<[RuleFace]>>,
    {
        SignDesc::new(
            NominalId::new(NominalSerial::from(0_u64), "Nat"),
            Vec::new(),
            [
                CtorDesc::new("Zero", Code::unit(), "Nat", Attrs::empty()),
                CtorDesc::new("Succ", Code::var("Nat"), "Nat", Attrs::empty()),
            ],
            opers,
            rules,
            DeclPolarity::Data,
            Attrs::empty(),
        )
    }

    /// A single-constructor `Wrap` data description whose one operation is
    /// `oper` and whose one face is `lhs ==> rhs`.
    ///
    /// # Specification
    /// trivial.
    fn wrapper_with<N>(
        oper: N,
        lhs: FreeTerm,
        rhs: FreeTerm,
    ) -> SignDesc<Ungraded>
    where
        N: Into<Name>,
    {
        SignDesc::new(
            NominalId::new(NominalSerial::from(0_u64), "Wrap"),
            Vec::new(),
            [CtorDesc::new(
                "MkWrap",
                Code::var("Nat"),
                "Wrap",
                Attrs::empty(),
            )],
            [OperDesc::new(
                oper,
                BridgeArity::single_output([SortRef::new("w", "Wrap")], SortRef::new("out", "Nat")),
                Attrs::empty(),
            )],
            [face(lhs, rhs)],
            DeclPolarity::Data,
            Attrs::empty(),
        )
    }

    /// The single-constructor `Wrap` description whose `unwrap` operation
    /// carries the inverse face, at `polarity`.
    ///
    /// # Specification
    /// trivial.
    fn wrapper(polarity: DeclPolarity) -> SignDesc<Ungraded>
    {
        let mut desc = wrapper_with(
            "unwrap",
            FreeTerm::op("unwrap", [FreeTerm::ctor("MkWrap", [FreeTerm::var("x")])]),
            FreeTerm::var("x"),
        );
        desc.polarity = polarity;
        desc
    }
}
