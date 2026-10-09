//! The rows of the fragment's exercised table a run's settled declarations
//! carry, read off what the run produced.
//!
//! # Read from the report, never pinned
//!
//! A gate over an unpopulated set passes vacuously. The corpus's anti-vacuity
//! is asserted on these counts: every row a green fixture can carry has at
//! least one settled declaration carrying it. Nothing pins how many: adding a
//! fixture changes a count and reddens nothing.
//!
//! # A former has one direction
//!
//! The judgement fixes each former's mode — a lambda and a return check, a
//! force and an application synthesise — so a former standing in a body the
//! checker accepted was judged in its own direction. The direction rows are
//! read off the formers in accepted bodies.

use core::fmt;

use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::ConversionCount;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::Verdict;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Produced;
use gandr_surface_corpus::SettleReport;
use gandr_surface_corpus::Settlement;
use gandr_surface_lowering::DeclarationCount;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringRefusal;

/// One row of the fragment's exercised table that a green fixture can carry.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Row
{
    /// A lambda checks: a lambda in a body the checker accepted.
    LambdaChecks,
    /// A return checks: a return in a body the checker accepted.
    ReturnChecks,
    /// A force synthesises: a force in a body the checker accepted.
    ForceSynthesises,
    /// An application synthesises: an application in a body the checker
    /// accepted.
    ApplicationSynthesises,
    /// The subsumption bridge: an accepted body that crossed a conversion
    /// bridge, a synthesised type converted to the expected one.
    SubsumptionBridge,
    /// An undefined term name: a body naming no binder or earlier
    /// declaration, refused by the lowering.
    UndefinedTermName,
    /// An undefined type head: a signature naming a type former no table
    /// answers, refused by the lowering.
    UndefinedTypeHead,
    /// A shape refusal: a return checked against a type that is no returner.
    ShapeRefusal,
    /// A non-synthesisable head: a lambda in application-head position.
    NonSynthesisableHead,
    /// A non-synthesisable definition: an unsigned definition whose body is a
    /// thunk.
    NonSynthesisableDefinition,
    /// An engine capability boundary: a reserved form, parsed and declined by
    /// name.
    ReservedForm,
    /// An addressable obligation: a signature no definition completes, owed.
    AddressableObligation,
}

impl Row
{
    /// Every row, in the order the table lists them.
    pub const ALL: [Self; 12_usize] = [
        Self::LambdaChecks,
        Self::ReturnChecks,
        Self::ForceSynthesises,
        Self::ApplicationSynthesises,
        Self::SubsumptionBridge,
        Self::UndefinedTermName,
        Self::UndefinedTypeHead,
        Self::ShapeRefusal,
        Self::NonSynthesisableHead,
        Self::NonSynthesisableDefinition,
        Self::ReservedForm,
        Self::AddressableObligation,
    ];
}

impl fmt::Display for Row
{
    /// Writes the row as the table names it.
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
            | Self::LambdaChecks => "a lambda checks",
            | Self::ReturnChecks => "a return checks",
            | Self::ForceSynthesises => "a force synthesises",
            | Self::ApplicationSynthesises => "an application synthesises",
            | Self::SubsumptionBridge => "the subsumption bridge",
            | Self::UndefinedTermName => "an undefined term name",
            | Self::UndefinedTypeHead => "an undefined type head",
            | Self::ShapeRefusal => "a shape refusal",
            | Self::NonSynthesisableHead => "a non-synthesisable head",
            | Self::NonSynthesisableDefinition => "a non-synthesisable definition",
            | Self::ReservedForm => "an engine capability boundary",
            | Self::AddressableObligation => "an addressable obligation",
        })
    }
}

/// How many settled declarations carry each row.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Exercised
{
    /// [`Row::LambdaChecks`].
    lambda_checks: DeclarationCount,
    /// [`Row::ReturnChecks`].
    return_checks: DeclarationCount,
    /// [`Row::ForceSynthesises`].
    force_synthesises: DeclarationCount,
    /// [`Row::ApplicationSynthesises`].
    application_synthesises: DeclarationCount,
    /// [`Row::SubsumptionBridge`].
    subsumption_bridge: DeclarationCount,
    /// [`Row::UndefinedTermName`].
    undefined_term_name: DeclarationCount,
    /// [`Row::UndefinedTypeHead`].
    undefined_type_head: DeclarationCount,
    /// [`Row::ShapeRefusal`].
    shape_refusal: DeclarationCount,
    /// [`Row::NonSynthesisableHead`].
    non_synthesisable_head: DeclarationCount,
    /// [`Row::NonSynthesisableDefinition`].
    non_synthesisable_definition: DeclarationCount,
    /// [`Row::ReservedForm`].
    reserved_form: DeclarationCount,
    /// [`Row::AddressableObligation`].
    addressable_obligation: DeclarationCount,
}

impl fmt::Display for Exercised
{
    /// Writes each row with its count, in table order, separated by `; `.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let mut separator = "";
        for row in Row::ALL {
            write!(f, "{separator}{row} {}", usize::from(self.count(row)))?;
            separator = "; ";
        }
        Ok(())
    }
}

impl Exercised
{
    /// How many settled declarations carry `row`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn count(
        &self,
        row: Row,
    ) -> DeclarationCount
    {
        match row {
            | Row::LambdaChecks => self.lambda_checks,
            | Row::ReturnChecks => self.return_checks,
            | Row::ForceSynthesises => self.force_synthesises,
            | Row::ApplicationSynthesises => self.application_synthesises,
            | Row::SubsumptionBridge => self.subsumption_bridge,
            | Row::UndefinedTermName => self.undefined_term_name,
            | Row::UndefinedTypeHead => self.undefined_type_head,
            | Row::ShapeRefusal => self.shape_refusal,
            | Row::NonSynthesisableHead => self.non_synthesisable_head,
            | Row::NonSynthesisableDefinition => self.non_synthesisable_definition,
            | Row::ReservedForm => self.reserved_form,
            | Row::AddressableObligation => self.addressable_obligation,
        }
    }

    /// The rows no settled declaration carries, in table order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the rows whose count is zero, in [`Row::ALL`] order.
    /// - provides: the anti-vacuity question a gate asks of a run.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty count set misses every row, and a module
    ///   carrying a known subset misses exactly the rest.
    /// - witness: `exercised::tests::a_module_carries_exactly_its_rows`
    #[inline]
    #[must_use]
    pub fn missing(&self) -> Vec<Row>
    {
        Row::ALL
            .into_iter()
            .filter(|&row| usize::from(self.count(row)) == 0_usize)
            .collect()
    }

    /// Add `other`'s counts to these, saturating.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every row's count is the saturating sum of the two.
    /// - provides: one count set over every source of a run.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two disjoint count sets are absorbed and every row
    ///   asserted at its sum.
    /// - witness: `exercised::tests::absorbing_sums_every_row`
    #[inline]
    pub fn absorb(
        &mut self,
        other: &Self,
    )
    {
        for row in Row::ALL {
            let slot = self.slot(row);
            *slot = DeclarationCount::from(
                usize::from(*slot).saturating_add(usize::from(other.count(row))),
            );
        }
    }

    /// The rows the settled declarations of one source carry.
    ///
    /// # Specification
    /// - requires: `report` settled `module`, whose terms `arena` holds.
    /// - ensures: each settled declaration counts once in each row it carries,
    ///   however often the row's former stands in its body; an unsettled
    ///   declaration counts in no row. An accepted body carries the direction
    ///   row of each of the four formers standing in it and, when it crossed a
    ///   conversion bridge, the subsumption row. An owed signature carries the
    ///   obligation row. A refusal carries the row it witnesses: the lowering's
    ///   unresolved name or type head, or its decline of a reserved form; the
    ///   checker's shape refusal of a return, its refusal of a lambda where a
    ///   type is synthesised, or of a thunk that is an unsigned definition's
    ///   whole body.
    /// - provides: the exercised rows the runner's report carries.
    /// - fails: never; a node the arena does not hold contributes nothing.
    /// - panics: none.
    /// - intension: walks each accepted body once with an explicit worklist.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one module per row, and a near miss beside each
    ///   refusal row: a thunk refused below an unsigned definition's body,
    ///   another former's shape refusal, an unsettled declaration carrying a
    ///   row's shape.
    /// - witness: `exercised::tests::a_module_carries_exactly_its_rows`
    /// - witness: `exercised::tests::an_unsettled_declaration_carries_no_row`
    /// - witness: `exercised::tests::a_near_miss_carries_no_refusal_row`
    #[must_use]
    pub(crate) fn of(
        arena: &CoreArena,
        module: &LoweredModule<'_>,
        report: &SettleReport<'_>,
    ) -> Self
    {
        let mut exercised = Self::default();
        let mut worklist = Vec::new();
        for (declaration, lowered) in report.declarations().iter().zip(module.declarations()) {
            if declaration.settlement() == Settlement::Settled {
                let carried = carried(arena, declaration, lowered, &mut worklist);
                exercised.absorb(&carried);
            }
        }
        exercised
    }

    /// Mark `row` as carried, at most once.
    ///
    /// # Specification
    /// trivial.
    fn mark(
        &mut self,
        row: Row,
    )
    {
        *self.slot(row) = DeclarationCount::from(1_usize);
    }

    /// The count `row` is tallied in.
    ///
    /// # Specification
    /// trivial.
    const fn slot(
        &mut self,
        row: Row,
    ) -> &mut DeclarationCount
    {
        match row {
            | Row::LambdaChecks => &mut self.lambda_checks,
            | Row::ReturnChecks => &mut self.return_checks,
            | Row::ForceSynthesises => &mut self.force_synthesises,
            | Row::ApplicationSynthesises => &mut self.application_synthesises,
            | Row::SubsumptionBridge => &mut self.subsumption_bridge,
            | Row::UndefinedTermName => &mut self.undefined_term_name,
            | Row::UndefinedTypeHead => &mut self.undefined_type_head,
            | Row::ShapeRefusal => &mut self.shape_refusal,
            | Row::NonSynthesisableHead => &mut self.non_synthesisable_head,
            | Row::NonSynthesisableDefinition => &mut self.non_synthesisable_definition,
            | Row::ReservedForm => &mut self.reserved_form,
            | Row::AddressableObligation => &mut self.addressable_obligation,
        }
    }
}

/// The rows one settled declaration carries, each counted once.
///
/// # Specification
/// trivial.
fn carried(
    arena: &CoreArena,
    declaration: &DeclarationReport<'_>,
    lowered: &LoweredDeclaration<'_>,
    worklist: &mut Vec<Node>,
) -> Exercised
{
    let mut rows = Exercised::default();
    match declaration.produced() {
        | Produced::Judged(Verdict::Checked { body, evidence, .. }) => {
            formers(arena, body, worklist, &mut rows);
            bridged(evidence.conversions(), &mut rows);
        },
        | Produced::Judged(Verdict::Synthesised { body, synthesised }) => {
            formers(arena, body, worklist, &mut rows);
            bridged(synthesised.conversions(), &mut rows);
        },
        | Produced::Judged(Verdict::Owed(_)) => rows.mark(Row::AddressableObligation),
        | Produced::Judged(Verdict::Refused(refusal)) => checking_row(refusal, lowered, &mut rows),
        | Produced::Unlowered(refusal) => lowering_row(refusal, &mut rows),
        | Produced::Guarded(_) => {},
    }
    rows
}

/// Mark the subsumption row when `conversions` counts a crossing.
///
/// # Specification
/// trivial.
fn bridged(
    conversions: ConversionCount,
    rows: &mut Exercised,
)
{
    if conversions > ConversionCount::default() {
        rows.mark(Row::SubsumptionBridge);
    }
}

/// Mark the row a checker refusal witnesses, if any.
///
/// # Specification
/// trivial.
fn checking_row(
    refusal: CheckRefusal,
    lowered: &LoweredDeclaration<'_>,
    rows: &mut Exercised,
)
{
    match refusal {
        | CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::Returner,
            ..
        } => rows.mark(Row::ShapeRefusal),
        | CheckRefusal::NotSynthesisable {
            form: CheckingForm::Lambda(_),
        } => rows.mark(Row::NonSynthesisableHead),
        | CheckRefusal::NotSynthesisable {
            form: CheckingForm::Thunk(thunk),
        } => {
            if is_whole_unsigned_body(lowered, thunk) == WholeBody::Whole {
                rows.mark(Row::NonSynthesisableDefinition);
            }
        },
        | CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::Thunk | ExpectedShape::Arrow,
            ..
        }
        | CheckRefusal::NotSynthesisable {
            form: CheckingForm::Return(_) | CheckingForm::Hole(_),
        }
        | CheckRefusal::TypeMismatch(_)
        | CheckRefusal::UnknownConstant { .. }
        | CheckRefusal::OutOfFragment { .. }
        | CheckRefusal::UnboundIndex { .. }
        | CheckRefusal::BudgetExceeded { .. }
        | CheckRefusal::DanglingNode { .. }
        | CheckRefusal::AdmissionOrder { .. }
        | CheckRefusal::MachineInvariant => {},
    }
}

/// Whether `thunk` is the whole body of `lowered`, an unsigned definition.
///
/// # Specification
/// trivial.
fn is_whole_unsigned_body(
    lowered: &LoweredDeclaration<'_>,
    thunk: ValueId,
) -> WholeBody
{
    match lowered.outcome() {
        | DeclarationOutcome::Bodied { body } if body == thunk => WholeBody::Whole,
        | DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Completed { .. }
        | DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Refused(_) => WholeBody::Inner,
    }
}

/// Mark the row a lowering refusal witnesses, if any.
///
/// # Specification
/// trivial.
fn lowering_row(
    refusal: LoweringRefusal<'_>,
    rows: &mut Exercised,
)
{
    match refusal {
        | LoweringRefusal::UnresolvedName { .. } => rows.mark(Row::UndefinedTermName),
        | LoweringRefusal::UnresolvedTypeHead { .. } => rows.mark(Row::UndefinedTypeHead),
        | LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Reserved,
            ..
        } => rows.mark(Row::ReservedForm),
        | LoweringRefusal::OutOfFragment {
            boundary:
                FragmentBoundary::Unadmitted | FragmentBoundary::WrongSort | FragmentBoundary::Arity(_),
            ..
        }
        | LoweringRefusal::DuplicateSignature { .. }
        | LoweringRefusal::DuplicateDefinition { .. }
        | LoweringRefusal::MalformedLiteral { .. }
        | LoweringRefusal::MalformedForm { .. }
        | LoweringRefusal::UnknownAttribute { .. }
        | LoweringRefusal::DuplicateAttribute { .. }
        | LoweringRefusal::MissingPayload { .. }
        | LoweringRefusal::NonValuePayload { .. }
        | LoweringRefusal::IllTypedPayload { .. }
        | LoweringRefusal::BudgetExceeded { .. }
        | LoweringRefusal::GrammarMismatch { .. }
        | LoweringRefusal::UnknownMold { .. } => {},
    }
}

/// Mark the direction row of each of the four formers standing in the body
/// at `body`.
///
/// # Specification
/// trivial.
fn formers(
    arena: &CoreArena,
    body: ValueId,
    worklist: &mut Vec<Node>,
    rows: &mut Exercised,
)
{
    worklist.clear();
    worklist.push(Node::Value(body));
    while let Some(node) = worklist.pop() {
        match node {
            | Node::Value(id) => match arena.value(id) {
                | Some(&Value::Thunk(suspended)) => worklist.push(Node::Computation(suspended)),
                | Some(&Value::Pair(first, second)) => {
                    worklist.push(Node::Value(first));
                    worklist.push(Node::Value(second));
                },
                | Some(&Value::Injection(_, injected)) => worklist.push(Node::Value(injected)),
                | Some(&Value::Lift { body: lifted, .. }) => worklist.push(Node::Value(lifted)),
                | Some(
                    &(Value::Variable { .. }
                    | Value::Constant(_)
                    | Value::Unit
                    | Value::Literal(_)),
                )
                | None => {},
            },
            | Node::Computation(id) => match arena.computation(id) {
                | Some(&Computation::Lambda(under)) => {
                    rows.mark(Row::LambdaChecks);
                    worklist.push(Node::Computation(under));
                },
                | Some(&Computation::Application(head, argument)) => {
                    rows.mark(Row::ApplicationSynthesises);
                    worklist.push(Node::Computation(head));
                    worklist.push(Node::Value(argument));
                },
                | Some(&Computation::Return(returned)) => {
                    rows.mark(Row::ReturnChecks);
                    worklist.push(Node::Value(returned));
                },
                | Some(&Computation::Force(forced)) => {
                    rows.mark(Row::ForceSynthesises);
                    worklist.push(Node::Value(forced));
                },
                | Some(&Computation::Bind(first, then)) => {
                    worklist.push(Node::Computation(first));
                    worklist.push(Node::Computation(then));
                },
                | Some(&Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                }) => {
                    worklist.push(Node::Value(scrutinee));
                    worklist.push(Node::Computation(on_left));
                    worklist.push(Node::Computation(on_right));
                },
                | None => {},
            },
        }
    }
}

/// A term node awaiting its visit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Node
{
    /// A value node.
    Value(ValueId),
    /// A computation node.
    Computation(gandr_core_term::ComputationId),
}

/// Whether a refused thunk is a definition's whole body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum WholeBody
{
    /// It is the whole body of an unsigned definition.
    Whole,
    /// It stands inside a body, or the declaration is signed.
    Inner,
}

#[cfg(test)]
mod tests
{
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::DeclarationCount;
    use gandr_surface_syntax::SourceText;

    use super::Exercised;
    use super::Row;
    use crate::compose::Composed;
    use crate::compose::LoweringCount;
    use crate::compose::compose;

    /// The rows `source`'s settled declarations carry under the fixture root.
    ///
    /// # Specification
    ///
    /// trivial.
    fn rows_of(source: SourceText<'_>) -> Exercised
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut lowerings = LoweringCount::default();
        match compose(&grammar, CorpusRoot::Fixture, source, &mut lowerings) {
            | Ok(Composed::Settled { exercised, .. }) => exercised,
            | Ok(Composed::Refused(refusal)) => panic!("refused as a whole: {refusal}"),
            | Err(fault) => panic!("faulted: {fault}"),
        }
    }

    /// The count set holding `rows`' counts and zero elsewhere.
    ///
    /// # Specification
    ///
    /// trivial.
    fn only(rows: &[(Row, DeclarationCount)]) -> Exercised
    {
        let mut exercised = Exercised::default();
        for &(row, count) in rows {
            *exercised.slot(row) = count;
        }
        exercised
    }

    #[test]
    fn a_module_carries_exactly_its_rows()
    {
        let table = [
            (
                r#"def answer : Integer ; def answer = 42 ;
def identity : U (Integer -> F Integer) ;
def identity = thunk { fn (x) { ret x } } ;
def applied : U (F Integer) ;
def applied = thunk { (force identity)(answer) } ;
def konst : U (Integer -> Integer -> F Integer) ;
def konst = thunk { fn (x) { fn (y) { ret x } } } ;"#,
                vec![
                    (Row::LambdaChecks, 2_usize),
                    (Row::ReturnChecks, 2_usize),
                    (Row::ForceSynthesises, 1_usize),
                    (Row::ApplicationSynthesises, 1_usize),
                    (Row::SubsumptionBridge, 4_usize),
                ],
            ),
            (r#"@[ refuses("UnresolvedName") ] def a = missing ;"#, vec![
                (Row::UndefinedTermName, 1_usize),
            ]),
            (
                r#"@[ refuses("UnresolvedTypeHead") ] def a : Natural ;"#,
                vec![(Row::UndefinedTypeHead, 1_usize)],
            ),
            (
                r#"@[ refuses("ShapeMismatch") ] def a : U (Integer -> F Integer) ; def a = thunk { ret 3 } ;"#,
                vec![(Row::ShapeRefusal, 1_usize)],
            ),
            (
                r#"@[ refuses("NotSynthesisable") ] def a : U (F Integer) ; def a = thunk { (fn (x) { ret x })(3) } ;"#,
                vec![(Row::NonSynthesisableHead, 1_usize)],
            ),
            (
                r#"@[ refuses("NotSynthesisable") ] def a = thunk { ret 3 } ;"#,
                vec![(Row::NonSynthesisableDefinition, 1_usize)],
            ),
            (
                r#"@[ refuses("OutOfFragment") ] def a : Integer * Integer ;"#,
                vec![(Row::ReservedForm, 1_usize)],
            ),
            (r#"@[ owes(1) ] def a : Integer ;"#, vec![(
                Row::AddressableObligation,
                1_usize,
            )]),
        ];
        for (source, rows) in table {
            let carried = rows_of(SourceText::from(source));
            let counted: Vec<(Row, DeclarationCount)> = rows
                .iter()
                .map(|&(row, count)| (row, DeclarationCount::from(count)))
                .collect();
            assert_eq!(carried, only(&counted), "{source}");
            let missing: Vec<Row> = Row::ALL
                .into_iter()
                .filter(|row| !rows.iter().any(|&(carried, _)| carried == *row))
                .collect();
            assert_eq!(
                carried.missing(),
                missing,
                "{source} misses every other row"
            );
        }
        assert_eq!(
            Exercised::default().missing(),
            Row::ALL.to_vec(),
            "an empty run misses every row"
        );
    }

    #[test]
    fn an_unsettled_declaration_carries_no_row()
    {
        let rows = rows_of(SourceText::from(
            r#"def a = missing ;
def b : Natural ;
@[ refuses("TypeMismatch") ] def c : Integer * Integer ;
def d : Integer ;
@[ refuses("UnresolvedName") ] def e : U (F Integer) ; def e = thunk { ret 3 } ;"#,
        ));
        assert_eq!(
            rows,
            Exercised::default(),
            "no unsettled declaration counts"
        );
    }

    #[test]
    fn a_near_miss_carries_no_refusal_row()
    {
        let rows = rows_of(SourceText::from(
            r#"@[ refuses("NotSynthesisable") ] def a : U (F Integer) ; def a = thunk { force (thunk { ret 3 }) } ;
@[ refuses("ShapeMismatch") ] def b : Integer ; def b = thunk { ret 3 } ;
@[ refuses("OutOfFragment") ] def c = fn (x) { ret x } ;"#,
        ));
        assert_eq!(
            rows,
            Exercised::default(),
            "a thunk below the body, a thunk's shape refusal and an unadmitted form witness none of the rows"
        );
    }

    #[test]
    fn absorbing_sums_every_row()
    {
        let n = |count: usize| DeclarationCount::from(count);
        let mut left = only(&[(Row::LambdaChecks, n(2)), (Row::ReservedForm, n(1))]);
        let right = only(&[
            (Row::LambdaChecks, n(3)),
            (Row::AddressableObligation, n(1)),
        ]);
        left.absorb(&right);
        for row in Row::ALL {
            let expected = match row {
                | Row::LambdaChecks => 5_usize,
                | Row::ReservedForm | Row::AddressableObligation => 1_usize,
                | Row::ReturnChecks
                | Row::ForceSynthesises
                | Row::ApplicationSynthesises
                | Row::SubsumptionBridge
                | Row::UndefinedTermName
                | Row::UndefinedTypeHead
                | Row::ShapeRefusal
                | Row::NonSynthesisableHead
                | Row::NonSynthesisableDefinition => 0_usize,
            };
            assert_eq!(left.count(row), DeclarationCount::from(expected), "{row}");
        }
    }
}
