//! Declaration checking: the judgement applied to one declaration, and to a
//! module of them in admission order.
//!
//! # The signature decides the direction
//!
//! A declaration with a declared type checks its body against it; one without
//! synthesises its body's type. The declared type is the contract: it enters
//! the signature table whether or not the body met it, so one wrong body does
//! not turn every later reference into an unknown constant. A body with no
//! signature supplies a type only when it synthesised one.
//!
//! # A hole read in both directions
//!
//! A hole in checking position absorbs the type handed in and owes it: the
//! declaration's verdict is [`Verdict::Owed`] and its [`ObligationEntry`]
//! enters the run's ledger. A hole in synthesis position has nothing to absorb
//! and is refused as a checking-only form. The hole carries no unknown type
//! that would let the run continue past a mismatch; the run continues because
//! every declaration is judged on its own.
//!
//! # Every declaration gets a verdict
//!
//! [`check_module`] judges every declaration, in the order given, and a
//! refused one does not stop the run: the report is total over the module.
//!
//! # An accepted body is a definition
//!
//! A declaration whose body was accepted defines its constant: a later decode
//! of a code naming it unfolds to that body. A refused or owed declaration
//! leaves its constant rigid. The report carries the lifts the run's value
//! bridges recorded beside the verdicts, so the kernel bridge writes each one
//! where it stands.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::code::Lift;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::declaration::signature;
use crate::formation::FormedValueType;
use crate::formation::form_value_type;
use crate::judgement::Checked;
use crate::judgement::Direction;
use crate::judgement::Synthesised;
use crate::judgement::check_value;
use crate::judgement::synthesise_value;
use crate::ledger::Absence;
use crate::ledger::ObligationEntry;
use crate::ledger::ObligationLedger;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::support::Supported;

/// The judgement's answer for one declaration.
///
/// An accepted verdict carries the body it judged, so a consumer re-deriving
/// the declaration — the kernel bridge — reads everything it needs here.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Verdict
{
    /// The body checked against the declared type.
    Checked
    {
        /// The declared type.
        declared: FormedValueType,
        /// The body checked.
        body: ValueId,
        /// The check's evidence.
        evidence: Checked,
    },
    /// The unsigned body synthesised its type.
    Synthesised
    {
        /// The body synthesised.
        body: ValueId,
        /// The synthesis's evidence.
        synthesised: Synthesised<FormedValueType>,
    },
    /// The body is a hole under a declared type, owed.
    Owed(ObligationEntry),
    /// The declaration was refused.
    Refused(CheckRefusal),
}

/// One declaration's verdict, beside the position and origin it was offered
/// with.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Judged
{
    /// The declaration's admission position.
    constant: ConstantIndex,
    /// The declaration's origin, echoed back.
    origin: OriginToken,
    /// The verdict.
    verdict: Verdict,
}

impl Judged
{
    /// The declaration's admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The declaration's origin.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(&self) -> OriginToken
    {
        self.origin
    }

    /// The verdict.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn verdict(&self) -> Verdict
    {
        self.verdict
    }
}

/// A module's verdicts, in the order given, and the obligations they owe.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ModuleReport
{
    /// One entry per declaration, in the order given.
    judged: Vec<Judged>,
    /// The holes owed, in the order met.
    ledger: ObligationLedger,
    /// The codes the run checked at a universe above their own, by node.
    lifts: BTreeMap<ValueId, Lift>,
    /// The body each accepted declaration defines its constant as, elaborated
    /// to the universe it was declared at, by position.
    definitions: BTreeMap<ConstantIndex, ValueId>,
}

impl ModuleReport
{
    /// One entry per declaration, in the order given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn judged(&self) -> &[Judged]
    {
        &self.judged
    }

    /// The holes owed, in the order met.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ledger(&self) -> &ObligationLedger
    {
        &self.ledger
    }

    /// The codes the run checked at a universe above their own, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lifts(&self) -> &BTreeMap<ValueId, Lift>
    {
        &self.lifts
    }

    /// The body each accepted declaration defines its constant as: its body,
    /// lifted to the universe it was declared at when the body is a code of a
    /// smaller one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn definitions(&self) -> &BTreeMap<ConstantIndex, ValueId>
    {
        &self.definitions
    }
}

/// Judge one declaration in `context`.
///
/// # Specification
/// - requires: nothing — an out-of-order position, an unformed signature and an
///   ill-typed body are admissible input and refused.
/// - ensures: the declaration is admitted at its position, then: a signature
///   and a body give [`Verdict::Checked`] when the body checks against the
///   formed signature; a signature and a hole give [`Verdict::Owed`] with the
///   hole's absence; a body alone gives [`Verdict::Synthesised`] when it
///   synthesises; neither is refused. An accepted verdict carries the body it
///   judged and defines the constant as that body. A formed signature enters
///   the signature table after the body is judged, whatever the body's verdict;
///   a synthesised type enters it after synthesis; a refused body alone enters
///   nothing.
/// - provides: the one obligation a declaration can owe, carried in its
///   verdict, so a caller judging a single declaration needs no ledger.
/// - fails: never; a refusal is the verdict [`Verdict::Refused`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the admission, the four
///   combinations of present and absent halves, and when a type enters the
///   table; separated by one declaration of each combination, an admission out
///   of order, a self-reference, and a reference after a refused signed body
///   and after a refused unsigned one.
/// - witness: `module::tests::each_combination_of_halves_gets_its_verdict`
/// - witness: `module::tests::an_admission_out_of_order_is_refused`
/// - witness: `module::tests::a_declaration_cannot_read_its_own_type`
/// - witness: `module::tests::a_refused_signed_body_still_supplies_its_type`
/// - witness: `module::tests::a_body_that_synthesised_nothing_supplies_no_type`
/// - witness: `module::tests::a_later_declaration_reads_an_earlier_type`
#[inline]
#[must_use]
pub fn check_declaration(
    context: &mut CheckingContext<'_>,
    declaration: &Declaration,
) -> Verdict
{
    let constant = declaration.constant();
    if let Err(refusal) = context.admit(constant) {
        return Verdict::Refused(refusal);
    }
    let direction = match declaration.signature() {
        | Maybe::Present(declared) => match form_value_type(context, declared) {
            | Ok(formed) => Direction::Check(formed),
            | Err(refusal) => return Verdict::Refused(refusal),
        },
        | Maybe::Absent(signature::Absent::Unsigned) => Direction::Synthesise,
    };
    let verdict = match declaration.body() {
        | Maybe::Present(body) => match direction {
            | Direction::Synthesise => match synthesise_value(context, body) {
                | Ok(synthesised) => Verdict::Synthesised { body, synthesised },
                | Err(refusal) => Verdict::Refused(refusal),
            },
            | Direction::Check(declared) => match check_value(context, body, declared) {
                | Ok(evidence) => Verdict::Checked {
                    declared,
                    body,
                    evidence,
                },
                | Err(refusal) => Verdict::Refused(refusal),
            },
        },
        | Maybe::Absent(body::Absent::Hole) => {
            match hole(direction, constant, declaration.origin()) {
                | Ok(absence) => Verdict::Owed(ObligationEntry::from(absence)),
                | Err(refusal) => Verdict::Refused(refusal),
            }
        },
    };
    match (direction, verdict) {
        | (Direction::Check(declared), Verdict::Checked { body, .. }) => {
            context.record(constant, declared);
            context.define(constant, declared, body);
        },
        | (
            Direction::Check(declared),
            Verdict::Synthesised { .. } | Verdict::Owed(_) | Verdict::Refused(_),
        ) => context.record(constant, declared),
        | (Direction::Synthesise, Verdict::Synthesised { synthesised, body }) => {
            context.record(constant, synthesised.produced());
            context.define(constant, synthesised.produced(), body);
        },
        | (
            Direction::Synthesise,
            Verdict::Checked { .. } | Verdict::Owed(_) | Verdict::Refused(_),
        ) => {},
    }
    verdict
}

/// Judge one declaration in `context`, and report the signature answers the
/// judgement consulted.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the verdict [`check_declaration`] gives, with the same effect on
///   `context`; beside it, every answer the judgement read from the signature
///   table, once per position, ascending by position, and no answer read before
///   this call.
/// - provides: the support an incremental caller compares pointwise before it
///   reuses the verdict: equal answers mean an equal judgement, because the
///   signature table is the only input outside the declaration the judgement
///   reads.
/// - fails: never; a refusal is the verdict [`Verdict::Refused`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the log's span and its canonical form,
///   separated by an unsupported judgement before a supported one, a supported
///   one reading positions out of order and one twice, a read of an unadmitted
///   position, and a refusal that stops the run before a later read.
/// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
/// - witness: `module::tests::a_refusal_cuts_the_support_where_the_run_stopped`
#[inline]
#[must_use]
pub fn check_declaration_supported(
    context: &mut CheckingContext<'_>,
    declaration: &Declaration,
) -> Supported
{
    context.start_support();
    let verdict = check_declaration(context, declaration);
    Supported::new(verdict, context.finish_support())
}

/// Judge every declaration of a module, in the order given.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one [`Judged`] per declaration, in the order given, each carrying
///   the verdict [`check_declaration`] gives at that point of the run; the
///   ledger holds exactly the owed verdicts' entries, in order; the lifts are
///   every lift the context's value bridges recorded by the run's end, and the
///   definitions every body the context defines a constant as.
/// - provides: total marking — a refused declaration does not stop the run.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the run's totality and the ledger's
///   feed, separated by a module mixing every verdict, with a refusal before
///   later declarations, asserted entry by entry, and the ledger asserted to
///   hold the owed entries and no refused one.
/// - witness: `module::tests::a_refusal_does_not_stop_the_run`
/// - witness: `module::tests::every_owed_hole_enters_the_ledger_in_order`
/// - witness: `module::tests::a_refusal_never_enters_the_ledger`
#[inline]
#[must_use]
pub fn check_module(
    context: &mut CheckingContext<'_>,
    declarations: &[Declaration],
) -> ModuleReport
{
    let mut judged = Vec::with_capacity(declarations.len());
    let mut ledger = ObligationLedger::new();
    for declaration in declarations {
        let verdict = check_declaration(context, declaration);
        if let Verdict::Owed(entry) = verdict {
            ledger.record(entry);
        }
        judged.push(Judged {
            constant: declaration.constant(),
            origin: declaration.origin(),
            verdict,
        });
    }
    ModuleReport {
        judged,
        ledger,
        lifts: context.lifts().clone(),
        definitions: context.definitions().definitions().collect(),
    }
}

/// The hole rule, in both directions.
///
/// # Specification
/// - requires: nothing.
/// - ensures: in checking position the hole absorbs the expected type and owes
///   it as the absence of the declaration at `constant`.
/// - fails: [`CheckRefusal::NotSynthesisable`] naming the hole in synthesis
///   position.
/// - panics: none.
fn hole(
    direction: Direction<FormedValueType>,
    constant: ConstantIndex,
    origin: OriginToken,
) -> Result<Absence, CheckRefusal>
{
    match direction {
        | Direction::Check(expected) => Ok(Absence::new(constant, expected, origin)),
        | Direction::Synthesise => Err(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Hole(constant),
        }),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use quenchant_shape::shape::Maybe;

    use super::Verdict;
    use super::check_declaration;
    use super::check_module;
    use crate::context::Atom;
    use crate::context::CheckBudget;
    use crate::context::CheckingContext;
    use crate::conversion::ConversionCount;
    use crate::declaration::Declaration;
    use crate::declaration::OriginToken;
    use crate::declaration::body;
    use crate::declaration::signature;
    use crate::fixture::integer_literal;
    use crate::fixture::text_literal;
    use crate::refusal::CheckRefusal;
    use crate::refusal::CheckingForm;
    use crate::refusal::CoreNode;
    use crate::refusal::Mismatch;
    use crate::refusal::TypeNode;
    use crate::refusal::UnadmittedFormer;

    /// An admission position in a fixture module.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct At(usize);

    /// The declaration at `position`, its origin `position + 100`.
    ///
    /// # Specification
    /// trivial.
    fn declaration(
        position: At,
        declared: Maybe<ValueTypeId, signature::Absent>,
        defined: Maybe<ValueId, body::Absent>,
    ) -> Declaration
    {
        Declaration::new(
            ConstantIndex::from(position.0),
            declared,
            defined,
            OriginToken::from(position.0.checked_add(100).unwrap()),
        )
    }

    /// No declared type.
    const UNSIGNED: Maybe<ValueTypeId, signature::Absent> =
        Maybe::Absent(signature::Absent::Unsigned);

    /// No body.
    const HOLE: Maybe<ValueId, body::Absent> = Maybe::Absent(body::Absent::Hole);

    #[test]
    fn each_combination_of_halves_gets_its_verdict()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let zero = arena.value_literal(integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let Verdict::Checked {
            declared,
            body,
            evidence,
        } = check_declaration(
            &mut context,
            &declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
        )
        else {
            panic!("a signature and a body check");
        };
        assert_eq!(
            (declared.id(), body),
            (integer, zero),
            "the verdict carries the declared type and the body it checked"
        );
        assert_eq!(
            evidence.conversions(),
            ConversionCount::from(1_usize),
            "the literal crossed the value bridge once"
        );
        let Verdict::Owed(entry) = check_declaration(
            &mut context,
            &declaration(At(1), Maybe::Present(integer), HOLE),
        )
        else {
            panic!("a signature over a hole is owed");
        };
        assert_eq!(
            (
                entry.absence().constant(),
                entry.absence().declared().id(),
                entry.absence().origin()
            ),
            (
                ConstantIndex::from(1_usize),
                integer,
                OriginToken::from(101_usize)
            ),
            "the hole in checking position absorbs the declared type and owes it"
        );
        let Verdict::Synthesised { body, synthesised } = check_declaration(
            &mut context,
            &declaration(At(2), UNSIGNED, Maybe::Present(zero)),
        )
        else {
            panic!("a body alone synthesises");
        };
        assert_eq!(
            (body, synthesised.produced()),
            (zero, context.atom(Atom::Integer)),
            "the unsigned literal synthesises its atom, and the verdict carries the body"
        );
        assert_eq!(
            check_declaration(&mut context, &declaration(At(3), UNSIGNED, HOLE)),
            Verdict::Refused(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Hole(ConstantIndex::from(3_usize)),
            }),
            "a hole in synthesis position has nothing to absorb and is refused"
        );
    }

    #[test]
    fn an_admission_out_of_order_is_refused()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_literal(integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert!(
            matches!(
                check_declaration(
                    &mut context,
                    &declaration(At(1), UNSIGNED, Maybe::Present(zero))
                ),
                Verdict::Synthesised { .. }
            ),
            "the first admission may take any position"
        );
        for repeated in [1_usize, 0_usize] {
            let verdict = check_declaration(
                &mut context,
                &declaration(At(repeated), UNSIGNED, Maybe::Present(zero)),
            );
            assert_eq!(
                verdict,
                Verdict::Refused(CheckRefusal::AdmissionOrder {
                    constant: ConstantIndex::from(repeated),
                    admitted: ConstantIndex::from(1_usize),
                }),
                "a position not above every admitted one is refused with both positions"
            );
            let Verdict::Refused(refusal) = verdict
            else {
                panic!("refused above");
            };
            assert_eq!(
                refusal.classify(),
                FailureClass::EngineFault,
                "an admission out of order is the producer's fault"
            );
        }
    }

    #[test]
    fn a_declaration_cannot_read_its_own_type()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let itself = arena.value_constant(ConstantIndex::from(0_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let verdict = check_declaration(
            &mut context,
            &declaration(At(0), Maybe::Present(integer), Maybe::Present(itself)),
        );
        assert_eq!(
            verdict,
            Verdict::Refused(CheckRefusal::UnknownConstant {
                at: itself,
                constant: ConstantIndex::from(0_usize),
            }),
            "a body sees only the declarations strictly before it, so self-reference finds no type"
        );
        let Verdict::Refused(refusal) = verdict
        else {
            panic!("refused above");
        };
        assert_eq!(
            refusal.classify(),
            FailureClass::MalformedSource,
            "an unknown constant is the author's"
        );
    }

    #[test]
    fn a_refused_signed_body_still_supplies_its_type()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_literal(text_literal());
        let earlier = arena.value_constant(ConstantIndex::from(0_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert!(
            matches!(
                check_declaration(
                    &mut context,
                    &declaration(At(0), Maybe::Present(integer), Maybe::Present(text))
                ),
                Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { .. }))
            ),
            "the text does not have the declared integer type"
        );
        let Verdict::Synthesised { synthesised, .. } = check_declaration(
            &mut context,
            &declaration(At(1), UNSIGNED, Maybe::Present(earlier)),
        )
        else {
            panic!("the reference synthesises");
        };
        assert_eq!(
            synthesised.produced().id(),
            integer,
            "the declared type is the contract a later reference reads, whatever the body did"
        );
    }

    #[test]
    fn a_body_that_synthesised_nothing_supplies_no_type()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_literal(integer_literal());
        let returned = arena.computation_return(zero);
        let thunk = arena.value_thunk(returned);
        let earlier = arena.value_constant(ConstantIndex::from(0_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            check_declaration(
                &mut context,
                &declaration(At(0), UNSIGNED, Maybe::Present(thunk))
            ),
            Verdict::Refused(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Thunk(thunk),
            }),
            "an unsigned thunk does not synthesise"
        );
        assert_eq!(
            context.signature(ConstantIndex::from(0_usize)),
            Maybe::Absent(crate::context::signature_table::Absent::Untyped),
            "the refused body supplied no type"
        );
        assert_eq!(
            check_declaration(
                &mut context,
                &declaration(At(1), UNSIGNED, Maybe::Present(earlier))
            ),
            Verdict::Refused(CheckRefusal::UnknownConstant {
                at: earlier,
                constant: ConstantIndex::from(0_usize),
            }),
            "a reference to it finds no type"
        );
    }

    #[test]
    fn a_later_declaration_reads_an_earlier_type()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let thunk_type = arena.value_type_thunk(returns_integer);
        let zero = arena.value_literal(integer_literal());
        let returned = arena.computation_return(zero);
        let thunk = arena.value_thunk(returned);
        let suspended = arena.value_constant(ConstantIndex::from(0_usize));
        let owed = arena.value_constant(ConstantIndex::from(1_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(thunk_type), Maybe::Present(thunk)),
            declaration(At(1), Maybe::Present(integer), HOLE),
            declaration(At(2), UNSIGNED, Maybe::Present(suspended)),
            declaration(At(3), Maybe::Present(integer), Maybe::Present(owed)),
        ];
        let report = check_module(&mut context, &module);
        let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
        assert!(
            matches!(verdicts[2], Verdict::Synthesised { synthesised, .. } if synthesised.produced().id() == thunk_type),
            "a reference synthesises the exact type its declaration supplied"
        );
        assert!(
            matches!(verdicts[3], Verdict::Checked { .. }),
            "an owed declaration supplies its declared type to later references"
        );
        assert_eq!(
            context
                .signature(ConstantIndex::from(1_usize))
                .map(crate::formation::FormedValueType::id),
            Maybe::Present(integer),
            "the table holds the owed declaration's type"
        );
    }

    #[test]
    fn a_refusal_does_not_stop_the_run()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let zero = arena.value_literal(integer_literal());
        let text = arena.value_literal(text_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
            declaration(At(2), Maybe::Present(integer), HOLE),
            declaration(At(3), UNSIGNED, HOLE),
            declaration(At(4), UNSIGNED, Maybe::Present(zero)),
        ];
        let report = check_module(&mut context, &module);
        let judged = report.judged();
        for (entry, offered) in judged.iter().zip(&module) {
            assert_eq!(
                (entry.constant(), entry.origin()),
                (offered.constant(), offered.origin()),
                "each verdict echoes its declaration's position and origin, in order"
            );
        }
        let [
            ref mismatched,
            ref checked,
            ref owed,
            ref unsigned_hole,
            ref synthesised,
        ] = *judged
        else {
            panic!("every declaration gets a verdict");
        };
        assert!(
            matches!(
                mismatched.verdict(),
                Verdict::Refused(CheckRefusal::TypeMismatch(_))
            ),
            "the first declaration is refused"
        );
        assert!(
            matches!(checked.verdict(), Verdict::Checked { .. }),
            "the next is judged on its own"
        );
        assert!(
            matches!(owed.verdict(), Verdict::Owed(_)),
            "the signed hole is owed"
        );
        assert!(
            matches!(
                unsigned_hole.verdict(),
                Verdict::Refused(CheckRefusal::NotSynthesisable { .. })
            ),
            "the unsigned hole is refused"
        );
        assert!(
            matches!(synthesised.verdict(), Verdict::Synthesised { .. }),
            "and the run goes on past it"
        );
    }

    #[test]
    fn every_owed_hole_enters_the_ledger_in_order()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let zero = arena.value_literal(integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
            declaration(At(1), Maybe::Present(string), HOLE),
            declaration(At(2), UNSIGNED, Maybe::Present(zero)),
            declaration(At(3), Maybe::Present(integer), HOLE),
        ];
        let report = check_module(&mut context, &module);
        let owed: Vec<_> = report
            .ledger()
            .entries()
            .iter()
            .map(|entry| {
                let absence = entry.absence();
                (
                    absence.constant(),
                    absence.declared().id(),
                    absence.origin(),
                )
            })
            .collect();
        assert_eq!(
            owed,
            [
                (
                    ConstantIndex::from(1_usize),
                    string,
                    OriginToken::from(101_usize)
                ),
                (
                    ConstantIndex::from(3_usize),
                    integer,
                    OriginToken::from(103_usize)
                ),
            ],
            "the ledger holds each owed hole, in module order"
        );
        assert_eq!(
            usize::from(report.ledger().count()),
            2_usize,
            "the count is the holes owed"
        );
    }

    #[test]
    fn a_refusal_never_enters_the_ledger()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unformed = arena.value_type_base(BaseType::Numeric);
        let text = arena.value_literal(text_literal());
        let unknown = arena.value_constant(ConstantIndex::from(9_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(1), UNSIGNED, HOLE),
            declaration(At(2), UNSIGNED, Maybe::Present(unknown)),
            declaration(At(3), Maybe::Present(unformed), HOLE),
            declaration(At(3), Maybe::Present(integer), HOLE),
        ];
        let report = check_module(&mut context, &module);
        assert!(
            report
                .judged()
                .iter()
                .all(|entry| matches!(entry.verdict(), Verdict::Refused(_))),
            "every declaration of this module is refused"
        );
        assert_eq!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(unformed)),
                former: UnadmittedFormer::NumericAtom,
            }),
            "a signed hole under an unformed signature is refused, not owed"
        );
        assert_eq!(
            usize::from(report.ledger().count()),
            0_usize,
            "a refusal of any class leaves the ledger empty"
        );
    }

    /// The answers of `supported`, positions and type ids, in order.
    ///
    /// # Specification
    /// trivial.
    fn answers(
        supported: &super::Supported
    ) -> Vec<(
        ConstantIndex,
        Maybe<ValueTypeId, crate::context::signature_table::Absent>,
    )>
    {
        supported
            .support()
            .consulted()
            .iter()
            .map(|consulted| {
                (
                    consulted.constant(),
                    consulted
                        .answer()
                        .map(crate::formation::FormedValueType::id),
                )
            })
            .collect()
    }

    #[test]
    fn the_support_holds_each_consulted_answer_once_in_position_order()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let inner = arena.comp_type_arrow(integer, returns_integer);
        let outer = arena.comp_type_arrow(integer, inner);
        let function_type = arena.value_type_thunk(outer);
        let suspended_type = arena.value_type_thunk(returns_integer);
        let zero = arena.value_literal(integer_literal());
        let x = arena.value_constant(ConstantIndex::from(0_usize));
        let f = arena.value_constant(ConstantIndex::from(1_usize));
        let unknown = arena.value_constant(ConstantIndex::from(7_usize));
        // thunk ((force f) x) x: reads f, then x, then x again.
        let forced = arena.computation_force(f);
        let once = arena.computation_application(forced, x);
        let twice = arena.computation_application(once, x);
        let suspended = arena.value_thunk(twice);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let _x = check_declaration(
            &mut context,
            &declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
        );
        let _f = check_declaration(
            &mut context,
            &declaration(At(1), Maybe::Present(function_type), HOLE),
        );
        let _read = check_declaration(
            &mut context,
            &declaration(At(2), UNSIGNED, Maybe::Present(x)),
        );
        let literal = super::check_declaration_supported(
            &mut context,
            &declaration(At(3), UNSIGNED, Maybe::Present(zero)),
        );
        assert_eq!(
            answers(&literal),
            [],
            "a judgement that reads no constant consults nothing, whatever ran before it"
        );
        let applied = super::check_declaration_supported(
            &mut context,
            &declaration(
                At(4),
                Maybe::Present(suspended_type),
                Maybe::Present(suspended),
            ),
        );
        assert!(
            matches!(applied.verdict(), Verdict::Checked { .. }),
            "the application checks"
        );
        assert_eq!(
            answers(&applied),
            [
                (ConstantIndex::from(0_usize), Maybe::Present(integer)),
                (ConstantIndex::from(1_usize), Maybe::Present(function_type)),
            ],
            "f read first and x read twice are each held once, ascending by position"
        );
        let missing = super::check_declaration_supported(
            &mut context,
            &declaration(At(5), UNSIGNED, Maybe::Present(unknown)),
        );
        assert_eq!(
            answers(&missing),
            [(
                ConstantIndex::from(7_usize),
                Maybe::Absent(crate::context::signature_table::Absent::Untyped)
            )],
            "an unadmitted position is consulted and answers its absence"
        );
    }

    #[test]
    fn a_refusal_cuts_the_support_where_the_run_stopped()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let inner = arena.comp_type_arrow(integer, returns_integer);
        let outer = arena.comp_type_arrow(integer, inner);
        let function_type = arena.value_type_thunk(outer);
        let suspended_type = arena.value_type_thunk(returns_integer);
        let zero = arena.value_literal(integer_literal());
        let text = arena.value_literal(text_literal());
        let s = arena.value_constant(ConstantIndex::from(0_usize));
        let f = arena.value_constant(ConstantIndex::from(1_usize));
        let x = arena.value_constant(ConstantIndex::from(2_usize));
        // thunk ((force f) s) x: s is a string, so the run stops before x.
        let forced = arena.computation_force(f);
        let once = arena.computation_application(forced, s);
        let twice = arena.computation_application(once, x);
        let suspended = arena.value_thunk(twice);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), UNSIGNED, Maybe::Present(text)),
            declaration(At(1), Maybe::Present(function_type), HOLE),
            declaration(At(2), Maybe::Present(integer), Maybe::Present(zero)),
        ];
        for offered in &module {
            let _judged = check_declaration(&mut context, offered);
        }
        let string = context.atom(Atom::String).id();
        let refused = super::check_declaration_supported(
            &mut context,
            &declaration(
                At(3),
                Maybe::Present(suspended_type),
                Maybe::Present(suspended),
            ),
        );
        assert!(
            matches!(
                refused.verdict(),
                Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { at, .. })) if at == s
            ),
            "the string argument is refused at the value bridge"
        );
        assert_eq!(
            answers(&refused),
            [
                (ConstantIndex::from(0_usize), Maybe::Present(string)),
                (ConstantIndex::from(1_usize), Maybe::Present(function_type)),
            ],
            "the support holds what the run consulted before the refusal and nothing after it"
        );
    }

    #[test]
    fn an_adopted_answer_is_read_as_if_judged()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(
            gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
            gandr_kernel_strata::Level::zero(),
        );
        let code = arena.value_quote(integer);
        let adopted = arena.value_constant(ConstantIndex::from(0_usize));
        let untyped = arena.value_constant(ConstantIndex::from(1_usize));
        let decoded = arena.value_type_element(adopted, gandr_kernel_strata::Level::zero());
        let zero = arena.value_literal(integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let formed =
            crate::formation::form_value_type(&mut context, small).expect("the universe forms");
        assert_eq!(
            context.adopt(
                ConstantIndex::from(0_usize),
                Maybe::Present(formed),
                Maybe::Present(code)
            ),
            Ok(()),
            "a first adoption takes any position"
        );
        assert_eq!(
            context.adopt(
                ConstantIndex::from(1_usize),
                Maybe::Absent(crate::context::signature_table::Absent::Untyped),
                Maybe::Absent(crate::code::unfolding::Absent::Rigid)
            ),
            Ok(()),
            "an adopted absence is admitted"
        );
        assert!(
            matches!(
                check_declaration(&mut context, &declaration(At(2), UNSIGNED, Maybe::Present(adopted))),
                Verdict::Synthesised { synthesised, .. } if synthesised.produced().id() == small
            ),
            "a later declaration reads the adopted type"
        );
        assert_eq!(
            check_declaration(
                &mut context,
                &declaration(At(3), UNSIGNED, Maybe::Present(untyped))
            ),
            Verdict::Refused(CheckRefusal::UnknownConstant {
                at: untyped,
                constant: ConstantIndex::from(1_usize),
            }),
            "a later declaration finds no type at an adopted absence"
        );
        assert_eq!(
            context.adopt(
                ConstantIndex::from(2_usize),
                Maybe::Absent(crate::context::signature_table::Absent::Untyped),
                Maybe::Absent(crate::code::unfolding::Absent::Rigid)
            ),
            Err(CheckRefusal::AdmissionOrder {
                constant: ConstantIndex::from(2_usize),
                admitted: ConstantIndex::from(3_usize),
            }),
            "an adoption out of order is refused with both positions"
        );
        assert_eq!(
            context
                .signature(ConstantIndex::from(2_usize))
                .map(crate::formation::FormedValueType::id),
            Maybe::Present(small),
            "the refused adoption left the table as it was"
        );
        assert!(
            matches!(
                check_declaration(
                    &mut context,
                    &declaration(At(4), Maybe::Present(decoded), Maybe::Present(zero))
                ),
                Verdict::Checked { .. }
            ),
            "a decode of the adopted code unfolds to the adopted body"
        );
    }
}
