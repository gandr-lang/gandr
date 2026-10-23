//! The forms the named programs leave out — projections, folds, list and
//! split cases, recursion, unfolded constants, unary and boolean and wide
//! primitives, holds and their accesses, delimited control — and the stops
//! the host answers, each in a program whose ending it states, ending alike
//! on both tiers and under the policy.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_value;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::control::EffectClause;
use gandr_core_term::control::StackFrame;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_core_term::primitive::Primitive;
use gandr_core_term::primitive::PrimitiveError;
use gandr_core_term::session::DialogueMove;
use gandr_core_term::session::Endpoint;
use gandr_core_term::session::RecordedMove;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::Status;
use gandr_runtime_emitter::evaluate;

use crate::support::BUDGET;
use crate::support::Integer;
use crate::support::Label;
use crate::support::Program;
use crate::support::Verdict;
use crate::support::agree;
use crate::support::agree_with;
use crate::support::focus;
use crate::support::integer;

/// A program built into an arena: its root, and the constants it defines,
/// by admission position, each by its value or opaque.
type Build = fn(&mut CoreArena) -> (ComputationId, Vec<Option<ValueId>>);

/// A form's program, and how it states it ends.
struct Form
{
    /// What the program is, for a failure's message.
    what: &'static str,
    /// The program.
    build: Build,
    /// How it ends.
    ends: Ends,
}

/// How a program ends.
#[derive(Clone, Copy)]
enum Ends
{
    /// Halted, its answer reading back as this rendering.
    Shows(&'static str),
    /// Halted, its answer something no reading writes, a capability.
    Unread,
    /// Stuck, for the reason this accepts.
    Stuck(fn(&Stuck) -> bool),
    /// Declined, for the reason this accepts.
    Declined(fn(&Declined) -> bool),
}

/// The intuitionistic variable at de Bruijn index `index`.
///
/// # Specification
/// trivial.
fn variable(
    core: &mut CoreArena,
    index: Index,
) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, index.0.into())
}

/// A de Bruijn index a program reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Index(u32);

/// A prelude row's name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Row(&'static str);

/// The prelude's row `name`.
///
/// # Specification
/// trivial.
fn prelude(name: Row) -> Primitive
{
    *PRELUDE
        .iter()
        .find(|row| row.name().as_ref() == name.0)
        .expect("the prelude holds the row")
}

/// The prelude's integer addition.
///
/// # Specification
/// trivial.
fn add() -> Primitive
{
    prelude(Row("add"))
}

/// The integers one, two and three.
///
/// # Specification
/// trivial.
fn one_two_three(core: &mut CoreArena) -> [ValueId; 3]
{
    [Integer(1), Integer(2), Integer(3)].map(|value| integer(core, value))
}

/// The native list of one, two and three.
///
/// # Specification
/// trivial.
fn list(core: &mut CoreArena) -> ValueId
{
    let nil = core.value_list_nil();
    one_two_three(core)
        .into_iter()
        .rev()
        .fold(nil, |tail, head| core.value_list_cons(head, tail))
}

/// Each form, its program and its stated answer.
///
/// # Specification
/// trivial.
fn forms() -> Vec<Form>
{
    Vec::from([
        Form {
            what: "#{x = 1, y = 2}.y",
            build: |core| {
                let [one, two, _] = one_two_three(core);
                let record = core.value_record(
                    [("x", one), ("y", two)]
                        .map(|(label, field)| (FieldLabel::from(String::from(label)), field))
                        .into(),
                );
                let root =
                    core.computation_record_projection(record, FieldLabel::from(String::from("y")));
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨2 |+ ★⟩"),
        },
        Form {
            what: "(1, 2, 3).2",
            build: |core| {
                let numbers = one_two_three(core);
                let tuple = core.value_tuple(&numbers);
                let root = core.computation_tuple_projection(tuple, Component::from(2_usize));
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨3 |+ ★⟩"),
        },
        Form {
            what: "fold [1, 2, 3] { nil => 0, cons(h, r) => h + r }",
            build: |core| {
                let list = list(core);
                let zero = integer(core, Integer(0));
                let on_nil = core.computation_return(zero);
                let operands = [variable(core, Index(1)), variable(core, Index(0))];
                let on_cons = core.computation_primitive(add(), Arguments::Binary(operands));
                let element = core.value_type_base(gandr_kernel_term::BaseType::Integer);
                let root = core.computation_list_fold(element, element, list, on_nil, on_cons);
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨6 |+ ★⟩"),
        },
        Form {
            what: "case [1, 2, 3] { nil => 0, cons(h, t) => h }",
            build: |core| {
                let list = list(core);
                let zero = integer(core, Integer(0));
                let on_nil = core.computation_return(zero);
                let head = variable(core, Index(1));
                let on_cons = core.computation_return(head);
                let root = core.computation_list_case(list, on_nil, on_cons);
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨1 |+ ★⟩"),
        },
        Form {
            what: "case (1, 2) { (a, b) => a + b }",
            build: |core| {
                let [one, two, _] = one_two_three(core);
                let pair = core.value_tuple(&[one, two]);
                let operands = [variable(core, Index(1)), variable(core, Index(0))];
                let body = core.computation_primitive(add(), Arguments::Binary(operands));
                let root = core.computation_split(pair, ComponentCount::from(2_usize), body);
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨3 |+ ★⟩"),
        },
        Form {
            what: "rec f { return 3 }",
            build: |core| {
                let [_, _, three] = one_two_three(core);
                let body = core.computation_return(three);
                let root = core.computation_fixpoint(body, FixpointEvidence::Partial);
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨3 |+ ★⟩"),
        },
        Form {
            what: "force seven, seven = thunk { return 7 }, twice",
            build: |core| {
                let seven = integer(core, Integer(7));
                let returned = core.computation_return(seven);
                let definition = core.value_thunk(returned);
                let constant = core.value_constant(ConstantIndex::from(0_usize));
                let first = core.computation_force(constant);
                let again = core.computation_force(constant);
                let operands = [variable(core, Index(1)), variable(core, Index(0))];
                let added = core.computation_primitive(add(), Arguments::Binary(operands));
                let rest = core.computation_bind(again, added);
                let root = core.computation_bind(first, rest);
                (root, Vec::from([Some(definition)]))
            },
            ends: Ends::Shows("⟨14 |+ ★⟩"),
        },
        Form {
            what: "(x <- return 1; fn y. x + y) 2",
            build: |core| {
                let [one, two, _] = one_two_three(core);
                let bound = core.computation_return(one);
                let operands = [variable(core, Index(1)), variable(core, Index(0))];
                let added = core.computation_primitive(add(), Arguments::Binary(operands));
                let function = core.computation_lambda(added);
                let head = core.computation_bind(bound, function);
                (core.computation_application(head, two), Vec::new())
            },
            ends: Ends::Shows("⟨3 |+ ★⟩"),
        },
        Form {
            what: r#"string.append("types are ", "machines")"#,
            build: |core| {
                let operands = ["types are ", "machines"].map(|text| {
                    core.value_literal(gandr_kernel_term::Literal::Text(
                        gandr_kernel_term::StringLiteral::new(String::from(text)),
                    ))
                });
                let append = prelude(Row("string.append"));
                let root = core.computation_primitive(append, Arguments::Binary(operands));
                (root, Vec::new())
            },
            ends: Ends::Shows(r#"⟨"types are machines" |+ ★⟩"#),
        },
        Form {
            what: "project 1 (x <- return 1; with { return x } { return 2 })",
            build: |core| {
                let [one, two, _] = one_two_three(core);
                let bound = core.computation_return(one);
                let x = variable(core, Index(0));
                let components = [core.computation_return(x), core.computation_return(two)];
                let lazy = core.computation_with(&components);
                let head = core.computation_bind(bound, lazy);
                (
                    core.computation_project(gandr_core_term::Component::from(1_usize), head),
                    Vec::new(),
                )
            },
            ends: Ends::Shows("⟨2 |+ ★⟩"),
        },
        Form {
            what: "return type(Integer)",
            build: |core| {
                let integer_type = core.value_type_base(gandr_kernel_term::BaseType::Integer);
                let code = core.value_quote(integer_type);
                (core.computation_return(code), Vec::new())
            },
            ends: Ends::Shows("⟨code |+ ★⟩"),
        },
        Form {
            what: "case Succ(Zero) { Zero => 0, Succ(n) => 1 }",
            build: |core| {
                let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
                let zero = core.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
                let one =
                    core.value_constructor(nat, ConstructorTag::from(1_usize), Vec::from([zero]));
                let [first, _, _] = one_two_three(core);
                let naught = integer(core, Integer(0));
                let returns_naught = core.computation_return(naught);
                let returns_one = core.computation_return(first);
                let field = core.computation_lambda(returns_one);
                let integer_type = core.value_type_base(gandr_kernel_term::BaseType::Integer);
                let motive = core.comp_type_returner(integer_type);
                let root = core.computation_data_case(
                    one,
                    motive,
                    Vec::from([returns_naught, field]),
                    [0_usize, 1]
                        .map(gandr_kernel_term::FieldCount::from)
                        .to_vec(),
                );
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨1 |+ ★⟩"),
        },
        Form {
            what: "neg 5",
            build: |core| {
                let five = integer(core, Integer(5));
                let root = core.computation_primitive(prelude(Row("neg")), Arguments::Unary(five));
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨-5 |+ ★⟩"),
        },
        Form {
            what: "x <- 1 < 2; not x",
            build: |core| {
                let [one, two, _] = one_two_three(core);
                let less =
                    core.computation_primitive(prelude(Row("lt")), Arguments::Binary([one, two]));
                let x = variable(core, Index(0));
                let not = core.computation_primitive(prelude(Row("bool.not")), Arguments::Unary(x));
                (core.computation_bind(less, not), Vec::new())
            },
            ends: Ends::Shows("⟨inr(()) |+ ★⟩"),
        },
        Form {
            what: "2^70 + 1",
            build: |core| {
                let big = core.value_literal(Literal::Integer(IntegerLiteral::new(
                    Sign::NonNegative,
                    Magnitude::from_decimal_text(String::from("1180591620717411303424"))
                        .expect("decimal digits"),
                )));
                let one = integer(core, Integer(1));
                let root = core.computation_primitive(add(), Arguments::Binary([big, one]));
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨1180591620717411303425 |+ ★⟩"),
        },
        Form {
            what: "hold x = [1, 2, 3]; access x[1] as w { resume(w, 20) }; consume x",
            build: |core| written_at(core, Integer(1)),
            ends: Ends::Shows("⟨cons(1, cons(20, cons(3, nil()))) |+ ★⟩"),
        },
        Form {
            what: "hold x = 5; access shared x as w { return w }",
            build: |core| {
                let five = integer(core, Integer(5));
                let view = core.value_variable(Zone::Linear, 0_u32.into());
                let read = core.computation_return(view);
                let access = core.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Shared,
                    held: DeBruijnIndex::from(0_u32),
                    place: Place::Whole,
                    body: read,
                });
                (held(core, five, access, HoldGrade::Many), Vec::new())
            },
            ends: Ends::Shows("⟨5 |+ ★⟩"),
        },
        Form {
            what: "hold[1] x = 5; access x as w { abort(w) } unwind { () }; consume x",
            build: |core| {
                let five = integer(core, Integer(5));
                let unit = core.value_unit();
                let unwind = core.computation_return(unit);
                let abort = core.computation_memory(MemoryForm::Abort {
                    view: DeBruijnIndex::from(0_u32),
                });
                let access = core.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Exclusive { unwind },
                    held: DeBruijnIndex::from(0_u32),
                    place: Place::Whole,
                    body: abort,
                });
                let consume = core.computation_memory(MemoryForm::Consume {
                    held: DeBruijnIndex::from(0_u32),
                });
                let body = core.computation_bind(access, consume);
                (held(core, five, body, HoldGrade::One), Vec::new())
            },
            ends: Ends::Shows("⟨5 |+ ★⟩"),
        },
        Form {
            what: "reset { hold[1] x = 5; access x as w { shift k. abandon(k) } unwind { () }; \
                   consume x }",
            build: |core| {
                let five = integer(core, Integer(5));
                let unit = core.value_unit();
                let unwind = core.computation_return(unit);
                let k = variable(core, Index(0));
                let abandoned = core.computation_abandon(k);
                let shifted = core.computation_shift(abandoned);
                let access = core.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Exclusive { unwind },
                    held: DeBruijnIndex::from(0_u32),
                    place: Place::Whole,
                    body: shifted,
                });
                let consume = core.computation_memory(MemoryForm::Consume {
                    held: DeBruijnIndex::from(0_u32),
                });
                let body = core.computation_bind(access, consume);
                let hold = held(core, five, body, HoldGrade::One);
                (core.computation_reset(hold), Vec::new())
            },
            ends: Ends::Shows("⟨() |+ ★⟩"),
        },
        Form {
            what: "reset { shift k. return 1 }",
            build: |core| {
                let [one, _, _] = one_two_three(core);
                let returned = core.computation_return(one);
                let shifted = core.computation_shift(returned);
                (core.computation_reset(shifted), Vec::new())
            },
            ends: Ends::Shows("⟨1 |+ ★⟩"),
        },
        Form {
            what: "1 / 0",
            build: |core| {
                let one = integer(core, Integer(1));
                let zero = integer(core, Integer(0));
                let root = core
                    .computation_primitive(prelude(Row("int.div")), Arguments::Binary([one, zero]));
                (root, Vec::new())
            },
            ends: Ends::Stuck(|stuck| {
                matches!(*stuck, Stuck::Primitive(PrimitiveError::DivisionByZero))
            }),
        },
        Form {
            what: "hold x = [1, 2, 3]; access x[5] as w { resume(w, 20) }; consume x",
            build: |core| written_at(core, Integer(5)),
            ends: Ends::Stuck(|stuck| matches!(*stuck, Stuck::Outside(_))),
        },
        Form {
            what: "shift k. return 1, no reset",
            build: |core| {
                let [one, _, _] = one_two_three(core);
                let returned = core.computation_return(one);
                (core.computation_shift(returned), Vec::new())
            },
            ends: Ends::Stuck(|stuck| matches!(*stuck, Stuck::ShiftNoReset(_))),
        },
        Form {
            what: "force c0, c0 undefined",
            build: |core| {
                let constant = core.value_constant(ConstantIndex::from(0_usize));
                (core.computation_force(constant), Vec::new())
            },
            ends: Ends::Stuck(|stuck| {
                *stuck == Stuck::UndefinedConstant(ConstantIndex::from(0_usize))
            }),
        },
        Form {
            what: "return reify [apply 3, project 1, bind x. return x]",
            build: |core| {
                let [_, _, three] = one_two_three(core);
                let x = variable(core, Index(0));
                let bound = core.computation_return(x);
                let stack = core.value_reify(Arc::from([
                    StackFrame::Apply(three),
                    StackFrame::Project(gandr_core_term::Component::from(1_usize)),
                    StackFrame::Bind(bound),
                ]));
                (core.computation_return(stack), Vec::new())
            },
            ends: Ends::Shows("⟨reify [apply(3); project[1]; bind(x; α) ⇒ ⟨x0 |+ α0⟩] |+ ★⟩"),
        },
        Form {
            what: "return Succ(Zero)",
            build: |core| {
                let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
                let zero = core.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
                let one =
                    core.value_constructor(nat, ConstructorTag::from(1_usize), Vec::from([zero]));
                (core.computation_return(one), Vec::from([None]))
            },
            ends: Ends::Shows("⟨ctor[1](ctor[0]()) |+ ★⟩"),
        },
        Form {
            what: "rec f { fn x. return x }",
            build: |core| {
                let x = variable(core, Index(0));
                let returned = core.computation_return(x);
                let function = core.computation_lambda(returned);
                (
                    core.computation_fixpoint(function, FixpointEvidence::Partial),
                    Vec::new(),
                )
            },
            ends: Ends::Shows("⟨cocase {apply(x; α) ⇒ ⟨x0 |+ α0⟩} |− ★⟩"),
        },
        Form {
            what: "force c0, c0 = c0",
            build: |core| {
                let constant = core.value_constant(ConstantIndex::from(0_usize));
                (
                    core.computation_force(constant),
                    Vec::from([Some(constant)]),
                )
            },
            ends: Ends::Stuck(|stuck| {
                *stuck == Stuck::CyclicConstant(ConstantIndex::from(0_usize))
            }),
        },
        Form {
            what: "() + 1",
            build: |core| {
                let unit = core.value_unit();
                let [one, _, _] = one_two_three(core);
                let root = core.computation_primitive(add(), Arguments::Binary([unit, one]));
                (root, Vec::new())
            },
            ends: Ends::Stuck(|stuck| matches!(*stuck, Stuck::NonScalar(_))),
        },
        Form {
            what: "resume 1 { fn z. return z }",
            build: |core| {
                let [one, _, _] = one_two_three(core);
                let z = variable(core, Index(0));
                let returned = core.computation_return(z);
                let function = core.computation_lambda(returned);
                (core.computation_resume(one, function), Vec::new())
            },
            ends: Ends::Stuck(|stuck| matches!(*stuck, Stuck::ResumedNonStack { .. })),
        },
        Form {
            what: "hold x = 5; access x as w { return () } unwind { () }",
            build: |core| {
                let five = integer(core, Integer(5));
                let unit = core.value_unit();
                let unwind = core.computation_return(unit);
                let body = core.computation_return(unit);
                let access = core.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Exclusive { unwind },
                    held: DeBruijnIndex::from(0_u32),
                    place: Place::Whole,
                    body,
                });
                (held(core, five, access, HoldGrade::Many), Vec::new())
            },
            ends: Ends::Stuck(|stuck| matches!(*stuck, Stuck::Unended(_))),
        },
        Form {
            what: "hold x = [1, 2, 3]; access shared x[2] as w { return w }",
            build: |core| {
                let list = list(core);
                let index = integer(core, Integer(2));
                let view = core.value_variable(Zone::Linear, 0_u32.into());
                let read = core.computation_return(view);
                let access = core.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Shared,
                    held: DeBruijnIndex::from(0_u32),
                    place: Place::At { index },
                    body: read,
                });
                (held(core, list, access, HoldGrade::Many), Vec::new())
            },
            ends: Ends::Shows("⟨3 |+ ★⟩"),
        },
        Form {
            what: "reset { abandon(reify [bind x. return x]) }",
            build: |core| {
                let x = variable(core, Index(0));
                let bound = core.computation_return(x);
                let stack = core.value_reify(Arc::from([StackFrame::Bind(bound)]));
                let abandoned = core.computation_abandon(stack);
                (core.computation_reset(abandoned), Vec::new())
            },
            ends: Ends::Shows("⟨() |+ ★⟩"),
        },
        Form {
            what: "\"one\" + 1",
            build: |core| {
                let text = core.value_literal(Literal::Text(
                    gandr_kernel_term::StringLiteral::new(String::from("one")),
                ));
                let [one, _, _] = one_two_three(core);
                let root = core.computation_primitive(add(), Arguments::Binary([text, one]));
                (root, Vec::new())
            },
            ends: Ends::Stuck(|stuck| {
                matches!(*stuck, Stuck::Primitive(PrimitiveError::ArgumentType))
            }),
        },
        Form {
            what: "handle a : Proc { a.exit(()) } with { pure(x) => x, oper exit(p, k) => k(p) }",
            build: |core| {
                let signature = proc(core);
                let capability = variable(core, Index(0));
                let unit = core.value_unit();
                let subject =
                    core.computation_exercise(capability, signature.clone(), "exit".into(), unit);
                let root = handled(core, Handler::Scope, signature, subject, Resumes::Payload);
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨() |+ ★⟩"),
        },
        Form {
            what: "handle { perform exit(()) } with { pure(x) => x, oper exit(p, k) => k(p) }",
            build: |core| {
                let signature = proc(core);
                let unit = core.value_unit();
                let subject = core.computation_perform(signature.clone(), "exit".into(), unit);
                let root = handled(core, Handler::Deep, signature, subject, Resumes::Payload);
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨() |+ ★⟩"),
        },
        Form {
            what: "handle { perform exit(()) } with { pure(x) => x, oper exit(p, k) => 9 }",
            build: |core| {
                let signature = proc(core);
                let unit = core.value_unit();
                let subject = core.computation_perform(signature.clone(), "exit".into(), unit);
                let root = handled(core, Handler::Deep, signature, subject, Resumes::Never);
                (root, Vec::new())
            },
            ends: Ends::Shows("⟨9 |+ ★⟩"),
        },
        Form {
            what: "perform exit(()), no handler",
            build: |core| {
                let signature = proc(core);
                let unit = core.value_unit();
                (
                    core.computation_perform(signature, "exit".into(), unit),
                    Vec::new(),
                )
            },
            ends: Ends::Stuck(|stuck| matches!(*stuck, Stuck::PerformNoHandler(_))),
        },
        Form {
            what: "handle a : Proc { return a } with { pure(x) => x, oper exit(p, k) => k(p) }",
            build: |core| {
                let signature = proc(core);
                let capability = variable(core, Index(0));
                let subject = core.computation_return(capability);
                let root = handled(core, Handler::Scope, signature, subject, Resumes::Payload);
                (root, Vec::new())
            },
            ends: Ends::Unread,
        },
        Form {
            what: "rec f { x <- force f; return x }",
            build: |core| {
                let own = variable(core, Index(0));
                let again = core.computation_force(own);
                let x = variable(core, Index(0));
                let rest = core.computation_return(x);
                let body = core.computation_bind(again, rest);
                (
                    core.computation_fixpoint(body, FixpointEvidence::Partial),
                    Vec::new(),
                )
            },
            ends: Ends::Declined(|declined| {
                matches!(*declined, Declined::Exhausted(Status::FramesExhausted))
            }),
        },
        Form {
            what: "rec f { force f }",
            build: |core| {
                let own = variable(core, Index(0));
                let again = core.computation_force(own);
                (
                    core.computation_fixpoint(again, FixpointEvidence::Partial),
                    Vec::new(),
                )
            },
            ends: Ends::Declined(|declined| {
                matches!(*declined, Declined::Exhausted(Status::FuelExhausted))
            }),
        },
        Form {
            what: "decompose(dialogue(left(sent(1)), right(received(1)), left(closed), \
                   right(closed)))",
            build: |core| {
                (
                    exchanged(core, [Endpoint::Left, Endpoint::Right]),
                    Vec::new(),
                )
            },
            ends: Ends::Shows(EXCHANGED),
        },
        Form {
            what: "decompose(dialogue(left(sent(1)), right(received(1)), right(closed), \
                   left(closed)))",
            build: |core| {
                (
                    exchanged(core, [Endpoint::Right, Endpoint::Left]),
                    Vec::new(),
                )
            },
            ends: Ends::Shows(EXCHANGED),
        },
    ])
}

/// The web of one message on `!Integer. end` and both closes, as the IL
/// renders its pieces in preorder: the send, then the left's close beside the
/// right's receipt and close, whichever endpoint the log closes first.
const EXCHANGED: &str = "⟨web[series(2), event(left, 0), parallel(2), event(left, 1), series(2), \
                         event(right, 0), event(right, 1)]() |+ ★⟩";

/// `decompose` of the dialogue that sends one and closes, its closes logged in
/// the order `closes` names.
///
/// # Specification
/// trivial.
fn exchanged(
    core: &mut CoreArena,
    closes: [Endpoint; 2],
) -> ComputationId
{
    let [one, _, _] = one_two_three(core);
    let turn = |endpoint, movement| DialogueMove { endpoint, movement };
    let dialogue = core.value_dialogue(Arc::from([
        turn(Endpoint::Left, RecordedMove::Sent(one)),
        turn(Endpoint::Right, RecordedMove::Received(one)),
        turn(closes[0], RecordedMove::Closed),
        turn(closes[1], RecordedMove::Closed),
    ]));
    core.computation_decompose(dialogue)
}

/// Which former handles an operation.
#[derive(Clone, Copy)]
enum Handler
{
    /// A deep handler, `handle { … } with { … }`.
    Deep,
    /// A scope minting the capability its subject exercises.
    Scope,
}

/// What an operation clause does with its continuation.
#[derive(Clone, Copy)]
enum Resumes
{
    /// Resumes it with the payload.
    Payload,
    /// Returns nine and never resumes it.
    Never,
}

/// The one-operation interface `Proc`, its `exit` taking and answering the
/// unit.
///
/// # Specification
/// trivial.
fn proc(core: &mut CoreArena) -> EffectSig
{
    let unit = core.value_type_unit();
    EffectSig::new(EffectName::from("Proc"), [EffectOp {
        name: "exit".into(),
        payload: unit,
        reply: unit,
    }])
    .expect("one operation is a signature")
}

/// `subject` handled by `handler` over `signature`: its return answered as
/// itself, its `exit` by a clause that `resumes` as named.
///
/// # Specification
/// trivial.
fn handled(
    core: &mut CoreArena,
    handler: Handler,
    signature: EffectSig,
    subject: ComputationId,
    resumes: Resumes,
) -> ComputationId
{
    let answer = variable(core, Index(0));
    let on_return = core.computation_return(answer);
    // Under the clause: the continuation, then the payload.
    let body = match resumes {
        Resumes::Payload => {
            let (continuation, payload) = (variable(core, Index(0)), variable(core, Index(1)));
            let replied = core.computation_return(payload);
            core.computation_resume(continuation, replied)
        },
        Resumes::Never => {
            let nine = integer(core, Integer(9));
            core.computation_return(nine)
        },
    };
    let clauses = Arc::from([EffectClause {
        operation: "exit".into(),
        body,
    }]);
    match handler {
        Handler::Deep => core.computation_handle(signature, subject, on_return, clauses),
        Handler::Scope => core.computation_scope(signature, subject, on_return, clauses),
    }
}

/// `hold x = [1, 2, 3]; access x[at] as w { resume(w, 20) } unwind { () };
/// consume x`.
///
/// # Specification
/// trivial.
fn written_at(
    core: &mut CoreArena,
    at: Integer,
) -> (ComputationId, Vec<Option<ValueId>>)
{
    let list = list(core);
    let unit = core.value_unit();
    let unwind = core.computation_return(unit);
    let twenty = integer(core, Integer(20));
    let resume = core.computation_memory(MemoryForm::Resume {
        view: DeBruijnIndex::from(0_u32),
        value: twenty,
    });
    let index = integer(core, at);
    let access = core.computation_memory(MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind },
        held: DeBruijnIndex::from(0_u32),
        place: Place::At { index },
        body: resume,
    });
    let consume = core.computation_memory(MemoryForm::Consume {
        held: DeBruijnIndex::from(0_u32),
    });
    let body = core.computation_bind(access, consume);
    (held(core, list, body, HoldGrade::Many), Vec::new())
}

/// `value` held at `grade`, `body` its scope.
///
/// # Specification
/// trivial.
fn held(
    core: &mut CoreArena,
    value: ValueId,
    body: ComputationId,
    grade: HoldGrade,
) -> ComputationId
{
    core.computation_memory(MemoryForm::Hold { value, body, grade })
}

/// Each form ends alike on both tiers and under the policy, as its program
/// states: halted with the answer it shows, or stuck for its own reason. A
/// constant it unfolds is defined by its focused value.
#[test]
fn each_form_ends_alike_on_both_executors_as_its_program_states()
{
    for Form { what, build, ends } in forms() {
        let mut core = CoreArena::new();
        let (root, defined) = build(&mut core);
        let program = Program {
            name: what,
            core,
            root,
        };
        let (mut commands, root) = focus(&program);
        let mut definitions = Definitions::new();
        let mut provenance = Provenance::new();
        for value in defined {
            let definition = match value {
                Some(value) => Definition::Transparent(
                    focus_value(&program.core, value, &mut commands, &mut provenance)
                        .unwrap_or_else(|refusal| {
                            panic!("{what}: the constant focuses: {refusal:?}")
                        }),
                ),
                None => Definition::Opaque,
            };
            let _ = definitions.push(definition);
        }
        let verdict = agree(Label(what), &commands, &definitions, root);
        let policy = agree_with(Label(what), &commands, &definitions, root, |store| {
            evaluate(&commands, &definitions, root, Fuel::from(BUDGET), store)
        });
        assert_eq!(verdict, policy, "{what} under the policy");
        match ends {
            Ends::Shows(shows) => assert_eq!(
                verdict,
                Verdict::Halted(Some(String::from(shows))),
                "{what} across the tiers"
            ),
            Ends::Stuck(blamed) => assert!(
                matches!(verdict, Verdict::Stuck(ref stuck) if blamed(stuck)),
                "{what} stops for its own reason, not {verdict:?}"
            ),
            Ends::Unread => assert_eq!(verdict, Verdict::Halted(None), "{what} reads nothing"),
            Ends::Declined(reason) => assert!(
                matches!(verdict, Verdict::Declined(ref declined) if reason(declined)),
                "{what} declines for its own reason, not {verdict:?}"
            ),
        }
    }
}
