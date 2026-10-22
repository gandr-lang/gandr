//! What the agreement suites share: the named programs and the answers they
//! state, a deterministic generator of closed positive-core programs, and the
//! comparison of native code's run with the portable executor's, value by
//! value across two stores.
//!
//! The emitter's suite includes this file too, so both packages hold their
//! tiers to one oracle.

use alloc::sync::Arc;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_terminal;
use gandr_core_sequent::render_command;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::control::EffectClause;
use gandr_core_term::control::StackFrame;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::Component;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_on;

/// The jumps a tier may take: the dispatcher's run budget.
pub const BUDGET: usize = 1 << 24;

/// An integer a test program is built from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Integer(pub i64);

/// The literal `value` in `core`.
///
/// # Specification
/// trivial.
pub fn integer(
    core: &mut CoreArena,
    value: Integer,
) -> ValueId
{
    let magnitude =
        Magnitude::from_decimal_text(value.0.unsigned_abs().to_string()).expect("decimal digits");
    let sign = if value.0 < 0 {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    core.value_literal(Literal::Integer(IntegerLiteral::new(sign, magnitude)))
}

/// A closed program.
pub struct Program
{
    /// What the program is, for a failure's message.
    pub name: &'static str,
    /// The arena holding it.
    pub core: CoreArena,
    /// The closed computation.
    pub root: ComputationId,
}

/// A closed program and the answer it states: the focused rendering of its
/// answer's reading.
pub struct Named
{
    /// The program.
    pub program: Program,
    /// What its answer reads back as.
    pub shows: &'static str,
}

/// The variable at de Bruijn index zero.
///
/// # Specification
/// trivial.
fn innermost(core: &mut CoreArena) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, 0_u32.into())
}

/// The named programs: the five positive-core programs a return, a bind, a
/// case, a constructor and their composition answer; three whose answer
/// suspends a computation — a function, a thunk and a pair holding one — so
/// a closure's site, captures and environment are compared too; three
/// primitive calls, answering an integer, an integer past 64 bits and a
/// boolean; a reified stack resumed, its application frame and its bind
/// frame, which reads a variable bound outside the stack; a lazy product
/// projected where it is built and after it was suspended, so an object
/// answers the projection it is entered with; a captured stack resumed
/// twice, whose frames return a pair bound outside the shift each time, so a
/// replay that gave the copy no owner of its own frees the pair the second
/// replay returns; a fold over a list built where it runs, whose cell
/// branch pairs each head with a pair bound outside the fold that the answer
/// holds too, so a walk that gave a tail or a capture no owner of its own
/// reads a freed cell; a held pair written back whole with a pair of two
/// reads of its view, and a held list of pairs written back past its head,
/// each answered beside a pair allocated after, so a read, a copied head or
/// a shared tail left without an owner is freed and its block reused; an
/// access abandoned by a shift whose unwind reads a pair the answer holds
/// too; a component projected from a fresh pair of pairs; a thunk forced
/// twice whose first answer is dropped before a fresh pair is allocated, so
/// a body that took its capture without an owner of its own frees it; a
/// handler whose return clause answers a pair bound outside it and whose
/// clause resumes its stack twice, so a handler frame copied without an
/// owner of that pair frees it; a captured stack resumed twice below the
/// frames it was captured from, whose inner frame answers to a frame the
/// stack holds, so a replay that left that frame's mark where the stack was
/// captured skips the frame; a handler whose first clause resumes its stack
/// and pairs what the resumption answers, where the resumed body performs a
/// second operation whose clause answers without resuming, so that clause's
/// answer is what the first resumption answers; a split and a nominal match
/// that each rebuild their dying scrutinee, so a reuse token built into with
/// the wrong fields or never built into answers wrongly, and a split whose
/// scrutinee a thunk also holds, so a shared cell overwritten in place
/// changes what the thunk answers; and a nominal branch answering a function
/// past its constructor's two fields, applied where the match stands, so a
/// branch run in place that took the application's frame for a field answers
/// the function unapplied.
///
/// # Specification
/// trivial.
pub fn named() -> Vec<Named>
{
    let mut programs = Vec::new();
    let mut push = |name, shows, core, root| {
        programs.push(Named {
            program: Program { name, core, root },
            shows,
        });
    };
    let mut core = CoreArena::new();
    let five = integer(&mut core, Integer(5));
    let root = core.computation_return(five);
    push("return 5", "⟨5 |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let seven = integer(&mut core, Integer(7));
    let bound = core.computation_return(seven);
    let variable = innermost(&mut core);
    let body = core.computation_return(variable);
    let root = core.computation_bind(bound, body);
    push("x <- return 7; return x", "⟨7 |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let three = integer(&mut core, Integer(-3));
    let scrutinee = core.value_injection(Side::Left.into(), three);
    let variable = innermost(&mut core);
    let arm = core.computation_return(variable);
    let root = core.computation_case(scrutinee, &[arm, arm]);
    push("case inl -3", "⟨-3 |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let pair = core.value_tuple(&[one, two]);
    let root = core.computation_return(pair);
    push("return (1, 2)", "⟨pair(1, 2) |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let eight = integer(&mut core, Integer(8));
    let injection = core.value_injection(Side::Right.into(), eight);
    let bound = core.computation_return(injection);
    let variable = innermost(&mut core);
    let arm = core.computation_return(variable);
    let body = core.computation_case(variable, &[arm, arm]);
    let root = core.computation_bind(bound, body);
    push("x <- return inr 8; case x", "⟨8 |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let nine = integer(&mut core, Integer(9));
    let bound = core.computation_return(nine);
    let variable = innermost(&mut core);
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let pair = core.value_tuple(&[variable, outer]);
    let returned = core.computation_return(pair);
    let function = core.computation_lambda(returned);
    let root = core.computation_bind(bound, function);
    push(
        "y <- return 9; fn x. return (x, y)",
        "⟨cocase {apply(x; α) ⇒ ⟨pair(x0, 9) |+ α0⟩} |− ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let four = integer(&mut core, Integer(4));
    let bound = core.computation_return(four);
    let variable = innermost(&mut core);
    let suspended = core.computation_return(variable);
    let thunk = core.value_thunk(suspended);
    let body = core.computation_return(thunk);
    let root = core.computation_bind(bound, body);
    push(
        "y <- return 4; return thunk { return y }",
        "⟨{force(α) ⇒ ⟨4 |+ α0⟩} |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let six = integer(&mut core, Integer(6));
    let identity_body = innermost(&mut core);
    let identity_return = core.computation_return(identity_body);
    let identity = core.computation_lambda(identity_return);
    let applied = core.computation_application(identity, six);
    let thunk = core.value_thunk(applied);
    let unit = core.value_unit();
    let pair = core.value_tuple(&[thunk, unit]);
    let root = core.computation_return(pair);
    push(
        "return (thunk { (fn x. return x) 6 }, ())",
        "⟨pair({force(α) ⇒ ⟨cocase {apply(x; α) ⇒ ⟨x0 |+ α0⟩} |− apply(6; α0)⟩}, ()) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let ten = integer(&mut core, Integer(10));
    let identity_body = innermost(&mut core);
    let identity_return = core.computation_return(identity_body);
    let identity = core.computation_lambda(identity_return);
    let root = core.computation_application(identity, ten);
    push("(fn x. return x) 10", "⟨10 |+ ★⟩", core, root);
    for (name, shows, primitive, left, right) in [
        ("add 2 3", "⟨5 |+ ★⟩", "add", 2_i64, 3_i64),
        (
            "mul 2^62 4",
            "⟨18446744073709551616 |+ ★⟩",
            "mul",
            0x4000_0000_0000_0000_i64,
            4_i64,
        ),
        ("lt 1 2", "⟨inl(()) |+ ★⟩", "lt", 1_i64, 2_i64),
    ] {
        let mut core = CoreArena::new();
        let left = integer(&mut core, Integer(left));
        let right = integer(&mut core, Integer(right));
        let row = *PRELUDE
            .iter()
            .find(|row| row.name().as_ref() == primitive)
            .expect("a prelude row");
        let root = core.computation_primitive(row, Arguments::Binary([left, right]));
        push(name, shows, core, root);
    }

    let mut core = CoreArena::new();
    let two = integer(&mut core, Integer(2));
    let three = integer(&mut core, Integer(3));
    let bound = core.computation_return(two);
    let head = innermost(&mut core);
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let pair = core.value_tuple(&[head, outer]);
    let bind = core.computation_return(pair);
    let stack = core.value_reify(
        [
            gandr_core_term::control::StackFrame::Apply(three),
            gandr_core_term::control::StackFrame::Bind(bind),
        ]
        .into(),
    );
    let argument = innermost(&mut core);
    let identity_return = core.computation_return(argument);
    let identity = core.computation_lambda(identity_return);
    let resumed = core.computation_resume(stack, identity);
    let root = core.computation_bind(bound, resumed);
    push(
        "y <- return 2; resume [apply 3, bind x. return (x, y)] { fn z. return z }",
        "⟨pair(3, 2) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let three = integer(&mut core, Integer(3));
    let first = core.computation_return(one);
    let second = core.computation_return(two);
    let third = core.computation_return(three);
    let lazy = core.computation_with(&[first, second, third]);
    let root = core.computation_project(Component::from(2_usize), lazy);
    push(
        "project 2 (with { return 1 } { return 2 } { return 3 })",
        "⟨3 |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let three = integer(&mut core, Integer(3));
    let first = core.computation_return(one);
    let second = core.computation_return(two);
    let third = core.computation_return(three);
    let lazy = core.computation_with(&[first, second, third]);
    let suspended = core.value_thunk(lazy);
    let bound = core.computation_return(suspended);
    let variable = innermost(&mut core);
    let forced = core.computation_force(variable);
    let projected = core.computation_project(Component::from(1_usize), forced);
    let root = core.computation_bind(bound, projected);
    push(
        "t <- return thunk { with { return 1 } { return 2 } { return 3 } }; project 1 (force t)",
        "⟨2 |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let pair = core.value_tuple(&[one, two]);
    let bound = core.computation_return(pair);
    let unit = core.value_unit();
    let resumed_with = core.computation_return(unit);
    let stack = innermost(&mut core);
    let first = core.computation_resume(stack, resumed_with);
    let again = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let second = core.computation_resume(again, resumed_with);
    let twice = core.computation_bind(first, second);
    let shifted = core.computation_shift(twice);
    let held = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let answered = core.computation_return(held);
    let rest = core.computation_bind(shifted, answered);
    let body = core.computation_bind(bound, rest);
    let root = core.computation_reset(body);
    push(
        "reset { x <- return (1, 2); _ <- shift k. { _ <- resume k { return () }; resume k { return () } }; return x }",
        "⟨pair(1, 2) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let three = integer(&mut core, Integer(3));
    let seven = integer(&mut core, Integer(7));
    let eight = integer(&mut core, Integer(8));
    let outer = core.value_tuple(&[seven, eight]);
    let bound = core.computation_return(outer);
    let nil = core.value_list_nil();
    let last = core.value_list_cons(three, nil);
    let middle = core.value_list_cons(two, last);
    let list = core.value_list_cons(one, middle);
    let unit = core.value_unit();
    let on_nil = core.computation_return(unit);
    let head = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let folded = innermost(&mut core);
    let kept = core.value_variable(Zone::Intuitionistic, 2_u32.into());
    let tagged = core.value_tuple(&[head, kept]);
    let cell = core.value_tuple(&[tagged, folded]);
    let on_cons = core.computation_return(cell);
    let unit_type = core.value_type_unit();
    let fold = core.computation_list_fold(unit_type, unit_type, list, on_nil, on_cons);
    let answer = innermost(&mut core);
    let again = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let both = core.value_tuple(&[answer, again]);
    let answered = core.computation_return(both);
    let rest = core.computation_bind(fold, answered);
    let root = core.computation_bind(bound, rest);
    push(
        "y <- return (7, 8); z <- fold [1, 2, 3] { nil ⇒ return (); cons h r ⇒ return ((h, y), r) }; return (z, y)",
        "⟨pair(pair(pair(1, pair(7, 8)), pair(pair(2, pair(7, 8)), pair(pair(3, pair(7, 8)), ()))), pair(7, 8)) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let seven = integer(&mut core, Integer(7));
    let eight = integer(&mut core, Integer(8));
    let held = core.value_tuple(&[one, two]);
    let read = core.value_variable(Zone::Linear, 0_u32.into());
    let written = core.value_tuple(&[read, read]);
    let resumed = core.computation_memory(MemoryForm::Resume {
        view: 0_u32.into(),
        value: written,
    });
    let unit = core.value_unit();
    let unwind = core.computation_return(unit);
    let access = core.computation_memory(MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind },
        held: 0_u32.into(),
        place: Place::Whole,
        body: resumed,
    });
    let after = core.value_tuple(&[seven, eight]);
    let whole = core.value_variable(Zone::Linear, 0_u32.into());
    let both = core.value_tuple(&[whole, after]);
    let answered = core.computation_return(both);
    let body = core.computation_bind(access, answered);
    let root = core.computation_memory(MemoryForm::Hold {
        value: held,
        body,
        grade: HoldGrade::Many,
    });
    push(
        "hold x = (1, 2); access x as w { resume(w, (w, w)) }; return (x, (7, 8))",
        "⟨pair(pair(pair(1, 2), pair(1, 2)), pair(7, 8)) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let five = integer(&mut core, Integer(5));
    let nine = integer(&mut core, Integer(9));
    let first = core.value_tuple(&[one, one]);
    let second = core.value_tuple(&[one, two]);
    let nil = core.value_list_nil();
    let last = core.value_list_cons(second, nil);
    let list = core.value_list_cons(first, last);
    let replacement = core.value_tuple(&[five, five]);
    let resumed = core.computation_memory(MemoryForm::Resume {
        view: 0_u32.into(),
        value: replacement,
    });
    let unit = core.value_unit();
    let unwind = core.computation_return(unit);
    let index = integer(&mut core, Integer(1));
    let access = core.computation_memory(MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind },
        held: 0_u32.into(),
        place: Place::At { index },
        body: resumed,
    });
    let after = core.value_tuple(&[nine, nine]);
    let whole = core.value_variable(Zone::Linear, 0_u32.into());
    let both = core.value_tuple(&[after, whole]);
    let answered = core.computation_return(both);
    let body = core.computation_bind(access, answered);
    let root = core.computation_memory(MemoryForm::Hold {
        value: list,
        body,
        grade: HoldGrade::Many,
    });
    push(
        "hold xs = [(1, 1), (1, 2)]; access xs[1] as w { resume(w, (5, 5)) }; return ((9, 9), xs)",
        "⟨pair(pair(9, 9), cons(pair(1, 1), cons(pair(5, 5), nil()))) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let seven = integer(&mut core, Integer(7));
    let eight = integer(&mut core, Integer(8));
    let nine = integer(&mut core, Integer(9));
    let outer = core.value_tuple(&[seven, eight]);
    let bound = core.computation_return(outer);
    let stack = innermost(&mut core);
    let abandoned = core.computation_abandon(stack);
    let shifted = core.computation_shift(abandoned);
    let kept = innermost(&mut core);
    let read = core.computation_return(kept);
    let unit = core.value_unit();
    let unwound = core.computation_return(unit);
    let unwind = core.computation_bind(read, unwound);
    let access = core.computation_memory(MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind },
        held: 0_u32.into(),
        place: Place::Whole,
        body: shifted,
    });
    let zero = integer(&mut core, Integer(0));
    let returned = core.computation_return(zero);
    let delimited = core.computation_bind(access, returned);
    let reset = core.computation_reset(delimited);
    let held = core.computation_memory(MemoryForm::Hold {
        value: one,
        body: reset,
        grade: HoldGrade::Many,
    });
    let again = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let after = core.value_tuple(&[nine, nine]);
    let both = core.value_tuple(&[again, after]);
    let answered = core.computation_return(both);
    let rest = core.computation_bind(held, answered);
    let root = core.computation_bind(bound, rest);
    push(
        "y <- return (7, 8); r <- hold x = 1; reset { access x as w { shift k. abandon k } unwind { _ <- return y; return () }; return 0 }; return (y, (9, 9))",
        "⟨pair(pair(7, 8), pair(9, 9)) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let three = integer(&mut core, Integer(3));
    let four = integer(&mut core, Integer(4));
    let five = integer(&mut core, Integer(5));
    let left = core.value_tuple(&[one, two]);
    let right = core.value_tuple(&[three, four]);
    let pair = core.value_tuple(&[left, right]);
    let bound = core.computation_return(pair);
    let record = innermost(&mut core);
    let projected = core.computation_tuple_projection(record, Component::from(1_usize));
    let field = innermost(&mut core);
    let after = core.value_tuple(&[five, five]);
    let both = core.value_tuple(&[field, after]);
    let answered = core.computation_return(both);
    let rest = core.computation_bind(projected, answered);
    let root = core.computation_bind(bound, rest);
    push(
        "p <- return ((1, 2), (3, 4)); q <- p.1; return (q, (5, 5))",
        "⟨pair(pair(3, 4), pair(5, 5)) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let seven = integer(&mut core, Integer(7));
    let eight = integer(&mut core, Integer(8));
    let nine = integer(&mut core, Integer(9));
    let outer = core.value_tuple(&[seven, eight]);
    let bound = core.computation_return(outer);
    let captured = innermost(&mut core);
    let suspended = core.computation_return(captured);
    let thunk = core.value_thunk(suspended);
    let made = core.computation_return(thunk);
    let first = innermost(&mut core);
    let forced = core.computation_force(first);
    let fresh = core.value_tuple(&[nine, nine]);
    let allocated = core.computation_return(fresh);
    let again = core.value_variable(Zone::Intuitionistic, 2_u32.into());
    let reforced = core.computation_force(again);
    let second = innermost(&mut core);
    let kept = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let both = core.value_tuple(&[second, kept]);
    let answered = core.computation_return(both);
    let tail = core.computation_bind(reforced, answered);
    let fed = core.computation_bind(allocated, tail);
    let dropped = core.computation_bind(forced, fed);
    let rest = core.computation_bind(made, dropped);
    let root = core.computation_bind(bound, rest);
    push(
        "y <- return (7, 8); f <- return thunk { return y }; _ <- force f; z <- return (9, 9); w <- force f; return (w, z)",
        "⟨pair(pair(7, 8), pair(9, 9)) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let zero = integer(&mut core, Integer(0));
    let one = integer(&mut core, Integer(1));
    let seven = integer(&mut core, Integer(7));
    let eight = integer(&mut core, Integer(8));
    let nine = integer(&mut core, Integer(9));
    let outer = core.value_tuple(&[seven, eight]);
    let bound = core.computation_return(outer);
    let payload = core.value_type_base(BaseType::Integer);
    let signature = EffectSig::new(EffectName::from("E"), [EffectOp {
        name: OperationName::from("op"),
        payload,
        reply: payload,
    }])
    .expect("one operation");
    let performed = core.computation_perform(signature.clone(), OperationName::from("op"), one);
    let answered = core.computation_return(zero);
    let subject = core.computation_bind(performed, answered);
    let kept = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let on_return = core.computation_return(kept);
    let fed = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let feed = core.computation_return(fed);
    let stack = innermost(&mut core);
    let first = core.computation_resume(stack, feed);
    let again = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let refed = core.value_variable(Zone::Intuitionistic, 2_u32.into());
    let refeed = core.computation_return(refed);
    let second = core.computation_resume(again, refeed);
    let clause = core.computation_bind(first, second);
    let handled = core.computation_handle(
        signature,
        subject,
        on_return,
        Arc::from([EffectClause {
            operation: OperationName::from("op"),
            body: clause,
        }]),
    );
    let result = innermost(&mut core);
    let after = core.value_tuple(&[nine, nine]);
    let both = core.value_tuple(&[result, after]);
    let returned = core.computation_return(both);
    let rest = core.computation_bind(handled, returned);
    let root = core.computation_bind(bound, rest);
    push(
        "y <- return (7, 8); r <- handle { _ <- op 1; return 0 } with { return _ ⇒ return y; op p k ⇒ _ <- resume k { return p }; resume k { return p } }; return (r, (9, 9))",
        "⟨pair(pair(7, 8), pair(9, 9)) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let three = integer(&mut core, Integer(3));
    let pair = core.value_tuple(&[one, two]);
    let bound = core.computation_return(pair);
    let unit = core.value_unit();
    let resumed_with = core.computation_return(unit);
    let stack = innermost(&mut core);
    let first = core.computation_resume(stack, resumed_with);
    let again = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let second = core.computation_resume(again, resumed_with);
    let earlier = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let later = innermost(&mut core);
    let answers = core.value_tuple(&[earlier, later]);
    let answered = core.computation_return(answers);
    let tail = core.computation_bind(second, answered);
    let twice = core.computation_bind(first, tail);
    let shifted = core.computation_shift(twice);
    let held = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let returned = core.computation_return(held);
    let body = core.computation_bind(shifted, returned);
    let thunk = core.value_thunk(body);
    let made = core.computation_return(thunk);
    let function = innermost(&mut core);
    let forced = core.computation_force(function);
    let result = innermost(&mut core);
    let extended = core.value_tuple(&[result, three]);
    let extend = core.computation_return(extended);
    let called = core.computation_bind(forced, extend);
    let rest = core.computation_bind(made, called);
    let delimited = core.computation_bind(bound, rest);
    let root = core.computation_reset(delimited);
    push(
        "reset { x <- return (1, 2); f <- return thunk { _ <- shift k. { a <- resume k { return () }; b <- resume k { return () }; return (a, b) }; return x }; y <- force f; return (y, 3) }",
        "⟨pair(pair(pair(1, 2), 3), pair(pair(1, 2), 3)) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let zero = integer(&mut core, Integer(0));
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let five = integer(&mut core, Integer(5));
    let seven = integer(&mut core, Integer(7));
    let nine = integer(&mut core, Integer(9));
    let payload = core.value_type_base(BaseType::Integer);
    let signature = EffectSig::new(EffectName::from("E"), [
        EffectOp {
            name: OperationName::from("first"),
            payload,
            reply: payload,
        },
        EffectOp {
            name: OperationName::from("second"),
            payload,
            reply: payload,
        },
    ])
    .expect("two operations");
    let firstly = core.computation_perform(signature.clone(), OperationName::from("first"), one);
    let secondly = core.computation_perform(signature.clone(), OperationName::from("second"), two);
    let earlier = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let later = innermost(&mut core);
    let both = core.value_tuple(&[earlier, later]);
    let answered = core.computation_return(both);
    let rest = core.computation_bind(secondly, answered);
    let subject = core.computation_bind(firstly, rest);
    let value = innermost(&mut core);
    let paired = core.value_tuple(&[value, zero]);
    let on_return = core.computation_return(paired);
    let fed = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let feed = core.computation_return(fed);
    let stack = innermost(&mut core);
    let resumed = core.computation_resume(stack, feed);
    let result = innermost(&mut core);
    let extended = core.value_tuple(&[result, five]);
    let extend = core.computation_return(extended);
    let resuming = core.computation_bind(resumed, extend);
    let sent = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let ended = core.value_tuple(&[sent, nine]);
    let ending = core.computation_return(ended);
    let handled = core.computation_handle(
        signature,
        subject,
        on_return,
        Arc::from([
            EffectClause {
                operation: OperationName::from("first"),
                body: resuming,
            },
            EffectClause {
                operation: OperationName::from("second"),
                body: ending,
            },
        ]),
    );
    let handled_value = innermost(&mut core);
    let outer = core.value_tuple(&[handled_value, seven]);
    let returned = core.computation_return(outer);
    let root = core.computation_bind(handled, returned);
    push(
        "r <- handle { a <- first 1; b <- second 2; return (a, b) } with { return v ⇒ return (v, 0); first p k ⇒ x <- resume k { return p }; return (x, 5); second q k ⇒ return (q, 9) }; return (r, 7)",
        "⟨pair(pair(pair(2, 9), 5), 7) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let pair = core.value_tuple(&[one, two]);
    let bound = core.computation_return(pair);
    let first = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let second = innermost(&mut core);
    let swapped = core.value_tuple(&[second, first]);
    let answered = core.computation_return(swapped);
    let scrutinee = innermost(&mut core);
    let split = core.computation_split(scrutinee, 2_usize.into(), answered);
    let root = core.computation_bind(bound, split);
    push(
        "x <- return (1, 2); split x { (a, b) ⇒ return (b, a) }",
        "⟨pair(2, 1) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let pair = core.value_tuple(&[one, two]);
    let bound = core.computation_return(pair);
    let kept = innermost(&mut core);
    let held = core.computation_return(kept);
    let thunk = core.value_thunk(held);
    let suspended = core.computation_return(thunk);
    let second = innermost(&mut core);
    let thunked = core.value_variable(Zone::Intuitionistic, 2_u32.into());
    let rebuilt = core.value_tuple(&[second, thunked]);
    let answered = core.computation_return(rebuilt);
    let scrutinee = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let split = core.computation_split(scrutinee, 2_usize.into(), answered);
    let rest = core.computation_bind(suspended, split);
    let root = core.computation_bind(bound, rest);
    push(
        "x <- return (1, 2); t <- return thunk { return x }; split x { (a, b) ⇒ return (b, t) }",
        "⟨pair(2, {force(α) ⇒ ⟨pair(1, 2) |+ α0⟩}) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let seven = integer(&mut core, Integer(7));
    let datatype = core.value_type_data(0_usize.into(), Vec::new());
    let scrutinee = core.value_constructor(datatype, 0_usize.into(), vec![one, two]);
    let first = core.value_variable(Zone::Intuitionistic, 2_u32.into());
    let argument = innermost(&mut core);
    let paired = core.value_tuple(&[first, argument]);
    let answered = core.computation_return(paired);
    let answer = core.computation_lambda(answered);
    let second = core.computation_lambda(answer);
    let branch = core.computation_lambda(second);
    let motive = core.comp_type_unknown();
    let cased = core.computation_data_case(scrutinee, motive, vec![branch], vec![2_usize.into()]);
    let root = core.computation_application(cased, seven);
    push(
        "(case C(1, 2) { C ⇒ fn a. fn b. fn z. return (a, z) }) 7",
        "⟨pair(1, 7) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let datatype = core.value_type_data(0_usize.into(), Vec::new());
    let built = core.value_constructor(datatype, 0_usize.into(), vec![one, two]);
    let bound = core.computation_return(built);
    let scrutinee = innermost(&mut core);
    let first = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let second = innermost(&mut core);
    let rebuilt = core.value_constructor(datatype, 0_usize.into(), vec![second, first]);
    let answered = core.computation_return(rebuilt);
    let inner = core.computation_lambda(answered);
    let branch = core.computation_lambda(inner);
    let motive = core.comp_type_unknown();
    let cased = core.computation_data_case(scrutinee, motive, vec![branch], vec![2_usize.into()]);
    let root = core.computation_bind(bound, cased);
    push(
        "x <- return C(1, 2); case x { C ⇒ fn a. fn b. return C(b, a) }",
        "⟨ctor[0](2, 1) |+ ★⟩",
        core,
        root,
    );
    programs
}

/// Focus `program` into a fresh command arena.
///
/// # Specification
/// trivial.
pub fn focus(program: &Program) -> (CommandArena, CommandId)
{
    let mut commands = CommandArena::new();
    let root = focus_computation(
        &program.core,
        program.root,
        &mut commands,
        &mut Provenance::new(),
    )
    .unwrap_or_else(|refusal| panic!("{}: focusing refused: {refusal:?}", program.name));
    (commands, root)
}

/// What a comparison is of, for a failure's message.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Label<'name>(pub &'name str);

/// The tier a run is compared on: native code where this host has a
/// patcher; elsewhere the executor, against a second run of itself.
pub const COMPARED: Tier = if PATCHER {
    Tier::Native
}
else {
    Tier::Executor
};

/// What the tiers answered, once they agreed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Verdict
{
    /// Both halted with equal answers, reading back as this rendering, or
    /// both with no reading.
    Halted(Option<String>),
    /// Both stopped stuck the same way; the executor's stop.
    Stuck(Stuck),
    /// Both declined for the same reason.
    Declined(Declined),
}

/// Run `root` on the executor and on [`COMPARED`], and compare.
///
/// # Specification
/// - ensures: as [`agree_with`], the compared run being [`COMPARED`]'s.
/// - executable: none — the comparison is the suite's oracle; a predicate over
///   it would be the walk itself.
///
/// # Adequacy
/// - hypothesis: L2 — every named program agrees across the tiers and states
///   its answer, and a difference of literal, head, field or presence is named.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::support::a_differing_answer_is_named`
pub fn agree(
    name: Label<'_>,
    commands: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> Verdict
{
    agree_with(
        Label(&format!("{} on {COMPARED:?}", name.0)),
        commands,
        definitions,
        root,
        |store| {
            evaluate_on(
                COMPARED,
                commands,
                definitions,
                root,
                Fuel::from(BUDGET),
                store,
            )
        },
    )
}

/// Run `root` on the executor and through `run`, and compare.
///
/// # Specification
/// - ensures: the two runs halt with answers equal value by value and reading
///   back alike, stop stuck the same way over equal values, or decline for the
///   same reason, and the executor's outcome is the verdict; a panic naming the
///   difference otherwise.
/// - executable: none — the comparison is the suite's oracle; a predicate over
///   it would be the walk itself.
///
/// # Adequacy
/// - hypothesis: L2 — every named program agrees across the tiers and under the
///   policy, and a difference of literal, head, field or presence is named.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::support::a_differing_answer_is_named`
pub fn agree_with(
    name: Label<'_>,
    commands: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    run: impl FnOnce(&mut Store) -> Result<Outcome, Declined>,
) -> Verdict
{
    let Label(name) = name;
    let mut expected_store = Store::new();
    let expected = evaluate_on(
        Tier::Executor,
        commands,
        definitions,
        root,
        Fuel::from(BUDGET),
        &mut expected_store,
    );
    let mut store = Store::new();
    let ran = run(&mut store);
    if let Err(difference) = same_outcome(&expected_store, &expected, &store, &ran) {
        panic!("{name}: the runs differ at {difference}");
    }
    match (expected, ran) {
        (Ok(Outcome::Halted(expected)), Ok(Outcome::Halted(answer))) => {
            let reading = reading(commands, &expected_store, expected);
            assert_eq!(
                reading,
                self::reading(commands, &store, answer),
                "{name}: the answers read back differently"
            );
            Verdict::Halted(reading)
        },
        (Ok(Outcome::Stuck(stuck)), _) => Verdict::Stuck(stuck),
        (Err(declined), _) => Verdict::Declined(declined),
        (Ok(Outcome::Halted(_)), other) => panic!("{name}: halted against {other:?}"),
    }
}

/// The focused rendering of the reading of `value`, or nothing when it has
/// none.
///
/// # Specification
/// trivial.
fn reading(
    commands: &CommandArena,
    store: &Store,
    value: HeapValueId,
) -> Option<String>
{
    let mut core = CoreArena::new();
    let back = read_back_terminal(commands, store, value, &mut core).ok()?;
    let mut focused = CommandArena::new();
    let root = focus_computation(&core, back, &mut focused, &mut Provenance::new())
        .expect("a reading focuses");
    Some(render_command(&focused, root))
}

/// Whether two runs' outcomes agree: equal answers, the same stop over equal
/// values, or the same decline.
///
/// # Specification
/// - ensures: `Ok` exactly when both halt with answers [`same_value`] accepts,
///   both stop stuck as [`same_stuck`] accepts, or both decline equally.
/// - executable: none — the walk is the comparison; a predicate would walk
///   again.
///
/// # Errors
/// A description of the difference.
///
/// # Adequacy
/// - hypothesis: L2 — equal outcomes agree, and a difference of kind is named.
/// - witness: `tests::support::a_differing_answer_is_named`
fn same_outcome(
    left_store: &Store,
    left: &Result<Outcome, Declined>,
    right_store: &Store,
    right: &Result<Outcome, Declined>,
) -> Result<(), String>
{
    match (left, right) {
        (&Ok(Outcome::Halted(first)), &Ok(Outcome::Halted(second))) => {
            same_value(left_store, first, right_store, second)
        },
        (&Ok(Outcome::Stuck(ref first)), &Ok(Outcome::Stuck(ref second))) => {
            same_stuck(left_store, first, right_store, second)
        },
        (&Err(first), &Err(second)) if first == second => Ok(()),
        (first, second) => Err(format!("{first:?} against {second:?}")),
    }
}

/// Whether two stops are the same: the same reason at the same site, over
/// equal values.
///
/// # Specification
/// - ensures: `Ok` exactly when both name the same reason and site and every
///   value they hold agrees under [`same_value`].
/// - executable: none — the walk is the comparison; a predicate would walk
///   again.
///
/// # Errors
/// A description of the difference.
///
/// # Adequacy
/// - hypothesis: L2 — equal stops agree, and a difference of reason, site or
///   held value is named.
/// - witness: `tests::support::a_differing_answer_is_named`
fn same_stuck(
    left_store: &Store,
    left: &Stuck,
    right_store: &Store,
    right: &Stuck,
) -> Result<(), String>
{
    match (left, right) {
        (
            &Stuck::Unobservable { value, head },
            &Stuck::Unobservable {
                value: other,
                head: also,
            },
        ) if head == also => same_value(left_store, value, right_store, other),
        (
            &Stuck::Unmatched { value, arms },
            &Stuck::Unmatched {
                value: other,
                arms: also,
            },
        ) if arms == also => same_value(left_store, value, right_store, other),
        (&Stuck::NonScalar(value), &Stuck::NonScalar(other)) => {
            same_value(left_store, value, right_store, other)
        },
        (
            &Stuck::ResumedNonStack { at, value },
            &Stuck::ResumedNonStack {
                at: also,
                value: other,
            },
        ) if at == also => same_value(left_store, value, right_store, other),
        (first, second) if first == second => Ok(()),
        (first, second) => Err(format!("{first:?} against {second:?}")),
    }
}

/// One pending pair of values.
type Pair = (HeapValueId, HeapValueId);

/// Whether the value `left` of `left_store` and `right` of `right_store`
/// are equal: the same literal or constant, the same head over equal fields,
/// the same frames over equal values, or the same suspended code over equal
/// environments.
///
/// # Specification
/// - ensures: `Ok` exactly when every pair the walk reaches agrees; two
///   capabilities agree, their identity being their address in each store.
/// - executable: none — the walk is the comparison; a predicate would walk
///   again.
///
/// # Errors
/// A description of the first pair that differs.
///
/// # Adequacy
/// - hypothesis: L2 — equal literals and constructions agree, and a difference
///   of literal, head, field or presence is named.
/// - witness: `tests::support::a_differing_answer_is_named`
pub fn same_value(
    left_store: &Store,
    left: HeapValueId,
    right_store: &Store,
    right: HeapValueId,
) -> Result<(), String>
{
    let mut pending: Vec<Pair> = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        let held = (left_store.value(left), right_store.value(right));
        let (Some(first), Some(second)) = held
        else {
            return Err(format!("{left:?} or {right:?} dangles"));
        };
        let mut environments = Vec::new();
        match (first, second) {
            (&HeapValue::Literal(ref first), &HeapValue::Literal(ref second))
                if first == second => {},
            (&HeapValue::Opaque(first), &HeapValue::Opaque(second)) if first == second => {},
            (&HeapValue::Code(first), &HeapValue::Code(second)) if first == second => {},
            (&HeapValue::Capability, &HeapValue::Capability) => {},
            (
                &HeapValue::Constructed {
                    ref tag,
                    ref fields,
                },
                &HeapValue::Constructed {
                    tag: ref other,
                    fields: ref others,
                },
            ) if tag == other && fields.len() == others.len() => {
                pending.extend(fields.iter().copied().zip(others.iter().copied()));
            },
            (&HeapValue::Stack { ref frames }, &HeapValue::Stack { frames: ref others })
                if frames.len() == others.len() =>
            {
                for (frame, other) in frames.iter().zip(others.iter()) {
                    match (*frame, *other) {
                        (StackFrame::Apply(argument), StackFrame::Apply(another)) => {
                            pending.push((argument, another));
                        },
                        (StackFrame::Project(side), StackFrame::Project(another))
                            if side == another => {},
                        (StackFrame::Bind(closed), StackFrame::Bind(another))
                            if closed.body == another.body =>
                        {
                            environments.push((closed.environment, another.environment));
                        },
                        (frame, other) => return Err(format!("{frame:?} against {other:?}")),
                    }
                }
            },
            (
                &HeapValue::Thunk { body, environment },
                &HeapValue::Thunk {
                    body: other,
                    environment: others,
                },
            ) if body == other => environments.push((environment, others)),
            (
                &HeapValue::Fixpoint {
                    body,
                    environment,
                    evidence,
                },
                &HeapValue::Fixpoint {
                    body: other,
                    environment: others,
                    evidence: claimed,
                },
            ) if body == other && evidence == claimed => environments.push((environment, others)),
            (
                &HeapValue::Closure {
                    producer,
                    environment,
                },
                &HeapValue::Closure {
                    producer: other,
                    environment: others,
                },
            ) if producer == other => environments.push((environment, others)),
            _ => return Err(format!("{first:?} against {second:?}")),
        }
        for (first, second) in environments {
            let firsts: Vec<_> = left_store.bound_values(first).collect();
            let seconds: Vec<_> = right_store.bound_values(second).collect();
            if firsts.len() != seconds.len() {
                return Err(format!(
                    "environments of {} and {} bindings",
                    firsts.len(),
                    seconds.len()
                ));
            }
            pending.extend(firsts.into_iter().zip(seconds));
        }
    }
    Ok(())
}

/// The comparison names a difference wherever one lies: a literal, a head,
/// a field beneath a constructor, a value one store lacks, the value or the
/// head a stop holds, and a halt against a decline.
#[test]
fn a_differing_answer_is_named()
{
    let literal = |value: u8| {
        let magnitude = Magnitude::from_decimal_text(value.to_string()).expect("decimal digits");
        HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude,
        )))
    };
    let construct = |side: Side, field: HeapValueId| HeapValue::Constructed {
        tag: ConstructorTag::Injection(side.into()),
        fields: Box::from([field]),
    };
    let mut left = Store::new();
    let mut right = Store::new();
    let allocate = |store: &mut Store, value: HeapValue| store.allocate(value).expect("room");
    let one = allocate(&mut left, literal(1));
    let other_one = allocate(&mut right, literal(1));
    let two = allocate(&mut right, literal(2));
    let boxed_one = allocate(&mut left, construct(Side::Left, one));
    let other_boxed_one = allocate(&mut right, construct(Side::Left, other_one));
    let boxed_two = allocate(&mut right, construct(Side::Left, two));
    let other_head = allocate(&mut right, construct(Side::Right, other_one));
    assert_eq!(
        Ok(()),
        same_value(&left, one, &right, other_one),
        "equal literals agree"
    );
    assert_eq!(
        Ok(()),
        same_value(&left, boxed_one, &right, other_boxed_one),
        "equal constructions agree"
    );
    for (first, second, what) in [
        (one, two, "a literal"),
        (boxed_one, boxed_two, "a field beneath a constructor"),
        (boxed_one, other_head, "a head"),
        (one, other_boxed_one, "a literal against a construction"),
    ] {
        assert!(
            same_value(&left, first, &right, second).is_err(),
            "{what} differs"
        );
    }
    assert!(
        same_value(&left, one, &Store::new(), one).is_err(),
        "a value one store lacks"
    );
    let unobservable = |value, head| Ok(Outcome::Stuck(Stuck::Unobservable { value, head }));
    let force = gandr_core_sequent::DestructorTag::Force;
    let apply = gandr_core_sequent::DestructorTag::Apply;
    assert_eq!(
        Ok(()),
        same_outcome(
            &left,
            &unobservable(boxed_one, force),
            &right,
            &unobservable(other_boxed_one, force)
        ),
        "equal stops agree"
    );
    let exhausted = Err(Declined::Exhausted(
        gandr_runtime_emitter::Status::FuelExhausted,
    ));
    assert_eq!(
        Ok(()),
        same_outcome(&left, &exhausted, &right, &exhausted),
        "equal declines agree"
    );
    for (first, second, what) in [
        (
            unobservable(boxed_one, force),
            unobservable(boxed_two, force),
            "a stop's value",
        ),
        (
            unobservable(boxed_one, force),
            unobservable(other_boxed_one, apply),
            "a stop's head",
        ),
        (
            Ok(Outcome::Halted(one)),
            exhausted,
            "a halt against a decline",
        ),
    ] {
        assert!(
            same_outcome(&left, &first, &right, &second).is_err(),
            "{what} differs"
        );
    }
}
