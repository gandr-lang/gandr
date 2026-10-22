//! The host seam on each tier: an operation no handler of the run claims is
//! offered to a scripted host, whose decisions — resume, decline, abort — the
//! run's outcome and the order of its offers are checked against.

use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::string::String;
use alloc::sync::Arc;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::check_command;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_value;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::control::EffectClause;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::host::HostSignatures;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostOutcome;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_on_with_host;
use gandr_runtime_emitter::evaluate_with_host;

/// The decimal digits of a test literal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digits(&'static str);

/// The jumps a run may take: no test program comes near.
///
/// # Specification
/// trivial.
fn budget() -> Fuel
{
    Fuel::from(1_usize << 20)
}

/// The tiers this host runs: native where a patcher exists, the executor
/// everywhere.
///
/// # Specification
/// trivial.
fn tiers() -> &'static [Tier]
{
    if PATCHER {
        &[Tier::Native, Tier::Executor]
    }
    else {
        &[Tier::Executor]
    }
}

/// The non-negative integer literal `digits` in `core`.
///
/// # Specification
/// trivial.
fn integer(
    core: &mut CoreArena,
    digits: Digits,
) -> ValueId
{
    let magnitude = Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits");
    core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        magnitude,
    )))
}

/// An interface `name` of one integer operation `operation`.
///
/// # Specification
/// trivial.
fn effect(
    core: &mut CoreArena,
    name: EffectName,
    operation: OperationName,
) -> EffectSig
{
    let integer = core.value_type_base(BaseType::Integer);
    EffectSig::new(name, [EffectOp {
        name: operation,
        payload: integer,
        reply: integer,
    }])
    .expect("one operation")
}

/// A handler of the one-operation `signature` over `subject`.
///
/// # Specification
/// trivial.
fn handler(
    core: &mut CoreArena,
    signature: EffectSig,
    subject: ComputationId,
    on_return: ComputationId,
    body: ComputationId,
) -> ComputationId
{
    let operation = signature
        .operations()
        .next()
        .expect("one-operation fixture")
        .name
        .clone();
    core.computation_handle(
        signature,
        subject,
        on_return,
        Arc::from([EffectClause { operation, body }]),
    )
}

/// One expected offer and the decision the host makes on it.
#[derive(Clone, Copy, Debug)]
struct Offer
{
    /// The interface's name.
    signature: &'static str,
    /// The operation within it.
    operation: &'static str,
    /// The payload's closed reading.
    payload: ValueId,
    /// The decision for this offer.
    answer: Answer,
}

/// A scripted host's decision.
#[derive(Clone, Copy, Debug)]
enum Answer
{
    /// Resume with a newly allocated integer.
    Integer(Digits),
    /// Resume with a newly allocated unit.
    Unit,
    /// Resume with the offered payload itself.
    Payload,
    /// Resume with a fresh copy of the offered payload.
    Copy,
    /// Leave the operation unhandled.
    Decline,
    /// Resume with a value the host builds itself.
    Built(Built),
}

/// A value a host builds for its reply, of a kind the run holds by a table or
/// does not hold at all.
#[derive(Clone, Copy, Debug)]
enum Built
{
    /// The text literal `reply`.
    Text,
    /// The unit in the left summand.
    Left,
    /// The opaque constant 7.
    Opaque,
    /// The nullary first constructor of the datatype declared at constant 0.
    Data,
    /// A capability, which no handler of the run introduced.
    Capability,
    /// Code the host built, which no function's code table holds.
    Code,
    /// The empty list, whose head no run of these programs builds.
    Nil,
}

/// What a hosted run is expected to end with.
#[derive(Clone, Copy, Debug)]
enum Expected
{
    /// A halted value, compared by its reading.
    Value(ValueId),
    /// Stuck at the perform of this interface and operation.
    Perform(&'static str, &'static str),
}

/// A host that expects its offers in order and decides each as scripted.
struct ScriptedHost<'core>
{
    /// The arena payloads are read back into.
    core: &'core mut CoreArena,
    /// The offers still expected, the next first.
    offers: VecDeque<Offer>,
}

impl HostHandler for ScriptedHost<'_>
{
    type Abort = core::convert::Infallible;

    /// Check the offer against the next expected one, then decide it.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        let expected = self.offers.pop_front().expect("no unsolicited host offer");
        assert_eq!(
            (expected.signature, expected.operation),
            (
                request.signature.name().as_ref(),
                request.operation.as_ref()
            )
        );
        assert!(
            request
                .signature
                .types()
                .all(|ty| values.annotations().value_type(ty).is_some()),
            "the offered interface's types resolve among the host's annotations"
        );
        let actual = values
            .read_back_value(request.payload, self.core)
            .expect("a closed payload reads back");
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(self.core, expected.payload, actual)
        );
        match expected.answer {
            Answer::Integer(digits) => HostReply::Resume(
                values
                    .allocate(HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
                        Sign::NonNegative,
                        Magnitude::from_decimal_text(String::from(digits.0))
                            .expect("decimal reply"),
                    ))))
                    .expect("the reply fits"),
            ),
            Answer::Unit => HostReply::Resume(
                values
                    .allocate(HeapValue::Constructed {
                        tag: ConstructorTag::Tuple(ProducerArity::ZERO),
                        fields: Box::new([]),
                    })
                    .expect("the reply fits"),
            ),
            Answer::Payload => HostReply::Resume(request.payload),
            Answer::Copy => {
                let copy = values
                    .value(request.payload)
                    .cloned()
                    .expect("the payload is held");
                HostReply::Resume(values.allocate(copy).expect("the reply fits"))
            },
            Answer::Decline => HostReply::Decline,
            Answer::Built(built) => {
                let value = match built {
                    Built::Text => {
                        HeapValue::Literal(Literal::Text(StringLiteral::new("reply".into())))
                    },
                    Built::Left => HeapValue::Constructed {
                        tag: ConstructorTag::Injection(Summand::from(0_usize)),
                        fields: Box::new([values
                            .allocate(HeapValue::Constructed {
                                tag: ConstructorTag::Tuple(ProducerArity::ZERO),
                                fields: Box::new([]),
                            })
                            .expect("the field fits")]),
                    },
                    Built::Opaque => HeapValue::Opaque(ConstantIndex::from(7_usize)),
                    Built::Data => HeapValue::Constructed {
                        tag: ConstructorTag::Data {
                            tag: gandr_kernel_term::ConstructorTag::from(0_usize),
                            arity: ProducerArity::ZERO,
                            family: Some(ConstantIndex::from(0_usize)),
                        },
                        fields: Box::new([]),
                    },
                    Built::Capability => HeapValue::Capability,
                    Built::Code => HeapValue::Code(self.core.value_unit()),
                    Built::Nil => HeapValue::Constructed {
                        tag: ConstructorTag::ListNil,
                        fields: Box::new([]),
                    },
                };
                HostReply::Resume(values.allocate(value).expect("the reply fits"))
            },
        }
    }
}

/// Check one hosted run's outcome against `expected`.
///
/// # Specification
/// trivial.
fn assert_outcome(
    core: &mut CoreArena,
    (arena, store): (&CommandArena, &Store),
    outcome: HostOutcome<core::convert::Infallible>,
    expected: Expected,
)
{
    match (outcome, expected) {
        (HostOutcome::Completed(Outcome::Halted(value)), Expected::Value(expected)) => {
            let actual = read_back_value(arena, store, value, core).expect("the answer reads back");
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(core, actual, expected)
            );
        },
        (
            HostOutcome::Completed(Outcome::Stuck(Stuck::PerformNoHandler(at))),
            Expected::Perform(name, operation),
        ) => {
            let CommandNode::Perform {
                ref signature,
                operation: ref found,
                ..
            } = *arena.command(at).expect("the blamed command")
            else {
                panic!("a decline blames the perform");
            };
            assert_eq!(
                (name, operation),
                (signature.name().as_ref(), found.as_ref())
            );
        },
        (outcome, expected) => panic!("{outcome:?} where {expected:?} was expected"),
    }
}

/// Run `program` with a scripted host on each tier and under the policy:
/// every offer occurs once, in order, and the run ends as `expected` says.
///
/// # Specification
/// trivial.
fn assert_host(
    core: &mut CoreArena,
    program: ComputationId,
    offers: &[Offer],
    expected: Expected,
)
{
    let mut arena = CommandArena::new();
    let root = focus_computation(core, program, &mut arena, &mut Provenance::new())
        .expect("the program focuses");
    assert_eq!(Ok(FreeSet::default()), check_command(&arena, root));
    let definitions = Definitions::new();
    for entry in tiers().iter().copied().map(Some).chain([None]) {
        let mut store = Store::new();
        let mut host = ScriptedHost {
            core: &mut *core,
            offers: offers.iter().copied().collect(),
        };
        let outcome = match entry {
            Some(tier) => evaluate_on_with_host(
                tier,
                (&arena, &definitions, root),
                (budget(), &mut store),
                &mut host,
            ),
            None => evaluate_with_host(
                &arena,
                &definitions,
                root,
                (budget(), &mut store),
                &mut host,
            ),
        }
        .unwrap_or_else(|declined| panic!("{entry:?} declined: {declined}"));
        assert!(
            host.offers.is_empty(),
            "{entry:?}: every prescribed offer occurs"
        );
        assert_outcome(core, (&arena, &store), outcome, expected);
    }
}

/// An operation outside every handler is offered once and resumes with the
/// host's reply.
#[test]
fn a_host_resumes_a_single_unhandled_perform()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let answer = integer(&mut core, Digits("42"));
    let signature = effect(&mut core, "E".into(), "op".into());
    let program = core.computation_perform(signature, "op".into(), five);
    assert_host(
        &mut core,
        program,
        &[Offer {
            signature: "E",
            operation: "op",
            payload: five,
            answer: Answer::Integer(Digits("42")),
        }],
        Expected::Value(answer),
    );
}

/// An exercise through a capability no handler introduced, which only the
/// host holds, is offered to the host and resumes with its reply.
#[test]
fn a_host_answers_an_exercise_through_a_capability_it_holds()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let held = integer(&mut core, Digits("7"));
    let answer = integer(&mut core, Digits("42"));
    let signature = effect(&mut core, "E".into(), "op".into());
    let program = core.computation_exercise(held, signature, "op".into(), five);
    assert_host(
        &mut core,
        program,
        &[Offer {
            signature: "E",
            operation: "op",
            payload: five,
            answer: Answer::Integer(Digits("42")),
        }],
        Expected::Value(answer),
    );
}

/// A declined operation leaves the run stuck at its perform.
#[test]
fn a_host_decline_blames_the_perform()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let identity = core.computation_return(zero);
    let signature = effect(&mut core, "E".into(), "op".into());
    let perform = core.computation_perform(signature, "op".into(), five);
    let program = core.computation_bind(perform, identity);
    assert_host(
        &mut core,
        program,
        &[Offer {
            signature: "E",
            operation: "op",
            payload: five,
            answer: Answer::Decline,
        }],
        Expected::Perform("E", "op"),
    );
}

/// A second operation whose payload is the first's reply is offered after
/// it, with that reply: the offers follow the run, not the source.
#[test]
fn a_host_is_offered_deep_re_entry_in_order()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let ten = integer(&mut core, Digits("10"));
    let ninety_nine = integer(&mut core, Digits("99"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let signature = effect(&mut core, "E".into(), "op".into());
    let first = core.computation_perform(signature.clone(), "op".into(), one);
    let second = core.computation_perform(signature, "op".into(), zero);
    let program = core.computation_bind(first, second);
    assert_host(
        &mut core,
        program,
        &[
            Offer {
                signature: "E",
                operation: "op",
                payload: one,
                answer: Answer::Integer(Digits("10")),
            },
            Offer {
                signature: "E",
                operation: "op",
                payload: ten,
                answer: Answer::Integer(Digits("99")),
            },
        ],
        Expected::Value(ninety_nine),
    );
}

/// An operation of an interface the nearest handler does not handle is
/// offered past it; the handler still answers its own operation after.
#[test]
fn a_host_is_offered_an_operation_past_a_handler_of_another()
{
    let mut core = CoreArena::new();
    let seven = integer(&mut core, Digits("7"));
    let eight = integer(&mut core, Digits("8"));
    let answer = integer(&mut core, Digits("555"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let identity = core.computation_return(zero);
    let keep = effect(&mut core, "E".into(), "keep".into());
    let escape = effect(&mut core, "E".into(), "escape".into());
    let first = core.computation_perform(escape, "escape".into(), seven);
    let second = core.computation_perform(keep.clone(), "keep".into(), eight);
    let subject = core.computation_bind(first, second);
    let clause = core.computation_return(answer);
    let program = handler(&mut core, keep, subject, identity, clause);
    assert_host(
        &mut core,
        program,
        &[Offer {
            signature: "E",
            operation: "escape",
            payload: seven,
            answer: Answer::Integer(Digits("20")),
        }],
        Expected::Value(answer),
    );
}

/// An operation the run's own handler claims never reaches the host.
#[test]
fn a_host_is_never_offered_a_claimed_perform()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let answer = integer(&mut core, Digits("77"));
    let signature = effect(&mut core, "E".into(), "op".into());
    let perform = core.computation_perform(signature.clone(), "op".into(), five);
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let identity = core.computation_return(zero);
    let clause = core.computation_return(answer);
    let program = handler(&mut core, signature, perform, identity, clause);
    assert_host(&mut core, program, &[], Expected::Value(answer));
}

/// The host's reply is an ordinary value to the rest of the run: one plus
/// a reply of nine answers ten.
#[test]
fn a_host_reply_flows_into_the_rest_of_the_run()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let ten = integer(&mut core, Digits("10"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let signature = effect(&mut core, "E".into(), "op".into());
    let perform = core.computation_perform(signature, "op".into(), one);
    let add = PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "add")
        .expect("native add");
    let body = core.computation_primitive(add, Arguments::Binary([zero, one]));
    let program = core.computation_bind(perform, body);
    assert_host(
        &mut core,
        program,
        &[Offer {
            signature: "E",
            operation: "op",
            payload: one,
            answer: Answer::Integer(Digits("9")),
        }],
        Expected::Value(ten),
    );
}

/// A pair and a native list are offered as they read back.
#[test]
fn a_host_reads_first_order_payloads_back_identically()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let three = integer(&mut core, Digits("3"));
    let unit = core.value_unit();
    let pair = core.value_tuple(&[one, two]);
    let nil = core.value_list_nil();
    let tail = core.value_list_cons(three, nil);
    let tail = core.value_list_cons(two, tail);
    let list = core.value_list_cons(one, tail);
    let unit_type = core.value_type_unit();
    let integer_type = core.value_type_base(BaseType::Integer);
    let pair_type = core.value_type_product(&[integer_type, integer_type]);
    let list_type = core.value_type_list(integer_type);
    for (payload, payload_type) in [(pair, pair_type), (list, list_type)] {
        let signature = EffectSig::new("Inspect".into(), [EffectOp {
            name: "see".into(),
            payload: payload_type,
            reply: unit_type,
        }])
        .expect("one operation");
        let program = core.computation_perform(signature, "see".into(), payload);
        assert_host(
            &mut core,
            program,
            &[Offer {
                signature: "Inspect",
                operation: "see",
                payload,
                answer: Answer::Unit,
            }],
            Expected::Value(unit),
        );
    }
}

/// A thunk offered as a payload reads back closed over its environment, and
/// handed back as the reply is the same thunk: forcing it answers seven.
#[test]
fn a_host_reply_of_its_payload_keeps_its_identity()
{
    let mut core = CoreArena::new();
    let seven = integer(&mut core, Digits("7"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let open_body = core.computation_return(zero);
    let open_thunk = core.value_thunk(open_body);
    let closed_body = core.computation_return(seven);
    let closed_thunk = core.value_thunk(closed_body);
    let integer_type = core.value_type_base(BaseType::Integer);
    let returner = core.comp_type_returner(integer_type);
    let thunk_type = core.value_type_thunk(returner);
    let signature = EffectSig::new("Inspect".into(), [EffectOp {
        name: "see".into(),
        payload: thunk_type,
        reply: thunk_type,
    }])
    .expect("one operation");
    let perform = core.computation_perform(signature, "see".into(), open_thunk);
    let force = core.computation_force(zero);
    let force_reply = core.computation_bind(perform, force);
    let lambda = core.computation_lambda(force_reply);
    let program = core.computation_application(lambda, seven);
    assert_host(
        &mut core,
        program,
        &[Offer {
            signature: "Inspect",
            operation: "see",
            payload: closed_thunk,
            answer: Answer::Payload,
        }],
        Expected::Value(seven),
    );
}

/// The process exit status a host abort carries.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExitCode(u8);

/// A host that stops the run at its first offer, or resumes with a value it
/// names.
struct ExitPolicy
{
    /// The reply, or none to abort.
    reply: Option<HeapValueId>,
    /// The offers seen.
    calls: usize,
}

impl HostHandler for ExitPolicy
{
    type Abort = ExitCode;

    /// Stop at `Proc.exit`, or resume with the named reply.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        self.calls = self.calls.saturating_add(1);
        assert_eq!(
            self.calls, 1,
            "the continuation never runs after an abort or a refused reply"
        );
        assert_eq!(
            (
                request.signature.name().as_ref(),
                request.operation.as_ref()
            ),
            ("Proc", "exit")
        );
        self.reply.map_or(HostReply::Abort(ExitCode(7)), |value| {
            assert!(values.value(value).is_none(), "the reply is foreign");
            HostReply::Resume(value)
        })
    }
}

/// An abort ends the run with the host's result and the operation after it
/// is never offered; a reply naming a value the caller's store does not hold
/// declines the run, the operation after it never offered either.
#[test]
fn a_host_abort_never_resumes_and_a_missing_reply_declines()
{
    let mut core = CoreArena::new();
    let host = HostSignatures::new(&mut core).expect("host interfaces");
    let seven = integer(&mut core, Digits("7"));
    let exit = core.computation_perform(host.proc, "exit".into(), seven);
    let unit = core.value_unit();
    let unreachable = core.computation_perform(host.env, "path".into(), unit);
    let program = core.computation_bind(exit, unreachable);
    let mut arena = CommandArena::new();
    let root = focus_computation(&core, program, &mut arena, &mut Provenance::new())
        .expect("the exit sequence focuses");
    let definitions = Definitions::new();
    let mut foreign = Store::new();
    let unit_value = || HeapValue::Constructed {
        tag: ConstructorTag::Tuple(ProducerArity::ZERO),
        fields: Box::new([]),
    };
    let mut missing = foreign.allocate(unit_value()).expect("a foreign value");
    for _ in 0_u32 .. 32_u32 {
        missing = foreign.allocate(unit_value()).expect("a foreign value");
    }
    for &tier in tiers() {
        let mut abort = ExitPolicy {
            reply: None,
            calls: 0,
        };
        assert_eq!(
            Ok(HostOutcome::Aborted(ExitCode(7))),
            evaluate_on_with_host(
                tier,
                (&arena, &definitions, root),
                (budget(), &mut Store::new()),
                &mut abort
            ),
            "{tier:?}"
        );
        assert_eq!(1, abort.calls, "{tier:?}");
        let mut invalid = ExitPolicy {
            reply: Some(missing),
            calls: 0,
        };
        assert_eq!(
            Err(Declined::Reply(missing)),
            evaluate_on_with_host(
                tier,
                (&arena, &definitions, root),
                (budget(), &mut Store::new()),
                &mut invalid
            ),
            "{tier:?}"
        );
        assert_eq!(1, invalid.calls, "{tier:?}");
    }
}

/// A reply the host builds of a text literal, an injection, an opaque
/// constant or a datatype's constructor is laid into the run and is the
/// run's answer, read back as built.
#[test]
fn a_host_built_reply_of_a_tabled_kind_is_the_answer()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let unit_type = core.value_type_unit();
    let text = core.value_literal(Literal::Text(StringLiteral::new("reply".into())));
    let text_type = core.value_type_base(BaseType::String);
    let left = core.value_injection(Summand::from(0_usize), unit);
    let sum_type = core.value_type_sum(&[unit_type, unit_type]);
    let opaque = core.value_constant(ConstantIndex::from(7_usize));
    let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let zero = core.value_constructor(
        nat,
        gandr_kernel_term::ConstructorTag::from(0_usize),
        Vec::new(),
    );
    for (built, reply, reply_type) in [
        (Built::Text, text, text_type),
        (Built::Left, left, sum_type),
        (Built::Opaque, opaque, unit_type),
        (Built::Data, zero, nat),
    ] {
        let signature = EffectSig::new("Ask".into(), [EffectOp {
            name: "ask".into(),
            payload: unit_type,
            reply: reply_type,
        }])
        .expect("one operation");
        let program = core.computation_perform(signature, "ask".into(), unit);
        assert_host(
            &mut core,
            program,
            &[Offer {
                signature: "Ask",
                operation: "ask",
                payload: unit,
                answer: Answer::Built(built),
            }],
            Expected::Value(reply),
        );
    }
}

/// A reply whose head or code the function builds itself is laid into the
/// run by its row in the function's table: `x <- ask(()); return (x, nil)`
/// answered with a built `nil` is `(nil, nil)`, and
/// `x <- ask(Integer); return (x, Integer)` answered with a fresh copy of its
/// payload is `(Integer, Integer)`, where a run that builds no list declines
/// the same `nil`.
#[test]
fn a_host_reply_the_function_tables_is_the_answer()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let unit_type = core.value_type_unit();
    let integer_type = core.value_type_base(BaseType::Integer);
    let list_type = core.value_type_list(integer_type);
    let nil = core.value_list_nil();
    let quoted = core.value_quote(integer_type);
    for (payload, answer, held, reply_type) in [
        (unit, Answer::Built(Built::Nil), nil, list_type),
        (quoted, Answer::Copy, quoted, unit_type),
    ] {
        let signature = EffectSig::new("Ask".into(), [EffectOp {
            name: "ask".into(),
            payload: unit_type,
            reply: reply_type,
        }])
        .expect("one operation");
        let asked = core.computation_perform(signature, "ask".into(), payload);
        let reply = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let pair = core.value_tuple(&[reply, held]);
        let returned = core.computation_return(pair);
        let program = core.computation_bind(asked, returned);
        let expected = core.value_tuple(&[held, held]);
        assert_host(
            &mut core,
            program,
            &[Offer {
                signature: "Ask",
                operation: "ask",
                payload,
                answer,
            }],
            Expected::Value(expected),
        );
    }
}

/// A reply the run cannot hold declines the run naming the reply: a
/// capability or code the host built, and a list whose head the function's
/// table lacks.
#[test]
fn a_host_built_reply_the_run_cannot_hold_declines()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let unit_type = core.value_type_unit();
    let signature = EffectSig::new("Ask".into(), [EffectOp {
        name: "ask".into(),
        payload: unit_type,
        reply: unit_type,
    }])
    .expect("one operation");
    let program = core.computation_perform(signature, "ask".into(), unit);
    let mut arena = CommandArena::new();
    let root = focus_computation(&core, program, &mut arena, &mut Provenance::new())
        .expect("the program focuses");
    let definitions = Definitions::new();
    for built in [Built::Capability, Built::Code, Built::Nil] {
        for entry in tiers().iter().copied().map(Some).chain([None]) {
            let mut store = Store::new();
            let mut host = ScriptedHost {
                core: &mut core,
                offers: VecDeque::from([Offer {
                    signature: "Ask",
                    operation: "ask",
                    payload: unit,
                    answer: Answer::Built(built),
                }]),
            };
            let ran = match entry {
                Some(tier) => evaluate_on_with_host(
                    tier,
                    (&arena, &definitions, root),
                    (budget(), &mut store),
                    &mut host,
                ),
                None => evaluate_with_host(
                    &arena,
                    &definitions,
                    root,
                    (budget(), &mut store),
                    &mut host,
                ),
            };
            assert!(
                host.offers.is_empty(),
                "{built:?} on {entry:?}: offered once"
            );
            assert!(
                matches!(ran, Err(Declined::Reply(_))),
                "{built:?} on {entry:?}: {ran:?}"
            );
        }
    }
}
