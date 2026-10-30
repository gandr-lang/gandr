use alloc::collections::BTreeMap;
#[test]
fn annotation_substitution_protects_local_binders()
{
    let mut arena = CoreArena::new();
    let local = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let captured = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let local_type = arena.value_type_element(local, Level::zero());
    let captured_type = arena.value_type_element(captured, Level::zero());
    let pair = arena.value_type_product(&[local_type, captured_type]);
    let unit = arena.value_type_unit();
    let code = arena.value_quote(unit);
    let closed = super::instantiate_value_type_under(&mut arena, pair, code, Binders::ONE);
    assert_eq!(
        arena.value_type(closed),
        Some(&ValueType::Product([local_type, unit].into()))
    );
}
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Binders;
use super::Carried;
use super::Crossing;
use super::Nesting;
use super::Node;
use super::Renaming;
use super::Unenclosed;
use super::constructor_classifier;
use super::constructor_classifier_at;
use super::cross_reducts;
use super::elaborate_nested_traced;
use super::fill_comp_type_hole;
use super::fill_hole;
use super::fill_value_hole;
use super::fill_value_type_hole;
use super::instantiate_comp_type;
use super::instantiate_value;
use super::relevel_value_type;
use super::rename_value_traced;
use super::rename_value_type_traced;
use super::shift_comp_type;
use super::shift_value_type;
use super::strengthen_comp_type;
use super::strengthen_value;
use super::strengthen_value_type;
use super::strengthening;
use super::substitute_environment;
use super::substitute_environment_comp_type;
use super::substitute_environment_traced;
use super::substitute_environment_value_type;
use super::wrap_marks;
use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::effect::EffectRow;
use crate::effect::capability::CapabilityGrade;
use crate::effect::capability::Region;
use crate::effect::capability::RegionBinder;
use crate::effect::capability::RegionDepth;
use crate::hole::HoleId;
use crate::hole::MarkIndex;
use crate::hole::NominationIndex;
use crate::hole::TermId;
use crate::relocation::Relocated;
use crate::syntax::CompType;
use crate::syntax::Computation;
use crate::syntax::Value;
use crate::syntax::ValueType;
use crate::syntax::Zone;

#[test]
fn an_abstraction_replaces_its_constant_by_a_variable_under_binders()
{
    let mut arena = CoreArena::new();
    let decoder = ConstantIndex::from(1_usize);
    let other = ConstantIndex::from(2_usize);
    // `U (El(el x) → F (El(el y)))`, the codomain under the arrow's binder.
    let decode = |arena: &mut CoreArena, constant: ConstantIndex, at: DeBruijnIndex| {
        let head = arena.value_constant(constant);
        let forced = arena.computation_force(head);
        let argument = arena.value_variable(Zone::Intuitionistic, at);
        let call = arena.computation_application(forced, argument);
        let code = arena.value_returned(call);
        arena.value_type_element(code, Level::zero())
    };
    let domain = decode(&mut arena, decoder, DeBruijnIndex::from(0_u32));
    let codomain = decode(&mut arena, decoder, DeBruijnIndex::from(1_u32));
    let returner = arena.comp_type_returner(codomain);
    let pi = arena.comp_type_pi(domain, returner);
    let subject = arena.value_type_thunk(pi);
    let read = super::abstract_constant_value_type(
        &mut arena,
        subject,
        decoder,
        DeBruijnIndex::from(5_u32),
    );
    // The decoder's head and argument in `El(head argument)`.
    let call = |arena: &CoreArena, decoded: ValueTypeId| {
        let Some(&ValueType::Element { code, .. }) = arena.value_type(decoded)
        else {
            panic!("a decode");
        };
        let Some(&Value::Returned(call)) = arena.value(code)
        else {
            panic!("a returned call");
        };
        let Some(&Computation::Application(forced, argument)) = arena.computation(call)
        else {
            panic!("an application");
        };
        let Some(&Computation::Force(head)) = arena.computation(forced)
        else {
            panic!("a forced head");
        };
        (arena.value(head).cloned(), arena.value(argument).cloned())
    };
    let variable = |index: u32| {
        Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        })
    };
    let Some(&ValueType::Thunk(pi)) = arena.value_type(read)
    else {
        panic!("a thunk");
    };
    let Some(&CompType::Pi { domain, codomain }) = arena.comp_type(pi)
    else {
        panic!("an arrow");
    };
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(codomain)
    else {
        panic!("a returner");
    };
    // The domain stands under no binder: the variable at the index. The
    // codomain stands under the arrow's: one past it. The arguments stand.
    assert_eq!(call(&arena, domain), (variable(5), variable(0)));
    assert_eq!(call(&arena, result), (variable(6), variable(1)));
    let unrelated = decode(&mut arena, other, DeBruijnIndex::from(0_u32));
    assert_eq!(
        super::abstract_constant_value_type(
            &mut arena,
            unrelated,
            decoder,
            DeBruijnIndex::from(5_u32)
        ),
        unrelated,
        "a type naming another constant is kept"
    );
}

/// A variable read: its zone and its index.
type Read = (Zone, u32);

/// Where a receive's body reads its payload `x` and a free variable `n`:
/// at the root, past a nested receive and a fork's parent, and inside a
/// lambda there.
#[derive(Clone, Copy)]
struct Reads
{
    /// `(held, count)` at the body's root.
    root: (Read, Read),
    /// `(held, count)` in the fork's parent.
    parent: (Read, Read),
    /// `(held, count)` inside the parent's lambda.
    lambda: (Read, Read),
}

/// `return (held, count) to returned. recv(c) as payload ;
/// fork (e : Integer) { close(e) } as d ;
/// return (held, payload, count, returned, thunk (\argument. return (held,
/// count, argument)))`, with `held` and `count` read as `reads` says and `c`
/// the linear index one past the payload.
///
/// # Specification
/// trivial.
fn exchange(
    arena: &mut CoreArena,
    reads: Reads,
) -> ComputationId
{
    use crate::session::SessionAction;
    let value = |arena: &mut CoreArena, (zone, index): Read| {
        arena.value_variable(zone, DeBruijnIndex::from(index))
    };
    let pair = [value(arena, reads.root.0), value(arena, reads.root.1)];
    let pair = arena.value_tuple(&pair);
    let bound = arena.computation_return(pair);
    let held = value(arena, reads.lambda.0);
    let count = value(arena, reads.lambda.1);
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let inner = arena.value_tuple(&[held, count, argument]);
    let inner = arena.computation_return(inner);
    let lambda = arena.computation_lambda(inner);
    let thunk = arena.value_thunk(lambda);
    let held = value(arena, reads.parent.0);
    let count = value(arena, reads.parent.1);
    let payload = arena.value_variable(Zone::Linear, DeBruijnIndex::from(1_u32));
    let returned = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outcome = arena.value_tuple(&[held, payload, count, returned, thunk]);
    let parent = arena.computation_return(outcome);
    let child = arena.computation_session(SessionAction::Close {
        endpoint: DeBruijnIndex::from(0_u32),
    });
    let protocol = arena.value_type_base(BaseType::Integer);
    let fork = arena.computation_session(SessionAction::Fork {
        protocol,
        child,
        parent,
    });
    let received = arena.computation_session(SessionAction::Receive {
        endpoint: DeBruijnIndex::from(1_u32),
        body: fork,
    });
    arena.computation_bind(bound, received)
}

/// #1319: a receive's payload, read at the root, past a nested receive and a
/// fork's parent, and inside a lambda there, becomes the one intuitionistic
/// binder outside the body, counted past the intuitionistic binders between;
/// a free intuitionistic index rises by one; the nested receive's payload and
/// every action subject stay linear.
#[test]
fn a_delinearised_payload_reads_its_binder_past_nested_linear_binders_1319()
{
    let linear = |index: u32| (Zone::Linear, index);
    let intuitionistic = |index: u32| (Zone::Intuitionistic, index);
    let mut arena = CoreArena::new();
    // Under the bind `returned` is #0 and `count` #1; past the nested receive
    // and the fork's parent `held` is linear #2; inside the lambda `count` is
    // #2.
    let body = exchange(&mut arena, Reads {
        root: (linear(0), intuitionistic(0)),
        parent: (linear(2), intuitionistic(1)),
        lambda: (linear(2), intuitionistic(2)),
    });
    // `held` is the new binder: #0 at the root, #1 under the bind, #2 inside
    // the lambda; `count` rises past it.
    let expected = exchange(&mut arena, Reads {
        root: (intuitionistic(0), intuitionistic(1)),
        parent: (intuitionistic(1), intuitionistic(2)),
        lambda: (intuitionistic(2), intuitionistic(3)),
    });
    let delinearised = super::delinearise(&mut arena, body);
    let (delinearised, expected) = (arena.value_thunk(delinearised), arena.value_thunk(expected));
    assert_eq!(
        crate::syntax::equal_certificate_syntax(&arena, delinearised, expected),
        crate::syntax::CertificateEquality::Equal
    );
}

/// `return (out, n) to _. abort(v) ; hold s = out ; { consume(s) to _.
/// fork (e : Integer) { close(e) } as d ; close(c) ; return (s, c, n) }`,
/// with `n` the innermost intuitionistic variable and `out`, `v` and `c` the
/// free linear slots `0`, `1` and `0` counted from where each is read, each
/// raised by `raised`.
///
/// # Specification
/// trivial.
fn held_and_forked(
    arena: &mut CoreArena,
    raised: Binders,
) -> ComputationId
{
    use crate::memory::HoldGrade;
    use crate::memory::MemoryForm;
    use crate::session::SessionAction;
    // A free slot `index` linear binders out past those the read stands under.
    let free = |past: u32| DeBruijnIndex::from(past.saturating_add(raised.0));
    let n = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    // Inside the fork's parent: `d` is #0, `s` #1, and `c` the free slot #2.
    let s = arena.value_variable(Zone::Linear, DeBruijnIndex::from(1_u32));
    let c = arena.value_variable(Zone::Linear, free(2));
    let outcome = arena.value_tuple(&[s, c, n]);
    let outcome = arena.computation_return(outcome);
    let closed = arena.computation_session(SessionAction::Close { endpoint: free(2) });
    let parent = arena.computation_bind(closed, outcome);
    let child = arena.computation_session(SessionAction::Close {
        endpoint: DeBruijnIndex::from(0_u32),
    });
    let protocol = arena.value_type_base(BaseType::Integer);
    let fork = arena.computation_session(SessionAction::Fork {
        protocol,
        child,
        parent,
    });
    let consumed = arena.computation_memory(MemoryForm::Consume {
        held: DeBruijnIndex::from(0_u32),
    });
    let scope = arena.computation_bind(consumed, fork);
    let out = arena.value_variable(Zone::Linear, free(0));
    let held = arena.computation_memory(MemoryForm::Hold {
        value: out,
        body: scope,
        grade: HoldGrade::Many,
    });
    let aborted = arena.computation_memory(MemoryForm::Abort { view: free(1) });
    let rest = arena.computation_bind(aborted, held);
    let pair = arena.value_tuple(&[out, n]);
    let first = arena.computation_return(pair);
    arena.computation_bind(first, rest)
}

/// #1500: a linear raise moves every free linear read — a variable, an
/// endpoint, a resident — past the binders the subject opens above it, and
/// leaves the hold's slot and the fork's end it binds, and every
/// intuitionistic variable, as they stand.
#[test]
fn a_linear_raise_moves_only_the_free_linear_indices_1500()
{
    let mut arena = CoreArena::new();
    let subject = held_and_forked(&mut arena, Binders::NONE);
    let expected = held_and_forked(&mut arena, Binders::from(2_u32));
    assert_ne!(subject, expected, "the raise moves something");
    let mut carried = Vec::new();
    let raised =
        super::raise_linear_traced(&mut arena, subject, Binders::from(2_u32), &mut carried);
    assert!(
        carried.contains(&Carried::Computation(subject, raised)),
        "the trace reports the subject's root rewritten: {carried:?}"
    );
    let (raised, expected) = (arena.value_thunk(raised), arena.value_thunk(expected));
    assert_eq!(
        crate::syntax::equal_certificate_syntax(&arena, raised, expected),
        crate::syntax::CertificateEquality::Equal
    );
    assert_eq!(
        super::raise_linear_traced(&mut arena, subject, Binders::NONE, &mut carried),
        subject,
        "a raise by nothing answers the subject"
    );
}

#[test]
fn native_motives_preserve_binder_and_field_order()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0));
    let one = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1));
    let nominal = ConstantIndex::from(7);
    let datatype = arena.value_type_data(nominal, vec![zero, one]);
    let motive = arena.comp_type_returner(datatype);
    let shifted = super::shift_comp_type_under(&mut arena, motive, Binders::ONE, Binders::from(2))
        .settle(&mut arena);
    let Some(&CompType::Returner {
        result: shifted, ..
    }) = arena.comp_type(shifted)
    else {
        panic!("returner motive");
    };
    let Some(matched_native_node) = arena.value_type(shifted)
    else {
        panic!("nominal motive");
    };
    let ValueType::Data {
        ref declaration,
        ref arguments,
    } = *matched_native_node
    else {
        panic!("nominal motive");
    };
    assert_eq!(*declaration, nominal);
    assert_eq!(
        arena.value(arguments[0]),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0)
        })
    );
    assert_eq!(
        arena.value(arguments[1]),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(3)
        })
    );

    let instantiated = super::instantiate_value_type(&mut arena, datatype, one);
    let Some(matched_native_node) = arena.value_type(instantiated)
    else {
        panic!("nominal substitution");
    };
    let ValueType::Data { ref arguments, .. } = *matched_native_node
    else {
        panic!("nominal substitution");
    };
    assert_eq!(
        arena.value(arguments[0]),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1)
        })
    );
    assert_eq!(
        arena.value(arguments[1]),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0)
        })
    );

    let constructor =
        arena.value_constructor(datatype, gandr_kernel_term::ConstructorTag::from(1), vec![
            zero, one,
        ]);
    let label = gandr_kernel_term::FieldLabel::from(alloc::string::String::from("field"));
    let record = arena.value_record(alloc::collections::BTreeMap::from([(
        label.clone(),
        constructor,
    )]));
    let shifted = super::shift_value(&mut arena, record, Binders::from(2)).settle(&mut arena);
    let Some(matched_native_node) = arena.value(shifted)
    else {
        panic!("record shift");
    };
    let Value::Record(ref fields) = *matched_native_node
    else {
        panic!("record shift");
    };
    let Some(matched_native_node) = arena.value(fields[&label])
    else {
        panic!("constructor shift");
    };
    let Value::Constructor {
        ref tag,
        ref fields,
        ..
    } = *matched_native_node
    else {
        panic!("constructor shift");
    };
    assert_eq!(*tag, gandr_kernel_term::ConstructorTag::from(1));
    assert_eq!(
        arena.value(fields[0]),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(2)
        })
    );
    assert_eq!(
        arena.value(fields[1]),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(3)
        })
    );
}

/// A family under its own binder lifted past one more binder keeps its
/// own index and lifts the ambient one; a lift of nothing is the family
/// itself.
#[test]
fn a_value_type_under_its_binder_lifts_only_the_ambient_index()
{
    let mut arena = CoreArena::new();
    let own = variable(&mut arena, DeBruijnIndex::from(0));
    let ambient = variable(&mut arena, DeBruijnIndex::from(1));
    let nominal = ConstantIndex::from(7);
    let family = arena.value_type_data(nominal, vec![own, ambient]);
    assert_eq!(
        super::shift_value_type_under(&mut arena, family, Binders::ONE, Binders::NONE),
        Relocated::from(family)
    );
    let lifted = super::shift_value_type_under(&mut arena, family, Binders::ONE, Binders::ONE)
        .settle(&mut arena);
    let Some(lifted) = arena.value_type(lifted)
    else {
        panic!("the family is in the arena");
    };
    let ValueType::Data { ref arguments, .. } = *lifted
    else {
        panic!("the family keeps its former");
    };
    let indices: Vec<Option<&Value>> = arguments
        .iter()
        .map(|&argument| arena.value(argument))
        .collect();
    assert_eq!(indices, [
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0)
        }),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(2)
        }),
    ]);
}

/// An intuitionistic occurrence at `index`.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, index)
}

/// The value type `El x` at the variable `index`.
///
/// # Specification
/// trivial.
fn decoded(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueTypeId
{
    let code = variable(arena, index);
    arena.value_type_element(code, Level::zero())
}

/// One token of a type's pre-order spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Token
{
    Returner,
    Arrow,
    Pi,
    CompElement,
    Base(BaseType),
    Element,
    Thunk,
    Product,
    Variable(u32),
    Constant(ConstantIndex),
    Pair,
    Quote,
    QuoteComputation,
    StaticLambda,
    StaticApplication,
    Other,
}

/// A node the spelling walk visits.
#[derive(Clone, Copy)]
enum Visit
{
    Value(ValueId),
    ValueType(ValueTypeId),
    CompType(CompTypeId),
}

/// The pre-order spelling of a computation type, through the formers the
/// generator writes: two types spell alike exactly when they are equal up
/// to node identity.
///
/// # Specification
/// trivial.
fn spelling(
    arena: &CoreArena,
    root: CompTypeId,
) -> Vec<Token>
{
    spelling_of(arena, Visit::CompType(root))
}

/// The pre-order spelling of a value, through the formers the static
/// tests write.
///
/// # Specification
/// trivial.
fn value_spelling(
    arena: &CoreArena,
    root: ValueId,
) -> Vec<Token>
{
    spelling_of(arena, Visit::Value(root))
}

/// The pre-order spelling of any node the walk visits.
///
/// # Specification
/// - requires: an acyclic arena graph in the reference fragment.
/// - ensures: a pre-order token sequence; unsupported or missing nodes emit
///   `Other`, so the observer does not separate those forms.
/// - provides: an identity-independent reading for finite reference checks.
/// - panics: none for the admitted graph.
///
/// # Adequacy
/// - hypothesis: L3 — an asymmetric dependent tree and a static application
///   have exact pre-order token sequences; these separate root-family
///   confusion, reversed child order and omitted variable payloads. Only the
///   generator and static-test fragment has a separating spelling.
/// - witness: `rewrite::tests::reference_helpers_have_ground_and_asymmetric_goldens`
/// - witness: `rewrite::tests::substitution_replaces_a_free_occurrence`
#[spec(ensures: |ret| ret.first() == Some(&match root {
        | Visit::CompType(id) => match arena.comp_type(id) {
            | Some(&CompType::Returner { .. }) => Token::Returner,
            | Some(&CompType::Arrow { .. }) => Token::Arrow,
            | Some(&CompType::Pi { .. }) => Token::Pi,
            | Some(&CompType::Element { .. }) => Token::CompElement,
            | Some(&CompType::Unknown | &CompType::With(..) | &CompType::Codata { .. }) | None => Token::Other,
        },
        | Visit::ValueType(id) => match arena.value_type(id) {
            | Some(&ValueType::Base(base)) => Token::Base(base),
            | Some(&ValueType::Element { .. }) => Token::Element,
            | Some(&ValueType::Thunk(_)) => Token::Thunk,
            | Some(&ValueType::Product(..)) => Token::Product,
            Some(&ValueType::Stack { .. } | &ValueType::List(_) | &ValueType::Data { .. } | &ValueType::Record(_) |
&ValueType::Sum(..) | &ValueType::PathUniverse(..) | &ValueType::Path { .. } | &ValueType::Bridge { .. } | &ValueType::Universe { ..
} | &ValueType::Lift { .. } | &ValueType::Abstract(_) | &ValueType::StaticPi { .. } | &ValueType::Sigma {
.. } | &ValueType::Capability { .. } | &ValueType::World(_) | &ValueType::Unknown | &ValueType::Buffer | &ValueType::Session(_) | &ValueType::Flow { .. } | &ValueType::Run(_) | &ValueType::Prefix(_) | &ValueType::Dialogue(_) | &ValueType::Web | &ValueType::Staged { .. } | &ValueType::Kept { .. } | &ValueType::Row | &ValueType::RowTail(_)) | None => Token::Other,
            },
        | Visit::Value(id) => match arena.value(id) {
            | Some(&Value::Variable { index, .. }) => Token::Variable(u32::from(index)),
            | Some(&Value::Constant(constant)) => Token::Constant(constant),
            | Some(&Value::Tuple(_)) => Token::Pair,
            | Some(&Value::Quote(_)) => Token::Quote,
            | Some(&Value::QuoteComputation(_)) => Token::QuoteComputation,
            | Some(&Value::StaticLambda(_)) => Token::StaticLambda,
            | Some(&Value::StaticApplication(..)) => Token::StaticApplication,
            Some(&Value::Reify(_) | &Value::ListNil | &Value::ListCons(..) | &Value::Constructor { .. } | &Value::Record(_) | &Value::Primitive { .. }
| &Value::Literal(_) | &Value::Injection(..) | &Value::Thunk(_) | &Value::Ascribe { .. }
| &Value::Lift { .. } | &Value::PathRefl(_) | &Value::Here(_) | &Value::Univalence(..) | &Value::Funext(..) | &Value::Equiv(..) | &Value::Ua { .. } | &Value::Compose { .. } | &Value::Returned(_) | &Value::Nested(_) | &Value::Run(_) | &Value::RecordUpdate { .. } | &Value::PathProduct(..) |
&Value::SessionRelated { .. } | &Value::Stay(_) | &Value::Then(..) | &Value::FlowProduct(..) | &Value::Forward(_) | &Value::FunctionFlow(..) | &Value::Recorded(_) | &Value::Dialogue(_) | &Value::Web(_) |
&Value::PathEquiv { .. } | &Value::Hole(_) | &Value::Mark { .. } | &Value::Row(_)) | None => Token::Other,
            },
    }))]
fn spelling_of(
    arena: &CoreArena,
    root: Visit,
) -> Vec<Token>
{
    let mut tokens = Vec::new();
    let mut pending = vec![root];
    while let Some(visit) = pending.pop() {
        match visit {
            Visit::CompType(id) => match arena.comp_type(id) {
                Some(&CompType::Returner { result, .. }) => {
                    tokens.push(Token::Returner);
                    pending.push(Visit::ValueType(result));
                },
                Some(&CompType::Arrow { domain, codomain }) => {
                    tokens.push(Token::Arrow);
                    pending.push(Visit::CompType(codomain));
                    pending.push(Visit::ValueType(domain));
                },
                Some(&CompType::Pi { domain, codomain }) => {
                    tokens.push(Token::Pi);
                    pending.push(Visit::CompType(codomain));
                    pending.push(Visit::ValueType(domain));
                },
                Some(&CompType::Element { code, .. }) => {
                    tokens.push(Token::CompElement);
                    pending.push(Visit::Value(code));
                },
                Some(&CompType::Unknown | &CompType::With(..) | &CompType::Codata { .. })
                | None => {
                    tokens.push(Token::Other);
                },
            },
            Visit::ValueType(id) => match arena.value_type(id) {
                Some(&ValueType::Base(base)) => tokens.push(Token::Base(base)),
                Some(&ValueType::Element { code, .. }) => {
                    tokens.push(Token::Element);
                    pending.push(Visit::Value(code));
                },
                Some(&ValueType::Thunk(body)) => {
                    tokens.push(Token::Thunk);
                    pending.push(Visit::CompType(body));
                },
                Some(&ValueType::Product(ref components)) => {
                    tokens.push(Token::Product);
                    pending.extend(
                        components
                            .iter()
                            .rev()
                            .map(|&component| Visit::ValueType(component)),
                    );
                },
                Some(_) | None => tokens.push(Token::Other),
            },
            Visit::Value(id) => match arena.value(id) {
                Some(&Value::Variable { index, .. }) => {
                    tokens.push(Token::Variable(u32::from(index)));
                },
                Some(&Value::Constant(constant)) => tokens.push(Token::Constant(constant)),
                Some(&Value::Tuple(ref components)) => {
                    tokens.push(Token::Pair);
                    pending.extend(
                        components
                            .iter()
                            .rev()
                            .map(|&component| Visit::Value(component)),
                    );
                },
                Some(&Value::Quote(quoted)) => {
                    tokens.push(Token::Quote);
                    pending.push(Visit::ValueType(quoted));
                },
                Some(&Value::QuoteComputation(quoted)) => {
                    tokens.push(Token::QuoteComputation);
                    pending.push(Visit::CompType(quoted));
                },
                Some(&Value::StaticLambda(body)) => {
                    tokens.push(Token::StaticLambda);
                    pending.push(Visit::Value(body));
                },
                Some(&Value::StaticApplication(head, argument)) => {
                    tokens.push(Token::StaticApplication);
                    pending.push(Visit::Value(argument));
                    pending.push(Visit::Value(head));
                },
                Some(_) | None => tokens.push(Token::Other),
            },
        }
    }
    tokens
}

/// What a generated node is.
#[derive(Clone, Copy, Debug)]
enum Shape
{
    Returner,
    Arrow,
    Pi,
    CompElement,
    Integer,
    Element,
    Thunk,
    Product,
    /// A variable of the context the tree is placed in, by level: level
    /// zero is the outermost binder.
    Free(u32),
    /// A variable bound inside the tree, by level counted from the
    /// tree's own outermost binder.
    Local(u32),
    Quote,
    QuoteComputation,
}

/// What a pending slot of the generator must be filled with.
#[derive(Clone, Copy, Debug)]
enum Kind
{
    Comp,
    ValueType,
    ValueCode,
    CompCode,
}

/// One generated node: its shape, its children in order, and how many of
/// the tree's own binders stand above it.
#[derive(Clone, Debug)]
struct GeneratedNode
{
    shape: Shape,
    children: Vec<usize>,
    binders: u32,
}

/// A generated tree, in pre-order: every child after its parent.
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
struct Tree
{
    nodes: Vec<GeneratedNode>,
}

/// A count the generator draws, bounds or places by.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Count(u32);

/// A deterministic xorshift stream.
#[repr(transparent)]
struct Stream(u64);

impl Stream
{
    /// The next draw below `bound`, which must be positive.
    ///
    /// # Specification
    /// - requires: `bound` is positive.
    /// - ensures: the next deterministic draw is strictly below `bound`.
    /// - provides: a bounded choice for the reference generator.
    /// - panics: none for the admitted positive bound.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — singleton, two-element and maximal positive ranges
    ///   distinguish the exclusive bound; bounded generated codomains exercise
    ///   the resulting choices against an independent reference.
    /// - witness: `rewrite::tests::reference_helpers_have_ground_and_asymmetric_goldens`
    /// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
    #[spec(requires: bound.0 > 0, ensures: |ret| ret.0 < bound.0)]
    fn below(
        &mut self,
        bound: Count,
    ) -> Count
    {
        self.0 ^= self.0.wrapping_shl(13);
        self.0 ^= self.0.wrapping_shr(7);
        self.0 ^= self.0.wrapping_shl(17);
        Count(u32::try_from(self.0.checked_rem(u64::from(bound.0)).unwrap()).unwrap())
    }
}

/// Generate a tree of `kind` over `frees` context levels, using `fuel` to
/// bound compound choices before completing a terminal code or type.
///
/// # Specification
/// - requires: `frees + fuel` fits u32.
/// - ensures: a nonempty pre-order tree of `kind`; children follow their
///   parent, free levels are below `frees`, and local levels are bound.
/// - provides: bounded compound choices; zero fuel still permits the terminal
///   code/type formers needed to reach a variable or base type.
/// - panics: none for the admitted counts.
///
/// # Adequacy
/// - hypothesis: L2 — the 600 deterministic generated trees feed independent
///   level-based and de Bruijn substitution readings. L3 — zero fuel and no
///   free variables have fixed ground spellings in every requested family,
///   distinguishing malformed terminal shapes and child arities.
/// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
/// - witness: `rewrite::tests::reference_helpers_have_ground_and_asymmetric_goldens`
#[spec(
        requires: frees.0.checked_add(fuel.0).is_some(),
        ensures: |ret| ret.nodes.first().is_some_and(|root| root.binders == 0 && match kind {
            | Kind::Comp => matches!(root.shape, Shape::Returner | Shape::Arrow | Shape::Pi | Shape::CompElement),
            | Kind::ValueType => matches!(root.shape, Shape::Integer | Shape::Element | Shape::Thunk | Shape::Product),
            | Kind::ValueCode => matches!(root.shape, Shape::Free(_) | Shape::Local(_) | Shape::Quote),
            | Kind::CompCode => matches!(root.shape, Shape::Free(_) | Shape::Local(_) | Shape::QuoteComputation),
        }) && ret.nodes.iter().enumerate().all(|(here, node)| node.binders <= fuel.0
            && node.children.iter().all(|child| *child > here && *child < ret.nodes.len())
            && match node.shape {
                | Shape::Free(level) => level < frees.0 && node.children.is_empty(),
                | Shape::Local(level) => level < node.binders && node.children.is_empty(),
                | Shape::Integer => node.children.is_empty(),
                | Shape::Arrow | Shape::Pi | Shape::Product => node.children.len() == 2,
                | Shape::Returner | Shape::CompElement | Shape::Element | Shape::Thunk | Shape::Quote | Shape::QuoteComputation => node.children.len() == 1,
            }),
    )]
fn generate(
    stream: &mut Stream,
    kind: Kind,
    frees: Count,
    fuel: Count,
) -> Tree
{
    let frees = frees.0;
    let mut tree = Tree::default();
    // (parent, kind, binders above, fuel left)
    let mut pending: Vec<(Option<usize>, Kind, u32, u32)> = vec![(None, kind, 0, fuel.0)];
    while let Some((parent, kind, binders, fuel)) = pending.pop() {
        let here = tree.nodes.len();
        if let Some(parent) = parent {
            tree.nodes[parent].children.push(here);
        }
        let variables = frees.checked_add(binders).unwrap();
        let leaf = fuel == 0;
        let less = fuel.saturating_sub(1);
        let variable_shape = |stream: &mut Stream| {
            let pick = stream.below(Count(variables)).0;
            if pick < frees {
                Shape::Free(pick)
            }
            else {
                Shape::Local(pick.checked_sub(frees).unwrap())
            }
        };
        // Children are pushed in reverse so they are generated in order.
        let (shape, children): (Shape, Vec<(Kind, u32)>) = match kind {
            Kind::Comp => match (leaf, stream.below(Count(4)).0) {
                (true, _) | (false, 0) => (Shape::Returner, vec![(Kind::ValueType, binders)]),
                (false, 1) => (Shape::Arrow, vec![
                    (Kind::ValueType, binders),
                    (Kind::Comp, binders),
                ]),
                (false, 2) => (Shape::Pi, vec![
                    (Kind::ValueType, binders),
                    (Kind::Comp, binders.checked_add(1).unwrap()),
                ]),
                (false, _) => (Shape::CompElement, vec![(Kind::CompCode, binders)]),
            },
            Kind::ValueType => match (leaf, stream.below(Count(4)).0) {
                (true, 0) | (_, 1) if variables > 0 => {
                    (Shape::Element, vec![(Kind::ValueCode, binders)])
                },
                (true, _) => (Shape::Integer, Vec::new()),
                (false, 0) => (Shape::Thunk, vec![(Kind::Comp, binders)]),
                (false, 2) => (Shape::Product, vec![
                    (Kind::ValueType, binders),
                    (Kind::ValueType, binders),
                ]),
                (false, _) => (Shape::Element, vec![(Kind::ValueCode, binders)]),
            },
            Kind::ValueCode => match (leaf, stream.below(Count(3)).0) {
                (true, _) | (false, 0 | 1) if variables > 0 => (variable_shape(stream), Vec::new()),
                (..) => (Shape::Quote, vec![(Kind::ValueType, binders)]),
            },
            Kind::CompCode => match (leaf, stream.below(Count(3)).0) {
                (true, _) | (false, 0 | 1) if variables > 0 => (variable_shape(stream), Vec::new()),
                (..) => (Shape::QuoteComputation, vec![(Kind::Comp, binders)]),
            },
        };
        tree.nodes.push(GeneratedNode {
            shape,
            children: Vec::new(),
            binders,
        });
        for &(child, child_binders) in children.iter().rev() {
            pending.push((Some(here), child, child_binders, less));
        }
    }
    tree
}

/// A node the builder minted.
#[derive(Clone, Copy, Debug)]
enum Built
{
    Value(ValueId),
    ValueType(ValueTypeId),
    CompType(CompTypeId),
}

/// How the builder reads a free variable.
#[derive(Clone, Copy)]
enum Reading<'tree>
{
    /// As an index at the depth it is reached at.
    Plain,
    /// The context level `binder` is replaced by the argument, built
    /// beforehand at every depth below the tree's own binders:
    /// `arguments[n]` stands under `n` of them. Levels past it drop by one.
    Spliced
    {
        binder: u32,
        arguments: &'tree [ValueId],
    },
    /// The context levels from `from` on stand `amount` levels deeper:
    /// `amount` binders are inserted before them, where a shift past the
    /// innermost `placement - amount - from` binders puts them.
    Inserted
    {
        from: u32, amount: u32
    },
}

/// Mint `tree` into `arena` with its root at absolute depth `placement`,
/// reading free variables as `reading` says.
///
/// # Specification
/// - requires: a nonempty well-formed generated tree; `placement` contains its
///   unspliced free levels, read where `reading` moves them, and every needed
///   replacement depth exists.
/// - ensures: a live arena root interpreting each level at its placement, with
///   the designated spliced level replaced without variable capture and the
///   inserted levels read past the binders inserted before them.
/// - provides: the level-based reference, independent of the rewrite engine.
/// - panics: none for an admitted tree and placement.
///
/// # Adequacy
/// - hypothesis: L2 — the level-based builder is the independent reading used
///   by 600 bounded substitution comparisons and the shift and strengthening
///   comparisons. L3 — ground roots of all three output families and a
///   dependent asymmetric tree pin the oracle against dropped children,
///   reversed order and a misplaced binder.
/// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
/// - witness: `rewrite::tests::reference_helpers_have_ground_and_asymmetric_goldens`
/// - witness: `rewrite::tests::a_settled_shift_agrees_with_the_level_reference`
#[spec(requires: !tree.nodes.is_empty(), ensures: |ret| match ret {
        | Built::Value(id) => arena.value(id).is_some(),
        | Built::ValueType(id) => arena.value_type(id).is_some(),
        | Built::CompType(id) => arena.comp_type(id).is_some(),
    })]
fn build(
    arena: &mut CoreArena,
    tree: &Tree,
    placement: Count,
    reading: Reading<'_>,
) -> Built
{
    let mut built: Vec<Option<Built>> = vec![None; tree.nodes.len()];
    for here in (0 .. tree.nodes.len()).rev() {
        let node = &tree.nodes[here];
        let depth = placement.0.checked_add(node.binders).unwrap();
        let child = |position: usize| built[node.children[position]].unwrap();
        let value_type = |position: usize| match child(position) {
            Built::ValueType(id) => id,
            Built::Value(_) | Built::CompType(_) => panic!("a value-type child"),
        };
        let comp_type = |position: usize| match child(position) {
            Built::CompType(id) => id,
            Built::Value(_) | Built::ValueType(_) => panic!("a computation-type child"),
        };
        let value = |position: usize| match child(position) {
            Built::Value(id) => id,
            Built::ValueType(_) | Built::CompType(_) => panic!("a value child"),
        };
        let minted = match node.shape {
            Shape::Returner => Built::CompType(arena.comp_type_returner(value_type(0))),
            Shape::Arrow => Built::CompType(arena.comp_type_arrow(value_type(0), comp_type(1))),
            Shape::Pi => Built::CompType(arena.comp_type_pi(value_type(0), comp_type(1))),
            Shape::CompElement => Built::CompType(arena.comp_type_element(value(0), Level::zero())),
            Shape::Integer => Built::ValueType(arena.value_type_base(BaseType::Integer)),
            Shape::Element => Built::ValueType(arena.value_type_element(value(0), Level::zero())),
            Shape::Thunk => Built::ValueType(arena.value_type_thunk(comp_type(0))),
            Shape::Product => {
                Built::ValueType(arena.value_type_product(&[value_type(0), value_type(1)]))
            },
            Shape::Quote => Built::Value(arena.value_quote(value_type(0))),
            Shape::QuoteComputation => Built::Value(arena.value_quote_computation(comp_type(0))),
            Shape::Local(level) => {
                let index = node
                    .binders
                    .checked_sub(1)
                    .unwrap()
                    .checked_sub(level)
                    .unwrap();
                Built::Value(variable(arena, DeBruijnIndex::from(index)))
            },
            Shape::Free(level) => match reading {
                Reading::Spliced { binder, arguments } if level == binder => {
                    Built::Value(arguments[usize::try_from(node.binders).unwrap()])
                },
                Reading::Spliced { binder, .. } if level > binder => {
                    let lowered = level.checked_sub(1).unwrap();
                    let index = depth.checked_sub(1).unwrap().checked_sub(lowered).unwrap();
                    Built::Value(variable(arena, DeBruijnIndex::from(index)))
                },
                Reading::Inserted { from, amount } if level >= from => {
                    let moved = level.checked_add(amount).unwrap();
                    let index = depth.checked_sub(1).unwrap().checked_sub(moved).unwrap();
                    Built::Value(variable(arena, DeBruijnIndex::from(index)))
                },
                Reading::Plain | Reading::Spliced { .. } | Reading::Inserted { .. } => {
                    let index = depth.checked_sub(1).unwrap().checked_sub(level).unwrap();
                    Built::Value(variable(arena, DeBruijnIndex::from(index)))
                },
            },
        };
        built[here] = Some(minted);
    }
    built[0].unwrap()
}

#[test]
fn instantiating_a_codomain_avoids_capture()
{
    let mut stream = Stream(0x9E37_79B9_7F4A_7C15);
    for round in 0 .. 600_u32 {
        let outer = round.checked_rem(3).unwrap();
        // The codomain reads the outer context and the dependent arrow's
        // own binder, at level `outer`; the argument reads the outer
        // context alone.
        let codomain = generate(
            &mut stream,
            Kind::Comp,
            Count(outer.checked_add(1).unwrap()),
            Count(4),
        );
        let argument = generate(&mut stream, Kind::ValueCode, Count(outer), Count(3));
        let mut arena = CoreArena::new();
        let Built::CompType(scoped) = build(
            &mut arena,
            &codomain,
            Count(outer.checked_add(1).unwrap()),
            Reading::Plain,
        )
        else {
            panic!("a computation type");
        };
        let Built::Value(supplied) = build(&mut arena, &argument, Count(outer), Reading::Plain)
        else {
            panic!("a value");
        };
        let machine = instantiate_comp_type(&mut arena, scoped, supplied);
        let deepest = codomain
            .nodes
            .iter()
            .map(|node| node.binders)
            .max()
            .unwrap();
        let arguments: Vec<ValueId> = (0 ..= deepest)
            .map(|binders| {
                let placement = Count(outer.checked_add(binders).unwrap());
                match build(&mut arena, &argument, placement, Reading::Plain) {
                    Built::Value(id) => id,
                    Built::ValueType(_) | Built::CompType(_) => panic!("a value"),
                }
            })
            .collect();
        let Built::CompType(reference) =
            build(&mut arena, &codomain, Count(outer), Reading::Spliced {
                binder: outer,
                arguments: &arguments,
            })
        else {
            panic!("a computation type");
        };
        assert_eq!(
            spelling(&arena, reference),
            spelling(&arena, machine),
            "round {round}: the machine agrees with the capture-free reference for {codomain:?} at {argument:?}"
        );
    }
}

#[test]
fn shifting_raises_free_indices_and_spares_bound_ones()
{
    let mut arena = CoreArena::new();
    // Π (_ : El #0). El #0 → F (El #1): the domain's #0 is free, the
    // codomain's #0 is the arrow's own binder and its #1 is free.
    let domain = decoded(&mut arena, DeBruijnIndex::from(0));
    let bound = decoded(&mut arena, DeBruijnIndex::from(0));
    let free = decoded(&mut arena, DeBruijnIndex::from(1));
    let result = arena.comp_type_returner(free);
    let codomain = arena.comp_type_arrow(bound, result);
    let subject = arena.comp_type_pi(domain, codomain);
    let shifted = shift_comp_type(&mut arena, subject, Binders::from(2_u32)).settle(&mut arena);

    let expected_domain = decoded(&mut arena, DeBruijnIndex::from(2));
    let expected_bound = decoded(&mut arena, DeBruijnIndex::from(0));
    let expected_free = decoded(&mut arena, DeBruijnIndex::from(3));
    let expected_result = arena.comp_type_returner(expected_free);
    let expected_codomain = arena.comp_type_arrow(expected_bound, expected_result);
    let expected = arena.comp_type_pi(expected_domain, expected_codomain);
    assert_eq!(
        spelling(&arena, expected),
        spelling(&arena, shifted),
        "free indices rise by the amount and the bound one stands"
    );

    let integer = arena.value_type_base(BaseType::Integer);
    assert_eq!(
        Relocated::from(integer),
        shift_value_type(&mut arena, integer, Binders::from(2_u32)),
        "a closed type shifts to itself"
    );
}

/// A shift answers its subject's own node under a relocation and mints
/// nothing; a second raise that folds into the first mints nothing either,
/// and one that does not fold settles the first before it. Settled, each
/// reads as the type the eager rewrite builds.
#[test]
fn a_shift_is_a_root_update()
{
    let mut arena = CoreArena::new();
    // El #0 → F (El #2).
    let near = decoded(&mut arena, DeBruijnIndex::from(0_u32));
    let far = decoded(&mut arena, DeBruijnIndex::from(2_u32));
    let result = arena.comp_type_returner(far);
    let subject = arena.comp_type_arrow(near, result);
    let integer = arena.value_type_base(BaseType::Integer);
    let closed = arena.comp_type_returner(integer);
    let mark = arena.watermark();
    let shifted = shift_comp_type(&mut arena, subject, Binders::from(2_u32));
    assert_eq!(
        shifted.node(),
        subject,
        "the shift answers the subject's own node"
    );
    assert_ne!(shifted, Relocated::from(subject), "under a relocation");
    assert_eq!(
        Relocated::from(closed),
        shift_comp_type(&mut arena, closed, Binders::ONE),
        "a closed type moves nothing and carries no relocation"
    );
    let again = shift_comp_type(&mut arena, shifted, Binders::ONE);
    assert_eq!(
        again.node(),
        subject,
        "a second raise past the same cutoff folds"
    );
    assert_eq!(mark, arena.watermark(), "no shift minted a node");
    let settled = again.settle(&mut arena);
    let near = decoded(&mut arena, DeBruijnIndex::from(3_u32));
    let far = decoded(&mut arena, DeBruijnIndex::from(5_u32));
    let result = arena.comp_type_returner(far);
    let expected = arena.comp_type_arrow(near, result);
    assert_eq!(
        spelling(&arena, expected),
        spelling(&arena, settled),
        "settled, both raises have moved every free index"
    );

    // F (El #0 × El #3) raised by one, then by one past two: the
    // displacements become +1 and +2, which no single relocation reads.
    let low = decoded(&mut arena, DeBruijnIndex::from(0_u32));
    let high = decoded(&mut arena, DeBruijnIndex::from(3_u32));
    let apart = arena.value_type_product(&[low, high]);
    let apart = arena.comp_type_returner(apart);
    let first = shift_comp_type(&mut arena, apart, Binders::ONE);
    let mark = arena.watermark();
    let second =
        super::shift_comp_type_under(&mut arena, first, Binders::from(2_u32), Binders::ONE);
    assert_ne!(
        mark,
        arena.watermark(),
        "a raise that does not fold settles the first"
    );
    let settled = second.settle(&mut arena);
    let low = decoded(&mut arena, DeBruijnIndex::from(1_u32));
    let high = decoded(&mut arena, DeBruijnIndex::from(5_u32));
    let expected = arena.value_type_product(&[low, high]);
    let expected = arena.comp_type_returner(expected);
    assert_eq!(
        spelling(&arena, expected),
        spelling(&arena, settled),
        "and reads as the two raises in turn"
    );
}

/// A strengthening refuses a type whose carried support selects one of its
/// binders, wherever the mention stands, lowers any other as a root update,
/// and reads a type naming only binders of its own as closed.
#[test]
fn a_strengthening_reads_the_carried_support()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    // U (Integer → F (Integer × El #0)): the binder named three formers down.
    let binder = decoded(&mut arena, DeBruijnIndex::from(0_u32));
    let pair = arena.value_type_product(&[integer, binder]);
    let returner = arena.comp_type_returner(pair);
    let arrow = arena.comp_type_arrow(integer, returner);
    let deep = arena.value_type_thunk(arrow);
    // U (Π (_ : Integer). F (El #0)): the zero is the Pi's own binder.
    let returner = arena.comp_type_returner(binder);
    let pi = arena.comp_type_pi(integer, returner);
    let own = arena.value_type_thunk(pi);
    // U (Integer → F (El #3)): only past both binders.
    let outer = decoded(&mut arena, DeBruijnIndex::from(3_u32));
    let returner = arena.comp_type_returner(outer);
    let arrow = arena.comp_type_arrow(integer, returner);
    let past_both = arena.value_type_thunk(arrow);
    let mark = arena.watermark();
    assert_eq!(
        Maybe::Absent(strengthening::Absent::MentionsBinder),
        strengthen_value_type(&mut arena, deep, Binders::ONE),
        "a mention under three formers is read off the root"
    );
    assert_eq!(
        Maybe::Present(Relocated::from(own)),
        strengthen_value_type(&mut arena, own, Binders::ONE),
        "a type naming only its own binder is closed"
    );
    let Maybe::Present(lowered) =
        strengthen_value_type(&mut arena, past_both, Binders::from(2_u32))
    else {
        panic!("a type reading only past both binders leaves them");
    };
    assert_eq!(
        lowered.node(),
        past_both,
        "the lowering answers the subject's own node"
    );
    assert_eq!(
        Maybe::Absent(strengthening::Absent::MentionsBinder),
        strengthen_value_type(&mut arena, past_both, Binders::from(4_u32)),
        "past four binders its index is one of them"
    );
    assert_eq!(mark, arena.watermark(), "no strengthening minted a node");
    let settled = lowered.settle(&mut arena);
    let outer = decoded(&mut arena, DeBruijnIndex::from(1_u32));
    let returner = arena.comp_type_returner(outer);
    let arrow = arena.comp_type_arrow(integer, returner);
    let expected = arena.value_type_thunk(arrow);
    assert_eq!(
        spelling_of(&arena, Visit::ValueType(expected)),
        spelling_of(&arena, Visit::ValueType(settled)),
        "settled, its index lowers by two"
    );
}

/// The index the code of the decode `child` names, read through its
/// relocation.
///
/// # Specification
/// trivial.
fn read_code(
    arena: &CoreArena,
    child: Relocated<ValueTypeId>,
) -> DeBruijnIndex
{
    let Some(&ValueType::Element { code, .. }) = arena.value_type(child.node())
    else {
        panic!("a decode");
    };
    let Some(&Value::Variable { zone, index }) = arena.value(code)
    else {
        panic!("a variable code");
    };
    child.relocation().variable(zone, index)
}

/// A child read under a relocated node composes the relocation with the
/// binders the child's position crosses, and a variable reads through it at
/// its occurrence; nothing is minted, and the reads agree with the settled
/// node.
#[test]
fn a_renaming_composes_on_a_child_read_and_applies_at_a_variable()
{
    let mut arena = CoreArena::new();
    // Σ (_ : El #0). El #1: the second factor reads the outer #0 past the
    // first factor's binder.
    let first = decoded(&mut arena, DeBruijnIndex::from(0_u32));
    let second = decoded(&mut arena, DeBruijnIndex::from(1_u32));
    let sigma = arena.value_type_sigma(first, second);
    let at = shift_value_type(&mut arena, sigma, Binders::from(2_u32)).relocation();
    let mark = arena.watermark();
    let first_read = arena.place_value_type(first, at);
    let second_read = arena.place_value_type(second, at.under(Binders::ONE));
    assert_eq!(
        DeBruijnIndex::from(2_u32),
        read_code(&arena, first_read),
        "the first factor reads its index raised"
    );
    assert_eq!(
        DeBruijnIndex::from(3_u32),
        read_code(&arena, second_read),
        "the second factor reads its outer index raised past the binder"
    );
    assert_eq!(
        DeBruijnIndex::from(0_u32),
        at.under(Binders::ONE)
            .variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
        "under the binder the binder itself stands"
    );
    assert_eq!(
        DeBruijnIndex::from(0_u32),
        at.variable(Zone::Linear, DeBruijnIndex::from(0_u32)),
        "a linear index stands"
    );
    assert_eq!(
        mark,
        arena.watermark(),
        "reading through the relocation minted nothing"
    );
    let settled = shift_value_type(&mut arena, sigma, Binders::from(2_u32)).settle(&mut arena);
    let Some(&ValueType::Sigma { first, second }) = arena.value_type(settled)
    else {
        panic!("a settled sigma");
    };
    assert_eq!(
        [first_read, second_read].map(|read| read_code(&arena, read)),
        [first, second].map(|child| read_code(&arena, Relocated::from(child))),
        "the reads agree with the settled node"
    );
}

/// A walk answers a node whose support stops below its depth with the node
/// itself, without entering it: a closed child and a codomain that reads
/// only its own binder never reach the memo, while the path to the free
/// index does.
#[test]
fn a_walk_enters_only_nodes_whose_support_reaches_its_depth()
{
    use super::Engine;
    use super::Rewrite;
    use crate::relocation::Offset;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let closed = arena.value_type_product(&[integer, integer]);
    // (Integer × Integer) × U (Π (_ : El #0). F (El #0)): the domain reads
    // the free #0, the codomain only the Pi's own binder.
    let domain = decoded(&mut arena, DeBruijnIndex::from(0_u32));
    let own = arena.comp_type_returner(domain);
    let pi = arena.comp_type_pi(domain, own);
    let thunk = arena.value_type_thunk(pi);
    let subject = arena.value_type_product(&[closed, thunk]);
    let unit = arena.value_unit();
    for rewrite in [
        Rewrite::Relocate(Offset::raise(Binders::ONE)),
        Rewrite::Substitute(unit),
    ] {
        let mut engine = Engine::new(&mut arena);
        let rewritten = engine.run(Node::ValueType(subject), Binders::NONE, rewrite);
        assert_ne!(
            Node::ValueType(subject),
            rewritten,
            "the free decode is rewritten"
        );
        for entered in [Node::ValueType(thunk), Node::CompType(pi)] {
            assert!(
                engine.memo.contains_key(&(entered, Binders::NONE, rewrite)),
                "{entered:?} leads to the free index and is entered"
            );
        }
        for skipped in [Node::ValueType(closed), Node::CompType(own)] {
            assert!(
                engine.memo.keys().all(|&(node, ..)| node != skipped),
                "{skipped:?} is answered without being entered"
            );
        }
    }
}

/// Whether `tree` names a free level at or past `from`.
///
/// # Specification
/// trivial.
fn reads_from(
    tree: &Tree,
    from: Count,
) -> Maybe<(), strengthening::Absent>
{
    if tree
        .nodes
        .iter()
        .any(|node| matches!(node.shape, Shape::Free(level) if level >= from.0))
    {
        Maybe::Absent(strengthening::Absent::MentionsBinder)
    }
    else {
        Maybe::Present(())
    }
}

/// `subject` lowered out of its innermost `past` binders and settled, read
/// through a thunk so the value-type strengthening serves a computation
/// type.
///
/// # Specification
/// trivial.
fn strengthened_past(
    arena: &mut CoreArena,
    subject: CompTypeId,
    past: Binders,
) -> CompTypeId
{
    let wrapped = arena.value_type_thunk(subject);
    let Maybe::Present(lowered) = strengthen_value_type(arena, wrapped, past)
    else {
        panic!("a subject reading none of the binders lowers");
    };
    let lowered = lowered.settle(arena);
    let Some(&ValueType::Thunk(body)) = arena.value_type(lowered)
    else {
        panic!("a thunk");
    };
    body
}

/// Settled, a shift, a shift of a relocated subject past any scope, and a
/// strengthening agree with the level-based reference over generated trees,
/// and a strengthening refuses exactly the trees naming a level it removes.
#[test]
fn a_settled_shift_agrees_with_the_level_reference()
{
    let mut stream = Stream(0xD1B5_4A32_D192_ED03);
    for round in 0 .. 600_u32 {
        let frees = round.checked_rem(4).unwrap();
        let tree = generate(&mut stream, Kind::Comp, Count(frees), Count(4));
        let first = stream.below(Count(3)).0;
        let amount = stream.below(Count(3)).0.checked_add(1).unwrap();
        let placed = frees.checked_add(first).unwrap();
        let scope = stream.below(Count(placed.checked_add(1).unwrap())).0;
        let cut = stream.below(Count(frees.checked_add(1).unwrap())).0;
        let mut arena = CoreArena::new();
        let built = |arena: &mut CoreArena, placement: u32, reading: Reading<'_>| match build(
            arena,
            &tree,
            Count(placement),
            reading,
        ) {
            Built::CompType(id) => id,
            Built::Value(_) | Built::ValueType(_) => panic!("a computation type"),
        };
        let subject = built(&mut arena, frees, Reading::Plain);
        let raised = shift_comp_type(&mut arena, subject, Binders::from(first));
        let twice = super::shift_comp_type_under(
            &mut arena,
            raised,
            Binders::from(scope),
            Binders::from(amount),
        );
        let [raised, twice] = [raised, twice].map(|relocated| relocated.settle(&mut arena));
        let raised_reference = built(&mut arena, placed, Reading::Plain);
        let twice_reference = built(
            &mut arena,
            placed.checked_add(amount).unwrap(),
            Reading::Inserted {
                from: placed.checked_sub(scope).unwrap(),
                amount,
            },
        );
        assert_eq!(
            spelling(&arena, raised_reference),
            spelling(&arena, raised),
            "round {round}: a raise by {first} reads {tree:?} placed {first} deeper"
        );
        assert_eq!(
            spelling(&arena, twice_reference),
            spelling(&arena, twice),
            "round {round}: a further raise by {amount} past {scope} inserts its binders there"
        );
        let lowered = strengthened_past(&mut arena, raised_reference, Binders::from(first));
        assert_eq!(
            spelling(&arena, subject),
            spelling(&arena, lowered),
            "round {round}: {tree:?} placed under {first} binders it never reads lowers out of them"
        );
        let wrapped = arena.value_type_thunk(subject);
        let removed = Binders::from(frees.checked_sub(cut).unwrap());
        assert_eq!(
            reads_from(&tree, Count(cut)),
            match strengthen_value_type(&mut arena, wrapped, removed) {
                Maybe::Present(_) => Maybe::Present(()),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            },
            "round {round}: {tree:?} refuses exactly when it names a level past {cut}"
        );
    }
}

#[test]
fn instantiating_a_decode_at_a_quote_decodes()
{
    let mut arena = CoreArena::new();
    let decode = decoded(&mut arena, DeBruijnIndex::from(0));
    let codomain = arena.comp_type_returner(decode);
    let integer = arena.value_type_base(BaseType::Integer);
    let code = arena.value_quote(integer);
    let instantiated = instantiate_comp_type(&mut arena, codomain, code);
    assert_eq!(
        Some(&CompType::Returner {
            result: integer,
            effects: crate::effect::EffectRow::EMPTY
        }),
        arena.comp_type(instantiated),
        "F (El x) at ⌜Integer⌝ is F Integer, with the decode read off the quote"
    );
}

#[test]
fn strengthening_refuses_a_mention_and_lowers_the_rest()
{
    let mut arena = CoreArena::new();
    let mentioning = decoded(&mut arena, DeBruijnIndex::from(0));
    let mentioning = arena.comp_type_returner(mentioning);
    assert_eq!(
        Maybe::Absent(strengthening::Absent::MentionsBinder),
        strengthen_comp_type(&mut arena, mentioning),
        "a type that reads the binder cannot leave it"
    );

    let outer = decoded(&mut arena, DeBruijnIndex::from(1));
    let outer = arena.comp_type_returner(outer);
    let Maybe::Present(lowered) = strengthen_comp_type(&mut arena, outer)
    else {
        panic!("a type that reads only an outer index leaves the binder");
    };
    let expected = decoded(&mut arena, DeBruijnIndex::from(0));
    let expected = arena.comp_type_returner(expected);
    let lowered = lowered.settle(&mut arena);
    assert_eq!(
        spelling(&arena, expected),
        spelling(&arena, lowered),
        "and its outer index lowers by one"
    );
}

#[test]
fn a_value_type_strengthens_unless_it_names_a_binder()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let inner = decoded(&mut arena, DeBruijnIndex::from(1));
    assert_eq!(
        Maybe::Present(Relocated::from(inner)),
        strengthen_value_type(&mut arena, inner, Binders::NONE),
        "past no binder the type is itself"
    );
    assert_eq!(
        Maybe::Absent(strengthening::Absent::MentionsBinder),
        strengthen_value_type(&mut arena, inner, Binders::from(2_u32)),
        "a type reading the outer of two binders cannot leave both"
    );
    let Maybe::Present(lowered) = strengthen_value_type(&mut arena, inner, Binders::ONE)
    else {
        panic!("a type reading only past the innermost binder leaves it");
    };
    let expected = decoded(&mut arena, DeBruijnIndex::from(0));
    let lowered = lowered.settle(&mut arena);
    let [expected, lowered] = [expected, lowered].map(|ty| arena.comp_type_returner(ty));
    assert_eq!(
        spelling(&arena, expected),
        spelling(&arena, lowered),
        "and its index lowers by one"
    );
    let outer = decoded(&mut arena, DeBruijnIndex::from(3));
    let Maybe::Present(lowered) = strengthen_value_type(&mut arena, outer, Binders::from(2_u32))
    else {
        panic!("a type reading only past both binders leaves them");
    };
    let expected = decoded(&mut arena, DeBruijnIndex::from(1));
    let lowered = lowered.settle(&mut arena);
    let [expected, lowered] = [expected, lowered].map(|ty| arena.comp_type_returner(ty));
    assert_eq!(
        spelling(&arena, expected),
        spelling(&arena, lowered),
        "and its index lowers by two"
    );
    assert_eq!(
        Maybe::Present(Relocated::from(integer)),
        strengthen_value_type(&mut arena, integer, Binders::from(2_u32)),
        "a closed type strengthens to itself"
    );
}

#[test]
fn a_value_strengthens_unless_it_names_a_binder()
{
    let mut arena = CoreArena::new();
    let inner = variable(&mut arena, DeBruijnIndex::from(0));
    let pair = {
        let outer = variable(&mut arena, DeBruijnIndex::from(3));
        arena.value_tuple(&[inner, outer])
    };
    assert_eq!(
        Maybe::Absent(strengthening::Absent::MentionsBinder),
        strengthen_value(&mut arena, pair, Binders::from(2_u32)),
        "a pair naming the innermost binder cannot leave it"
    );
    let outer = variable(&mut arena, DeBruijnIndex::from(3));
    let Maybe::Present(lowered) = strengthen_value(&mut arena, outer, Binders::from(2_u32))
    else {
        panic!("a value naming only past both binders leaves them");
    };
    let lowered = lowered.settle(&mut arena);
    assert_eq!(
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32)
        }),
        arena.value(lowered),
        "and its index lowers by two"
    );
    let unit = arena.value_unit();
    assert_eq!(
        Maybe::Present(Relocated::from(unit)),
        strengthen_value(&mut arena, unit, Binders::from(2_u32)),
        "a closed value strengthens to itself"
    );
}

#[test]
fn a_constructor_classifier_binds_only_the_fields_named_after_them()
{
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(
        crate::classifier::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let family = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(family);
    let chain = |arena: &CoreArena, classifier: ValueTypeId| match arena.value_type(classifier) {
        Some(&ValueType::Thunk(chain)) => spelling(arena, chain),
        _ => panic!("a constructor's classifier is a thunk"),
    };
    // `(a : Type, x : El a)`: the second field names the first.
    let element = decoded(&mut arena, DeBruijnIndex::from(0));
    let dependent = constructor_classifier(&mut arena, family, &[universe, element]);
    let inner = arena.comp_type_arrow(element, returner);
    let expected = arena.comp_type_pi(universe, inner);
    assert_eq!(
        spelling(&arena, expected),
        chain(&arena, dependent),
        "a field the next names is bound, the last is a plain arrow"
    );
    // `(a : Type, n : Integer)`: nothing names the first.
    let plain = constructor_classifier(&mut arena, family, &[universe, family]);
    let inner = arena.comp_type_arrow(family, returner);
    let expected = arena.comp_type_arrow(universe, inner);
    assert_eq!(
        spelling(&arena, expected),
        chain(&arena, plain),
        "independent fields read as plain arrows"
    );
}

#[test]
fn a_constructor_classifier_at_its_result_binds_the_fields_the_result_names()
{
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(
        crate::classifier::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let integer = arena.value_type_base(BaseType::Integer);
    let chain = |arena: &CoreArena, classifier: ValueTypeId| match arena.value_type(classifier) {
        Some(&ValueType::Thunk(chain)) => spelling(arena, chain),
        _ => panic!("a constructor's classifier is a thunk"),
    };
    // `(a : Type, n : Integer)` standing at `El a`, read under both fields:
    // the result names the first and not the second, and is not lifted.
    let result = decoded(&mut arena, DeBruijnIndex::from(1));
    let classified = constructor_classifier_at(&mut arena, result, &[universe, integer]);
    let past_n = decoded(&mut arena, DeBruijnIndex::from(0));
    let returner = arena.comp_type_returner(past_n);
    let inner = arena.comp_type_arrow(integer, returner);
    let expected = arena.comp_type_pi(universe, inner);
    assert_eq!(
        spelling(&arena, expected),
        chain(&arena, classified),
        "the field the result names is bound, the other a plain arrow"
    );
}

#[test]
fn a_shared_type_is_rewritten_once_per_node()
{
    /// A product chain of sixty-four doublings over `El #index`, whose
    /// unfolding is exponential and whose node count is linear.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: sixty-four product levels, each sharing both children, above
    ///   a decode of the intuitionistic variable at `index`.
    /// - provides: a linear representation with an exponential unfolding.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shift over sixty-four shared product levels has
    ///   exactly the watermark of the original plus one rewritten chain,
    ///   distinguishing loss of sharing from expansion of the exponentially
    ///   large unfolding.
    /// - witness: `rewrite::tests::a_shared_type_is_rewritten_once_per_node`
    #[spec(ensures: |ret| {
            let mut current = ret;
            let mut valid = true;
            for _ in 0_u32..64_u32 {
                if let Some(held) = arena.value_type(current) && let ValueType::Product(ref components) = *held && let [first, second] = **components {
                    valid &= first == second;
                    current = first;
                } else { valid = false; }
            }
            valid && matches!(arena.value_type(current), Some(ValueType::Element { code, .. })
                if arena.value(*code) == Some(&Value::Variable { zone: Zone::Intuitionistic, index }))
        })]
    fn chain(
        arena: &mut CoreArena,
        index: DeBruijnIndex,
    ) -> ValueTypeId
    {
        let mut shared = decoded(arena, index);
        for _ in 0 .. 64_u32 {
            shared = arena.value_type_product(&[shared, shared]);
        }
        shared
    }

    let mut arena = CoreArena::new();
    let subject = chain(&mut arena, DeBruijnIndex::from(0));
    let shifted = shift_value_type(&mut arena, subject, Binders::ONE).settle(&mut arena);
    assert_ne!(subject, shifted, "the free index was raised");

    let mut reference = CoreArena::new();
    let _original = chain(&mut reference, DeBruijnIndex::from(0));
    let _raised = chain(&mut reference, DeBruijnIndex::from(1));
    assert_eq!(
        reference.watermark(),
        arena.watermark(),
        "the shift minted exactly one more copy of the shared chain, never its unfolding"
    );
}

#[test]
fn substitution_replaces_a_free_occurrence()
{
    let mut arena = CoreArena::new();
    // F #0 #1 under one binder, at G: the binder's #0 becomes G and the
    // outer #1 lowers to #0.
    let operator = arena.value_constant(ConstantIndex::from(0_usize));
    let bound = variable(&mut arena, DeBruijnIndex::from(0));
    let outer = variable(&mut arena, DeBruijnIndex::from(1));
    let inner = arena.value_static_application(operator, bound);
    let body = arena.value_static_application(inner, outer);
    let argument = arena.value_constant(ConstantIndex::from(1_usize));
    let reduct = instantiate_value(&mut arena, body, argument);
    assert_eq!(
        vec![
            Token::StaticApplication,
            Token::StaticApplication,
            Token::Constant(ConstantIndex::from(0_usize)),
            Token::Constant(ConstantIndex::from(1_usize)),
            Token::Variable(0),
        ],
        value_spelling(&arena, reduct),
        "the free occurrence is the argument and the outer index lowers by one"
    );
}

#[test]
fn substitution_stops_at_a_shadowing_binder()
{
    let mut arena = CoreArena::new();
    // λ. ⟨#0, #1⟩ under one binder: the inner #0 is the lambda's own and
    // stays; the inner #1 is the substituted binder.
    let own = variable(&mut arena, DeBruijnIndex::from(0));
    let substituted = variable(&mut arena, DeBruijnIndex::from(1));
    let pair = arena.value_tuple(&[own, substituted]);
    let body = arena.value_static_lambda(pair);
    let argument = arena.value_constant(ConstantIndex::from(1_usize));
    let reduct = instantiate_value(&mut arena, body, argument);
    assert_eq!(
        vec![
            Token::StaticLambda,
            Token::Pair,
            Token::Variable(0),
            Token::Constant(ConstantIndex::from(1_usize)),
        ],
        value_spelling(&arena, reduct),
        "the shadowing lambda's own occurrence is spared"
    );

    let only_own = variable(&mut arena, DeBruijnIndex::from(0));
    let closed = arena.value_static_lambda(only_own);
    assert_eq!(
        closed,
        instantiate_value(&mut arena, closed, argument),
        "and a body that never reads the binder is returned as it stands"
    );
}

#[test]
fn substitution_avoids_capture()
{
    let mut arena = CoreArena::new();
    // λ. #1 under one binder, at the open argument #0: carried under the
    // lambda the argument is #1, not the lambda's own #0.
    let substituted = variable(&mut arena, DeBruijnIndex::from(1));
    let body = arena.value_static_lambda(substituted);
    let argument = variable(&mut arena, DeBruijnIndex::from(0));
    let reduct = instantiate_value(&mut arena, body, argument);
    assert_eq!(
        vec![Token::StaticLambda, Token::Variable(1)],
        value_spelling(&arena, reduct),
        "the open argument rises past the binder it crosses"
    );
}

#[test]
fn binder_counts_clamp_at_the_ceiling()
{
    for (input, expected) in [
        (0_u32, 1_u32),
        (u32::MAX - 1, u32::MAX),
        (u32::MAX, u32::MAX),
    ] {
        assert_eq!(Binders::from(expected), Binders::from(input).deeper());
        assert_eq!(
            Binders::from(expected),
            Binders::past(DeBruijnIndex::from(input))
        );
    }
    for (input, count, expected) in [
        (3_u32, 0_usize, 3_u32),
        (3_u32, 1_usize, 4_u32),
        (3_u32, 4_usize, 7_u32),
        (u32::MAX - 1, 4_usize, u32::MAX),
        (0_u32, usize::MAX, u32::MAX),
    ] {
        assert_eq!(
            Binders::from(expected),
            Binders::from(input).deeper_by(crate::ComponentCount::from(count)),
            "{input} binders past {count} more"
        );
        assert_eq!(
            Binders::from(expected),
            Binders::from(input).beyond(Binders::from(u32::try_from(count).unwrap_or(u32::MAX))),
            "{input} binders beyond {count} more"
        );
    }
}

#[test]
fn occurrence_rules_separate_depth_boundaries()
{
    use super::Engine;
    use super::Occurrence;
    use super::Rewrite;
    use crate::relocation::Offset;
    let mut arena = CoreArena::new();
    let replacement = arena.value_constant(ConstantIndex::from(7_usize));
    // depth, index, shift by one, lowering by one (None marks the binder
    // itself, which a strengthening refuses off the support before any walk).
    for (depth, index, raised, lowered) in [
        (0_u32, 0_u32, 1_u32, None),
        (0, 1, 2, Some(0)),
        (1, 0, 0, Some(0)),
        (1, 1, 2, None),
        (1, 2, 3, Some(1)),
        (1, u32::MAX, u32::MAX, Some(u32::MAX - 1)),
    ] {
        let id = variable(&mut arena, DeBruijnIndex::from(index));
        let mut engine = Engine::new(&mut arena);
        let zero_shift = engine.occurrence(
            id,
            DeBruijnIndex::from(index),
            Binders::from(depth),
            Rewrite::Relocate(Offset::ZERO),
        );
        assert_eq!(Occurrence::Answered(id), zero_shift);
        let Occurrence::Answered(shifted) = engine.occurrence(
            id,
            DeBruijnIndex::from(index),
            Binders::from(depth),
            Rewrite::Relocate(Offset::raise(Binders::ONE)),
        )
        else {
            panic!("a shift answers directly");
        };
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(raised)
            }),
            engine.arena.value(shifted)
        );
        if index < depth {
            assert_eq!(id, shifted);
        }
        let substituted = engine.occurrence(
            id,
            DeBruijnIndex::from(index),
            Binders::from(depth),
            Rewrite::Substitute(replacement),
        );
        match lowered {
            None if depth == 0 => assert_eq!(Occurrence::Answered(replacement), substituted),
            None => assert_eq!(
                Occurrence::Carried(replacement, Binders::from(depth)),
                substituted
            ),
            Some(expected) => {
                let Occurrence::Answered(answer) = substituted
                else {
                    panic!("an unselected index is not carried");
                };
                assert_eq!(
                    Some(&Value::Variable {
                        zone: Zone::Intuitionistic,
                        index: DeBruijnIndex::from(expected)
                    }),
                    engine.arena.value(answer)
                );
                if index < depth {
                    assert_eq!(id, answer);
                }
            },
        }
        let Occurrence::Answered(answer) = engine.occurrence(
            id,
            DeBruijnIndex::from(index),
            Binders::from(depth),
            Rewrite::Relocate(Offset::lower(Binders::ONE)),
        )
        else {
            panic!("a relocation never carries a replacement");
        };
        if let Some(expected) = lowered {
            assert_eq!(
                Some(&Value::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(expected)
                }),
                engine.arena.value(answer)
            );
        }
    }
    // An environment entry is answered at the root and carried beneath a
    // binder, as a substitution's replacement is.
    for (depth, expected) in [
        (0_u32, Occurrence::Answered(replacement)),
        (1, Occurrence::Carried(replacement, Binders::ONE)),
    ] {
        let id = variable(&mut arena, DeBruijnIndex::from(depth));
        let mut engine = Engine::new(&mut arena);
        engine.environment.push(replacement);
        assert_eq!(
            expected,
            engine.occurrence(
                id,
                DeBruijnIndex::from(depth),
                Binders::from(depth),
                Rewrite::Environment,
            )
        );
    }
}

#[test]
fn reference_helpers_have_ground_and_asymmetric_goldens()
{
    let mut stream = Stream(0x9E37_79B9_7F4A_7C15);
    for bound in [1_u32, 2, u32::MAX] {
        for _ in 0_u32 .. 32_u32 {
            assert!(stream.below(Count(bound)).0 < bound);
        }
    }
    for (kind, expected) in [
        (Kind::Comp, vec![
            Token::Returner,
            Token::Base(BaseType::Integer),
        ]),
        (Kind::ValueType, vec![Token::Base(BaseType::Integer)]),
        (Kind::ValueCode, vec![
            Token::Quote,
            Token::Base(BaseType::Integer),
        ]),
        (Kind::CompCode, vec![
            Token::QuoteComputation,
            Token::Returner,
            Token::Base(BaseType::Integer),
        ]),
    ] {
        let tree = generate(&mut stream, kind, Count(0), Count(0));
        let mut arena = CoreArena::new();
        let built = build(&mut arena, &tree, Count(0), Reading::Plain);
        let visit = match built {
            Built::Value(id) => Visit::Value(id),
            Built::ValueType(id) => Visit::ValueType(id),
            Built::CompType(id) => Visit::CompType(id),
        };
        assert_eq!(expected, spelling_of(&arena, visit));
    }
    let tree = Tree {
        nodes: vec![
            GeneratedNode {
                shape: Shape::Pi,
                children: vec![1, 2],
                binders: 0,
            },
            GeneratedNode {
                shape: Shape::Integer,
                children: vec![],
                binders: 0,
            },
            GeneratedNode {
                shape: Shape::CompElement,
                children: vec![3],
                binders: 1,
            },
            GeneratedNode {
                shape: Shape::Local(0),
                children: vec![],
                binders: 1,
            },
        ],
    };
    let mut arena = CoreArena::new();
    let Built::CompType(root) = build(&mut arena, &tree, Count(0), Reading::Plain)
    else {
        panic!("the Pi is a computation type");
    };
    assert_eq!(
        vec![
            Token::Pi,
            Token::Base(BaseType::Integer),
            Token::CompElement,
            Token::Variable(0)
        ],
        spelling(&arena, root)
    );
}

#[test]
fn congruences_preserve_formers_and_child_order()
{
    use super::Engine;
    use super::Node;
    let mut arena = CoreArena::new();
    let v0 = variable(&mut arena, DeBruijnIndex::from(0));
    let v1 = variable(&mut arena, DeBruijnIndex::from(1));
    let w0 = variable(&mut arena, DeBruijnIndex::from(3));
    let w1 = variable(&mut arena, DeBruijnIndex::from(5));
    let c0 = arena.computation_return(v0);
    let c1 = arena.computation_return(v1);
    let d0 = arena.computation_return(w0);
    let d1 = arena.computation_return(w1);
    let t0 = arena.value_type_element(v0, Level::zero());
    let t1 = arena.value_type_element(v1, Level::zero());
    let u0 = arena.value_type_base(BaseType::Integer);
    let u1 = arena.value_type_unit();
    let k0 = arena.comp_type_returner(t0);
    let k1 = arena.comp_type_returner(t1);
    let l0 = arena.comp_type_returner(u0);
    let l1 = arena.comp_type_returner(u1);
    let level = Level::zero().succ().expect("one");
    for (original, unchanged, changed, expected) in [
        (
            arena.value_tuple(&[v0, v1]),
            vec![Node::Value(v0), Node::Value(v1)],
            vec![Node::Value(w0), Node::Value(w1)],
            Value::Tuple([w0, w1].into()),
        ),
        (
            arena.value_injection(gandr_kernel_term::Side::Left.into(), v0),
            vec![Node::Value(v0)],
            vec![Node::Value(w0)],
            Value::Injection(gandr_kernel_term::Side::Left.into(), w0),
        ),
        (
            arena.value_injection(gandr_kernel_term::Side::Right.into(), v1),
            vec![Node::Value(v1)],
            vec![Node::Value(w1)],
            Value::Injection(gandr_kernel_term::Side::Right.into(), w1),
        ),
        (
            arena.value_thunk(c0),
            vec![Node::Computation(c0)],
            vec![Node::Computation(d0)],
            Value::Thunk(d0),
        ),
        (
            arena.value_lift(level.clone(), v0),
            vec![Node::Value(v0)],
            vec![Node::Value(w0)],
            Value::Lift {
                target: level.clone(),
                body: w0,
            },
        ),
        (
            arena.value_quote(t0),
            vec![Node::ValueType(t0)],
            vec![Node::ValueType(u0)],
            Value::Quote(u0),
        ),
        (
            arena.value_quote_computation(k0),
            vec![Node::CompType(k0)],
            vec![Node::CompType(l0)],
            Value::QuoteComputation(l0),
        ),
        (
            arena.value_static_lambda(v0),
            vec![Node::Value(v0)],
            vec![Node::Value(w0)],
            Value::StaticLambda(w0),
        ),
        (
            arena.value_static_application(v0, v1),
            vec![Node::Value(v0), Node::Value(v1)],
            vec![Node::Value(w0), Node::Value(w1)],
            Value::StaticApplication(w0, w1),
        ),
    ] {
        let mark = arena.watermark();
        let mut engine = Engine::new(&mut arena);
        engine.results.extend(unchanged);
        assert_eq!(Node::Value(original), engine.close(Node::Value(original)));
        assert_eq!(mark, engine.arena.watermark());
        engine.results.extend(changed);
        let Node::Value(rewritten) = engine.close(Node::Value(original))
        else {
            panic!("the family is preserved");
        };
        assert_ne!(original, rewritten);
        assert_eq!(Some(&expected), engine.arena.value(rewritten));
        assert!(engine.results.is_empty());
    }
    for (original, unchanged, changed, expected) in [
        (
            arena.computation_lambda(c0),
            vec![Node::Computation(c0)],
            vec![Node::Computation(d0)],
            crate::Computation::Lambda(d0),
        ),
        (
            arena.computation_application(c0, v0),
            vec![Node::Computation(c0), Node::Value(v0)],
            vec![Node::Computation(d0), Node::Value(w0)],
            crate::Computation::Application(d0, w0),
        ),
        (
            arena.computation_return(v0),
            vec![Node::Value(v0)],
            vec![Node::Value(w0)],
            crate::Computation::Return(w0),
        ),
        (
            arena.computation_force(v1),
            vec![Node::Value(v1)],
            vec![Node::Value(w1)],
            crate::Computation::Force(w1),
        ),
        (
            arena.computation_bind(c0, c1),
            vec![Node::Computation(c0), Node::Computation(c1)],
            vec![Node::Computation(d0), Node::Computation(d1)],
            crate::Computation::Bind(d0, d1),
        ),
        (
            arena.computation_case(v0, &[c0, c1]),
            vec![
                Node::Value(v0),
                Node::Computation(c0),
                Node::Computation(c1),
            ],
            vec![
                Node::Value(w0),
                Node::Computation(d0),
                Node::Computation(d1),
            ],
            crate::Computation::Case {
                scrutinee: w0,
                branches: [d0, d1].into(),
            },
        ),
    ] {
        let mark = arena.watermark();
        let mut engine = Engine::new(&mut arena);
        engine.results.extend(unchanged);
        assert_eq!(
            Node::Computation(original),
            engine.close(Node::Computation(original))
        );
        assert_eq!(mark, engine.arena.watermark());
        engine.results.extend(changed);
        let Node::Computation(rewritten) = engine.close(Node::Computation(original))
        else {
            panic!("the family is preserved");
        };
        assert_ne!(original, rewritten);
        assert_eq!(Some(&expected), engine.arena.computation(rewritten));
        assert!(engine.results.is_empty());
    }
    for (original, unchanged, changed, expected) in [
        (
            arena.value_type_product(&[t0, t1]),
            vec![Node::ValueType(t0), Node::ValueType(t1)],
            vec![Node::ValueType(u0), Node::ValueType(u1)],
            ValueType::Product([u0, u1].into()),
        ),
        (
            arena.value_type_sum(&[t0, t1]),
            vec![Node::ValueType(t0), Node::ValueType(t1)],
            vec![Node::ValueType(u0), Node::ValueType(u1)],
            ValueType::Sum([u0, u1].into()),
        ),
        (
            arena.value_type_static_pi(t0, t1),
            vec![Node::ValueType(t0), Node::ValueType(t1)],
            vec![Node::ValueType(u0), Node::ValueType(u1)],
            ValueType::StaticPi {
                domain: u0,
                codomain: u1,
            },
        ),
        (
            arena.value_type_thunk(k0),
            vec![Node::CompType(k0)],
            vec![Node::CompType(l0)],
            ValueType::Thunk(l0),
        ),
        (
            arena.value_type_lift(t0, level.clone()),
            vec![Node::ValueType(t0)],
            vec![Node::ValueType(u0)],
            ValueType::Lift {
                inner: u0,
                target: level.clone(),
            },
        ),
        (
            arena.value_type_element(v0, level.clone()),
            vec![Node::Value(v0)],
            vec![Node::Value(w0)],
            ValueType::Element {
                code: w0,
                target: level.clone(),
            },
        ),
    ] {
        let mark = arena.watermark();
        let mut engine = Engine::new(&mut arena);
        engine.results.extend(unchanged);
        assert_eq!(
            Node::ValueType(original),
            engine.close(Node::ValueType(original))
        );
        assert_eq!(mark, engine.arena.watermark());
        engine.results.extend(changed);
        let Node::ValueType(rewritten) = engine.close(Node::ValueType(original))
        else {
            panic!("the family is preserved");
        };
        assert_ne!(original, rewritten);
        assert_eq!(Some(&expected), engine.arena.value_type(rewritten));
        assert!(engine.results.is_empty());
    }
    for (original, unchanged, changed, expected) in [
        (
            arena.comp_type_returner(t0),
            vec![Node::ValueType(t0)],
            vec![Node::ValueType(u0)],
            CompType::Returner {
                result: u0,
                effects: crate::effect::EffectRow::EMPTY,
            },
        ),
        (
            arena.comp_type_arrow(t0, k0),
            vec![Node::ValueType(t0), Node::CompType(k0)],
            vec![Node::ValueType(u0), Node::CompType(l0)],
            CompType::Arrow {
                domain: u0,
                codomain: l0,
            },
        ),
        (
            arena.comp_type_pi(t1, k1),
            vec![Node::ValueType(t1), Node::CompType(k1)],
            vec![Node::ValueType(u1), Node::CompType(l1)],
            CompType::Pi {
                domain: u1,
                codomain: l1,
            },
        ),
        (
            arena.comp_type_element(v1, level.clone()),
            vec![Node::Value(v1)],
            vec![Node::Value(w1)],
            CompType::Element {
                code: w1,
                target: level,
            },
        ),
    ] {
        let mark = arena.watermark();
        let mut engine = Engine::new(&mut arena);
        engine.results.extend(unchanged);
        assert_eq!(
            Node::CompType(original),
            engine.close(Node::CompType(original))
        );
        assert_eq!(mark, engine.arena.watermark());
        engine.results.extend(changed);
        let Node::CompType(rewritten) = engine.close(Node::CompType(original))
        else {
            panic!("the family is preserved");
        };
        assert_ne!(original, rewritten);
        assert_eq!(Some(&expected), engine.arena.comp_type(rewritten));
        assert!(engine.results.is_empty());
    }
    let quoted_value = arena.value_quote(u0);
    let quoted_comp = arena.value_quote_computation(l0);
    let undecoded_comp = arena.comp_type_element(v0, Level::zero());
    let mark = arena.watermark();
    let mut engine = Engine::new(&mut arena);
    engine.results.push(Node::Value(quoted_value));
    assert_eq!(Node::ValueType(u0), engine.close(Node::ValueType(t0)));
    engine.results.push(Node::Value(quoted_comp));
    assert_eq!(
        Node::CompType(l0),
        engine.close(Node::CompType(undecoded_comp))
    );
    assert_eq!(mark, engine.arena.watermark());
}

#[test]
fn binding_sites_distinguish_free_bound_and_linear_indices()
{
    use super::Engine;
    use super::Node;
    use super::Rewrite;
    let mut arena = CoreArena::new();
    let zero = variable(&mut arena, DeBruijnIndex::from(0));
    let one = variable(&mut arena, DeBruijnIndex::from(1));
    let linear = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0));
    let pair = arena.value_tuple(&[zero, one]);
    let shared = arena.computation_return(pair);
    let linear_branch = arena.computation_return(linear);
    let case = arena.computation_case(zero, &[shared, linear_branch]);
    let bind = arena.computation_bind(shared, shared);
    let lambda = arena.computation_lambda(shared);
    let split = arena.computation_split(one, crate::ComponentCount::from(2_usize), shared);
    let empty_split = arena.computation_split(zero, crate::ComponentCount::from(0_usize), shared);
    for (root, expected) in [
        (case, vec![1_u32, 0, 2]),
        (bind, vec![1, 2, 0, 2]),
        (lambda, vec![0, 2]),
        (split, vec![2, 0, 1]),
        (empty_split, vec![1, 1, 2]),
    ] {
        let Node::Computation(rewritten) = Engine::new(&mut arena).run(
            Node::Computation(root),
            Binders::NONE,
            Rewrite::Relocate(crate::relocation::Offset::raise(Binders::ONE)),
        )
        else {
            panic!("computation");
        };
        let mut pending = vec![Node::Computation(rewritten)];
        let mut actual = Vec::new();
        let mut linear_seen = Vec::new();
        while let Some(node) = pending.pop() {
            match node {
                Node::Value(id) => match *arena.value(id).expect("a value child") {
                    Value::Variable {
                        zone: Zone::Intuitionistic,
                        index,
                    } => actual.push(u32::from(index)),
                    Value::Variable {
                        zone: Zone::Linear,
                        index,
                    } => linear_seen.push(u32::from(index)),
                    Value::Tuple(ref components) => {
                        pending.extend(
                            components
                                .iter()
                                .rev()
                                .map(|&component| Node::Value(component)),
                        );
                    },
                    Value::Primitive { .. }
                    | Value::PathRefl(_)
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Here(_)
                    | Value::Univalence(..)
                    | Value::Funext(..)
                    | Value::Equiv(..)
                    | Value::Ua { .. }
                    | Value::Compose { .. }
                    | Value::SessionRelated { .. }
                    | Value::Stay(_)
                    | Value::Then(..)
                    | Value::FlowProduct(..)
                    | Value::Forward(_)
                    | Value::FunctionFlow(..)
                    | Value::Recorded(_)
                    | Value::Dialogue(_)
                    | Value::Web(_)
                    | Value::Returned(_)
                    | Value::Nested(_)
                    | Value::Run(_)
                    | Value::RecordUpdate { .. }
                    | Value::Constant(_)
                    | Value::Literal(_)
                    | Value::Injection(..)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Thunk(_)
                    | Value::Ascribe { .. }
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..)
                    | Value::Constructor { .. }
                    | Value::Record(_)
                    | Value::Row(_)
                    | Value::Hole(_)
                    | Value::Mark { .. }
                    | Value::Reify(_) => panic!("the golden uses variables and pairs"),
                },
                Node::Computation(id) => {
                    match *arena.computation(id).expect("a computation child") {
                        crate::Computation::Lambda(body) => {
                            pending.push(Node::Computation(body));
                        },
                        crate::Computation::Return(value) => {
                            pending.push(Node::Value(value));
                        },
                        crate::Computation::Bind(bound, body) => {
                            pending.extend([Node::Computation(body), Node::Computation(bound)]);
                        },
                        crate::Computation::Case {
                            scrutinee,
                            ref branches,
                        } => {
                            pending.extend(
                                branches
                                    .iter()
                                    .rev()
                                    .map(|&branch| Node::Computation(branch)),
                            );
                            pending.push(Node::Value(scrutinee));
                        },
                        crate::Computation::Split {
                            scrutinee, body, ..
                        } => {
                            pending.extend([Node::Computation(body), Node::Value(scrutinee)]);
                        },
                        crate::Computation::Primitive { .. }
                        | crate::Computation::Transport(..)
                        | crate::Computation::PathTransport { .. }
                        | crate::Computation::Ride { .. }
                        | crate::Computation::TelescopeTransport { .. }
                        | crate::Computation::Fixpoint { .. }
                        | crate::Computation::Application(..)
                        | crate::Computation::Force(_)
                        | crate::Computation::Decompose(_)
                        | crate::Computation::DataCase { .. }
                        | crate::Computation::RecordProjection(..)
                        | crate::Computation::TupleProjection(..)
                        | crate::Computation::Hole(_)
                        | crate::Computation::Mark { .. }
                        | crate::Computation::Ascribe { .. }
                        | crate::Computation::ListFold { .. }
                        | crate::Computation::ListCase { .. }
                        | crate::Computation::Perform { .. }
                        | crate::Computation::Handle { .. }
                        | crate::Computation::Exercise { .. }
                        | crate::Computation::Scope { .. }
                        | crate::Computation::Resume(..)
                        | crate::Computation::Abandon(_)
                        | crate::Computation::Reset(_)
                        | crate::Computation::Shift(_)
                        | crate::Computation::With(..)
                        | crate::Computation::Project(..)
                        | crate::Computation::Session(_)
                        | crate::Computation::Memory(_)
                        | crate::Computation::World(_) => {
                            panic!("the golden uses binding computations and return")
                        },
                    }
                },
                Node::ValueType(_) | Node::CompType(_) => panic!("the golden contains terms"),
            }
        }
        assert_eq!(expected, actual);
        assert_eq!(if root == case { vec![0] } else { vec![] }, linear_seen);
    }
    let domain = arena.value_type_element(zero, Level::zero());
    let codomain = arena.value_type_element(one, Level::zero());
    let static_pi = arena.value_type_static_pi(domain, codomain);
    let result = arena.comp_type_returner(domain);
    let mark = arena.watermark();
    assert_eq!(
        Relocated::from(static_pi),
        shift_value_type(&mut arena, static_pi, Binders::NONE)
    );
    assert_eq!(
        Relocated::from(result),
        shift_comp_type(&mut arena, result, Binders::NONE)
    );
    assert_eq!(mark, arena.watermark());
    let shifted = shift_value_type(&mut arena, static_pi, Binders::ONE).settle(&mut arena);
    let Some(&ValueType::StaticPi { domain, codomain }) = arena.value_type(shifted)
    else {
        panic!("static Pi");
    };
    for (child, index) in [(domain, 1_u32), (codomain, 2_u32)] {
        let Some(&ValueType::Element { code, .. }) = arena.value_type(child)
        else {
            panic!("a neutral decode");
        };
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(index)
            }),
            arena.value(code)
        );
    }
    let linear_type = arena.comp_type_element(linear, Level::zero());
    let mark = arena.watermark();
    assert_eq!(
        Maybe::Present(Relocated::from(linear_type)),
        strengthen_comp_type(&mut arena, linear_type)
    );
    assert_eq!(mark, arena.watermark());
}

#[test]
fn a_fill_replaces_exactly_the_named_holes()
{
    let mut arena = CoreArena::new();
    let named = arena.value_hole(HoleId::from(1_u32));
    let other = arena.value_hole(HoleId::from(2_u32));
    let computation_named = arena.computation_hole(HoleId::from(1_u32));
    let pair = arena.value_tuple(&[named, other]);
    let returned = arena.computation_return(pair);
    let subject = arena.computation_bind(computation_named, returned);
    let filling = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let TermId::Computation(filled) = fill_hole(
        &mut arena,
        TermId::Computation(subject),
        HoleId::from(1_u32),
        TermId::Value(filling),
    )
    else {
        panic!("a fill keeps the subject's family");
    };
    let Some(&Computation::Bind(bound, body)) = arena.computation(filled)
    else {
        panic!("a filled bind");
    };
    assert_eq!(
        bound, computation_named,
        "a hole of the other family stands"
    );
    let Some(&Computation::Return(value)) = arena.computation(body)
    else {
        panic!("a filled return");
    };
    assert_eq!(
        arena.value(value),
        Some(&Value::Tuple([filling, other].into())),
        "the named hole takes the filling uncarried, and another name stands"
    );
    let unit = arena.value_unit();
    let mark = arena.watermark();
    assert_eq!(
        fill_hole(
            &mut arena,
            TermId::Value(unit),
            HoleId::from(1_u32),
            TermId::Value(filling)
        ),
        TermId::Value(unit)
    );
    assert_eq!(mark, arena.watermark(), "a hole-free subject mints nothing");

    let computation_other = arena.computation_hole(HoleId::from(2_u32));
    let sequenced = arena.computation_bind(computation_named, computation_other);
    let computed = arena.computation_return(unit);
    let TermId::Computation(filled) = fill_hole(
        &mut arena,
        TermId::Computation(sequenced),
        HoleId::from(1_u32),
        TermId::Computation(computed),
    )
    else {
        panic!("a fill keeps the subject's family");
    };
    assert_eq!(
        Some(&Computation::Bind(computed, computation_other)),
        arena.computation(filled),
        "a computation filling takes the named computation hole, and another name stands"
    );
}

#[test]
fn a_solution_fills_a_type_raised_past_its_scope_1216()
{
    // `?a := #0`, solved one binder deep. Read one binder deep, `El ?a`
    // takes `#0`; inside `(b : Type) -> F (El ?a)`, a binder further in, it
    // takes `#1`; read at no binder it stands, the hole's scope not open.
    let mut arena = CoreArena::new();
    let hole = HoleId::nominated(NominationIndex::from(0_u32)).expect("the first nominated name");
    let standing = arena.value_hole(hole);
    let solution = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let solved = (solution, Binders::ONE);
    let decoded = arena.value_type_element(standing, Level::zero());
    let filled = fill_value_type_hole(&mut arena, (decoded, Binders::ONE), hole, solved);
    assert_eq!(
        arena.value_type(filled),
        Some(&ValueType::Element {
            code: solution,
            target: Level::zero()
        }),
        "at the solution's scope the hole takes it as it stands"
    );
    assert_eq!(
        fill_value_type_hole(&mut arena, (decoded, Binders::NONE), hole, solved),
        decoded,
        "read outside the solution's scope the hole stands"
    );
    let small = arena.value_type_universe(
        crate::classifier::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let returned = arena.comp_type_returner(decoded);
    let dependent = arena.comp_type_pi(small, returned);
    let filled = fill_comp_type_hole(&mut arena, (dependent, Binders::ONE), hole, solved);
    let Some(&CompType::Pi { codomain, .. }) = arena.comp_type(filled)
    else {
        panic!("a filled pi: {:?}", arena.comp_type(filled));
    };
    let Some(&CompType::Returner { result: read, .. }) = arena.comp_type(codomain)
    else {
        panic!("a filled returner");
    };
    let Some(&ValueType::Element { code, .. }) = arena.value_type(read)
    else {
        panic!("a filled decode");
    };
    assert_eq!(
        arena.value(code),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32)
        }),
        "under the pi's binder the solution is raised past it"
    );
    let returned = arena.computation_return(standing);
    let lambda = arena.computation_lambda(returned);
    let suspended = arena.value_thunk(lambda);
    let filled = fill_value_hole(&mut arena, (suspended, Binders::ONE), hole, solved);
    let Some(&Value::Thunk(lambda)) = arena.value(filled)
    else {
        panic!("a filled thunk");
    };
    let Some(&Computation::Lambda(body)) = arena.computation(lambda)
    else {
        panic!("a filled lambda");
    };
    let Some(&Computation::Return(value)) = arena.computation(body)
    else {
        panic!("a filled return");
    };
    assert_eq!(
        arena.value(value),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32)
        }),
        "a value's hole under a lambda takes the solution raised past it"
    );
    let unit = arena.value_type_unit();
    assert_eq!(
        fill_value_type_hole(&mut arena, (unit, Binders::ONE), hole, solved),
        unit,
        "a type holding no hole is its own filling"
    );
}

#[test]
fn a_wrap_marks_exactly_the_named_nodes()
{
    let mut arena = CoreArena::new();
    let occurrence = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let unit = arena.value_unit();
    let pair = arena.value_tuple(&[occurrence, unit]);
    let returned = arena.computation_return(pair);
    let sites = BTreeMap::from([
        (TermId::Value(occurrence), MarkIndex::from(0_u32)),
        (TermId::Value(pair), MarkIndex::from(1_u32)),
        (TermId::Computation(returned), MarkIndex::from(2_u32)),
    ]);
    let TermId::Computation(wrapped) =
        wrap_marks(&mut arena, TermId::Computation(returned), &sites)
    else {
        panic!("a wrap keeps the subject's family");
    };
    let Some(&Computation::Mark { mark, body }) = arena.computation(wrapped)
    else {
        panic!("the named computation is marked");
    };
    assert_eq!(mark, MarkIndex::from(2_u32));
    let Some(&Computation::Return(value)) = arena.computation(body)
    else {
        panic!("the mark wraps the rebuilt return");
    };
    let Some(&Value::Mark { mark, body }) = arena.value(value)
    else {
        panic!("the named pair is marked");
    };
    assert_eq!(mark, MarkIndex::from(1_u32));
    let Some(&[first, second]) = arena.value(body).and_then(Value::components)
    else {
        panic!("the mark wraps the rebuilt pair");
    };
    assert_eq!(second, unit, "an unnamed sibling stands");
    assert_eq!(
        arena.value(first),
        Some(&Value::Mark {
            mark: MarkIndex::from(0_u32),
            body: occurrence,
        }),
        "a named variable is marked in place"
    );
    let mark = arena.watermark();
    assert_eq!(
        wrap_marks(&mut arena, TermId::Value(unit), &sites),
        TermId::Value(unit)
    );
    assert_eq!(mark, arena.watermark(), "an unnamed subject mints nothing");
}

#[test]
fn a_crossing_runs_its_reduct_at_exactly_the_named_values()
{
    let mut arena = CoreArena::new();
    let crossed = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let unit = arena.value_unit();
    let pair = arena.value_tuple(&[crossed, unit]);
    let returned = arena.computation_return(pair);
    let subject = arena.value_thunk(returned);
    let reduct = ConstantIndex::from(7_usize);
    let crossings = BTreeMap::from([(crossed, Crossing {
        by: reduct,
        carriers: Vec::new(),
    })]);
    let (mut carried, mut runs) = (Vec::new(), Vec::new());
    let rebuilt = cross_reducts(&mut arena, subject, &crossings, &mut carried, &mut runs);
    let Some(&Value::Thunk(body)) = arena.value(rebuilt)
    else {
        panic!("the rebuilt subject is a thunk");
    };
    let Some(&Computation::Return(value)) = arena.computation(body)
    else {
        panic!("the thunk's body is a return");
    };
    let Some(&[first, second]) = arena.value(value).and_then(Value::components)
    else {
        panic!("the return's value is a pair");
    };
    assert_eq!(second, unit, "an uncrossed sibling stands");
    assert_eq!(
        runs,
        [first],
        "the crossed value stands as the run minted for it"
    );
    let Some(&Value::Run(applied)) = arena.value(first)
    else {
        panic!("a crossed value stands as a run");
    };
    let Some(&Computation::Application(head, argument)) = arena.computation(applied)
    else {
        panic!("the run applies the reduct");
    };
    assert_eq!(
        argument, crossed,
        "the reduct is applied to the crossed value itself"
    );
    let Some(&Computation::Force(forced)) = arena.computation(head)
    else {
        panic!("the application's head forces a value");
    };
    assert_eq!(
        arena.value(forced),
        Some(&Value::Constant(reduct)),
        "the run forces the reduct the crossing names"
    );
    assert!(
        carried.contains(&Carried::Value(subject, rebuilt))
            && !carried
                .iter()
                .any(|&pair| matches!(pair, Carried::Value(held, _) if held == crossed)),
        "the rebuild reports the subject, and a crossed value carried to itself is no pair: {carried:?}"
    );
    let mark = arena.watermark();
    let (mut none, mut minted) = (Vec::new(), Vec::new());
    assert_eq!(
        cross_reducts(&mut arena, unit, &crossings, &mut none, &mut minted),
        unit
    );
    assert!(
        mark == arena.watermark() && none.is_empty() && minted.is_empty(),
        "a subject reaching no crossed value mints nothing"
    );
}

#[test]
fn an_update_builds_the_kept_fields_beside_the_overlay()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| crate::FieldLabel::from(String::from(name));
    let base = arena.value_constant(ConstantIndex::from(0_usize));
    let other = arena.value_constant(ConstantIndex::from(1_usize));
    let unit = arena.value_unit();
    let overlay = arena.value_record(BTreeMap::from([(label("b"), unit)]));
    let named = arena.value_record_update(base, overlay);
    let unnamed = arena.value_record_update(other, overlay);
    let pair = arena.value_tuple(&[named, unnamed]);
    let returned = arena.computation_return(pair);
    let subject = arena.value_thunk(returned);
    let updates = BTreeMap::from([(named, Vec::from([label("a")]))]);
    let mut carried = Vec::new();
    let rebuilt = super::build_updates(&mut arena, subject, &updates, &mut carried);
    let expected = {
        let kept = arena.computation_record_projection(base, label("a"));
        let kept = arena.value_returned(kept);
        let record = arena.value_record(BTreeMap::from([(label("a"), kept), (label("b"), unit)]));
        let pair = arena.value_tuple(&[record, unnamed]);
        let returned = arena.computation_return(pair);
        arena.value_thunk(returned)
    };
    assert_eq!(
        crate::equal_certificate_syntax(&arena, rebuilt, expected),
        crate::CertificateEquality::Equal,
        "the named update stands as the record of `⟨b.a⟩` beside the overlay's `b`, and the \
         unnamed one stands as written"
    );
    assert!(
        carried.contains(&Carried::Value(subject, rebuilt))
            && !carried
                .iter()
                .any(|&pair| matches!(pair, Carried::Value(held, _) if held == unnamed)),
        "the rebuild reports the subject, and the unnamed update carried to itself is no pair: \
         {carried:?}"
    );
    let mark = arena.watermark();
    let mut none = Vec::new();
    assert_eq!(
        super::build_updates(&mut arena, unnamed, &updates, &mut none),
        unnamed
    );
    assert!(
        mark == arena.watermark() && none.is_empty(),
        "a subject reaching no named update mints nothing"
    );
}

/// #2159: an update standing in a path type's endpoint builds its record
/// there, and the endpoint it does not reach stands as written.
#[test]
fn an_update_in_a_type_builds_its_record_2159()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| crate::FieldLabel::from(String::from(name));
    let base = arena.value_constant(ConstantIndex::from(0_usize));
    let unit = arena.value_unit();
    let overlay = arena.value_record(BTreeMap::from([(label("b"), unit)]));
    let named = arena.value_record_update(base, overlay);
    let carrier = arena.value_type_unit();
    let subject = arena.value_type_path(carrier, named, base);
    let updates = BTreeMap::from([(named, Vec::from([label("a")]))]);
    let mut carried = Vec::new();
    let rebuilt = super::build_type_updates(&mut arena, subject, &updates, &mut carried);
    let Some(&crate::ValueType::Path { left, right, .. }) = arena.value_type(rebuilt)
    else {
        panic!("the rebuilt type is still a path");
    };
    let expected = {
        let kept = arena.computation_record_projection(base, label("a"));
        let kept = arena.value_returned(kept);
        arena.value_record(BTreeMap::from([(label("a"), kept), (label("b"), unit)]))
    };
    assert_eq!(
        crate::equal_certificate_syntax(&arena, left, expected),
        crate::CertificateEquality::Equal,
        "the update in the left endpoint stands as the record of `⟨b.a⟩` beside the overlay's `b`"
    );
    assert_eq!(
        right, base,
        "the right endpoint, reaching no update, stands as written"
    );
    let plain = arena.value_type_path(carrier, base, base);
    let mark = arena.watermark();
    let mut none = Vec::new();
    assert_eq!(
        super::build_type_updates(&mut arena, plain, &updates, &mut none),
        plain
    );
    assert!(
        mark == arena.watermark() && none.is_empty(),
        "a type reaching no named update mints nothing"
    );
}

/// #2217: an update whose base is another update keeps, in a type's build, the
/// component the record the inner update stands as holds, never a projection
/// off that record; a body's build keeps the projection, its base run as
/// written.
#[test]
fn an_update_of_an_update_in_a_type_keeps_the_inner_record_s_fields_2217()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| crate::FieldLabel::from(String::from(name));
    let base = arena.value_constant(ConstantIndex::from(0_usize));
    let unit = arena.value_unit();
    let first = arena.value_record(BTreeMap::from([(label("a"), unit)]));
    let inner = arena.value_record_update(base, first);
    let second = arena.value_record(BTreeMap::from([(label("b"), unit)]));
    let outer = arena.value_record_update(inner, second);
    let carrier = arena.value_type_unit();
    let subject = arena.value_type_path(carrier, outer, base);
    let updates = BTreeMap::from([
        (inner, Vec::from([label("b")])),
        (outer, Vec::from([label("a")])),
    ]);
    let rebuilt = super::build_type_updates(&mut arena, subject, &updates, &mut Vec::new());
    let Some(&crate::ValueType::Path { left, .. }) = arena.value_type(rebuilt)
    else {
        panic!("the rebuilt type is still a path");
    };
    let record = arena.value_record(BTreeMap::from([(label("a"), unit), (label("b"), unit)]));
    assert_eq!(
        crate::equal_certificate_syntax(&arena, left, record),
        crate::CertificateEquality::Equal,
        "the outer update keeps `a` as the inner record holds it, beside its own `b`"
    );
    let projected = {
        let kept = arena.computation_record_projection(base, label("b"));
        let kept = arena.value_returned(kept);
        let built = arena.value_record(BTreeMap::from([(label("a"), unit), (label("b"), kept)]));
        let kept = arena.computation_record_projection(built, label("a"));
        let kept = arena.value_returned(kept);
        arena.value_record(BTreeMap::from([(label("a"), kept), (label("b"), unit)]))
    };
    let body = super::build_updates(&mut arena, outer, &updates, &mut Vec::new());
    assert_eq!(
        crate::equal_certificate_syntax(&arena, body, projected),
        crate::CertificateEquality::Equal,
        "a body's build projects the kept field off the inner record"
    );
}

#[test]
fn a_crossing_applies_its_carriers_before_the_value()
{
    let mut arena = CoreArena::new();
    let crossed = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let integer = arena.value_type_base(BaseType::Integer);
    let carrier = arena.value_quote(integer);
    let returned = arena.computation_return(crossed);
    let subject = arena.value_thunk(returned);
    let forget = ConstantIndex::from(3_usize);
    let crossings = BTreeMap::from([(crossed, Crossing {
        by: forget,
        carriers: Vec::from([carrier]),
    })]);
    let (mut carried, mut runs) = (Vec::new(), Vec::new());
    let _rebuilt = cross_reducts(&mut arena, subject, &crossings, &mut carried, &mut runs);
    let &[run] = runs.as_slice()
    else {
        panic!("one run is minted for the one crossed value: {runs:?}");
    };
    let Some(&Value::Run(applied)) = arena.value(run)
    else {
        panic!("a crossed value stands as a run");
    };
    let Some(&Computation::Application(head, argument)) = arena.computation(applied)
    else {
        panic!("the run applies the map to the value");
    };
    assert_eq!(argument, crossed, "the value is the last argument");
    let Some(&Computation::Application(forced, first)) = arena.computation(head)
    else {
        panic!("the map is applied to its carrier before the value");
    };
    assert_eq!(first, carrier, "the carrier is the first argument");
    let Some(&Computation::Force(map)) = arena.computation(forced)
    else {
        panic!("the head of the application forces the map");
    };
    assert_eq!(
        arena.value(map),
        Some(&Value::Constant(forget)),
        "the run forces the map the crossing names"
    );
}

/// Apply the constant `callee`, forced, to `argument`.
///
/// # Specification
/// trivial.
fn call(
    arena: &mut CoreArena,
    callee: ConstantIndex,
    argument: ValueId,
) -> ComputationId
{
    let callee = arena.value_constant(callee);
    let forced = arena.computation_force(callee);
    arena.computation_application(forced, argument)
}

/// A compact pre-order reading of the term formers the elaboration tests
/// write, so a rebuilt term compares with the spelling it should have.
///
/// # Specification
/// trivial.
fn term_text(
    arena: &CoreArena,
    root: ValueId,
) -> String
{
    enum Piece
    {
        Value(ValueId),
        Computation(ComputationId),
        Text(&'static str),
    }
    let mut text = String::new();
    let mut pending = vec![Piece::Value(root)];
    while let Some(piece) = pending.pop() {
        let (head, children): (String, Vec<Piece>) = match piece {
            Piece::Text(written) => {
                text.push_str(written);
                continue;
            },
            Piece::Value(id) => match arena.value(id) {
                Some(&Value::Variable { index, .. }) => {
                    (format!("v{}", u32::from(index)), Vec::new())
                },
                Some(&Value::Constant(constant)) => {
                    (format!("#{}", usize::from(constant)), Vec::new())
                },
                Some(&Value::Thunk(body)) => ("thunk".into(), vec![Piece::Computation(body)]),
                Some(&Value::Nested(body)) => ("nested".into(), vec![Piece::Computation(body)]),
                Some(&Value::Run(body)) => ("run".into(), vec![Piece::Computation(body)]),
                Some(&Value::Tuple(ref components)) => (
                    "tuple".into(),
                    components
                        .iter()
                        .map(|&component| Piece::Value(component))
                        .collect(),
                ),
                Some(&Value::StaticApplication(head, argument)) => ("static".into(), vec![
                    Piece::Value(head),
                    Piece::Value(argument),
                ]),
                _ => ("?".into(), Vec::new()),
            },
            Piece::Computation(id) => match arena.computation(id) {
                Some(&Computation::Lambda(body)) => {
                    ("lambda".into(), vec![Piece::Computation(body)])
                },
                Some(&Computation::Bind(bound, body)) => ("bind".into(), vec![
                    Piece::Computation(bound),
                    Piece::Computation(body),
                ]),
                Some(&Computation::Return(value)) => ("return".into(), vec![Piece::Value(value)]),
                Some(&Computation::Force(value)) => ("force".into(), vec![Piece::Value(value)]),
                Some(&Computation::Application(head, argument)) => ("apply".into(), vec![
                    Piece::Computation(head),
                    Piece::Value(argument),
                ]),
                Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => (
                    "case".into(),
                    core::iter::once(Piece::Value(scrutinee))
                        .chain(branches.iter().map(|&branch| Piece::Computation(branch)))
                        .collect(),
                ),
                _ => ("?".into(), Vec::new()),
            },
        };
        text.push_str(&head);
        if children.is_empty() {
            continue;
        }
        text.push('(');
        pending.push(Piece::Text(")"));
        for (position, child) in children.into_iter().enumerate().rev() {
            pending.push(child);
            if position > 0 {
                pending.push(Piece::Text(","));
            }
        }
    }
    text
}

#[test]
fn an_elaboration_runs_in_written_order_before_its_region()
{
    let mut arena = CoreArena::new();
    let [first_x, inner_x, last_x] =
        [(); 3].map(|()| variable(&mut arena, DeBruijnIndex::from(0_u32)));
    let first = call(&mut arena, ConstantIndex::from(1_usize), first_x);
    let first = arena.value_nested(first);
    let inner = call(&mut arena, ConstantIndex::from(3_usize), inner_x);
    let inner = arena.value_nested(inner);
    let second = call(&mut arena, ConstantIndex::from(2_usize), inner);
    let second = arena.value_run(second);
    let head = call(&mut arena, ConstantIndex::from(0_usize), first);
    let spine = arena.computation_application(head, second);
    let region = arena.computation_application(spine, last_x);
    let lambda = arena.computation_lambda(region);
    let subject = arena.value_thunk(lambda);
    let nesting = BTreeMap::from([(first, Nesting::Run), (inner, Nesting::Run)]);
    let mut carried = Vec::new();
    let mut binds = Vec::new();
    let Ok(elaborated) =
        elaborate_nested_traced(&mut arena, subject, &nesting, &mut carried, &mut binds)
    else {
        panic!("every run stands in a computation");
    };
    assert_eq!(
        term_text(&arena, elaborated),
        "thunk(lambda(bind(apply(force(#1),v0),bind(bind(apply(force(#3),v1),apply(force(#2),v0)),apply(apply(apply(force(#0),v1),v0),v2)))))",
        "the head's run binds outermost, the argument's next carried past it, the run nested in the argument's own call binds inside that call, and the body reads each run by its bind and every free index past them all",
    );
    let runs: Vec<ValueId> = binds.iter().map(|&(run, _)| run).collect();
    assert_eq!(
        runs,
        [inner, second, first],
        "binds are minted innermost first"
    );
    let Some(&(_, outermost)) = binds.last()
    else {
        panic!("three binds");
    };
    assert!(
        carried.contains(&Carried::Computation(region, outermost)),
        "the region is reported as the binds that wrap it"
    );
}

#[test]
fn an_elaboration_suspends_and_runs_as_decided()
{
    let mut arena = CoreArena::new();
    let [suspended_x, run_x] = [(); 2].map(|()| variable(&mut arena, DeBruijnIndex::from(0_u32)));
    let suspended = call(&mut arena, ConstantIndex::from(1_usize), suspended_x);
    let suspended = arena.value_nested(suspended);
    let run = call(&mut arena, ConstantIndex::from(2_usize), run_x);
    let run = arena.value_nested(run);
    let pair = arena.value_tuple(&[suspended, run]);
    let returned = arena.computation_return(pair);
    let lambda = arena.computation_lambda(returned);
    let subject = arena.value_thunk(lambda);
    let nesting = BTreeMap::from([(suspended, Nesting::Thunk), (run, Nesting::Run)]);
    let mut carried = Vec::new();
    let mut binds = Vec::new();
    let minted = arena.watermark();
    let Ok(elaborated) =
        elaborate_nested_traced(&mut arena, subject, &nesting, &mut carried, &mut binds)
    else {
        panic!("every run stands in a computation");
    };
    let reported: alloc::collections::BTreeSet<Node> = carried
        .iter()
        .map(|pair| match *pair {
            Carried::Value(_, written) => Node::Value(written),
            Carried::Computation(_, written) => Node::Computation(written),
            Carried::ValueType(_, written) => Node::ValueType(written),
            Carried::CompType(_, written) => Node::CompType(written),
        })
        .chain(binds.iter().map(|&(_, bind)| Node::Computation(bind)))
        .collect();
    let unreported: Vec<Node> = arena
        .values_since(minted)
        .map(Node::Value)
        .chain(arena.computations_since(minted).map(Node::Computation))
        .filter(|node| !reported.contains(node))
        .collect();
    assert_eq!(
        unreported,
        [],
        "every node the elaboration minted is reported beside a node it stands for, the \
             region's body closed around the suspension among them"
    );
    assert_eq!(
        term_text(&arena, elaborated),
        "thunk(lambda(bind(apply(force(#2),v0),return(tuple(thunk(apply(force(#1),v1)),v0)))))",
        "the suspension stays in place as a thunk, carried past the run's bind",
    );
    assert_eq!(binds.len(), 1, "only the run mints a bind");
    let mark = arena.watermark();
    let Ok(unchanged) = elaborate_nested_traced(
        &mut arena,
        pair,
        &BTreeMap::new(),
        &mut Vec::new(),
        &mut binds,
    )
    else {
        panic!("an undecided nested computation is not a run");
    };
    assert_eq!(unchanged, pair, "nothing decided, nothing rebuilt");
    assert_eq!(mark, arena.watermark(), "and nothing minted");
}

/// A call written at an application's head is forced nested: suspended, the
/// force of its thunk stands as the call itself, which was not rebuilt from
/// the force and so is not reported beside it; run, the force reads the
/// bind's variable (#3935).
#[test]
fn a_forced_suspension_elaborates_as_its_call_3935()
{
    let mut arena = CoreArena::new();
    let x = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let head = call(&mut arena, ConstantIndex::from(1_usize), x);
    let nested = arena.value_nested(head);
    let forced = arena.computation_force(nested);
    let argument = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let applied = arena.computation_application(forced, argument);
    let lambda = arena.computation_lambda(applied);
    let subject = arena.value_thunk(lambda);
    for (decided, expected, why) in [
        (
            Nesting::Thunk,
            "thunk(lambda(apply(apply(force(#1),v0),v0)))",
            "a suspended head is the call it spells",
        ),
        (
            Nesting::Run,
            "thunk(lambda(bind(apply(force(#1),v0),apply(force(v0),v1))))",
            "a run head binds ahead and the force reads its variable",
        ),
    ] {
        let mut carried = Vec::new();
        let Ok(elaborated) = elaborate_nested_traced(
            &mut arena,
            subject,
            &BTreeMap::from([(nested, decided)]),
            &mut carried,
            &mut Vec::new(),
        )
        else {
            panic!("the head stands in the application");
        };
        assert_eq!(term_text(&arena, elaborated), expected, "{why}");
        assert!(
            !carried.contains(&Carried::Computation(forced, head)),
            "the call a suspended head stands as is no node rebuilt from its force"
        );
    }
}

#[test]
fn an_elaboration_never_hoists_out_of_a_thunk_or_an_arm()
{
    let mut arena = CoreArena::new();
    let [scrutinee, armed_x, suspended_x] =
        [(); 3].map(|()| variable(&mut arena, DeBruijnIndex::from(0_u32)));
    let armed = call(&mut arena, ConstantIndex::from(1_usize), armed_x);
    let armed = arena.value_nested(armed);
    let suspended = call(&mut arena, ConstantIndex::from(2_usize), suspended_x);
    let suspended = arena.value_nested(suspended);
    let first_arm = arena.computation_return(armed);
    let inner = arena.computation_return(suspended);
    let thunk = arena.value_thunk(inner);
    let second_arm = arena.computation_return(thunk);
    let case = arena.computation_case(scrutinee, &[first_arm, second_arm]);
    let lambda = arena.computation_lambda(case);
    let subject = arena.value_thunk(lambda);
    let nesting = BTreeMap::from([(armed, Nesting::Run), (suspended, Nesting::Run)]);
    let Ok(elaborated) = elaborate_nested_traced(
        &mut arena,
        subject,
        &nesting,
        &mut Vec::new(),
        &mut Vec::new(),
    )
    else {
        panic!("every run stands in a computation");
    };
    assert_eq!(
        term_text(&arena, elaborated),
        "thunk(lambda(case(v0,apply(force(#1),v0),return(thunk(apply(force(#2),v0))))))",
        "an arm's run stands inside the arm and a thunk's inside the thunk, each its region's \
         whole computation where that region only returns it; the case stands as written",
    );
}

#[test]
fn a_run_in_no_computation_is_unenclosed()
{
    let mut arena = CoreArena::new();
    let argument = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let computation = call(&mut arena, ConstantIndex::from(1_usize), argument);
    let nested = arena.value_nested(computation);
    let definition = arena.value_tuple(&[nested]);
    let refused = elaborate_nested_traced(
        &mut arena,
        definition,
        &BTreeMap::from([(nested, Nesting::Run)]),
        &mut Vec::new(),
        &mut Vec::new(),
    );
    assert_eq!(
        refused.map_err(Unenclosed::run),
        Err(nested),
        "a definition's own value has no computation to run before"
    );
    let Ok(suspended) = elaborate_nested_traced(
        &mut arena,
        definition,
        &BTreeMap::from([(nested, Nesting::Thunk)]),
        &mut Vec::new(),
        &mut Vec::new(),
    )
    else {
        panic!("a suspension needs no computation around it");
    };
    assert_eq!(
        term_text(&arena, suspended),
        "tuple(thunk(apply(force(#1),v0)))"
    );
    let operator = arena.value_constant(ConstantIndex::from(0_usize));
    let run = arena.value_run(computation);
    let erased = arena.value_static_application(operator, run);
    let returned = arena.computation_return(erased);
    let subject = arena.value_thunk(returned);
    let refused = elaborate_nested_traced(
        &mut arena,
        subject,
        &BTreeMap::new(),
        &mut Vec::new(),
        &mut Vec::new(),
    );
    assert_eq!(
        refused.map_err(Unenclosed::run),
        Err(run),
        "static content is erased before anything runs, so no run hoists out of it"
    );
}

#[test]
fn a_decision_no_term_reaches_is_unenclosed()
{
    let mut arena = CoreArena::new();
    let argument = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let computation = call(&mut arena, ConstantIndex::from(1_usize), argument);
    let nested = arena.value_nested(computation);
    let indexed = arena.value_type_element(nested, Level::zero());
    let constructed = arena.value_constructor(
        indexed,
        gandr_kernel_term::ConstructorTag::from(0_usize),
        alloc::vec::Vec::new(),
    );
    let returned = arena.computation_return(constructed);
    let subject = arena.value_thunk(returned);
    for decided in [Nesting::Run, Nesting::Thunk] {
        assert_eq!(
            elaborate_nested_traced(
                &mut arena,
                subject,
                &BTreeMap::from([(nested, decided)]),
                &mut Vec::new(),
                &mut Vec::new(),
            )
            .map_err(Unenclosed::run),
            Err(nested),
            "a computation standing in a type has nothing to run before or suspend in"
        );
    }
}

#[test]
fn an_environment_substitution_replaces_every_free_index()
{
    let mut arena = CoreArena::new();
    let entries = [
        arena.value_constant(ConstantIndex::from(5_usize)),
        variable(&mut arena, DeBruijnIndex::from(0_u32)),
    ];
    let [zero, one, two, three] =
        [0_u32, 1, 2, 3].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
    let top = arena.value_tuple(&[zero, one]);
    let TermId::Value(at_top) = substitute_environment(&mut arena, TermId::Value(top), &entries)
    else {
        panic!("a substitution keeps the subject's family");
    };
    assert_eq!(
        arena.value(at_top),
        Some(&Value::Tuple([entries[0], entries[1]].into()))
    );
    let inner = arena.value_tuple(&[zero, one]);
    let outer = arena.value_tuple(&[two, three]);
    let both = arena.value_tuple(&[inner, outer]);
    let returned = arena.computation_return(both);
    let lambda = arena.computation_lambda(returned);
    let TermId::Computation(substituted) =
        substitute_environment(&mut arena, TermId::Computation(lambda), &entries)
    else {
        panic!("a substitution keeps the subject's family");
    };
    let Some(&Computation::Lambda(body)) = arena.computation(substituted)
    else {
        panic!("a substituted lambda");
    };
    let Some(&Computation::Return(value)) = arena.computation(body)
    else {
        panic!("a substituted return");
    };
    let Some(&[inner, outer]) = arena.value(value).and_then(Value::components)
    else {
        panic!("a substituted pair");
    };
    let index_of = |arena: &CoreArena, id| match arena.value(id) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => Some(u32::from(index)),
        Some(_) | None => None,
    };
    let Some(&[bound, first_entry]) = arena.value(inner).and_then(Value::components)
    else {
        panic!("the inner pair");
    };
    assert_eq!(
        index_of(&arena, bound),
        Some(0),
        "the lambda's own index stands"
    );
    assert_eq!(first_entry, entries[0], "a closed entry is placed as it is");
    let Some(&[second_entry, past]) = arena.value(outer).and_then(Value::components)
    else {
        panic!("the outer pair");
    };
    assert_eq!(
        index_of(&arena, second_entry),
        Some(1),
        "an open entry is carried under the binder"
    );
    assert_eq!(
        index_of(&arena, past),
        Some(1),
        "an index past the environment is lowered by its length"
    );
    let mark = arena.watermark();
    assert_eq!(
        substitute_environment(&mut arena, TermId::Computation(lambda), &[]),
        TermId::Computation(lambda)
    );
    assert_eq!(
        mark,
        arena.watermark(),
        "an empty environment mints nothing"
    );
}

#[test]
fn an_environment_substitution_reaches_into_types()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let constant = arena.value_constant(ConstantIndex::from(5_usize));
    let entries = [constant];
    let [zero, one, two] =
        [0_u32, 1, 2].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
    let path = arena.value_type_path(integer, zero, two);
    let substituted = substitute_environment_value_type(&mut arena, path, &entries);
    let index_of = |arena: &CoreArena, id| match arena.value(id) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => Some(u32::from(index)),
        Some(_) | None => None,
    };
    let Some(&ValueType::Path {
        carrier,
        left,
        right,
    }) = arena.value_type(substituted)
    else {
        panic!("the substituted path");
    };
    assert_eq!(
        (carrier, left, index_of(&arena, right)),
        (integer, constant, Some(1)),
        "a covered index is its entry and one past the environment is lowered"
    );
    // `Π (_ : Integer). F Path(Integer, #0, #1)`: the codomain's own binder
    // stands, and the covered index under it is the entry.
    let under = arena.value_type_path(integer, zero, one);
    let returns = arena.comp_type_returner(under);
    let pi = arena.comp_type_pi(integer, returns);
    let substituted = substitute_environment_comp_type(&mut arena, pi, &entries);
    let Some(&CompType::Pi { domain, codomain }) = arena.comp_type(substituted)
    else {
        panic!("the substituted Π");
    };
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(codomain)
    else {
        panic!("the substituted codomain");
    };
    let Some(&ValueType::Path {
        carrier,
        left,
        right,
    }) = arena.value_type(result)
    else {
        panic!("the substituted path under the Π");
    };
    assert_eq!(
        (domain, carrier, index_of(&arena, left), right),
        (integer, integer, Some(0), constant),
        "the bound index stands under its Π"
    );
    let mark = arena.watermark();
    assert_eq!(substitute_environment_comp_type(&mut arena, pi, &[]), pi);
    assert_eq!(
        substitute_environment_value_type(&mut arena, path, &[]),
        path
    );
    assert_eq!(
        mark,
        arena.watermark(),
        "an empty environment mints nothing"
    );
}

#[test]
fn a_traced_substitution_reports_every_node_it_rewrote()
{
    let mut arena = CoreArena::new();
    let entry = variable(&mut arena, DeBruijnIndex::from(4_u32));
    let closed = arena.value_constant(ConstantIndex::from(5_usize));
    let [bound, free] = [0_u32, 1].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
    let triple = arena.value_tuple(&[bound, free, closed]);
    let returned = arena.computation_return(triple);
    let lambda = arena.computation_lambda(returned);
    let mut carried = Vec::new();
    let TermId::Computation(substituted) = substitute_environment_traced(
        &mut arena,
        TermId::Computation(lambda),
        &[entry],
        &mut carried,
    )
    else {
        panic!("a substitution keeps the subject's family");
    };
    let Some(&Computation::Lambda(body)) = arena.computation(substituted)
    else {
        panic!("a substituted lambda");
    };
    let Some(&Computation::Return(value)) = arena.computation(body)
    else {
        panic!("a substituted return");
    };
    let Some(&[kept, shifted, constant]) = arena.value(value).and_then(Value::components)
    else {
        panic!("a substituted triple");
    };
    assert_eq!(kept, bound, "the lambda's own index is kept");
    assert_eq!(constant, closed, "a closed value is kept");
    assert_eq!(
        arena.value(shifted),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(5_u32),
        }),
        "the entry is carried under the lambda"
    );
    carried.sort_unstable();
    let mut expected = vec![
        Carried::Value(entry, shifted),
        Carried::Value(free, shifted),
        Carried::Value(triple, value),
        Carried::Computation(returned, body),
        Carried::Computation(lambda, substituted),
    ];
    expected.sort_unstable();
    assert_eq!(
        carried, expected,
        "every rewritten node is reported beside its source, and no kept one"
    );
    let mark = arena.watermark();
    let mut none = Vec::new();
    assert_eq!(
        substitute_environment_traced(&mut arena, TermId::Computation(lambda), &[], &mut none),
        TermId::Computation(lambda)
    );
    assert!(
        none.is_empty() && mark == arena.watermark(),
        "an empty environment mints and reports nothing"
    );
}

#[test]
fn a_relevelling_reads_only_the_binders_decodes_at_its_level()
{
    let mut arena = CoreArena::new();
    let zero = Level::zero();
    let one = Level::constant(LevelConstant::from(1_u64));
    let binder = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let decoded = arena.value_type_element(binder, zero.clone());
    let listed = arena.value_type_list(decoded);
    let foreign = arena.value_type_element(outer, zero.clone());
    let computed = arena.comp_type_element(binder, zero);
    let suspended = arena.value_type_thunk(computed);
    // Under the pi's own binder the family's binder counts one and the pi's
    // argument zero, so `foreign` there decodes the binder and `decoded` the
    // argument.
    let inner = arena.value_type_product(&[foreign, decoded]);
    let returns = arena.comp_type_returner(inner);
    let pi = arena.comp_type_pi(decoded, returns);
    let dependent = arena.value_type_thunk(pi);
    let family = arena.value_type_product(&[decoded, listed, foreign, suspended, dependent]);
    let relevelled = relevel_value_type(&mut arena, family, one.clone());
    let at_one = |arena: &CoreArena, id: ValueTypeId, code: ValueId| {
        matches!(arena.value_type(id), Some(&ValueType::Element { code: read, ref target })
            if read == code && *target == one)
    };
    let Some(&ValueType::Product(ref parts)) = arena.value_type(relevelled)
    else {
        panic!("the family stays a product");
    };
    let &[top, list, kept, thunk, pi_thunk] = &**parts
    else {
        panic!("the family keeps its five factors");
    };
    assert!(
        at_one(&arena, top, binder),
        "the binder's decode reads at one"
    );
    assert!(
        matches!(arena.value_type(list), Some(&ValueType::List(element)) if at_one(&arena, element, binder)),
        "the decode under a list reads at one"
    );
    assert_eq!(kept, foreign, "an outer variable's decode stands");
    assert!(
        matches!(arena.value_type(thunk), Some(&ValueType::Thunk(inside))
            if matches!(arena.comp_type(inside), Some(&CompType::Element { code, ref target })
                if code == binder && *target == one)),
        "a computation type's decode of the binder reads at one"
    );
    let Some(&ValueType::Thunk(pi)) = arena.value_type(pi_thunk)
    else {
        panic!("the dependent factor stays a thunk");
    };
    let Some(&CompType::Pi { domain, codomain }) = arena.comp_type(pi)
    else {
        panic!("the dependent factor stays a pi");
    };
    assert!(
        at_one(&arena, domain, binder),
        "the pi's domain decodes the binder at one"
    );
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(codomain)
    else {
        panic!("the pi's codomain stays a returner");
    };
    assert!(
        matches!(arena.value_type(result), Some(&ValueType::Product(ref inner))
            if matches!(**inner, [shifted, own] if at_one(&arena, shifted, outer) && own == decoded)),
        "under the pi the binder, one further out, reads at one and the pi's argument stands"
    );
    assert_eq!(
        relevel_value_type(&mut arena, relevelled, one.clone()),
        relevelled,
        "a family already at the level answers itself"
    );
    assert_eq!(
        relevel_value_type(&mut arena, foreign, one),
        foreign,
        "a family that never decodes its binder answers itself"
    );
}

#[test]
fn a_renaming_replaces_exactly_the_named_constants_and_atoms()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let renamed_atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let kept_atom = arena.value_type_abstract(ConstantIndex::from(1_usize));
    let renamed_constant = arena.value_constant(ConstantIndex::from(2_usize));
    let kept_constant = arena.value_constant(ConstantIndex::from(3_usize));
    let bound = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let quoted = arena.value_quote(renamed_atom);
    let kept_quote = arena.value_quote(kept_atom);
    let tuple = arena.value_tuple(&[bound, renamed_constant, kept_constant, quoted, kept_quote]);
    let returned = arena.computation_return(tuple);
    let lambda = arena.computation_lambda(returned);
    let thunk = arena.value_thunk(lambda);
    let mut renaming = Renaming::new();
    renaming.constant(ConstantIndex::from(2_usize), ConstantIndex::from(7_usize));
    renaming.atom(ConstantIndex::from(0_usize), integer);
    let mut carried = Vec::new();
    let renamed = rename_value_traced(&mut arena, thunk, &renaming, &mut carried);
    let Some(&Value::Thunk(body)) = arena.value(renamed)
    else {
        panic!("a renamed thunk");
    };
    let Some(&Computation::Lambda(inner)) = arena.computation(body)
    else {
        panic!("a renamed lambda");
    };
    let Some(&Computation::Return(value)) = arena.computation(inner)
    else {
        panic!("a renamed return");
    };
    let Some(&[variable_kept, constant, other, code, other_code]) =
        arena.value(value).and_then(Value::components)
    else {
        panic!("a renamed tuple");
    };
    assert_eq!(variable_kept, bound, "a bound variable is no constant");
    assert_eq!(
        arena.value(constant),
        Some(&Value::Constant(ConstantIndex::from(7_usize))),
        "the named constant is replaced at every depth"
    );
    assert_eq!(
        other, kept_constant,
        "a constant the renaming does not name stands"
    );
    assert_eq!(
        arena.value(code),
        Some(&Value::Quote(integer)),
        "a quoted atom reads as the type it is renamed to"
    );
    assert_eq!(
        other_code, kept_quote,
        "an atom the renaming does not name stands"
    );
    carried.sort_unstable();
    let mut expected = vec![
        Carried::Value(renamed_constant, constant),
        Carried::ValueType(renamed_atom, integer),
        Carried::Value(quoted, code),
        Carried::Value(tuple, value),
        Carried::Computation(returned, inner),
        Carried::Computation(lambda, body),
        Carried::Value(thunk, renamed),
    ];
    expected.sort_unstable();
    assert_eq!(
        carried, expected,
        "every rewritten node is reported, and no kept one"
    );
    let mut type_carried = Vec::new();
    assert_eq!(
        rename_value_type_traced(&mut arena, renamed_atom, &renaming, &mut type_carried),
        integer,
        "an atom standing alone is the type it is renamed to"
    );
    assert_eq!(
        rename_value_type_traced(&mut arena, kept_atom, &renaming, &mut type_carried),
        kept_atom
    );
    assert_eq!(type_carried, vec![Carried::ValueType(
        renamed_atom,
        integer
    )]);
}

#[test]
fn a_renaming_places_each_named_bound_region_wherever_it_stands()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let named = Region::Bound(RegionBinder::from(0_u32));
    let unnamed = Region::Bound(RegionBinder::from(1_u32));
    let scoped = Region::Scoped(RegionDepth::from(1_u32));
    let placed = Region::Scoped(RegionDepth::from(3_u32));
    let kept_named = arena.value_type_kept(integer, named);
    let kept_unnamed = arena.value_type_kept(integer, unnamed);
    let kept_scoped = arena.value_type_kept(integer, scoped);
    let capability = arena.value_type_capability(EffectRow::EMPTY, CapabilityGrade::Durable, named);
    let parts = arena.value_type_product(&[kept_named, kept_unnamed, kept_scoped, capability]);
    let inner = arena.comp_type_returner(parts);
    let suspended = arena.value_type_thunk(inner);
    let console =
        crate::effect::EffectSig::new(crate::effect::EffectName::from("Console"), alloc::vec![
            crate::effect::EffectOp {
                name: crate::effect::OperationName::from("print"),
                payload: integer,
                reply: integer,
            }
        ])
        .expect("one operation");
    let instances = |at: Region| {
        EffectRow::from_placed([
            (console.clone(), Region::Held),
            (console.clone(), at),
            (console.clone(), unnamed),
        ])
        .expect("three instances apart")
    };
    let answer = arena.comp_type_returner_with_effects(suspended, instances(named));
    let arrow = arena.comp_type_arrow(kept_named, answer);
    let function = arena.value_type_thunk(arrow);
    let mut renaming = Renaming::new();
    renaming.region(RegionBinder::from(0_u32), placed);
    let mut carried = Vec::new();
    let renamed = rename_value_type_traced(&mut arena, function, &renaming, &mut carried);
    let Some(&ValueType::Thunk(body)) = arena.value_type(renamed)
    else {
        panic!("a renamed thunk type");
    };
    let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(body)
    else {
        panic!("a renamed arrow");
    };
    assert_eq!(
        arena.value_type(domain),
        Some(&ValueType::Kept {
            value: integer,
            region: placed
        }),
        "the domain keeps its value at the region the binder is placed at"
    );
    let Some(&CompType::Returner {
        result,
        ref effects,
    }) = arena.comp_type(codomain)
    else {
        panic!("a renamed returner");
    };
    assert_eq!(
        effects,
        &instances(placed),
        "the row's instance at the binder is placed with it; the default and the unnamed stand"
    );
    let Some(&ValueType::Thunk(suspended_body)) = arena.value_type(result)
    else {
        panic!("a renamed suspension");
    };
    let Some(&CompType::Returner {
        result: product, ..
    }) = arena.comp_type(suspended_body)
    else {
        panic!("a renamed inner returner");
    };
    let Some(&ValueType::Product(ref components)) = arena.value_type(product)
    else {
        panic!("a renamed product");
    };
    let &[first, second, third, fourth] = &**components
    else {
        panic!("four components");
    };
    assert_eq!(
        arena.value_type(first),
        Some(&ValueType::Kept {
            value: integer,
            region: placed
        }),
        "a kept type inside a suspension's answer is placed too"
    );
    assert_eq!(
        (second, third),
        (kept_unnamed, kept_scoped),
        "a bound region the renaming does not name and a scoped region stand"
    );
    assert!(
        matches!(arena.value_type(fourth), Some(&ValueType::Capability { region, .. }) if region == placed),
        "a capability at the binder lives at the region it is placed at"
    );
    assert!(
        carried.contains(&Carried::ValueType(kept_named, domain)),
        "the placed kept type is reported beside the one it was rewritten from"
    );
}

#[test]
fn a_traced_shift_raises_only_past_its_scope()
{
    let mut arena = CoreArena::new();
    let [own, kept, past] =
        [0_u32, 1, 2].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
    let triple = arena.value_tuple(&[own, kept, past]);
    let returned = arena.computation_return(triple);
    let lambda = arena.computation_lambda(returned);
    let mut carried = Vec::new();
    let shifted =
        super::shift_computation_under(&mut arena, lambda, Binders::ONE, Binders::from(2_u32))
            .settle_traced(&mut arena, &mut carried);
    let Some(&Computation::Lambda(body)) = arena.computation(shifted)
    else {
        panic!("a shifted lambda");
    };
    let Some(&Computation::Return(value)) = arena.computation(body)
    else {
        panic!("a shifted return");
    };
    let Some(&[first, second, raised]) = arena.value(value).and_then(Value::components)
    else {
        panic!("a shifted triple");
    };
    assert_eq!(
        (first, second),
        (own, kept),
        "the lambda's own index and the one inside the scope stand"
    );
    assert_eq!(
        arena.value(raised),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(4_u32),
        }),
        "an index past the scope is raised by the amount"
    );
    carried.sort_unstable();
    let mut expected = vec![
        Carried::Value(past, raised),
        Carried::Value(triple, value),
        Carried::Computation(returned, body),
        Carried::Computation(lambda, shifted),
    ];
    expected.sort_unstable();
    assert_eq!(
        carried, expected,
        "exactly the rewritten nodes are reported"
    );
    let mark = arena.watermark();
    let mut none = Vec::new();
    assert_eq!(
        super::shift_computation_under(&mut arena, lambda, Binders::ONE, Binders::NONE)
            .settle_traced(&mut arena, &mut none),
        lambda
    );
    assert!(
        none.is_empty() && mark == arena.watermark(),
        "no amount mints and reports nothing"
    );
}

#[test]
fn a_traced_type_shift_reports_each_copy()
{
    let mut arena = CoreArena::new();
    let [kept, past] = [0_u32, 1].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
    let carrier = arena.value_type_unit();
    let path = arena.value_type_path(carrier, kept, past);
    let returner = arena.comp_type_returner(path);
    let mut carried = Vec::new();
    let shifted = super::shift_comp_type_under(&mut arena, returner, Binders::ONE, Binders::ONE)
        .settle_traced(&mut arena, &mut carried);
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(shifted)
    else {
        panic!("a shifted returner");
    };
    let Some(&ValueType::Path { left, right, .. }) = arena.value_type(result)
    else {
        panic!("a shifted path type");
    };
    assert_eq!(left, kept, "the endpoint inside the scope stands");
    assert_eq!(
        arena.value(right),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(2_u32),
        }),
        "the endpoint past the scope is raised"
    );
    carried.sort_unstable();
    let mut expected = vec![
        Carried::Value(past, right),
        Carried::ValueType(path, result),
        Carried::CompType(returner, shifted),
    ];
    expected.sort_unstable();
    assert_eq!(
        carried, expected,
        "exactly the rewritten nodes are reported"
    );
    let mark = arena.watermark();
    let mut none = Vec::new();
    assert_eq!(
        super::shift_comp_type_under(&mut arena, returner, Binders::ONE, Binders::NONE)
            .settle_traced(&mut arena, &mut none),
        returner
    );
    assert!(
        none.is_empty() && mark == arena.watermark(),
        "no amount mints and reports nothing"
    );
}

#[test]
fn a_traced_value_type_shift_reports_each_copy()
{
    let mut arena = CoreArena::new();
    let [kept, past] = [0_u32, 1].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
    let carrier = arena.value_type_unit();
    let path = arena.value_type_path(carrier, kept, past);
    let mut carried = Vec::new();
    let shifted = super::shift_value_type_under(&mut arena, path, Binders::ONE, Binders::ONE)
        .settle_traced(&mut arena, &mut carried);
    let Some(&ValueType::Path { left, right, .. }) = arena.value_type(shifted)
    else {
        panic!("a shifted path type");
    };
    assert_eq!(left, kept, "the endpoint inside the scope stands");
    assert_eq!(
        arena.value(right),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(2_u32),
        }),
        "the endpoint past the scope is raised"
    );
    carried.sort_unstable();
    let mut expected = vec![
        Carried::Value(past, right),
        Carried::ValueType(path, shifted),
    ];
    expected.sort_unstable();
    assert_eq!(
        carried, expected,
        "exactly the rewritten nodes are reported"
    );
    let mark = arena.watermark();
    let mut none = Vec::new();
    assert_eq!(
        super::shift_value_type_under(&mut arena, path, Binders::ONE, Binders::NONE)
            .settle_traced(&mut arena, &mut none),
        path
    );
    assert!(
        none.is_empty() && mark == arena.watermark(),
        "no amount mints and reports nothing"
    );
}

#[test]
fn a_traced_instantiation_replaces_its_binder()
{
    let mut arena = CoreArena::new();
    let argument = variable(&mut arena, DeBruijnIndex::from(3_u32));
    let [own, binder, outer] =
        [0_u32, 1, 2].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
    let triple = arena.value_tuple(&[own, binder, outer]);
    let returned = arena.computation_return(triple);
    let lambda = arena.computation_lambda(returned);
    let mut carried = Vec::new();
    let instantiated =
        super::instantiate_computation_traced(&mut arena, lambda, argument, &mut carried);
    let Some(&Computation::Lambda(body)) = arena.computation(instantiated)
    else {
        panic!("an instantiated lambda");
    };
    let Some(&Computation::Return(value)) = arena.computation(body)
    else {
        panic!("an instantiated return");
    };
    let Some(&[kept, placed, lowered]) = arena.value(value).and_then(Value::components)
    else {
        panic!("an instantiated triple");
    };
    let index_of = |arena: &CoreArena, id| match arena.value(id) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => Some(u32::from(index)),
        Some(_) | None => None,
    };
    assert_eq!(kept, own, "the lambda's own index stands");
    assert_eq!(
        index_of(&arena, placed),
        Some(4),
        "the binder is the argument, carried under the lambda"
    );
    assert_eq!(
        index_of(&arena, lowered),
        Some(1),
        "an index past the binder is lowered by one"
    );
    carried.sort_unstable();
    let mut expected = vec![
        Carried::Value(argument, placed),
        Carried::Value(binder, placed),
        Carried::Value(outer, lowered),
        Carried::Value(triple, value),
        Carried::Computation(returned, body),
        Carried::Computation(lambda, instantiated),
    ];
    expected.sort_unstable();
    assert_eq!(
        carried, expected,
        "exactly the rewritten nodes are reported"
    );
}

/// A clause read through the continuation it resumes (#2272): beneath its
/// stack binder `k`, `resume(k, return ())` runs as `x ← return (); N`,
/// `abandon(k)` returns the unit, `return k` returns the function `λx. N`,
/// and an index past `k` is lowered by one.
#[test]
fn a_clause_resumes_through_its_continuation_2272()
{
    let mut arena = CoreArena::new();
    // N, beneath the fed value: `return (x, #1)`, #1 the context's first.
    let [fed, outer] = [0_u32, 1].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
    let pair = arena.value_tuple(&[fed, outer]);
    let continuation = arena.computation_return(pair);
    let unit = arena.value_unit();
    let returned_unit = arena.computation_return(unit);
    let stack = fed;
    let resumed = arena.computation_resume(stack, returned_unit);
    let abandoned = arena.computation_abandon(stack);
    let escaped = arena.computation_return(stack);
    let past = arena.computation_return(outer);
    let [ran, ended, held, lowered] = [resumed, abandoned, escaped, past]
        .map(|body| super::resume_through(&mut arena, body, continuation));
    let returned = |arena: &CoreArena, id| match arena.computation(id) {
        Some(&Computation::Return(value)) => arena.value(value).cloned(),
        Some(_) | None => None,
    };
    assert_eq!(
        arena.computation(ran),
        Some(&Computation::Bind(returned_unit, continuation)),
        "a resumption runs the continuation at what it is fed"
    );
    assert_eq!(
        returned(&arena, ended).as_ref().and_then(Value::components),
        Some(&[][..]),
        "an abandonment returns the unit"
    );
    let Some(Value::Thunk(suspended)) = returned(&arena, held)
    else {
        panic!("the stack used as a value is a suspended function");
    };
    assert_eq!(
        arena.computation(suspended),
        Some(&Computation::Lambda(continuation)),
        "the stack used as a value is the continuation's function"
    );
    assert_eq!(
        returned(&arena, lowered),
        Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        }),
        "an index past the stack is lowered by one"
    );
}

#[test]
fn a_traced_instantiation_reports_no_computation_or_type_it_kept()
{
    let mut arena = CoreArena::new();
    let argument = arena.value_constant(ConstantIndex::from(7_usize));
    let free = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let unit = arena.value_unit();
    let unit_type = arena.value_type_unit();
    let moved = arena.computation_return(free);
    let kept = arena.computation_return(unit);
    let sequenced = arena.computation_bind(moved, kept);
    let annotation = arena.comp_type_returner(unit_type);
    let body = arena.computation_ascribe(sequenced, annotation);
    let mut carried = Vec::new();
    let instantiated =
        super::instantiate_computation_traced(&mut arena, body, argument, &mut carried);
    assert!(
        !carried.iter().any(|pair| matches!(
            *pair,
            Carried::Computation(held, _) if held == kept
        ) || matches!(*pair, Carried::CompType(held, _) if held == annotation)),
        "a kept computation or computation type is no carried pair: {carried:?}"
    );
    assert!(
        carried.contains(&Carried::Computation(body, instantiated)),
        "while the rewritten root is"
    );
}

/// One former spelled around `child`, which stands where none of the
/// former's own binders reaches; a computation is held in a thunk and a type
/// in a quote, so each reads as a value.
pub type Former = fn(&mut CoreArena, ValueId) -> ValueId;

/// One former and the name its failures are reported under.
pub struct Witnessed
{
    /// The former's name.
    pub what: &'static str,
    /// The former.
    pub former: Former,
}

/// The formers the rebuild decisions, and the importer's relocation, are
/// witnessed at.
///
/// # Specification
/// trivial.
pub fn formers() -> Vec<Witnessed>
{
    use alloc::sync::Arc;

    use crate::control::EffectClause;
    use crate::effect::EffectName;
    use crate::effect::EffectOp;
    use crate::effect::EffectSig;
    use crate::effect::OperationName;
    use crate::memory::MemoryForm;
    use crate::primitive::Arguments;
    use crate::session::RecordedMove;
    use crate::session::SessionAction;
    use crate::session::SessionRelation;

    /// The one-operation interface the effect formers carry.
    ///
    /// # Specification
    /// trivial.
    fn probe(arena: &mut CoreArena) -> EffectSig
    {
        let unit = arena.value_type_unit();
        EffectSig::new(EffectName::from("Probe"), [EffectOp {
            name: OperationName::from("ask"),
            payload: unit,
            reply: unit,
        }])
        .expect("one operation")
    }
    /// `Path(Unit, child, ())`: a type that reads `child` in no binder.
    ///
    /// # Specification
    /// trivial.
    fn path(
        arena: &mut CoreArena,
        child: ValueId,
    ) -> ValueTypeId
    {
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        arena.value_type_path(unit_type, child, unit)
    }
    /// `return ()`.
    ///
    /// # Specification
    /// trivial.
    fn done(arena: &mut CoreArena) -> ComputationId
    {
        let unit = arena.value_unit();
        arena.computation_return(unit)
    }
    /// The handler clauses: `ask` answered by `return ()`.
    ///
    /// # Specification
    /// trivial.
    fn clauses(arena: &mut CoreArena) -> Arc<[EffectClause]>
    {
        let body = done(arena);
        Arc::from([EffectClause {
            operation: OperationName::from("ask"),
            body,
        }])
    }
    let reflexivity: Former = |a, c| a.value_path_refl(c);
    let rows: Vec<(&'static str, Former)> = alloc::vec![
        ("reflexivity", reflexivity),
        ("here", |a, c| a.value_here(c)),
        ("returned", |a, c| {
            let body = a.computation_return(c);
            a.value_returned(body)
        }),
        ("nested", |a, c| {
            let body = a.computation_return(c);
            a.value_nested(body)
        }),
        ("run", |a, c| {
            let body = a.computation_return(c);
            a.value_run(body)
        }),
        ("path product", |a, c| {
            let unit = a.value_unit();
            a.value_path_product(unit, c)
        }),
        ("funext", |a, c| {
            let unit = a.value_unit();
            a.value_funext(c, unit)
        }),
        ("equivalence", |a, c| {
            let unit = a.value_unit();
            a.value_equiv(unit, c)
        }),
        ("session identity", |a, c| {
            let unit = a.value_unit();
            a.value_session_related(SessionRelation::Equivalence, unit, c, unit)
        }),
        ("session identity's payload paths", |a, c| {
            let unit = a.value_unit();
            a.value_session_related(SessionRelation::Equivalence, unit, unit, c)
        }),
        ("stay", |a, c| a.value_stay(c)),
        ("then", |a, c| {
            let unit = a.value_unit();
            a.value_then(c, unit)
        }),
        ("flow product", |a, c| {
            let unit = a.value_unit();
            a.value_flow_product(unit, c)
        }),
        ("forward", |a, c| a.value_forward(c)),
        ("function flow", |a, c| {
            let unit = a.value_unit();
            a.value_function_flow(c, unit)
        }),
        ("recorded run", |a, c| {
            a.value_recorded(Arc::from([RecordedMove::Closed, RecordedMove::Sent(c)]))
        }),
        ("univalence", |a, c| {
            let description = || crate::ua::Description {
                name: gandr_theory_levitation::Name::from("M"),
                generators: alloc::boxed::Box::from([]),
            };
            let sides = Arc::new(crate::ua::Sides {
                source: description(),
                target: description(),
            });
            let stratum = crate::ua::Stratum {
                degree: gandr_theory_sites::Degree::from(1_usize),
                bound: gandr_theory_sites::ShapeSize::from(4_usize),
            };
            let unit = a.value_unit();
            a.value_ua(stratum, sides, unit, c)
        }),
        ("path equivalence", |a, c| {
            let unit_type = a.value_type_unit();
            let unit = a.value_unit();
            a.value_path_equiv(unit_type, unit, c, Arc::default())
        }),
        ("marked value", |a, c| a
            .value_mark(MarkIndex::from(0_u32), c)),
        ("cell", |a, c| {
            let nil = a.value_list_nil();
            a.value_list_cons(c, nil)
        }),
        ("constructor", |a, c| {
            let unit_type = a.value_type_unit();
            a.value_constructor(
                unit_type,
                gandr_kernel_term::ConstructorTag::from(0_usize),
                vec![c],
            )
        }),
        ("perform", |a, c| {
            let signature = probe(a);
            let body = a.computation_perform(signature, OperationName::from("ask"), c);
            a.value_thunk(body)
        }),
        ("exercise", |a, c| {
            let signature = probe(a);
            let unit = a.value_unit();
            let body = a.computation_exercise(c, signature, OperationName::from("ask"), unit);
            a.value_thunk(body)
        }),
        ("handler", |a, c| {
            let signature = probe(a);
            let subject = a.computation_return(c);
            let (on_return, clauses) = (done(a), clauses(a));
            let body = a.computation_handle(signature, subject, on_return, clauses);
            a.value_thunk(body)
        }),
        ("scope", |a, c| {
            let signature = probe(a);
            // The subject stands under the capability's binder.
            let under_capability = super::shift_value(a, c, Binders::ONE).settle(a);
            let subject = a.computation_return(under_capability);
            let (on_return, clauses) = (done(a), clauses(a));
            let body = a.computation_scope(signature, subject, on_return, clauses);
            a.value_thunk(body)
        }),
        ("list fold", |a, c| {
            let unit_type = a.value_type_unit();
            let (nil, cons) = (done(a), done(a));
            let body = a.computation_list_fold(unit_type, unit_type, c, nil, cons);
            a.value_thunk(body)
        }),
        ("native operation", |a, c| {
            let row = crate::primitive::PRELUDE
                .first()
                .copied()
                .expect("the prelude has a row");
            let unit = a.value_unit();
            let body = a.computation_primitive(row, Arguments::Binary([unit, c]));
            a.value_thunk(body)
        }),
        ("nominal case", |a, c| {
            let unit_type = a.value_type_unit();
            let motive = a.comp_type_returner(unit_type);
            let branch = done(a);
            let body = a.computation_data_case(c, motive, vec![branch], vec![
                gandr_kernel_term::FieldCount::from(0_usize),
            ]);
            a.value_thunk(body)
        }),
        ("record projection", |a, c| {
            let body = a.computation_record_projection(
                c,
                gandr_kernel_term::FieldLabel::from(String::from("a")),
            );
            a.value_thunk(body)
        }),
        ("tuple projection", |a, c| {
            let body =
                a.computation_tuple_projection(c, gandr_kernel_term::Component::from(0_usize));
            a.value_thunk(body)
        }),
        ("transport", |a, c| {
            let unit = a.value_unit();
            let body = a.computation_transport(c, unit);
            a.value_thunk(body)
        }),
        ("path transport", |a, c| {
            let unit_type = a.value_type_unit();
            let unit = a.value_unit();
            let body = a.computation_path_transport(unit_type, c, unit);
            a.value_thunk(body)
        }),
        ("ride", |a, c| {
            let unit_type = a.value_type_unit();
            let unit = a.value_unit();
            let body = a.computation_ride(unit_type, c, unit);
            a.value_thunk(body)
        }),
        ("telescope transport", |a, c| {
            let unit_type = a.value_type_unit();
            let motive = a.comp_type_returner(unit_type);
            let unit = a.value_unit();
            let body = a.computation_telescope_transport(motive, c, unit, unit, unit);
            a.value_thunk(body)
        }),
        ("fixpoint", |a, c| {
            let under_self = super::shift_value(a, c, Binders::ONE).settle(a);
            let returned = a.computation_return(under_self);
            let body =
                a.computation_fixpoint(returned, gandr_kernel_term::FixpointEvidence::Partial);
            a.value_thunk(body)
        }),
        ("marked computation", |a, c| {
            let returned = a.computation_return(c);
            let body = a.computation_mark(MarkIndex::from(0_u32), returned);
            a.value_thunk(body)
        }),
        ("session action", |a, c| {
            let body = a.computation_session(SessionAction::Send {
                endpoint: DeBruijnIndex::from(0_u32),
                payload: c,
            });
            a.value_thunk(body)
        }),
        ("memory form", |a, c| {
            let rest = done(a);
            let body = a.computation_memory(MemoryForm::Hold {
                value: c,
                body: rest,
                grade: crate::memory::HoldGrade::Many,
            });
            a.value_thunk(body)
        }),
        ("world form", |a, c| {
            let rest = done(a);
            let body = a.computation_world(crate::world::WorldForm::Leta {
                value: c,
                body: rest,
            });
            a.value_thunk(body)
        }),
        ("record type", |a, c| {
            let field = path(a, c);
            let record = a.value_type_record(BTreeMap::from([(
                gandr_kernel_term::FieldLabel::from(String::from("a")),
                field,
            )]));
            a.value_quote(record)
        }),
        ("list type", |a, c| {
            let element = path(a, c);
            let list = a.value_type_list(element);
            a.value_quote(list)
        }),
        ("path universe", |a, c| {
            let unit = a.value_unit();
            let universe = a.value_type_path_universe(c, unit);
            a.value_quote(universe)
        }),
        ("flow type", |a, c| {
            let unit_type = a.value_type_unit();
            let unit = a.value_unit();
            let flow = a.value_type_flow(unit_type, unit, c);
            a.value_quote(flow)
        }),
        ("run type", |a, c| {
            let run = a.value_type_run(c);
            a.value_quote(run)
        }),
        ("prefix type", |a, c| {
            let prefix = a.value_type_prefix(c);
            a.value_quote(prefix)
        }),
        ("located type", |a, c| {
            let inner = path(a, c);
            let located = a.value_type_world(crate::world::WorldType::At {
                inner,
                world: crate::world::World::Host,
            });
            a.value_quote(located)
        }),
        ("staged type", |a, c| {
            let base = path(a, c);
            let stage = gandr_kernel_term::Stage::At(gandr_kernel_term::StageId::from(0_usize));
            let staged = a.value_type_staged(base, stage);
            a.value_quote(staged)
        }),
        ("session type", |a, c| {
            use crate::session::PayloadCount;
            use crate::session::PayloadSlot;
            use crate::session::Protocol;
            use crate::session::ProtocolState;
            use crate::session::ProtocolSyntax;
            use crate::session::SessionType;
            let send = Protocol::new(
                vec![
                    ProtocolSyntax::Send {
                        payload: PayloadSlot::from(0_usize),
                        next: ProtocolState::from(1_usize),
                    },
                    ProtocolSyntax::End,
                ],
                ProtocolState::from(0_usize),
                PayloadCount::from(1_usize),
            )
            .expect("a send, then the end");
            let payload = path(a, c);
            let session = SessionType::new(
                alloc::sync::Arc::new(send),
                alloc::sync::Arc::from([payload]),
            )
            .expect("one payload for one slot");
            let ty = a.value_type_session(session);
            a.value_quote(ty)
        }),
        ("dependent pair type", |a, c| {
            let first = path(a, c);
            let unit_type = a.value_type_unit();
            let sigma = a.value_type_sigma(first, unit_type);
            a.value_quote(sigma)
        }),
        ("lazy product of computation types", |a, c| {
            let first = path(a, c);
            let first = a.comp_type_returner(first);
            let unit_type = a.value_type_unit();
            let second = a.comp_type_returner(unit_type);
            let with = a.alloc_comp_type(CompType::With([second, first, second].into()));
            a.value_quote_computation(with)
        }),
        ("tuple", |a, c| {
            let unit = a.value_unit();
            a.value_tuple(&[unit, c])
        }),
        ("injection", |a, c| a.value_injection(
            gandr_kernel_term::Summand::from(1_usize),
            c
        )),
        ("lift", |a, c| a.value_lift(Level::zero(), c)),
        ("record", |a, c| {
            a.value_record(BTreeMap::from([(
                gandr_kernel_term::FieldLabel::from(String::from("a")),
                c,
            )]))
        }),
        ("static application", |a, c| {
            let unit = a.value_unit();
            let head = a.value_static_lambda(unit);
            a.value_static_application(head, c)
        }),
        ("static lambda", |a, c| {
            let under = super::shift_value(a, c, Binders::ONE).settle(a);
            a.value_static_lambda(under)
        }),
        ("reified stack", |a, c| {
            let body = done(a);
            a.value_reify(Arc::from([
                crate::control::StackFrame::Apply(c),
                crate::control::StackFrame::Bind(body),
            ]))
        }),
        ("lambda", |a, c| {
            let under = super::shift_value(a, c, Binders::ONE).settle(a);
            let returned = a.computation_return(under);
            let body = a.computation_lambda(returned);
            a.value_thunk(body)
        }),
        ("application", |a, c| {
            let head = done(a);
            let body = a.computation_application(head, c);
            a.value_thunk(body)
        }),
        ("bind", |a, c| {
            let (bound, rest) = (a.computation_return(c), done(a));
            let body = a.computation_bind(bound, rest);
            a.value_thunk(body)
        }),
        ("ascription", |a, c| {
            let returned = a.computation_return(c);
            let unit_type = a.value_type_unit();
            let ty = a.comp_type_returner(unit_type);
            let body = a.computation_ascribe(returned, ty);
            a.value_thunk(body)
        }),
        ("binary case", |a, c| {
            let branches = [done(a), done(a)];
            let body = a.computation_case(c, &branches);
            a.value_thunk(body)
        }),
        ("split", |a, c| {
            let rest = done(a);
            let body = a.computation_split(c, crate::syntax::ComponentCount::from(2_usize), rest);
            a.value_thunk(body)
        }),
        ("list case", |a, c| {
            let (nil, cons) = (done(a), done(a));
            let body = a.computation_list_case(c, nil, cons);
            a.value_thunk(body)
        }),
        ("resume", |a, c| {
            let rest = done(a);
            let body = a.computation_resume(c, rest);
            a.value_thunk(body)
        }),
        ("lazy product", |a, c| {
            let (returned, other) = (a.computation_return(c), done(a));
            let with = a.computation_with(&[other, returned]);
            let body = a.computation_project(crate::Component::from(1_usize), with);
            a.value_thunk(body)
        }),
        ("reset", |a, c| {
            let returned = a.computation_return(c);
            let body = a.computation_reset(returned);
            a.value_thunk(body)
        }),
    ];
    rows.into_iter()
        .map(|(what, former)| Witnessed { what, former })
        .collect()
}

#[test]
fn every_former_is_kept_when_nothing_beneath_it_changes_and_carries_what_does()
{
    let mut arena = CoreArena::new();
    let free = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let argument = arena.value_constant(ConstantIndex::from(7_usize));
    let closed = arena.value_unit();
    for Witnessed { what, former } in formers() {
        let kept = former(&mut arena, closed);
        let open = former(&mut arena, free);
        let expected = former(&mut arena, argument);
        let both = arena.value_tuple(&[kept, open]);
        let rewritten = instantiate_value(&mut arena, both, argument);
        let Some(&Value::Tuple(ref components)) = arena.value(rewritten)
        else {
            panic!("{what}: the tuple is kept a tuple");
        };
        let &[first, second] = &**components
        else {
            panic!("{what}: the tuple keeps its arity");
        };
        assert_eq!(
            kept, first,
            "{what}: a former nothing beneath changes is the node itself"
        );
        assert_ne!(
            open, second,
            "{what}: a former over a change is minted anew"
        );
        assert_eq!(
            crate::CertificateEquality::Equal,
            crate::equal_certificate_syntax(&arena, second, expected),
            "{what}: the change is carried into the fresh node"
        );
    }
}

/// With nothing decided, elaboration keeps every former that holds no run,
/// reporting nothing rebuilt. The run former standing alone is in no
/// computation's values and is refused by name; returned from a computation,
/// it is the computation it runs, which mints no bind.
#[test]
fn an_undecided_elaboration_keeps_every_former_but_the_run()
{
    let mut arena = CoreArena::new();
    let child = arena.value_constant(ConstantIndex::from(7_usize));
    let undecided = BTreeMap::new();
    for Witnessed { what, former } in formers() {
        let subject = former(&mut arena, child);
        let (mut carried, mut binds) = (Vec::new(), Vec::new());
        let elaborated =
            elaborate_nested_traced(&mut arena, subject, &undecided, &mut carried, &mut binds);
        if what == "run" {
            assert_eq!(elaborated, Err(Unenclosed { run: subject }), "{what}");
            let returned = arena.computation_return(subject);
            let held = arena.value_thunk(returned);
            let ran =
                elaborate_nested_traced(&mut arena, held, &undecided, &mut carried, &mut binds);
            assert!(
                matches!(ran, Ok(rebuilt) if rebuilt != held) && binds.is_empty(),
                "{what}: a returned run is the computation it runs"
            );
        }
        else {
            assert_eq!(elaborated, Ok(subject), "{what}: nothing to elaborate");
            assert!(
                carried.is_empty() && binds.is_empty(),
                "{what}: nothing is rebuilt"
            );
        }
    }
}

#[test]
fn an_instantiation_at_a_call_binds_it_ahead_of_each_decode_reading_it()
{
    let mut arena = CoreArena::new();
    // `El ⟨force(head) argument⟩`, each by its index.
    let decode = |arena: &mut CoreArena, head: u32, argument: u32| {
        let head = variable(arena, DeBruijnIndex::from(head));
        let forced = arena.computation_force(head);
        let argument = variable(arena, DeBruijnIndex::from(argument));
        let call = arena.computation_application(forced, argument);
        let code = arena.value_returned(call);
        arena.value_type_element(code, Level::zero())
    };
    // `El ⟨c ← force(f) g; force(tm) c⟩`: the call bound ahead of the family.
    let bound = |arena: &mut CoreArena, (f, g): (u32, u32), tm: u32| {
        let head = variable(arena, DeBruijnIndex::from(f));
        let forced = arena.computation_force(head);
        let argument = variable(arena, DeBruijnIndex::from(g));
        let ahead = arena.computation_application(forced, argument);
        let family = variable(arena, DeBruijnIndex::from(tm));
        let forced = arena.computation_force(family);
        let read = variable(arena, DeBruijnIndex::from(0_u32));
        let applied = arena.computation_application(forced, read);
        let bind = arena.computation_bind(ahead, applied);
        let code = arena.value_returned(bind);
        arena.value_type_element(code, Level::zero())
    };
    // Outside the binder `tm` is 0, `extend` 1 and `g` 2; under it, one more.
    let head = variable(&mut arena, DeBruijnIndex::from(1_u32));
    let forced = arena.computation_force(head);
    let g = variable(&mut arena, DeBruijnIndex::from(2_u32));
    let call = arena.computation_application(forced, g);
    let argument = arena.value_nested(call);
    // `Path(Unit, ⟨force(head) at⟩, at)`: a returned code as an endpoint.
    let endpoint = |arena: &mut CoreArena, head: u32, at: ValueId| {
        let head = variable(arena, DeBruijnIndex::from(head));
        let forced = arena.computation_force(head);
        let call = arena.computation_application(forced, at);
        let code = arena.value_returned(call);
        let unit = arena.value_type_unit();
        arena.value_type_path(unit, code, at)
    };
    // `tm(x)`, `tm(g)`, `x` outside any code, `tm(x)` under a binder, and an
    // endpoint reading `x`.
    let reads = decode(&mut arena, 1, 0);
    let spares = decode(&mut arena, 1, 3);
    let x = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let bare = arena.value_type_element(x, Level::zero());
    let unit = arena.value_type_unit();
    let deeper = decode(&mut arena, 2, 1);
    let deeper = arena.comp_type_returner(deeper);
    let deeper = arena.comp_type_pi(unit, deeper);
    let under = arena.value_type_thunk(deeper);
    let x = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let ends = endpoint(&mut arena, 1, x);
    let product = arena.value_type_product(&[reads, spares, bare, under, ends]);
    let codomain = arena.comp_type_returner(product);
    let instantiated = super::instantiate_comp_type_at_call(&mut arena, codomain, argument, call);
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(instantiated)
    else {
        panic!("a returner");
    };
    let Some(ValueType::Product(components)) = arena.value_type(result).cloned()
    else {
        panic!("a product");
    };
    let &[reads, spares, bare, under, ends] = &*components
    else {
        panic!("five components");
    };
    // The decode reading the binder binds the call ahead of its code; the one
    // that does not is substituted plainly; the decode of the binder itself
    // reads the call returned, as a type written with the call does (#3937);
    // under an inner binder the call rises past it; an endpoint holds the call
    // in place, as the lowering writes one.
    let returned = arena.value_returned(call);
    let expected = [
        bound(&mut arena, (1, 2), 1),
        decode(&mut arena, 0, 2),
        arena.value_type_element(returned, Level::zero()),
    ];
    let unit = arena.value_type_unit();
    let deeper = bound(&mut arena, (2, 3), 2);
    let deeper = arena.comp_type_returner(deeper);
    let deeper = arena.comp_type_pi(unit, deeper);
    let deeper = arena.value_type_thunk(deeper);
    let held = endpoint(&mut arena, 0, argument);
    for (what, found, expected) in [
        ("a decode reading the binder", reads, expected[0]),
        ("a decode sparing it", spares, expected[1]),
        ("the decode of the binder itself", bare, expected[2]),
        ("a decode under an inner binder", under, deeper),
        ("an endpoint reading the binder", ends, held),
    ] {
        assert_eq!(
            crate::syntax::equal_type_syntax(&arena, found, expected),
            crate::CertificateEquality::Equal,
            "{what}"
        );
    }
}
