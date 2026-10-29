use super::*;

/// A lambda whose sequenced body returns a static code outside the focusing
/// image.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a lambda sequences a returned unit before returning a static
///   lambda; all core references resolve, but focusing refuses the code.
/// - provides: a refusal after entering nested translation work without
///   violating a core constructor's precondition.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — focusing this valid nested core graph after an earlier
///   translation refuses the static code and preserves both destination marks
///   and the earlier provenance. This distinguishes missing rollback and damage
///   to the prefix; it covers this unsupported form, not an invalid source
///   arena.
/// - witness: `focus::tests::a_refused_focusing_leaves_the_arena_at_its_mark`
#[spec(ensures: |ret| match core.computation(ret) {
        | Some(&Computation::Lambda(bind)) => match core.computation(bind) {
            | Some(&Computation::Bind(bound, body)) => matches!(core.computation(bound), Some(&Computation::Return(unit)) if core.value(unit) == Some(&Value::unit()))
                && matches!(core.computation(body), Some(&Computation::Return(code)) if matches!(core.value(code), Some(&Value::StaticLambda(_)))),
            | _ => false,
        },
        | _ => false,
    })]
fn lambda_over_a_static_code(core: &mut CoreArena) -> ComputationId
{
    let unit = core.value_unit();
    let code = core.value_static_lambda(unit);
    let bound = core.computation_return(unit);
    let body = core.computation_return(code);
    let bind = core.computation_bind(bound, body);
    core.computation_lambda(bind)
}

/// A translation refused part-way leaves the arena and the provenance
/// table exactly at the marks they had on entry, though it had minted
/// nodes before the refusal.
#[test]
fn a_refused_focusing_leaves_the_arena_at_its_mark()
{
    let mut core = CoreArena::new();
    let refused = lambda_over_a_static_code(&mut core);
    let fine_value = core.value_unit();
    let fine = core.computation_return(fine_value);

    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let earlier = focus_computation(&core, fine, &mut arena, &mut provenance)
        .expect("a closed return focuses");
    let arena_mark = arena.watermark();
    let provenance_mark = provenance.len();

    let outcome = focus_computation(&core, refused, &mut arena, &mut provenance);
    assert!(
        matches!(outcome, Err(FocusRefusal::Code(_))),
        "the static code is refused by name: {outcome:?}"
    );
    assert_eq!(
        arena_mark,
        arena.watermark(),
        "the arena is back at its mark"
    );
    assert_eq!(
        provenance_mark,
        provenance.len(),
        "the provenance table is back at its mark"
    );
    assert_eq!(
        Some(FocusOrigin::Return),
        provenance.origin(earlier),
        "the earlier translation is untouched"
    );
}

/// Focusing records each bind of the caller's arena beside the binder `μ̃x.c`
/// it minted, the inner bind first. It records no bind of an identity
/// combinator's own build, whose writers name nodes of another arena. A
/// refusal after a bind is recorded drops that bind's entry.
#[test]
fn each_bind_records_its_binder_beside_its_writer()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let pair = core.value_tuple(&[unit, unit]);
    let first = core.computation_return(unit);
    let second = core.computation_return(pair);
    let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let tail = core.computation_return(bound);
    let inner = core.computation_bind(second, tail);
    let nested = core.computation_bind(first, inner);
    let binders = |arena: &CommandArena| {
        (0_u32 ..)
            .take(usize::from(arena.consumer_count()))
            .map(ConsumerId::from)
            .filter(|&consumer| {
                matches!(
                    arena.consumer(consumer),
                    Some(&ConsumerNode::MuTilde { .. })
                )
            })
            .collect::<Vec<_>>()
    };

    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let _root =
        focus_computation(&core, nested, &mut arena, &mut provenance).expect("nested binds focus");
    let recorded: Vec<(ConsumerId, ComputationId)> = provenance.binds().collect();
    let minted = binders(&arena);
    assert_eq!(
        (minted, alloc::vec![second, first]),
        (
            recorded.iter().map(|&(binder, _)| binder).collect(),
            recorded.iter().map(|&(_, writer)| writer).collect()
        ),
        "each binder minted stands beside its writer, the inner bind's first"
    );

    let code = core.value_static_lambda(unit);
    let refused_head = core.computation_return(code);
    let refused = core.computation_bind(refused_head, tail);
    let outcome = focus_computation(&core, refused, &mut arena, &mut provenance);
    assert!(
        matches!(outcome, Err(FocusRefusal::Code(_))),
        "the writer's static code is refused after its bind: {outcome:?}"
    );
    assert_eq!(
        recorded,
        provenance.binds().collect::<Vec<_>>(),
        "the refused bind leaves no entry, and the kept ones stay"
    );

    let unit_type = core.value_type_unit();
    let quoted = core.value_quote(unit_type);
    let kept = core.value_stay(quoted);
    let flow = core.value_flow_product(kept, kept);
    let writer = core.computation_return(flow);
    let program = core.computation_bind(writer, tail);
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let _root = focus_computation(&core, program, &mut arena, &mut provenance)
        .expect("a flow product focuses");
    assert!(
        binders(&arena).len() > 1,
        "the pairing combinator's build mints binders of its own"
    );
    assert_eq!(
        alloc::vec![writer],
        provenance
            .binds()
            .map(|(_, written)| written)
            .collect::<Vec<_>>(),
        "only the caller's bind is recorded"
    );
}

/// A quote of either sort focuses to a code producer naming the same quote:
/// `⌜Integer⌝` and `⌜F Integer⌝` each import back from the IL's annotations
/// to the type they quote.
#[test]
fn a_quote_focuses_to_the_code_it_names()
{
    let mut core = CoreArena::new();
    let integer = core.value_type_base(gandr_kernel_term::BaseType::Integer);
    let returns_integer = core.comp_type_returner(integer);
    let quoted = core.value_quote(integer);
    let quoted_computation = core.value_quote_computation(returns_integer);
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let mut read_back = |code| {
        let producer =
            focus_value(&core, code, &mut arena, &mut provenance).expect("a quote focuses");
        let Some(&ProducerNode::Code(held)) = arena.producer(producer)
        else {
            panic!("a quote focuses to a code producer");
        };
        let mut back = CoreArena::new();
        let value = gandr_core_term::TypeImporter::new(arena.annotations(), &mut back)
            .value(held)
            .expect("the code imports back");
        (back, value)
    };
    let is_integer = |arena: &CoreArena, ty| {
        arena.value_type(ty)
            == Some(&gandr_core_term::ValueType::Base(
                gandr_kernel_term::BaseType::Integer,
            ))
    };
    let (back, value) = read_back(quoted);
    assert!(
        matches!(back.value(value), Some(&Value::Quote(ty)) if is_integer(&back, ty)),
        "the value code reads back as `⌜Integer⌝`"
    );
    let (back, value) = read_back(quoted_computation);
    assert!(
        matches!(
            back.value(value),
            Some(&Value::QuoteComputation(ty)) if matches!(
                back.comp_type(ty),
                Some(&gandr_core_term::CompType::Returner { result, .. }) if is_integer(&back, result)
            )
        ),
        "the computation code reads back as `⌜F Integer⌝`"
    );
}

/// A static lambda and a static application have no producer: each is
/// refused naming it, and the arena is left at its mark.
#[test]
fn a_static_code_is_refused_by_name()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let lambda = core.value_static_lambda(unit);
    let applied = core.value_static_application(lambda, unit);
    for code in [lambda, applied] {
        let term = core.computation_return(code);
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let mark = arena.watermark();
        assert_eq!(
            focus_computation(&core, term, &mut arena, &mut provenance),
            Err(FocusRefusal::Code(code)),
            "the static code is refused by name"
        );
        assert_eq!(mark, arena.watermark(), "the arena is back at its mark");
    }
}

/// A value hole and a mark are refused by name; a computation hole is reached
/// as the perform of the reached-hole interface, its payload the hole's name
/// (#1881).
#[test]
fn a_hole_is_reached_and_a_mark_refused_by_name_1881()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let hole = core.value_hole(gandr_core_term::hole::HoleId::from(0_u32));
    let marked = core.value_mark(gandr_core_term::hole::MarkIndex::from(0_u32), unit);
    for incomplete in [hole, marked] {
        let term = core.computation_return(incomplete);
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let mark = arena.watermark();
        assert_eq!(
            focus_computation(&core, term, &mut arena, &mut provenance),
            Err(FocusRefusal::IncompleteValue(incomplete)),
            "the value is refused by name"
        );
        assert_eq!(mark, arena.watermark(), "the arena is back at its mark");
    }
    let returned = core.computation_return(unit);
    let computation_mark =
        core.computation_mark(gandr_core_term::hole::MarkIndex::from(1_u32), returned);
    let term = core.computation_bind(computation_mark, returned);
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    assert_eq!(
        focus_computation(&core, term, &mut arena, &mut provenance),
        Err(FocusRefusal::IncompleteComputation(computation_mark)),
        "the mark is refused by name"
    );
    let computation_hole = core.computation_hole(gandr_core_term::hole::HoleId::from(7_u32));
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let reached = focus_computation(&core, computation_hole, &mut arena, &mut provenance)
        .expect("a computation hole focuses");
    let Some(&crate::il::CommandNode::Perform {
        ref signature,
        ref operation,
        route: crate::il::Route::Nearest,
        payload,
        ..
    }) = arena.command(reached)
    else {
        panic!(
            "a hole is reached as a perform: {:?}",
            arena.command(reached)
        );
    };
    assert_eq!(
        (signature.name().as_ref(), operation.as_ref()),
        (crate::il::REACHED_HOLE, crate::il::REACHED)
    );
    assert!(
        matches!(
            arena.producer(payload),
            Some(&crate::il::ProducerNode::Literal(gandr_kernel_term::Literal::Integer(ref place)))
                if place.magnitude().as_ref() == "7"
        ),
        "the payload names the hole"
    );
}

#[test]
fn a_placement_is_refused_by_name()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let placed = core.computation_session(gandr_core_term::session::SessionAction::Place {
        payload: unit,
        body: returned,
    });
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let mark = arena.watermark();
    assert_eq!(
        focus_computation(&core, placed, &mut arena, &mut provenance),
        Err(FocusRefusal::Placement(placed)),
        "the placement is refused by name"
    );
    assert_eq!(mark, arena.watermark(), "the arena is back at its mark");
}

/// A record focuses to the record head of its labels in the core's
/// canonical order, each field under its own label: two records holding
/// the same fields under swapped labels have swapped images, and the record
/// of no labels is a record, not the unit.
#[test]
fn a_record_focuses_to_its_labels_in_canonical_order()
{
    let mut core = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let first = core.value_constant(gandr_kernel_term::ConstantIndex::from(0_usize));
    let second = core.value_constant(gandr_kernel_term::ConstantIndex::from(1_usize));
    let record = core.value_record(alloc::collections::BTreeMap::from([
        (label("b"), second),
        (label("a"), first),
    ]));
    let swapped = core.value_record(alloc::collections::BTreeMap::from([
        (label("b"), first),
        (label("a"), second),
    ]));
    let empty = core.value_record(alloc::collections::BTreeMap::new());
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let mut image = |value| {
        let producer =
            focus_value(&core, value, &mut arena, &mut provenance).expect("a record focuses");
        let Some(ProducerNode::Constructor {
            tag: ConstructorTag::Record(labels),
            producers,
            consumers,
        }) = arena.producer(producer).cloned()
        else {
            panic!("a record focuses to a record head");
        };
        assert!(consumers.is_empty(), "a record carries no consumer");
        let labels: Vec<_> = labels
            .iter()
            .map(AsRef::as_ref)
            .map(alloc::string::String::from)
            .collect();
        let fields: Vec<_> = producers
            .iter()
            .map(|&field| arena.producer(field).cloned())
            .collect();
        (labels, fields)
    };
    let constant = |position: usize| {
        Some(ProducerNode::Constant(
            gandr_kernel_term::ConstantIndex::from(position),
        ))
    };
    assert_eq!(
        (
            alloc::vec![
                alloc::string::String::from("a"),
                alloc::string::String::from("b")
            ],
            alloc::vec![constant(0), constant(1)]
        ),
        image(record),
        "the fields stand in label order, each under its own label"
    );
    assert_eq!(
        (
            alloc::vec![
                alloc::string::String::from("a"),
                alloc::string::String::from("b")
            ],
            alloc::vec![constant(1), constant(0)]
        ),
        image(swapped),
        "swapping the fields' labels swaps the fields"
    );
    assert_eq!(
        (Vec::new(), Vec::new()),
        image(empty),
        "the record of no labels is a record head of none"
    );
}

/// A tuple projection and a record projection each focus to the positive
/// cut of their subject against a selection of the field they name, which
/// carries the continuation itself: a projection bound by a sequence
/// returns straight to the binder, neither named nor shifted.
#[test]
fn a_projection_selects_by_position_or_label()
{
    let mut core = CoreArena::new();
    let subject = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let label = gandr_kernel_term::FieldLabel::from(alloc::string::String::from("s"));
    let component = gandr_core_term::Component::from(2_usize);
    let rest = core.computation_return(subject);
    let projections = [
        (
            core.computation_record_projection(subject, label.clone()),
            Selector::Label(label),
        ),
        (
            core.computation_tuple_projection(subject, component),
            Selector::Component(component),
        ),
    ];
    for (projection, selector) in projections {
        let term = core.computation_bind(projection, rest);
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let root = focus_computation(&core, term, &mut arena, &mut provenance)
            .expect("a projection of a bound variable focuses");
        let Some(&crate::il::CommandNode::Cut {
            polarity,
            producer,
            consumer,
        }) = arena.command(root)
        else {
            panic!("the projection is the root cut");
        };
        assert_eq!(
            Polarity::Positive,
            polarity,
            "a selection observes positive data"
        );
        assert_eq!(
            Some(&ProducerNode::Variable {
                zone: gandr_core_term::Zone::Intuitionistic,
                index: 0_u32.into(),
            }),
            arena.producer(producer),
            "the subject is sent as it is"
        );
        let Some(&ConsumerNode::Select {
            selector: ref found,
            then,
        }) = arena.consumer(consumer)
        else {
            panic!("the subject is cut against a selection");
        };
        assert_eq!(&selector, found, "the selection names the projected field");
        assert!(
            matches!(arena.consumer(then), Some(&ConsumerNode::MuTilde { .. })),
            "the selection returns straight to the sequence's binder"
        );
        assert_eq!(Some(FocusOrigin::Projection), provenance.origin(root));
    }
}

/// Focusing threads no name supply: one term focused into two fresh
/// arenas builds identical arenas, and every covariable it mints is the
/// innermost one.
#[test]
fn focusing_mints_no_name()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let identity_body = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let identity_return = core.computation_return(identity_body);
    let identity = core.computation_lambda(identity_return);
    let thunk = core.value_thunk(identity);
    let forced = core.computation_force(thunk);
    let applied = core.computation_application(forced, unit);
    let bound = core.computation_bind(applied, returned);
    let function = core.computation_lambda(bound);
    let term = core.computation_application(function, unit);

    let focus_fresh = |core: &CoreArena| {
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let root = focus_computation(core, term, &mut arena, &mut provenance)
            .expect("a closed term focuses");
        (arena, provenance, root)
    };
    let (first, first_provenance, first_root) = focus_fresh(&core);
    let (second, second_provenance, second_root) = focus_fresh(&core);
    assert_eq!(first, second, "equal inputs build identical arenas");
    assert_eq!(
        first_provenance, second_provenance,
        "and identical provenance"
    );
    assert_eq!(first_root, second_root, "and the same root");

    let consumers = usize::from(first.consumer_count());
    for offset in 0 .. consumers {
        let id = ConsumerId::from(u32::try_from(offset).expect("a small arena"));
        if let Some(&ConsumerNode::Covariable(index)) = first.consumer(id) {
            assert_eq!(
                CovariableIndex::from(0_u32),
                index,
                "every focused covariable is the innermost one"
            );
        }
    }
}

/// Sparse command origins distinguish a gap, an endpoint and a truncated
/// suffix.
#[test]
fn provenance_lookup_distinguishes_unrecorded_commands()
{
    let mut provenance = Provenance::new();
    let first = CommandId::from(0_u32);
    let last = CommandId::from(2_u32);
    assert_eq!(None, provenance.origin(first));
    provenance.record(first, FocusOrigin::Return);
    provenance.record(last, FocusOrigin::Case);
    assert_eq!(Some(FocusOrigin::Return), provenance.origin(first));
    assert_eq!(Some(FocusOrigin::Case), provenance.origin(last));
    assert_eq!(None, provenance.origin(CommandId::from(1_u32)));
    assert_eq!(None, provenance.origin(CommandId::from(3_u32)));
    provenance.truncate_to(NodeCount::from(1_usize));
    assert_eq!(Some(FocusOrigin::Return), provenance.origin(first));
    assert_eq!(None, provenance.origin(last));
}

/// Each entry point reports the exact missing root and preserves earlier
/// translations.
#[test]
fn each_focus_entry_rolls_back_dangling_inputs()
{
    let core = CoreArena::new();
    let mut elsewhere = CoreArena::new();
    let value = elsewhere.value_unit();
    let computation = elsewhere.computation_return(value);
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let earlier = focus_computation(&elsewhere, computation, &mut arena, &mut provenance)
        .expect("closed return");
    let before = arena.clone();
    let origins = provenance.clone();
    assert_eq!(
        Err(FocusRefusal::DanglingComputation(computation)),
        focus_computation(&core, computation, &mut arena, &mut provenance)
    );
    assert_eq!(before, arena);
    assert_eq!(origins, provenance);
    assert_eq!(
        Err(FocusRefusal::DanglingValue(value)),
        focus_value(&core, value, &mut arena, &mut provenance)
    );
    assert_eq!(before, arena);
    assert_eq!(origins, provenance);
    assert_eq!(
        Err(FocusRefusal::DanglingValue(value)),
        focus_top_value(&core, value, &mut arena, &mut provenance)
    );
    assert_eq!(before, arena);
    assert_eq!(origins, provenance);
    assert_eq!(
        Err(FocusRefusal::DanglingValue(value)),
        focus_definition(&core, value, &mut arena, &mut provenance)
    );
    assert_eq!(before, arena);
    assert_eq!(origins, provenance);
    assert_eq!(Some(FocusOrigin::Return), provenance.origin(earlier));
}

/// A computed value `⟨return ()⟩` focuses to the `μ` that runs its
/// computation against the `μ`'s own covariable; the value it computes
/// focuses to itself, no `μ`.
#[test]
fn a_computed_value_focuses_to_the_capture_that_runs_it()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let computed = core.value_returned(returned);
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let capture = focus_definition(&core, computed, &mut arena, &mut provenance)
        .expect("a computed value focuses");
    let plain =
        focus_definition(&core, unit, &mut arena, &mut provenance).expect("a value focuses");
    assert_eq!(
        (
            alloc::string::String::from("μα. ⟨() |+ α0⟩"),
            alloc::string::String::from("()")
        ),
        (
            crate::pretty::render_producer(&arena, capture),
            crate::pretty::render_producer(&arena, plain)
        ),
        "the computed value runs under its capture, the value stands as itself"
    );
}

/// Both result stacks reject every non-singleton shape and pop in LIFO
/// order.
#[test]
fn result_stacks_enforce_singletons_and_lifo()
{
    let core = CoreArena::new();
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let first = arena
        .mint_producer(ProducerNode::Constant(0_usize.into()))
        .expect("leaf");
    let last = arena
        .mint_producer(ProducerNode::Constant(1_usize.into()))
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let before = arena
        .mint_cut(Polarity::Positive, first, top)
        .expect("live children");
    let after = arena
        .mint_cut(Polarity::Positive, last, top)
        .expect("live children");
    let producers = [first, last];
    let commands = [before, after];
    for producer_count in 0_usize ..= 2_usize {
        for command_count in 0_usize ..= 2_usize {
            let mut run = Focusing::new(&core, &mut arena, &mut provenance);
            run.producers
                .extend_from_slice(&producers[.. producer_count]);
            run.commands.extend_from_slice(&commands[.. command_count]);
            let expected = if producer_count == 1 && command_count == 0 {
                Ok(first)
            }
            else {
                Err(FocusRefusal::TranslationInvariant)
            };
            assert_eq!(expected, run.single_producer());
            let mut run = Focusing::new(&core, &mut arena, &mut provenance);
            run.producers
                .extend_from_slice(&producers[.. producer_count]);
            run.commands.extend_from_slice(&commands[.. command_count]);
            let expected = if command_count == 1 && producer_count == 0 {
                Ok(before)
            }
            else {
                Err(FocusRefusal::TranslationInvariant)
            };
            assert_eq!(expected, run.single_command());
        }
    }
    let mut run = Focusing::new(&core, &mut arena, &mut provenance);
    run.producers.extend_from_slice(&producers);
    run.commands.extend_from_slice(&commands);
    assert_eq!(Ok(last), run.pop_producer());
    assert_eq!(Ok(first), run.pop_producer());
    assert_eq!(Err(FocusRefusal::TranslationInvariant), run.pop_producer());
    assert_eq!(Ok(after), run.pop_command());
    assert_eq!(Ok(before), run.pop_command());
    assert_eq!(Err(FocusRefusal::TranslationInvariant), run.pop_command());
}
