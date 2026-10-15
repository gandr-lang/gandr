use super::*;

/// Build one nullary operation for the row laws.
///
/// # Specification
/// trivial.
fn signature(
    name: EffectName,
    payload: ValueTypeId,
) -> EffectSig
{
    EffectSig::new(name, alloc::vec![EffectOp {
        name: OperationName::from("run"),
        payload,
        reply: payload
    }])
    .unwrap()
}

#[test]
fn empty_is_the_bottom()
{
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let row = EffectRow::singleton(signature(EffectName::from("State"), unit));
    assert_eq!(Purity::Pure, EffectRow::<ValueTypeId>::EMPTY.purity());
    assert_eq!(Purity::Effectful, row.purity());
    assert_eq!(
        RowInclusion::Included,
        EffectRow::EMPTY.is_subset(&row, &arena)
    );
    assert_eq!(
        RowInclusion::Included,
        EffectRow::EMPTY.is_subset(&EffectRow::EMPTY, &arena)
    );
}

#[test]
fn subset_is_a_preorder_with_union_as_join()
{
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let state = EffectRow::singleton(signature(EffectName::from("State"), unit));
    let io = EffectRow::singleton(signature(EffectName::from("IO"), unit));
    let joined = state.union(&io, &arena).unwrap();
    assert_eq!(RowInclusion::Included, state.is_subset(&state, &arena));
    assert_eq!(RowInclusion::Included, state.is_subset(&joined, &arena));
    assert_eq!(RowInclusion::Included, io.is_subset(&joined, &arena));
    assert_eq!(RowInclusion::Excluded, joined.is_subset(&state, &arena));
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let conflicting = EffectRow::singleton(signature(EffectName::from("State"), integer));
    assert_eq!(
        RowInclusion::Excluded,
        state.is_subset(&conflicting, &arena)
    );
    assert_eq!(
        Err(EffectConflict::Signature(EffectName::from("State"))),
        state.union(&conflicting, &arena)
    );
}

#[test]
fn union_is_a_canonical_set_and_without_subtracts()
{
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let state = EffectRow::singleton(signature(EffectName::from("State"), unit));
    let io = EffectRow::singleton(signature(EffectName::from("IO"), unit));
    assert_eq!(state.union(&io, &arena), io.union(&state, &arena));
    assert_eq!(Ok(state.clone()), state.union(&state, &arena));
    assert_eq!(
        state,
        state
            .union(&io, &arena)
            .unwrap()
            .without(&EffectName::from("IO"))
    );
    assert_eq!(state, state.without(&EffectName::from("Absent")));
}

#[test]
fn signature_resolves_operations_by_name()
{
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let get = EffectOp {
        name: OperationName::from("get"),
        payload: unit,
        reply: integer,
    };
    let put = EffectOp {
        name: OperationName::from("put"),
        payload: integer,
        reply: unit,
    };
    let state = EffectSig::new(EffectName::from("State"), alloc::vec![
        put.clone(),
        get.clone()
    ])
    .unwrap();
    assert_eq!(Maybe::Present(&get), state.operation(&get.name));
    assert_eq!(Maybe::Present(&put), state.operation(&put.name));
    assert_eq!(
        Maybe::Absent(UnknownOperation),
        state.operation(&OperationName::from("absent"))
    );
    assert_eq!(
        Err(EffectConflict::DuplicateOperation(get.name.clone())),
        EffectSig::new(EffectName::from("State"), alloc::vec![get.clone(), get])
    );
}

#[test]
fn signature_inclusion_ignores_allocation_identity()
{
    let mut arena = crate::CoreArena::new();
    let first_unit = arena.value_type_unit();
    let second_unit = arena.value_type_unit();
    let first_list = arena.value_type_list(first_unit);
    let second_list = arena.value_type_list(second_unit);
    let first = EffectRow::singleton(signature(EffectName::from("ListOp"), first_list));
    let second = EffectRow::singleton(signature(EffectName::from("ListOp"), second_list));
    assert_eq!(RowInclusion::Included, first.is_subset(&second, &arena));
    assert_eq!(RowInclusion::Included, second.is_subset(&first, &arena));
    assert_eq!(Ok(first.clone()), first.union(&second, &arena));
    let first_returner = arena.comp_type_returner_with_effects(first_list, first.clone());
    let second_returner = arena.comp_type_returner_with_effects(second_list, second);
    let first_thunk = arena.value_type_thunk(first_returner);
    let second_thunk = arena.value_type_thunk(second_returner);
    assert_eq!(
        RowInclusion::Included,
        signature(EffectName::from("ThunkOp"), first_thunk).inclusion(
            &signature(EffectName::from("ThunkOp"), second_thunk),
            &arena
        )
    );
    let changed = EffectRow::singleton(
        EffectSig::new(EffectName::from("ListOp"), alloc::vec![EffectOp {
            name: OperationName::from("run"),
            payload: second_list,
            reply: second_unit,
        }])
        .unwrap(),
    );
    assert_eq!(RowInclusion::Excluded, first.is_subset(&changed, &arena));
    assert_eq!(
        Err(EffectConflict::Signature(EffectName::from("ListOp"))),
        first.union(&changed, &arena)
    );
}

#[test]
fn operation_types_survive_substitution_and_import()
{
    let mut source = crate::CoreArena::new();
    let unit = source.value_type_unit();
    let variable = source.value_variable(
        crate::Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(0_u32),
    );
    let parameter = source.value_type_element(variable, gandr_kernel_strata::Level::zero());
    let list = source.value_type_list(parameter);
    let get = OperationName::from("get");
    let put = OperationName::from("put");
    let row = EffectRow::singleton(
        EffectSig::new(EffectName::from("State"), alloc::vec![
            EffectOp {
                name: get.clone(),
                payload: unit,
                reply: list
            },
            EffectOp {
                name: put.clone(),
                payload: list,
                reply: unit
            },
        ])
        .unwrap(),
    );
    let open = source.comp_type_returner_with_effects(unit, row);
    let quote = source.value_quote(unit);
    let closed = crate::instantiate_comp_type(&mut source, open, quote);
    let thunk = source.value_type_thunk(closed);
    let mut target = crate::CoreArena::new();
    let _occupied = target.value_type_base(gandr_kernel_term::BaseType::String);
    let imported = crate::TypeImporter::new(&source, &mut target)
        .value_type(thunk)
        .unwrap();
    let Some(&crate::ValueType::Thunk(body)) = target.value_type(imported)
    else {
        panic!("thunk");
    };
    let Some(&crate::CompType::Returner {
        result,
        ref effects,
    }) = target.comp_type(body)
    else {
        panic!("returner");
    };
    assert_eq!(Some(&crate::ValueType::unit()), target.value_type(result));
    let signature = effects.signatures().next().unwrap();
    let Maybe::Present(get) = signature.operation(&get)
    else {
        panic!("get");
    };
    let Maybe::Present(put) = signature.operation(&put)
    else {
        panic!("put");
    };
    assert_eq!((get.payload, get.reply), (put.reply, put.payload));
    assert_eq!(
        Some(&crate::ValueType::unit()),
        target.value_type(get.payload)
    );
    let Some(&crate::ValueType::List(element)) = target.value_type(get.reply)
    else {
        panic!("list");
    };
    assert_eq!(Some(&crate::ValueType::unit()), target.value_type(element));
    let crate::CompType::Returner { ref effects, .. } = *source.comp_type(open).unwrap()
    else {
        panic!("original returner");
    };
    let original = effects.signatures().next().unwrap();
    let Maybe::Present(original_get) = original.operation(&OperationName::from("get"))
    else {
        panic!("original get");
    };
    assert_eq!(list, original_get.reply);
    assert!(matches!(
        source.value_type(parameter),
        Some(crate::ValueType::Element { .. })
    ));
}

#[test]
fn relocation_keeps_names_and_refuses_duplicate_interfaces()
{
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let state = EffectSig::new(EffectName::from("State"), alloc::vec![
        EffectOp {
            name: OperationName::from("put"),
            payload: integer,
            reply: unit,
        },
        EffectOp {
            name: OperationName::from("get"),
            payload: unit,
            reply: integer,
        },
    ])
    .unwrap();
    let mut visited = alloc::vec::Vec::new();
    let relocated = state
        .try_relocate(|id| {
            visited.push(id);
            Ok::<_, ValueTypeId>(id)
        })
        .unwrap();
    assert_eq!(visited, [unit, integer, integer, unit]);
    assert_eq!(relocated, state);
    assert_eq!(
        state.try_relocate(|id| if id == integer { Err(id) } else { Ok(id) }),
        Err(integer)
    );
    let row = EffectRow::singleton(state.clone());
    assert_eq!(row.try_relocate(Ok::<_, ValueTypeId>), Ok(row.clone()));
    assert_eq!(
        EffectRow::<ValueTypeId>::EMPTY.try_relocate(Ok::<_, ValueTypeId>),
        Ok(EffectRow::EMPTY)
    );
    let io = signature(EffectName::from("IO"), unit);
    assert_eq!(
        EffectRow::from_signatures([state.clone(), state.clone()]),
        Err(EffectConflict::Signature(EffectName::from("State")))
    );
    assert_eq!(
        EffectRow::from_signatures([io.clone(), state]),
        row.union(&EffectRow::singleton(io), &arena)
    );
    assert_eq!(
        EffectRow::<ValueTypeId>::from_signatures([]),
        Ok(EffectRow::EMPTY)
    );
}
