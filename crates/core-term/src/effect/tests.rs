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

/// The default label of the interface named `name`.
///
/// # Specification
/// trivial.
fn label(name: Label) -> EffectLabel
{
    EffectLabel::Interface(name)
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
fn a_tail_rides_every_traversal_of_a_row()
{
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let variable = arena.value_variable(crate::Zone::Intuitionistic, 0_u32.into());
    let tail = arena.value_type_row_tail(variable);
    let other_variable = arena.value_variable(crate::Zone::Intuitionistic, 1_u32.into());
    let other_tail = arena.value_type_row_tail(other_variable);
    let state = EffectRow::singleton(signature(EffectName::from("State"), unit));
    let open = state.with_tail(Some(tail));
    assert_eq!(Some(tail), open.tail());
    assert_eq!(None, open.with_tail(None).tail(), "closing drops the tail");
    assert_eq!(
        Purity::Effectful,
        EffectRow::EMPTY.with_tail(Some(tail)).purity(),
        "a bare tail may stand for an interface"
    );
    assert_eq!(
        alloc::vec![unit, unit, tail],
        open.types().collect::<alloc::vec::Vec<_>>(),
        "the tail comes after the operations' types"
    );
    let mut forward = alloc::vec::Vec::new();
    let _unchanged = open.try_map_types(TypeOrder::Forward, |ty| {
        forward.push(ty);
        Ok::<_, ()>(ty)
    });
    assert_eq!(forward, open.types().collect::<alloc::vec::Vec<_>>());
    let mut reverse = alloc::vec::Vec::new();
    let _unchanged = open.try_map_types(TypeOrder::Reverse, |ty| {
        reverse.push(ty);
        Ok::<_, ()>(ty)
    });
    assert_eq!(
        reverse,
        open.types().rev().collect::<alloc::vec::Vec<_>>(),
        "reverse order maps the tail first"
    );
    let retailed = open.try_map_types(TypeOrder::Forward, |ty| {
        Ok::<_, ()>(if ty == tail { other_tail } else { ty })
    });
    assert_eq!(Ok(state.with_tail(Some(other_tail))), retailed);
    let relocated = open.try_relocate(|ty| Ok::<_, ()>(if ty == tail { integer } else { ty }));
    assert_eq!(
        Ok(Some(integer)),
        relocated.map(|row| row.tail()),
        "relocation carries the tail's image"
    );
    let io = EffectRow::singleton(signature(EffectName::from("IO"), unit));
    assert_eq!(
        Ok(state
            .union(&io, &arena)
            .expect("apart")
            .with_tail(Some(tail))),
        open.union(&io, &arena),
        "a join keeps the one tail"
    );
    assert_eq!(
        Err(EffectConflict::Tails),
        open.union(&io.with_tail(Some(other_tail)), &arena),
        "two different tails are refused"
    );
    assert_eq!(
        state.with_tail(Some(tail)),
        state
            .union(&io, &arena)
            .expect("apart")
            .with_tail(Some(tail))
            .without(&label("IO".into())),
        "removing an instance keeps the tail"
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
        Err(EffectConflict::Signature(label("State".into()))),
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
            .without(&label("IO".into()))
    );
    assert_eq!(state, state.without(&label("Absent".into())));
}

#[test]
fn a_join_by_identity_refuses_equal_types_minted_twice()
{
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let again = arena.value_type_unit();
    let row = arena.value_type_row();
    let state = EffectRow::singleton(signature(EffectName::from("State"), unit));
    let restated = EffectRow::singleton(signature(EffectName::from("State"), again));
    let io = EffectRow::singleton(signature(EffectName::from("IO"), unit));
    assert_eq!(
        state.union(&io, &arena),
        state.union_by_identity(&io),
        "apart rows join to their union"
    );
    assert_eq!(
        Ok(state.clone()),
        state.union_by_identity(&state),
        "a label shared at the same ids joins once"
    );
    assert_eq!(
        (
            Ok(state.clone()),
            Err(EffectConflict::Signature(label("State".into())))
        ),
        (
            state.union(&restated, &arena),
            state.union_by_identity(&restated)
        ),
        "equal types minted twice agree structurally and not by identity"
    );
    assert_eq!(
        state
            .union(&io, &arena)
            .map(|both| both.with_tail(Some(unit))),
        state.with_tail(Some(unit)).union_by_identity(&io),
        "the join is open through the one tail"
    );
    assert_eq!(
        Err(EffectConflict::Tails),
        state
            .with_tail(Some(unit))
            .union_by_identity(&io.with_tail(Some(row))),
        "two different tails are refused"
    );
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
        Err(EffectConflict::Signature(label("ListOp".into()))),
        first.union(&changed, &arena)
    );
}

#[test]
fn a_signature_includes_another_only_at_one_name_and_one_operation_table()
{
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let list = arena.value_type_list(unit);
    let operation = |name, payload, reply| EffectOp {
        name: OperationName::from(name),
        payload,
        reply,
    };
    let probe = |operations: alloc::vec::Vec<EffectOp>| {
        EffectSig::new(EffectName::from("Probe"), operations).expect("distinct operations")
    };
    let base = probe(alloc::vec![operation("run", unit, unit)]);
    for (other, what) in [
        (
            probe(alloc::vec![
                operation("run", unit, unit),
                operation("stop", unit, unit)
            ]),
            "one more operation",
        ),
        (
            probe(alloc::vec![operation("stop", unit, unit)]),
            "another operation name",
        ),
        (
            probe(alloc::vec![operation("run", list, unit)]),
            "another payload",
        ),
        (
            probe(alloc::vec![operation("run", unit, list)]),
            "another reply",
        ),
    ] {
        assert_eq!(
            RowInclusion::Excluded,
            base.inclusion(&other, &arena),
            "{what} excludes"
        );
    }
    let row = EffectRow::singleton(signature(EffectName::from("A"), unit))
        .union(
            &EffectRow::singleton(signature(EffectName::from("B"), unit)),
            &arena,
        )
        .expect("two interfaces");
    assert_eq!(
        "⟨A, B⟩",
        alloc::format!("{row:?}"),
        "names are separated, not prefixed"
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
        Err(EffectConflict::Signature(label("State".into())))
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

#[test]
fn the_row_operations_are_the_set_arithmetic_of_their_names()
{
    use alloc::collections::BTreeSet;

    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let names = ["A", "B", "C"].map(EffectName::from);
    let subsets = names.iter().fold(
        alloc::vec![BTreeSet::<EffectName>::new()],
        |subsets, name| {
            subsets
                .iter()
                .flat_map(|subset| {
                    let mut grown = subset.clone();
                    let _added = grown.insert(name.clone());
                    [subset.clone(), grown]
                })
                .collect()
        },
    );
    let rows: alloc::vec::Vec<(BTreeSet<EffectName>, EffectRow)> = subsets
        .into_iter()
        .map(|subset| {
            let row =
                EffectRow::from_signatures(subset.iter().map(|name| signature(name.clone(), unit)))
                    .unwrap();
            (subset, row)
        })
        .collect();
    let named = |row: &EffectRow| {
        row.signatures()
            .map(|held| held.name().clone())
            .collect::<BTreeSet<_>>()
    };
    let apart = EffectName::from("B");
    let disagreeing = EffectRow::singleton(signature(apart.clone(), integer));
    for (left_names, left) in rows.iter().map(|held| (&held.0, &held.1)) {
        for name in &names {
            let removed = left.without(&label(name.as_ref().into()));
            assert!(
                named(&removed)
                    .iter()
                    .eq(left_names.iter().filter(|held| *held != name)),
                "{left:?} without {name:?}"
            );
            let present = if left_names.contains(name) {
                EffectPresence::Present
            }
            else {
                EffectPresence::Absent
            };
            assert_eq!(
                left.contains(&label(name.as_ref().into())),
                present,
                "{name:?} in {left:?}"
            );
        }
        for (right_names, right) in rows.iter().map(|held| (&held.0, &held.1)) {
            let joined = left.union(right, &arena).unwrap();
            assert_eq!(
                named(&joined),
                left_names | right_names,
                "{left:?} with {right:?}"
            );
            let included = if left_names.is_subset(right_names) {
                RowInclusion::Included
            }
            else {
                RowInclusion::Excluded
            };
            assert_eq!(
                left.is_subset(right, &arena),
                included,
                "{left:?} in {right:?}"
            );
        }
        let refused = if left_names.contains(&apart) {
            Err(EffectConflict::Signature(label(apart.as_ref().into())))
        }
        else {
            Ok(())
        };
        assert_eq!(
            left.union(&disagreeing, &arena).map(|_| ()),
            refused,
            "{left:?} with a `B` of another signature"
        );
        let empty = if left_names.is_empty() {
            RowInclusion::Included
        }
        else {
            RowInclusion::Excluded
        };
        assert_eq!(
            left.is_subset(&disagreeing, &arena),
            empty,
            "{left:?} in a `B` of another signature"
        );
    }
}

#[test]
fn an_instance_is_apart_from_its_interface_and_from_another_region()
{
    use crate::effect::capability::RegionBinder;
    use crate::effect::capability::RegionDepth;
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let name = EffectName::from("Console");
    let console = signature(name.clone(), unit);
    let scope = Region::Scoped(RegionDepth::from(1_u32));
    let bound = Region::Bound(RegionBinder::from(0_u32));
    assert_eq!(
        label("Console".into()),
        EffectLabel::at(&name, Region::Held)
    );
    assert_eq!(scope, EffectLabel::at(&name, scope).region());
    assert_eq!(Region::Held, label("Console".into()).region());
    let default = EffectRow::singleton(console.clone());
    assert_eq!(
        default,
        EffectRow::instance(console.clone(), Region::Held),
        "the held instance is the interface's default"
    );
    let scoped = EffectRow::instance(console.clone(), scope);
    let abstracted = EffectRow::instance(console.clone(), bound);
    assert_eq!(RowInclusion::Excluded, scoped.is_subset(&default, &arena));
    assert_eq!(RowInclusion::Excluded, default.is_subset(&scoped, &arena));
    assert_eq!(
        RowInclusion::Excluded,
        scoped.is_subset(&abstracted, &arena)
    );
    let all = default
        .union(&scoped, &arena)
        .and_then(|row| row.union(&abstracted, &arena))
        .expect("three instances apart");
    assert_eq!(3, all.instances().len());
    assert_eq!(
        alloc::vec![scope, bound],
        all.regions().collect::<alloc::vec::Vec<_>>()
    );
    assert_eq!(RowInclusion::Included, scoped.is_subset(&all, &arena));
    assert_eq!(
        default.union(&abstracted, &arena).expect("apart"),
        all.without(&EffectLabel::at(&name, scope)),
        "discharging one instance keeps the others"
    );
    assert_eq!(
        default.union(&scoped, &arena),
        EffectRow::from_placed([(console.clone(), Region::Held), (console.clone(), scope)])
    );
    assert_eq!(
        Err(EffectConflict::Signature(EffectLabel::at(&name, scope))),
        EffectRow::from_placed([(console.clone(), scope), (console, scope)])
    );
}

#[test]
fn renaming_an_instance_region_moves_its_label()
{
    use crate::effect::capability::RegionBinder;
    use crate::effect::capability::RegionDepth;
    let mut arena = crate::CoreArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let name = EffectName::from("Console");
    let console = signature(name.clone(), unit);
    let first = Region::Bound(RegionBinder::from(0_u32));
    let second = Region::Bound(RegionBinder::from(1_u32));
    let outer = Region::Scoped(RegionDepth::from(1_u32));
    let inner = Region::Scoped(RegionDepth::from(2_u32));
    let row = EffectRow::from_placed([
        (console.clone(), Region::Held),
        (console.clone(), first),
        (console.clone(), second),
    ])
    .expect("three instances apart");
    let placing = |to_first: Region, to_second: Region| {
        move |region: Region| {
            if region == first {
                to_first
            }
            else if region == second {
                to_second
            }
            else {
                region
            }
        }
    };
    assert_eq!(
        EffectRow::from_placed([
            (console.clone(), Region::Held),
            (console.clone(), outer),
            (console.clone(), inner),
        ]),
        row.try_map_regions(placing(outer, inner)),
        "each bound instance moves to its scope"
    );
    assert_eq!(
        EffectRow::from_placed([(console.clone(), Region::Held), (console.clone(), inner)]),
        row.try_map_regions(placing(Region::Held, inner)),
        "an instance placed at the held region is the default"
    );
    assert_eq!(
        EffectRow::from_placed([(console.clone(), Region::Held), (console.clone(), outer)]),
        row.try_map_regions(placing(outer, outer)),
        "two instances placed at one region are one"
    );
    assert_eq!(Ok(row.clone()), row.try_map_regions(|region| region));
    let variable = arena.value_variable(crate::Zone::Intuitionistic, 0_u32.into());
    let tail = arena.value_type_row_tail(variable);
    assert_eq!(
        Ok(Some(tail)),
        row.with_tail(Some(tail))
            .try_map_regions(placing(outer, inner))
            .map(|moved| moved.tail()),
        "the tail rides the renaming"
    );
    let other =
        EffectRow::from_placed([(console, first), (signature(name.clone(), integer), second)])
            .expect("two instances apart");
    assert_eq!(
        Err(EffectConflict::Signature(EffectLabel::at(&name, outer))),
        other.try_map_regions(placing(outer, outer)),
        "two signatures cannot meet at one instance"
    );
}
