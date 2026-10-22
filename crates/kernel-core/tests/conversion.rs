//! Codes compared by the structural conversion walk: a code built by a former
//! over one constant converts with a second copy of itself and stays apart
//! from its twin over another constant.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_kernel_core::Convertibility;
use gandr_kernel_core::convertible_value_types;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

/// A code former, holding the constant it is given at one leaf.
struct Former
{
    /// The code, over the constant `c`.
    what: &'static str,
    /// Builds the code over the constant it is given.
    build: fn(&mut TermArena, ValueId) -> ValueId,
}

/// The decoded type `El code`, the code kept as written.
///
/// # Specification
/// trivial.
fn decoded(
    arena: &mut TermArena,
    code: ValueId,
) -> ValueTypeId
{
    arena.value_type_element(code, Level::zero())
}

/// `F 1`.
///
/// # Specification
/// trivial.
fn returns_unit(arena: &mut TermArena) -> gandr_kernel_term::CompTypeId
{
    let unit = arena.value_type_unit();
    arena.comp_type_returner(unit)
}

/// `thunk (return ())`.
///
/// # Specification
/// trivial.
fn done(arena: &mut TermArena) -> gandr_kernel_term::ComputationId
{
    let unit = arena.value_unit();
    arena.computation_return(unit)
}

/// The formers, each over the constant `c` at one leaf.
///
/// # Specification
/// trivial.
fn formers() -> Vec<Former>
{
    Vec::from([
        Former {
            what: "#{a = c}",
            build: |a, c| {
                a.value_record(BTreeMap::from([(FieldLabel::from(String::from("a")), c)]))
            },
        },
        Former {
            what: "c ⊗ c",
            build: |a, c| a.value_path_product(c, c),
        },
        Former {
            what: "c ⊗~ c",
            build: |a, c| a.value_flow_product(c, c),
        },
        Former {
            what: "c :: nil",
            build: |a, c| {
                let nil = a.value_list_nil();
                a.value_list_cons(c, nil)
            },
        },
        Former {
            what: "c c, statically applied",
            build: |a, c| a.value_static_application(c, c),
        },
        Former {
            what: "refl c",
            build: |a, c| a.value_path_refl(c),
        },
        Former {
            what: "here c",
            build: |a, c| a.value_here(c),
        },
        Former {
            what: "stay c",
            build: |a, c| a.value_stay(c),
        },
        Former {
            what: "thunk (case c of { () ↦ return () })",
            build: |a, c| {
                let arm = done(a);
                let motive = returns_unit(a);
                let case = a.computation_data_case(c, motive, Vec::from([arm]));
                a.value_thunk(case)
            },
        },
        Former {
            what: "thunk (split c as (_, _) in return ())",
            build: |a, c| {
                let body = done(a);
                let motive = returns_unit(a);
                let split = a.computation_sigma_split(c, motive, body);
                a.value_thunk(split)
            },
        },
        Former {
            what: "thunk (c.a)",
            build: |a, c| {
                let projected =
                    a.computation_record_projection(c, FieldLabel::from(String::from("a")));
                a.value_thunk(projected)
            },
        },
        Former {
            what: "thunk (c.0)",
            build: |a, c| {
                let projected = a.computation_tuple_projection(c, Component::from(0_usize));
                a.value_thunk(projected)
            },
        },
        Former {
            what: "thunk (fold c { nil ↦ return (); _ :: _ ↦ return () })",
            build: |a, c| {
                let (on_nil, on_cons) = (done(a), done(a));
                let one = a.value_type_unit();
                let fold = a.computation_list_fold(one, one, c, on_nil, on_cons);
                a.value_thunk(fold)
            },
        },
        Former {
            what: "thunk (case c of { nil ↦ return (); _ :: _ ↦ return () })",
            build: |a, c| {
                let (on_nil, on_cons) = (done(a), done(a));
                let case = a.computation_list_case(c, on_nil, on_cons);
                a.value_thunk(case)
            },
        },
        Former {
            what: "thunk (transport (y. 1) along c of ())",
            build: |a, c| {
                let one = a.value_type_unit();
                let unit = a.value_unit();
                let transported = a.computation_path_transport(one, c, unit);
                a.value_thunk(transported)
            },
        },
        Former {
            what: "thunk (ride (y. 1) c ())",
            build: |a, c| {
                let one = a.value_type_unit();
                let unit = a.value_unit();
                let ridden = a.computation_ride(one, c, unit);
                a.value_thunk(ridden)
            },
        },
    ])
}

/// Each former's code over `c` converts with a second copy of itself, built
/// at fresh ids, and is apart from its twin over `d`: the walk descends into
/// every child the former holds.
#[test]
fn each_code_former_converts_with_its_copy_and_not_with_its_twin()
{
    for Former { what, build } in formers() {
        let mut arena = TermArena::new();
        let c = arena.value_constant(ConstantIndex::from(0_usize));
        let d = arena.value_constant(ConstantIndex::from(1_usize));
        let [one, copy, twin] = [c, c, d].map(|leaf| {
            let code = build(&mut arena, leaf);
            decoded(&mut arena, code)
        });
        assert_eq!(
            Convertibility::Convertible,
            convertible_value_types(&arena, one, copy),
            "{what}: copies"
        );
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, one, twin),
            "{what}: twins"
        );
    }
}
