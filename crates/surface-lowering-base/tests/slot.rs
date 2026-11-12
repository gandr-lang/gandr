//! The role of each slot a module's lowering fills, read through the
//! production lowering route of `gandr-surface-lowering`.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering_base::fixture::grammar;
use gandr_surface_lowering_base::fixture::parsed;
use gandr_surface_lowering_base::namespace::Recognition;
use gandr_surface_lowering_base::slot::Role;
use gandr_surface_syntax::SourceText;

/// The name and the role of each declaration `text` lowers to, in order.
///
/// # Specification
/// trivial.
fn roles(text: &str) -> Vec<(String, Role)>
{
    let grammar = grammar();
    let tree = parsed(&grammar, SourceText::from(text));
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    module
        .declarations()
        .iter()
        .map(|declaration| {
            (
                String::from(declaration.name().as_ref()),
                declaration.role(),
            )
        })
        .collect()
}

/// A member's written signature declares it and its derived type is a
/// witness; an opaque ascription's abstract component is declared before the
/// members it seals.
#[test]
fn each_slot_is_read_with_its_role()
{
    let named = |name: &str, role| (String::from(name), role);
    assert_eq!(
        roles(
            "module M where { def f : +U (Integer -> -F Integer); def f(x : Integer) -> -F \
             Integer { return x } }"
        ),
        [named("f", Role::Declared), named("f", Role::Witness)]
    );
    assert_eq!(
        roles(
            "module Counter :> *{type T, seed : T} where { type T = Integer; def seed = 7; }\ndef \
             held : Counter.T = Counter.seed;\ndef n : Integer = Counter.seed;\n"
        ),
        [
            named("T", Role::Abstract),
            named("seed", Role::Declared),
            named("held", Role::Declared),
            named("n", Role::Declared),
        ]
    );
}
