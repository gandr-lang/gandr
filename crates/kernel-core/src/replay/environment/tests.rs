//! Witnesses for the replay's environments: a variable bound to a variable
//! reads its binder's value through one alias.

use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;

use super::CellIndex;
use super::Closure;
use super::Environment;
use super::Environments;
use super::Held;

/// How many variables the chain binds after its first cell.
const LINKS: u32 = 64;

#[test]
fn a_chain_of_variables_aliases_the_cell_that_holds_its_value()
{
    let mut arena = TermArena::new();
    let innermost = arena.value_variable(DeBruijnIndex::from(0_u32));
    let unit = arena.value_unit();
    let open = arena.value_variable(DeBruijnIndex::from(3_u32));
    for start in [unit, open] {
        let mut cells = Environments::default();
        let mut environment = cells.push(&arena, Environment::EMPTY, Closure::closed(start));
        for _link in 0 .. LINKS {
            environment = cells.push(&arena, environment, Closure {
                node: innermost,
                environment,
            });
        }
        assert_eq!(
            cells.cells.first().map(|cell| cell.held),
            Some(Held::Value(Closure::closed(start))),
            "the first cell holds the value, a variable of the handed context too"
        );
        assert!(
            cells
                .cells
                .iter()
                .skip(1)
                .all(|cell| cell.held == Held::Alias(CellIndex(0))),
            "every link aliases the first cell, never the link before it"
        );
        for depth in 0 ..= LINKS {
            let variable = arena.value_variable(DeBruijnIndex::from(depth));
            assert_eq!(
                cells.resolve(&arena, Closure {
                    node: variable,
                    environment,
                }),
                Closure::closed(start),
                "the variable {depth} binders out reads the first cell's value"
            );
        }
    }
}
