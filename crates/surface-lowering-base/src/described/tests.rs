//! The substitution a described law reads its sides through. The cases that
//! lower a source and read its described types are in this crate's
//! integration target, `tests::described`.

use alloc::collections::BTreeMap;

use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;

/// Substitution rebuilds every node kind a rule term holds and replaces
/// only the variables the map names, keeping the rest and every atom.
#[test]
fn substitution_rebuilds_every_node_and_replaces_only_mapped_variables()
{
    let written = |x: &str| {
        FreeTerm::op("f", [
            FreeTerm::ctor("C", [FreeTerm::var(x), FreeTerm::var("y")]),
            FreeTerm::results([FreeTerm::var(x)]),
            FreeTerm::inst("t", [FreeTerm::var(x)]),
            FreeTerm::abs(
                "a",
                FreeTerm::op("g", [FreeTerm::var(x), FreeTerm::var("a")]),
            ),
        ])
    };
    let x = Name::from("x");
    let by = BTreeMap::from([(&x, FreeTerm::var("z"))]);
    assert!(
        super::substitute(&written("x"), &by) == written("z"),
        "every `x` under every node kind reads `z`; `y` and the atom stay"
    );
    assert!(
        super::substitute(&written("x"), &BTreeMap::new()) == written("x"),
        "an empty map leaves the term as written"
    );
}
