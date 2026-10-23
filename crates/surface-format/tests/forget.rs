//! The forgetting maps the explicit form writes beside a checker (#2130): a
//! crossing by a map onto the theory it forgets, at carriers the checker
//! quotes, and no other.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Crossing;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_format::forgettings;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::Forgetting as Minted;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::coincide::Decisions;
use gandr_surface_lowering::lower_unit;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::Forgetting;
use gandr_surface_pretty::Name;
use gandr_surface_syntax::SourceText;

/// A counter over the integers, a pairing with both its carriers manifest,
/// and a monoid over the integers, whose sort set also takes the map onto
/// the semigroup it includes.
const SOURCE: &str = "theory Counter {
  sort C : Type;
  oper zero : () --> C;
}

theory Pairing {
  sort A : Type;
  sort B : Type;
  oper first : () --> A;
  oper second : () --> B;
}

theory Semigroup {
  sort M : Type;
  oper mul : (x : M, y : M) --> M;
}

theory Monoid {
  include Semigroup;
  oper one : () --> M;
}

def counted(m : Model(Counter) with sort C = Integer) -> -F Integer { return 0 }

def paired(p : Model(Pairing) with sort A = Integer with sort B = Unit) -> -F Integer { return 0 }

def monoidal(m : Model(Monoid) with sort M = Integer) -> -F Integer { return 0 }
";

/// #2130: of the checker's crossings, the explicit form writes those by a
/// map onto the theory it forgets whose every carrier is a quoted type, each
/// sort beside its carrier in the map's order; a carrier that is no quote, a
/// map that a reduct carries further and a constant that is no forgetting map
/// are left to the checker.
#[test]
fn a_forgetting_map_is_written_only_at_quoted_carriers_onto_its_own_theory_2130()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let parsed = parse(&grammar, SourceText::from(SOURCE)).expect("the source parses");
    let unit = Unit::single();
    let mut arena = CoreArena::new();
    let module = lower_unit(
        &grammar,
        parsed.tree(),
        &unit,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the source lowers");
    let minted = |sorts: &[&str], own: bool| -> &Minted {
        module
            .forgettings()
            .iter()
            .find(|map| {
                (map.onto == map.theory) == own
                    && map
                        .sorts
                        .iter()
                        .map(AsRef::as_ref)
                        .eq(sorts.iter().copied())
            })
            .expect("the unit mints the map")
    };
    let (counter, pairing) = (minted(&["C"], true), minted(&["A", "B"], true));
    let composite = minted(&["M"], false);
    let unit_type = arena.value_type_unit();
    let unit_twice = arena.value_type_sum(&[unit_type, unit_type]);
    let (quoted_unit, quoted_twice) = (arena.value_quote(unit_type), arena.value_quote(unit_twice));
    let mut crossed = (0_usize ..).map(|index| arena.value_constant(ConstantIndex::from(index)));
    let mut crossed = || crossed.next().expect("the constants never run out");
    let (written, both, unquoted, restricted, unmapped) =
        (crossed(), crossed(), crossed(), crossed(), crossed());
    let crossings: BTreeMap<_, _> = [
        (written, counter.map, vec![quoted_unit]),
        (both, pairing.map, vec![quoted_unit, quoted_twice]),
        (unquoted, counter.map, vec![written]),
        (restricted, composite.map, vec![quoted_unit]),
        (unmapped, counter.theory, vec![quoted_unit]),
    ]
    .into_iter()
    .map(|(value, by, carriers)| (value, Crossing { by, carriers }))
    .collect();
    let expected: BTreeMap<_, _> = [
        (written, Forgetting {
            theory: counter.theory,
            sorts: vec![(Name::from("C"), CoreNode::ValueType(unit_type))],
        }),
        (both, Forgetting {
            theory: pairing.theory,
            sorts: vec![
                (Name::from("A"), CoreNode::ValueType(unit_type)),
                (Name::from("B"), CoreNode::ValueType(unit_twice)),
            ],
        }),
    ]
    .into_iter()
    .collect();
    assert_eq!(
        forgettings(&module, &arena, &crossings),
        expected.into_iter().collect::<Vec<_>>(),
        "only the maps onto their own theory at quoted carriers are written, ascending"
    );
}
