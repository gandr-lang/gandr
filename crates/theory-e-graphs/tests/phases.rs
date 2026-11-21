//! Saturation: the read, apply and rebuild phases of each round.

use alloc::vec::Vec;

use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_coherent_resolutions::Variable;
use gandr_theory_e_graphs::Budget;
use gandr_theory_e_graphs::Count;
use gandr_theory_e_graphs::EGraph;
use gandr_theory_e_graphs::Outcome;

use crate::fixtures::Names;
use crate::fixtures::classes;
use crate::fixtures::op;
use crate::fixtures::var;

/// The operations of the naturals: zero, the successor and addition.
const NAT: Names = Names(&["z", "s", "add"]);

/// A rule of the naturals with addition.
#[derive(Clone, Copy, Debug)]
enum Rule
{
    /// `add(z, x) = x`.
    Unit,
    /// `add(s(x), y) = s(add(x, y))`.
    Step,
}

/// The naturals with addition by its two rules, stated in `order`, and three
/// terms that each normalize to three.
///
/// # Specification
/// trivial.
fn naturals(order: &[Rule]) -> EGraph
{
    let (zero, successor, add) = (0, 1, 2);
    let mut table = TermTable::default();
    let x = var(&mut table, Variable::from(0));
    let y = var(&mut table, Variable::from(1));
    let z = op(&mut table, Operation::from(zero), &[]);
    let one = op(&mut table, Operation::from(successor), &[z]);
    let two = op(&mut table, Operation::from(successor), &[one]);
    let three = op(&mut table, Operation::from(successor), &[two]);
    let sx = op(&mut table, Operation::from(successor), &[x]);
    let unit = op(&mut table, Operation::from(add), &[z, x]);
    let step = op(&mut table, Operation::from(add), &[sx, y]);
    let inner = op(&mut table, Operation::from(add), &[x, y]);
    let stepped = op(&mut table, Operation::from(successor), &[inner]);
    let seeds = [
        op(&mut table, Operation::from(add), &[two, one]),
        op(&mut table, Operation::from(add), &[one, two]),
        three,
    ];
    let mut graph = EGraph::new(table, ());
    for seed in seeds {
        let _class = graph.add(seed).expect("a table term");
    }
    for &rule in order {
        let (left, right) = match rule {
            Rule::Unit => (unit, x),
            Rule::Step => (step, stepped),
        };
        let _place = graph.equation(left, right).expect("a rule of the naturals");
    }
    graph
}

#[test]
fn two_orders_of_the_equations_give_the_same_classes()
{
    // egg, § 3.3: a round reads every match before it applies one, so a cut
    // after any round gives one set of classes in either order.
    for rounds in [1_usize, 2, 16] {
        let budget = Budget {
            rounds: Count::from(rounds),
            nodes: Count::from(1_000_usize),
        };
        let mut found = Vec::new();
        for order in [[Rule::Unit, Rule::Step], [Rule::Step, Rule::Unit]] {
            let mut graph = naturals(&order);
            let run = graph.saturate(budget).expect("a saturation");
            found.push((run.outcome, classes(&graph, NAT)));
        }
        assert_eq!(found[0], found[1], "{rounds} rounds");
        let expected = if rounds == 16 {
            Outcome::Saturated
        }
        else {
            Outcome::Exhausted
        };
        assert_eq!(found[0].0, expected, "{rounds} rounds");
    }
    let mut graph = naturals(&[Rule::Unit, Rule::Step]);
    let _run = graph
        .saturate(Budget {
            rounds: Count::from(16_usize),
            nodes: Count::from(1_000_usize),
        })
        .expect("a saturation");
    let three = classes(&graph, NAT)
        .into_iter()
        .find(|class| class.contains("s(s(s(z)))"))
        .expect("the class of three");
    for sum in ["add(s(s(z)),s(z))", "add(s(z),s(s(z)))"] {
        assert!(three.contains(sum), "{sum} is three");
    }
}

#[test]
fn a_saturation_that_grows_stops_at_its_budget()
{
    // `f(x) = f(s(x))` makes a new class each round: `s(a)`, then `s(s(a))`.
    let (a, f, s) = (0, 1, 2);
    let mut table = TermTable::default();
    let x = var(&mut table, Variable::from(0));
    let start = op(&mut table, Operation::from(a), &[]);
    let fa = op(&mut table, Operation::from(f), &[start]);
    let fx = op(&mut table, Operation::from(f), &[x]);
    let sx = op(&mut table, Operation::from(s), &[x]);
    let fsx = op(&mut table, Operation::from(f), &[sx]);
    let mut graph = EGraph::new(table, ());
    let _class = graph.add(fa).expect("a table term");
    let _place = graph.equation(fx, fsx).expect("an open equation");
    let mut small = graph.clone();
    let run = graph
        .saturate(Budget {
            rounds: Count::from(3_usize),
            nodes: Count::from(1_000_usize),
        })
        .expect("a saturation");
    assert_eq!(run.outcome, Outcome::Exhausted);
    assert_eq!(run.rounds, Count::from(3_usize));
    let run = small
        .saturate(Budget {
            rounds: Count::from(100_usize),
            nodes: Count::from(6_usize),
        })
        .expect("a saturation");
    assert_eq!(
        run.outcome,
        Outcome::Exhausted,
        "the budget of nodes stops it"
    );
}

#[test]
fn a_class_that_holds_its_own_image_saturates()
{
    // `f(x) = f(f(x))` puts `f(f(a))` in the class of `f(a)`. The class then
    // holds `f` of itself, so it stands for every `f(…(a))`, and the next
    // match binds `x` to that class again.
    let mut table = TermTable::default();
    let x = var(&mut table, Variable::from(0));
    let a = op(&mut table, Operation::from(0), &[]);
    let fa = op(&mut table, Operation::from(1), &[a]);
    let ffa = op(&mut table, Operation::from(1), &[fa]);
    let fx = op(&mut table, Operation::from(1), &[x]);
    let ffx = op(&mut table, Operation::from(1), &[fx]);
    let mut graph = EGraph::new(table, ());
    let _class = graph.add(fa).expect("a table term");
    let _place = graph.equation(fx, ffx).expect("an open equation");
    let run = graph
        .saturate(Budget {
            rounds: Count::from(100_usize),
            nodes: Count::from(1_000_usize),
        })
        .expect("a saturation");
    assert_eq!(run.outcome, Outcome::Saturated);
    assert_eq!(graph.find(fa), graph.find(ffa));
    // The second match binds `x` to the class's root, `f(a)`, and adds
    // `f(f(f(a)))`; the class holds it, so no third match is new.
    assert_eq!(graph.tally().nodes, Count::from(4_usize));
}

#[test]
fn a_pattern_matches_modulo_the_classes()
{
    // `f(g(x)) = h(x)` meets `f(a)` once `a = g(c)` puts `g(c)` in the class
    // of `a`'s argument.
    let names = Names(&["a", "c", "f", "g", "h"]);
    let (head_f, head_g, head_h) = (2, 3, 4);
    let mut table = TermTable::default();
    let x = var(&mut table, Variable::from(0));
    let a = op(&mut table, Operation::from(0), &[]);
    let c = op(&mut table, Operation::from(1), &[]);
    let gc = op(&mut table, Operation::from(head_g), &[c]);
    let fa = op(&mut table, Operation::from(head_f), &[a]);
    let gx = op(&mut table, Operation::from(head_g), &[x]);
    let fgx = op(&mut table, Operation::from(head_f), &[gx]);
    let hx = op(&mut table, Operation::from(head_h), &[x]);
    let mut graph = EGraph::new(table, ());
    let _class = graph.add(fa).expect("a table term");
    let _ground = graph.equation(a, gc).expect("a ground equation");
    let _open = graph.equation(fgx, hx).expect("an open equation");
    let run = graph
        .saturate(Budget {
            rounds: Count::from(8_usize),
            nodes: Count::from(100_usize),
        })
        .expect("a saturation");
    assert_eq!(run.outcome, Outcome::Saturated);
    let hc = op(graph.table_mut(), Operation::from(head_h), &[c]);
    assert_eq!(
        graph.find(fa),
        graph.find(hc),
        "{:?}",
        classes(&graph, names)
    );
    let explanation = graph.explain(fa, hc).expect("one class");
    assert_eq!(
        explanation.replay(graph.table(), graph.equations(), (fa, hc)),
        Ok(())
    );
}
