//! The proof-producing e-graph on the corpus, rung 3 of the rewriting ladder.
//!
//! Congruence closure is ground completion. So on a block whose rules are
//! ground, the e-graph of the rules must join exactly the terms that have one
//! normal form under the block's rules, which the coincidence check admits as
//! convergent. The suite reads each such block into the term table of its
//! Lawvere theory, closes its terms under its rules, and compares the classes
//! with the normal forms. On every other first-order block, it seeds the
//! e-graph with the block's ground terms up to a size, saturates the e-graph
//! with the block's rules, and makes the same comparison. Each explanation
//! that joins two seeds replays against the table and the rules alone.
//!
//! # References
//!
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-egraphs — an e-graph is a convergent ground rewriting
//!   system, and on a ground block it joins exactly what completion joins.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use gandr_theory_coherent_resolutions::LawvereTheory;
use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermHead;
use gandr_theory_coherent_resolutions::TermNode;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_e_graphs::Budget;
use gandr_theory_e_graphs::Count;
use gandr_theory_e_graphs::EGraph;
use gandr_theory_e_graphs::Outcome;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::TermView;

use crate::lawvere::presented;
use crate::squier::Reading;
use crate::squier::certified;
use crate::squier::corpus;
use crate::squier::each_block;
use crate::squier::rules_of;

/// The largest seed of a block, in nodes: five, so a binary operation's
/// seeds reach two applications nested both ways.
const SEED_SIZE: usize = 5;

/// The most seeds of one block.
const SEEDS: usize = 200;

/// The limits of one saturation.
///
/// # Specification
/// trivial.
fn budget() -> Budget
{
    Budget {
        rounds: Count::from(12_usize),
        nodes: Count::from(2_000_usize),
    }
}

/// What the suite finds for one reading of one block.
#[derive(Debug)]
struct Finding
{
    /// The source and the reading.
    name: String,
    /// How the saturation stops.
    outcome: Outcome,
}

/// Whether each rule of a reading is ground.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rules
{
    /// Each side of each rule binds no name and holds no variable.
    Ground,
    /// A side of a rule binds a name or holds a variable.
    Open,
}

/// Whether each side of each rule of `rules` binds no name and holds no
/// variable.
///
/// # Specification
/// trivial.
fn rules_kind(rules: &[(FreeTerm, FreeTerm)]) -> Rules
{
    let mut pending: Vec<TermView<'_>> = rules
        .iter()
        .flat_map(|&(ref left, ref right)| [left.view(), right.view()])
        .collect();
    while let Some(view) = pending.pop() {
        match view {
            TermView::Ctor { args, .. } | TermView::Op { args, .. } => {
                pending.extend(args.map(gandr_theory_levitation::TermNode::view));
            },
            TermView::Var(_)
            | TermView::Results { .. }
            | TermView::Inst { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. }
            | TermView::Bound(_) => return Rules::Open,
        }
    }
    Rules::Ground
}

/// The terms of `rules` with each of their arguments, in order of place.
///
/// # Specification
/// trivial.
fn subterms(
    table: &TermTable,
    rules: &[(TermPlace, TermPlace)],
) -> Vec<TermPlace>
{
    let mut found = BTreeSet::new();
    let mut pending: Vec<TermPlace> = rules
        .iter()
        .copied()
        .flat_map(<[TermPlace; 2]>::from)
        .collect();
    while let Some(place) = pending.pop() {
        if found.insert(place) {
            pending.extend(
                table
                    .node(place)
                    .expect("a rule term")
                    .children
                    .iter()
                    .copied(),
            );
        }
    }
    found.into_iter().collect()
}

/// The ground terms of `theory`'s operations, by size up to [`SEED_SIZE`],
/// at most [`SEEDS`] of them, interned in the theory's table.
///
/// # Specification
/// trivial.
fn seeds(theory: &mut LawvereTheory) -> Vec<TermPlace>
{
    let arities: Vec<usize> = theory
        .arities()
        .iter()
        .map(|&arity| usize::from(arity))
        .collect();
    // By size, the terms of that size.
    let mut sized: Vec<Vec<TermPlace>> = vec![Vec::new(); SEED_SIZE + 1];
    let mut count = 0_usize;
    for (size, below) in (1 ..= SEED_SIZE).zip(0_usize ..) {
        for (operation, &arity) in arities.iter().enumerate() {
            if (arity == 0) != (size == 1) {
                continue;
            }
            // Each way to share the `below` nodes under the root among the
            // arguments, each at least one: each argument leaves room for the
            // `rest` arguments after it, and the last takes what remains.
            let mut tuples: Vec<(Vec<TermPlace>, usize)> = vec![(Vec::new(), 0)];
            for rest in (0 .. arity).rev() {
                let mut longer = Vec::new();
                for &(ref tuple, used) in &tuples {
                    let room = below.saturating_sub(used);
                    let sizes = sized
                        .iter()
                        .enumerate()
                        .skip(1)
                        .take(room.saturating_sub(rest));
                    for (child_size, children) in sizes {
                        if rest == 0 && child_size != room {
                            continue;
                        }
                        for &child in children {
                            let mut grown = tuple.clone();
                            grown.push(child);
                            longer.push((grown, used.saturating_add(child_size)));
                        }
                    }
                }
                tuples = longer;
            }
            for (children, _) in tuples {
                if count == SEEDS {
                    return sized.into_iter().flatten().collect();
                }
                let term = theory
                    .table_mut()
                    .intern(TermNode {
                        head: TermHead::Op(Operation::from(operation)),
                        children,
                    })
                    .expect("each child is in the table");
                sized[size].push(term);
                count = count.saturating_add(1);
            }
        }
    }
    sized.into_iter().flatten().collect()
}

/// Close `seeds` under `theory`'s rules, compare each two seeds' classes with
/// their normal forms, and replay the explanation that joins each seed to the
/// first seed of its class.
///
/// # Specification
/// trivial.
fn closed(
    name: String,
    theory: &mut LawvereTheory,
    seeds: &[TermPlace],
) -> Finding
{
    let mut graph = EGraph::new(theory.table().clone(), ());
    for &seed in seeds {
        let _class = graph.add(seed).expect("a seed is in the table");
    }
    for &(left, right) in theory.rules() {
        let _place = graph.equation(left, right).expect("a rule of the block");
    }
    let run = graph.saturate(budget()).expect("a saturation");
    let mut first: BTreeMap<TermPlace, TermPlace> = BTreeMap::new();
    if run.outcome == Outcome::Saturated {
        let normal: Vec<TermPlace> = seeds
            .iter()
            .map(|&seed| theory.normal_form(seed).expect("a normal form"))
            .collect();
        for (&left, &left_normal) in seeds.iter().zip(&normal) {
            for (&right, &right_normal) in seeds.iter().zip(&normal) {
                let joined = graph.find(left) == graph.find(right);
                assert_eq!(
                    joined,
                    left_normal == right_normal,
                    "{name}: {left:?} and {right:?} join apart from their normal forms"
                );
            }
        }
        for &seed in seeds {
            let class = graph.find(seed).expect("a held seed");
            let leader = *first.entry(class).or_insert(seed);
            let explanation = graph.explain(leader, seed).expect("one class");
            assert_eq!(
                explanation.replay(graph.table(), graph.equations(), (leader, seed)),
                Ok(()),
                "{name}: the explanation of {seed:?} replays"
            );
        }
    }
    Finding {
        name,
        outcome: run.outcome,
    }
}

/// The findings of each reading of each corpus block that `keep` admits,
/// with its rules and its theory.
///
/// # Specification
/// trivial.
fn findings<Keep>(mut keep: Keep) -> Vec<Finding>
where
    Keep: FnMut(&[(FreeTerm, FreeTerm)], &mut LawvereTheory) -> Option<Vec<TermPlace>>,
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut found = Vec::new();
    for path in corpus() {
        let text = std::fs::read_to_string(&path).expect("a corpus source reads");
        let source = SourceText::from(text.as_str());
        let _lowering = each_block(&grammar, source, |cells| {
            if certified(cells).is_none() {
                return;
            }
            for reading in [Reading::Terms, Reading::Commands] {
                let rules = rules_of(cells, reading);
                if rules.is_empty() {
                    continue;
                }
                let Ok((mut theory, _names)) = presented(&rules)
                else {
                    continue;
                };
                if let Some(seeds) = keep(&rules, &mut theory) {
                    found.push(closed(
                        format!("{} {reading:?}", path.display()),
                        &mut theory,
                        &seeds,
                    ));
                }
            }
        });
    }
    found
}

#[test]
fn each_ground_block_joins_exactly_what_completion_joins()
{
    let found = findings(|rules, theory| {
        (rules_kind(rules) == Rules::Ground).then(|| subterms(theory.table(), theory.rules()))
    });
    assert!(!found.is_empty(), "the corpus holds ground blocks");
    for finding in &found {
        assert_eq!(finding.outcome, Outcome::Saturated, "{}", finding.name);
    }
}

#[test]
fn each_first_order_block_saturates_to_its_normal_forms()
{
    let found = findings(|rules, theory| {
        let open = rules_kind(rules) == Rules::Open;
        let constant = theory
            .arities()
            .iter()
            .any(|&arity| usize::from(arity) == 0);
        (open && constant).then(|| seeds(theory))
    });
    assert!(!found.is_empty(), "the corpus holds first-order blocks");
    let exhausted: Vec<&str> = found
        .iter()
        .filter(|finding| finding.outcome == Outcome::Exhausted)
        .map(|finding| finding.name.as_str())
        .collect();
    assert!(
        exhausted.is_empty(),
        "saturation passes its budget on {exhausted:?}"
    );
}
