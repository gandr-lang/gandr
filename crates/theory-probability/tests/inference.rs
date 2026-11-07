//! Exact inference over factor graphs: the sprinkler network of probe 16, a
//! chain of sixteen variables, and a contextual family of three tables.

use gandr_theory_cellular_sheaves::CoverIndex;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::OrderedSemiring as _;
use gandr_theory_ordered_algebras::Reach;
use gandr_theory_ordered_algebras::check;
use gandr_theory_probability::Arity;
use gandr_theory_probability::FactorGraph;
use gandr_theory_probability::Family;
use gandr_theory_probability::Gluing;
use gandr_theory_probability::InferenceError;
use gandr_theory_probability::JunctionTree;
use gandr_theory_probability::MaxTimes;
use gandr_theory_probability::Possibility;
use gandr_theory_probability::Probability;
use gandr_theory_probability::Scope;
use gandr_theory_probability::Table;
use gandr_theory_probability::Value;
use gandr_theory_probability::Variable;

/// Whether it is cloudy.
///
/// # Specification
/// trivial.
fn cloudy() -> Variable
{
    Variable::from(0)
}

/// Whether the sprinkler is on.
///
/// # Specification
/// trivial.
fn sprinkler() -> Variable
{
    Variable::from(1)
}

/// Whether it rains.
///
/// # Specification
/// trivial.
fn rain() -> Variable
{
    Variable::from(2)
}

/// Whether the grass is wet.
///
/// # Specification
/// trivial.
fn wet() -> Variable
{
    Variable::from(3)
}

/// The scope of `variables`, each with two values.
///
/// # Specification
/// trivial.
fn binary(variables: &[Variable]) -> Scope
{
    Scope::new(
        variables
            .iter()
            .map(|&variable| (variable, Arity::from(2)))
            .collect(),
    )
    .expect("a scope of distinct binary variables")
}

/// The table over the binary `variables` whose weight at each entry is
/// `weight` of the scope and the entry.
///
/// # Specification
/// trivial.
fn table(
    variables: &[Variable],
    weight: impl Fn(&Scope, Entry) -> Rational,
) -> Table<Rational>
{
    let scope = binary(variables);
    let weights = (0 .. usize::from(scope.width()))
        .map(|entry| weight(&scope, Entry::from(entry)))
        .collect();
    Table::new(scope, weights).expect("one weight for each entry")
}

/// Whether `variable` is true at `entry` of `scope`.
///
/// # Specification
/// trivial.
fn holds(
    scope: &Scope,
    entry: Entry,
    variable: Variable,
) -> Truth
{
    match scope.value(entry, variable).map(u32::from) {
        Some(1) => Truth::True,
        _ => Truth::False,
    }
}

/// A binary value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Truth
{
    /// Zero.
    False,
    /// One.
    True,
}

/// `chance` when `truth` is true, and one less it when false.
///
/// # Specification
/// trivial.
fn given(
    truth: Truth,
    chance: Rational,
) -> Rational
{
    match truth {
        Truth::True => chance,
        Truth::False => Rational::ONE
            .plus(chance.times(rational!(-1, 1)).expect("a negated chance"))
            .expect("one less a chance"),
    }
}

/// The sprinkler network: a fair cloud, the sprinkler and the rain given the
/// cloud, and wet grass given the sprinkler and the rain.
///
/// # Specification
/// trivial.
fn network() -> FactorGraph<Rational>
{
    let of_cloud = table(&[cloudy()], |scope, entry| {
        given(holds(scope, entry, cloudy()), rational!(1, 2))
    });
    let of_sprinkler = table(&[cloudy(), sprinkler()], |scope, entry| {
        let chance = match holds(scope, entry, cloudy()) {
            Truth::True => rational!(1, 10),
            Truth::False => rational!(1, 2),
        };
        given(holds(scope, entry, sprinkler()), chance)
    });
    let of_rain = table(&[cloudy(), rain()], |scope, entry| {
        let chance = match holds(scope, entry, cloudy()) {
            Truth::True => rational!(4, 5),
            Truth::False => rational!(1, 5),
        };
        given(holds(scope, entry, rain()), chance)
    });
    let of_wet = table(&[sprinkler(), rain(), wet()], |scope, entry| {
        let chance = match (
            holds(scope, entry, sprinkler()),
            holds(scope, entry, rain()),
        ) {
            (Truth::False, Truth::False) => Rational::ZERO,
            (Truth::True, Truth::True) => rational!(99, 100),
            _ => rational!(9, 10),
        };
        given(holds(scope, entry, wet()), chance)
    });
    FactorGraph::new(vec![Arity::from(2); 4], vec![
        of_cloud,
        of_sprinkler,
        of_rain,
        of_wet,
    ])
    .expect("the network's factors")
}

/// The joint weight of each world of `graph`, by the product of its factors:
/// the reference that sum-product meets, read world by world.
///
/// # Specification
/// trivial.
fn joint(graph: &FactorGraph<Rational>) -> Table<Rational>
{
    let scope = graph.scope().expect("the scope of every variable");
    let weights = (0 .. usize::from(scope.width()))
        .map(|world| {
            graph
                .factors()
                .iter()
                .fold(Rational::ONE, |product, factor| {
                    let at = (0 .. usize::from(factor.scope().width()))
                        .find(|&entry| {
                            factor.scope().variables().all(|(variable, _)| {
                                factor.scope().value(Entry::from(entry), variable)
                                    == scope.value(Entry::from(world), variable)
                            })
                        })
                        .expect("the factor's entry of the world");
                    product
                        .times(*factor.weights().get(at).expect("a weight"))
                        .expect("a product in range")
                })
        })
        .collect();
    Table::new(scope, weights).expect("one weight for each world")
}

/// The sum of `of`'s weights over each entry of `onto`, by enumeration.
///
/// # Specification
/// trivial.
fn summed(
    of: &Table<Rational>,
    onto: &Scope,
) -> Vec<Rational>
{
    (0 .. usize::from(onto.width()))
        .map(|target| {
            (0 .. usize::from(of.scope().width()))
                .filter(|&entry| {
                    onto.variables().all(|(variable, _)| {
                        of.scope().value(Entry::from(entry), variable)
                            == onto.value(Entry::from(target), variable)
                    })
                })
                .fold(Rational::ZERO, |sum, entry| {
                    sum.plus(*of.weights().get(entry).expect("a weight"))
                        .expect("a sum in range")
                })
        })
        .collect()
}

/// The order that gives the network its two cliques of three.
///
/// # Specification
/// trivial.
fn order() -> [Variable; 4]
{
    [wet(), cloudy(), sprinkler(), rain()]
}

/// A scope gives its variables in ascending order whatever order they come
/// in, with the product of their arities as its width. A variable named
/// twice, an arity of zero, a table one weight short, and a factor over a
/// variable the graph does not hold or with another arity are each refused
/// by name.
#[test]
fn a_scope_orders_its_variables_and_refuses_a_repeat()
{
    let scope = Scope::new(vec![(rain(), Arity::from(3)), (cloudy(), Arity::from(2))])
        .expect("two distinct variables");
    assert_eq!(scope.variables().collect::<Vec<_>>(), [
        (cloudy(), Arity::from(2)),
        (rain(), Arity::from(3))
    ]);
    assert_eq!(scope.width(), Width::from(6_usize));
    // The last variable runs fastest: entry 4 is cloudy 1 and rain 1.
    assert_eq!(
        (
            scope.value(Entry::from(4_usize), cloudy()),
            scope.value(Entry::from(4_usize), rain())
        ),
        (Some(Value::from(1)), Some(Value::from(1)))
    );
    assert_eq!(
        Scope::new(vec![(rain(), Arity::from(2)), (rain(), Arity::from(2))]),
        Err(InferenceError::Repeated(rain()))
    );
    assert_eq!(
        Scope::new(vec![(wet(), Arity::from(0))]),
        Err(InferenceError::NoValue(wet()))
    );
    assert_eq!(
        Table::new(binary(&[cloudy()]), vec![Rational::ONE]),
        Err(InferenceError::Width {
            expected: Width::from(2_usize),
            given: Width::from(1_usize),
        })
    );
    let fifth = Variable::from(4);
    assert_eq!(
        FactorGraph::new(vec![Arity::from(2); 4], vec![table(&[fifth], |_, _| {
            Rational::ONE
        })]),
        Err(InferenceError::Unknown(fifth))
    );
    let ternary = Table::new(
        Scope::new(vec![(wet(), Arity::from(3))]).expect("one variable"),
        vec![Rational::ONE; 3],
    )
    .expect("three weights");
    assert_eq!(
        FactorGraph::new(vec![Arity::from(2); 4], vec![ternary]),
        Err(InferenceError::Mismatched(wet()))
    );
}

/// Over the probability semiring, each clique belief of the network is the
/// marginal of the joint on the clique's variables, entry by entry, and so is
/// each variable's marginal. The joint is the product of the factors over
/// each of the sixteen worlds, and it sums to one.
#[test]
fn sum_product_gives_the_marginals_of_the_network()
{
    let graph = network();
    let tree = JunctionTree::new(&graph, &order()).expect("the network's tree");
    assert_eq!(tree.cliques(), [
        binary(&[sprinkler(), rain(), wet()]),
        binary(&[cloudy(), sprinkler(), rain()])
    ]);
    let reference = joint(&graph);
    assert_eq!(
        summed(&reference, &binary(&[])),
        [Rational::ONE],
        "the joint sums to one"
    );
    let calibrated = tree
        .calibrate(&Probability::default(), &graph)
        .expect("the network calibrates");
    for belief in calibrated.family().members() {
        assert_eq!(
            belief.weights(),
            summed(&reference, belief.scope()),
            "the belief over {:?}",
            belief.scope()
        );
    }
    for variable in [cloudy(), sprinkler(), rain(), wet()] {
        let onto = binary(&[variable]);
        let marginal = calibrated
            .marginal(&Probability::default(), &onto)
            .expect("a clique holds each variable");
        assert_eq!(marginal.weights(), summed(&reference, &onto), "{variable}");
    }
    // The grass is wet with weight 0.6471 by the reference.
    assert_eq!(summed(&reference, &binary(&[wet()])), [
        rational!(3529, 10_000),
        rational!(6471, 10_000)
    ]);
}

/// Over the max-times semiring the decoded world of the network is the world
/// of greatest joint weight: cloudy, the sprinkler off, rain and wet grass,
/// with weight `81/250`. That is also the greatest weight of the first
/// clique's max-marginal.
#[test]
fn max_times_gives_the_most_likely_world_of_the_network()
{
    let graph = network();
    let tree = JunctionTree::new(&graph, &order()).expect("the network's tree");
    let calibrated = tree
        .calibrate(&MaxTimes::default(), &graph)
        .expect("the network calibrates");
    let assignment = tree
        .decode(&MaxTimes::default(), &calibrated)
        .expect("the network decodes");
    let reference = joint(&graph);
    let (best, weight) = reference
        .weights()
        .iter()
        .enumerate()
        .max_by(|left, right| left.1.cmp(right.1))
        .expect("sixteen worlds");
    assert_eq!(*weight, rational!(81, 250));
    for variable in [cloudy(), sprinkler(), rain(), wet()] {
        assert_eq!(
            assignment.value(variable),
            reference.scope().value(Entry::from(best), variable),
            "{variable}"
        );
    }
    assert_eq!(
        [cloudy(), sprinkler(), rain(), wet()]
            .map(|variable| assignment.value(variable).map(u32::from)),
        [Some(1), Some(0), Some(1), Some(1)]
    );
    let greatest = calibrated
        .family()
        .members()
        .first()
        .and_then(|belief| belief.weights().iter().max())
        .copied();
    assert_eq!(greatest, Some(rational!(81, 250)));
}

/// The calibrated cliques of the network glue on their separator, sprinkler
/// and rain, to the weights `29/100`, `41/100`, `21/100` and `9/100`, and
/// every entry of positive weight extends to a world. Each of the sixteen
/// clique weights, raised by `1/100` in turn, gives one disagreement at the
/// separator entry it sums into, with both weights.
#[test]
fn the_clique_marginals_glue_and_a_changed_weight_is_obstructed()
{
    let semiring = Probability::default();
    let graph = network();
    let tree = JunctionTree::new(&graph, &order()).expect("the network's tree");
    let calibrated = tree
        .calibrate(&semiring, &graph)
        .expect("the network calibrates");
    let family = calibrated.family();
    let separator = binary(&[sprinkler(), rain()]);
    let by_hand = vec![
        rational!(29, 100),
        rational!(41, 100),
        rational!(21, 100),
        rational!(9, 100),
    ];
    assert_eq!(
        family.glue(&semiring),
        Ok(Gluing::Glued(vec![
            Table::new(separator.clone(), by_hand.clone()).expect("four weights")
        ]))
    );
    assert_eq!(family.possibility(&semiring), Ok(Possibility::Extends));
    for (member, belief) in family.members().iter().enumerate() {
        for entry in 0 .. belief.weights().len() {
            let mut weights = belief.weights().to_vec();
            let raised = weights.get_mut(entry).expect("an entry");
            *raised = raised.plus(rational!(1, 100)).expect("a raised weight");
            let mut members = family.members().to_vec();
            *members.get_mut(member).expect("a member") =
                Table::new(belief.scope().clone(), weights).expect("the same width");
            let changed =
                Family::new(members, family.overlaps().to_vec()).expect("the same overlaps");
            let at = [sprinkler(), rain()].map(|variable| {
                belief
                    .scope()
                    .value(Entry::from(entry), variable)
                    .map(u32::from)
            });
            let target = match at {
                [Some(sprinkler), Some(rain)] => sprinkler
                    .checked_mul(2)
                    .and_then(|twice| twice.checked_add(rain))
                    .and_then(|sum| usize::try_from(sum).ok())
                    .expect("two bits"),
                _ => panic!("the clique holds the separator"),
            };
            let kept = *by_hand.get(target).expect("a separator weight");
            let moved = kept.plus(rational!(1, 100)).expect("a raised weight");
            let weights = if member == 0 {
                (moved, kept)
            }
            else {
                (kept, moved)
            };
            match changed.glue(&semiring) {
                Ok(Gluing::Obstructed(differences)) => {
                    assert_eq!(differences.len(), 1, "member {member}, entry {entry}");
                    let difference = differences.first().expect("one disagreement");
                    assert_eq!(
                        (
                            difference.members,
                            &difference.overlap,
                            difference.entry,
                            difference.weights
                        ),
                        (
                            (CoverIndex::from(0_usize), CoverIndex::from(1_usize)),
                            &separator,
                            Entry::from(target),
                            weights
                        ),
                        "member {member}, entry {entry}"
                    );
                },
                verdict => panic!("member {member}, entry {entry} glues: {verdict:?}"),
            }
        }
    }
}

/// Three tables over `{A, B}`, `{B, C}` and `{A, C}`, each putting half its
/// weight on each of the two entries where its variables differ. Each two
/// agree on their overlap, so the family glues, with a fair coin on each
/// shared variable. No world has all three pairs different, so the first
/// entry of positive weight, `A = 0` and `B = 1`, extends to no world, and no
/// joint has the three tables as marginals. An overlap with a fourth member
/// is refused by its number.
#[test]
fn a_contextual_family_glues_and_is_refused_a_joint()
{
    let semiring = Probability::default();
    let (a, b, c) = (Variable::from(0), Variable::from(1), Variable::from(2));
    let apart = |first: Variable, second: Variable| {
        table(&[first, second], move |scope, entry| {
            if holds(scope, entry, first) == holds(scope, entry, second) {
                Rational::ZERO
            }
            else {
                rational!(1, 2)
            }
        })
    };
    let overlaps = vec![
        (CoverIndex::from(0_usize), CoverIndex::from(1_usize)),
        (CoverIndex::from(1_usize), CoverIndex::from(2_usize)),
        (CoverIndex::from(0_usize), CoverIndex::from(2_usize)),
    ];
    let members = vec![apart(a, b), apart(b, c), apart(a, c)];
    let family = Family::new(members.clone(), overlaps).expect("three members");
    let coin = vec![rational!(1, 2); 2];
    assert_eq!(
        family.glue(&semiring),
        Ok(Gluing::Glued(vec![
            Table::new(binary(&[b]), coin.clone()).expect("two weights"),
            Table::new(binary(&[c]), coin.clone()).expect("two weights"),
            Table::new(binary(&[a]), coin).expect("two weights"),
        ]))
    );
    assert_eq!(
        family.possibility(&semiring),
        Ok(Possibility::Contextual {
            member: CoverIndex::from(0_usize),
            entry: Entry::from(1_usize),
        })
    );
    assert_eq!(
        Family::new(members, vec![(
            CoverIndex::from(0_usize),
            CoverIndex::from(3_usize)
        )]),
        Err(InferenceError::NoMember(CoverIndex::from(3_usize)))
    );
}

/// The path `{A, B}`, `{B, C}`, `{A, C}` is a tree, but `A` lies at its two
/// ends and not between them, so it is refused by `A`. Three edges on three
/// cliques, a repeated edge, and an edge past the cliques are refused. An
/// order that leaves a variable out, names one twice, or names one the graph
/// does not hold is refused by that variable.
#[test]
fn a_tree_without_running_intersection_is_refused()
{
    let (a, b, c) = (Variable::from(0), Variable::from(1), Variable::from(2));
    let cliques = vec![binary(&[a, b]), binary(&[b, c]), binary(&[a, c])];
    let edge = |first: usize, second: usize| (CoverIndex::from(first), CoverIndex::from(second));
    assert_eq!(
        JunctionTree::with_tree(cliques.clone(), &[edge(0, 1), edge(1, 2)]),
        Err(InferenceError::RunningIntersection(a))
    );
    for edges in [vec![edge(0, 1), edge(1, 2), edge(0, 2)], vec![
        edge(0, 1),
        edge(1, 0),
    ]] {
        assert_eq!(
            JunctionTree::with_tree(cliques.clone(), &edges),
            Err(InferenceError::NotATree)
        );
    }
    assert_eq!(
        JunctionTree::with_tree(cliques, &[edge(0, 1), edge(1, 3)]),
        Err(InferenceError::NoMember(CoverIndex::from(3_usize)))
    );
    let graph = network();
    assert_eq!(
        JunctionTree::new(&graph, &[wet(), cloudy(), sprinkler()]),
        Err(InferenceError::NotEliminated(rain()))
    );
    assert_eq!(
        JunctionTree::new(&graph, &[wet(), wet(), cloudy(), sprinkler(), rain()]),
        Err(InferenceError::Repeated(wet()))
    );
    let ninth = Variable::from(9);
    assert_eq!(
        JunctionTree::new(&graph, &[ninth]),
        Err(InferenceError::Unknown(ninth))
    );
}

/// The length of the chain.
const LENGTH: u32 = 16;

/// A chain of sixteen binary variables: the first is one with weight `2/3`,
/// and each next one keeps the value of the one before with weight `3/4`
/// after an even variable and changes it with weight `3/4` after an odd one.
///
/// # Specification
/// trivial.
fn chain() -> FactorGraph<Rational>
{
    let first = table(&[Variable::from(0)], |scope, entry| {
        given(holds(scope, entry, Variable::from(0)), rational!(2, 3))
    });
    let steps = (0 .. LENGTH - 1).map(|place| {
        let after = place.checked_add(1).expect("a next variable");
        let (before, after) = (Variable::from(place), Variable::from(after));
        table(&[before, after], move |scope, entry| {
            let same = holds(scope, entry, before) == holds(scope, entry, after);
            let keeps = place % 2 == 0;
            if same == keeps {
                rational!(3, 4)
            }
            else {
                rational!(1, 4)
            }
        })
    });
    FactorGraph::new(
        vec![Arity::from(2); 16],
        core::iter::once(first).chain(steps).collect(),
    )
    .expect("the chain's factors")
}

/// The chain of sixteen eliminated from its first variable gives fifteen
/// cliques of two. Each variable's marginal meets the sum over the 65 536
/// assignments, and the decoded assignment is the one of greatest joint
/// weight: one, one, then pairs that alternate.
#[test]
fn a_chain_of_sixteen_marginalises_and_decodes()
{
    let graph = chain();
    let order: Vec<Variable> = (0 .. LENGTH).map(Variable::from).collect();
    let tree = JunctionTree::new(&graph, &order).expect("the chain's tree");
    assert_eq!(tree.cliques().len(), 15);
    assert_eq!(tree.edges().count(), 14);
    let reference = joint(&graph);
    let calibrated = tree
        .calibrate(&Probability::default(), &graph)
        .expect("the chain calibrates");
    for variable in (0 .. LENGTH).map(Variable::from) {
        let onto = binary(&[variable]);
        let marginal = calibrated
            .marginal(&Probability::default(), &onto)
            .expect("a clique holds each variable");
        assert_eq!(marginal.weights(), summed(&reference, &onto), "{variable}");
    }
    let most = tree
        .calibrate(&MaxTimes::default(), &graph)
        .expect("the chain calibrates");
    let assignment = tree
        .decode(&MaxTimes::default(), &most)
        .expect("the chain decodes");
    let (best, _) = reference
        .weights()
        .iter()
        .enumerate()
        .max_by(|left, right| left.1.cmp(right.1))
        .expect("65 536 assignments");
    let decoded: Vec<_> = (0 .. LENGTH)
        .map(|place| assignment.value(Variable::from(place)).map(u32::from))
        .collect();
    let greatest: Vec<_> = (0 .. LENGTH)
        .map(|place| {
            reference
                .scope()
                .value(Entry::from(best), Variable::from(place))
                .map(u32::from)
        })
        .collect();
    assert_eq!(decoded, greatest);
    assert_eq!(
        decoded,
        [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0].map(Some)
    );
}

/// The probability and the max-times semirings each pass the sixteen laws
/// of the ordered-algebras checker on generated non-negative rationals, and
/// each orders the rationals as numbers.
#[test]
fn the_rational_semirings_pass_every_law()
{
    let generated = vec![
        Rational::ZERO,
        rational!(1, 3),
        rational!(1, 2),
        Rational::ONE,
        rational!(7, 4),
    ];
    let probability = Probability::generated(generated.clone());
    let decided = check(&probability).expect("every law holds");
    assert_eq!(
        (usize::from(decided.laws()), decided.reach()),
        (16, Reach::Generated)
    );
    let most = MaxTimes::generated(generated);
    let decided = check(&most).expect("every law holds");
    assert_eq!(
        (usize::from(decided.laws()), decided.reach()),
        (16, Reach::Generated)
    );
    assert_eq!(
        most.compare(&rational!(1, 2), &rational!(1, 3)),
        Comparison::NotBelow
    );
    assert_eq!(
        most.add(&rational!(1, 2), &rational!(1, 3)),
        Ok(rational!(1, 2))
    );
}

/// Two factors of weight `2^-100` over one variable multiply to `2^-200`,
/// past the 128-bit integers, so calibration refuses it by name.
#[test]
fn a_weight_past_the_integers_is_refused()
{
    let tiny = rational!(1, 1 << 100);
    let only = Variable::from(0);
    let factor = table(&[only], move |_, _| tiny);
    let graph =
        FactorGraph::new(vec![Arity::from(2)], vec![factor.clone(), factor]).expect("two factors");
    let tree = JunctionTree::new(&graph, &[only]).expect("one clique");
    assert_eq!(
        tree.calibrate(&Probability::default(), &graph),
        Err(InferenceError::Overflow)
    );
}
