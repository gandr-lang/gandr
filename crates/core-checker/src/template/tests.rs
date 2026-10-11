//! Gate clauses over staging equations and complete producer certificates.

use gandr_kernel_core::admission::Proposal;
use gandr_kernel_core::admission::Refusal;
use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Type;

use super::draft::Drafter;
use super::draft::Finished;
use super::draft::Rebasing;
use super::draft::Walk;
use super::draft::Widening;
use super::*;

/// Fixture family cardinality.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Members(usize);

/// Distinct ground bodies in a family.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Arms(usize);

/// Harvest real quote/splice normalization equations at controlled instances.
///
/// # Specification
/// - ensures: one closed cancellation equation per member, cycling over arms.
/// - panics: fixture allocation or normalization failure.
///
/// # Adequacy
/// - hypothesis: L2 — ordinary typed replay independently checks the fixtures.
/// - witness: `template::tests::every_member_admits_as_its_plain_replay`
#[spec(requires: arms.0 > 0, ensures: |output| output.1.len() == members.0)]
fn cancellations(
    members: Members,
    arms: Arms,
) -> (Arena, Vec<Step>)
{
    let (arena, certificates) = normalized(Edition::Generated { members, arms });
    let family = certificates
        .into_iter()
        .flat_map(|certificate| certificate.steps)
        .collect();
    (arena, family)
}

/// Independent tree observer, without the pattern graph's interning or sizes.
///
/// # Specification
/// - ensures: counts every syntactic occurrence below the supplied root.
/// - panics: malformed fixture syntax or count overflow.
///
/// # Adequacy
/// - hypothesis: L2 — the gate's independently summed F separates omitted
///   sides.
/// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
#[spec(ensures: |output| usize::from(output) > 0)]
fn nodes(
    arena: &Arena,
    root: TermId,
) -> NodeCount
{
    let mut pending = Vec::from([root]);
    let mut count = 0_usize;
    while let Some(id) = pending.pop() {
        count = count.checked_add(1).unwrap();
        pending.extend(arena.term(id).unwrap().children().into_iter().flatten());
    }
    NodeCount::from(count)
}

#[test]
fn a_template_is_emitted_only_below_its_expansion_factor()
{
    for members in [2, 8, 16, 32, 64] {
        for arms in [1, 2, 4, 8] {
            let (arena, family) = cancellations(Members(members), Arms(arms));
            let mut cache = InheritanceCache::new();
            let produced = produce(
                &arena,
                &family,
                PriceGate::Unmemoized,
                &mut cache,
                &mut Budget(1_000_000),
            )
            .unwrap();
            let plain = family.iter().fold(0_usize, |sum, step| {
                sum.checked_add(usize::from(nodes(&arena, step.source)))
                    .unwrap()
                    .checked_add(usize::from(nodes(&arena, step.target)))
                    .unwrap()
                    .checked_add(1)
                    .unwrap()
            });
            let cost = produced.cost();
            assert_eq!(usize::from(cost.plain_size), plain);
            let distinct = arms.min(members);
            let expected = if distinct == 1 {
                5
            }
            else {
                5_usize.saturating_add(distinct.saturating_mul(2))
            };
            assert_eq!(usize::from(cost.template_size), expected);
            assert_eq!(usize::from(cost.plain_replayed_steps), members);
            match produced {
                | Production::WorkBoundExceeded { .. } => {
                    panic!("the original gate has no memoized allowance")
                },
                | Production::SchemaWorkBound { .. } => {},
                | Production::Go(_) => {
                    let size = usize::from(cost.template_size);
                    assert!(size < plain.checked_div(size).unwrap());
                    assert!(size.checked_mul(size).unwrap() < plain);
                },
                | Production::Plain { reason, .. } => {
                    assert!(matches!(reason, TemplateRefusal::DoesNotPay { .. }));
                    assert_eq!(usize::from(cache.checked()), 0);
                },
            }
        }
    }
}

#[test]
fn every_member_admits_as_its_plain_replay()
{
    let (mut arena, family) = cancellations(Members(64), Arms(2));
    let Production::Go(template) = produce(
        &arena,
        &family,
        PriceGate::Unmemoized,
        &mut InheritanceCache::new(),
        &mut Budget(1_000_000),
    )
    .unwrap()
    else {
        panic!("paying family");
    };
    let token = arena.alloc_type(Type::In(Model(0))).unwrap();
    for step in &family {
        assert_eq!(
            template.admit(&arena, step.source, &mut Budget(100_000)),
            replay_equation(&mut arena, *step, &mut Budget(100_000))
        );
        let certificate = Certificate {
            source: step.source,
            target: step.target,
            steps: Vec::from([*step]),
        };
        let plain = gandr_kernel_core::stage::replay(
            &mut arena,
            &[token],
            &certificate,
            &mut Budget(100_000),
        );
        let compressed = readmit(
            &mut arena,
            &[token],
            &certificate,
            &[Production::Go(template.clone())],
            &mut Budget(100_000),
        );
        assert_eq!(compressed, plain);
        assert!(plain.is_ok());
    }
    let mut arena = Arena::default();
    let token = arena.alloc_type(Type::In(Model(0))).unwrap();
    let program = gandr_core_nbe::stage::power(&mut arena, Model(0)).unwrap();
    for exponent in 0 ..= 8 {
        let number = arena
            .alloc(Term::Natural(Stage::Outer, Natural(exponent)))
            .unwrap();
        let source = arena.alloc(Term::Apply(program, number)).unwrap();
        let inner = arena.alloc_type(Type::Nat(Stage::Inner(Model(0)))).unwrap();
        let input = arena.alloc(Term::Variable(Index(0))).unwrap();
        let input = arena.alloc(Term::Quote(input)).unwrap();
        let source = arena.alloc(Term::Apply(source, input)).unwrap();
        let source = arena.alloc(Term::Splice(source)).unwrap();
        let source = arena.alloc(Term::Lambda(inner, source)).unwrap();
        let source = arena.alloc(Term::Quote(source)).unwrap();
        let certificate =
            gandr_core_nbe::stage::normalize(&mut arena, source, &mut Budget(1_000_000)).unwrap();
        let mut productions = Vec::new();
        let mut cache = InheritanceCache::new();
        for family in harvest(&arena, ProgramId(0), core::slice::from_ref(&certificate)).unwrap() {
            productions.push(
                produce(
                    &arena,
                    &family.members,
                    PriceGate::Unmemoized,
                    &mut cache,
                    &mut Budget(10_000_000),
                )
                .unwrap(),
            );
        }
        let plain = gandr_kernel_core::stage::replay(
            &mut arena,
            &[token],
            &certificate,
            &mut Budget(10_000_000),
        );
        assert!(plain.is_ok());
        assert_eq!(
            readmit(
                &mut arena,
                &[token],
                &certificate,
                &productions,
                &mut Budget(10_000_000)
            ),
            plain
        );
        let mut corrupt = certificate.clone();
        corrupt.target = arena
            .alloc(Term::Natural(Stage::Outer, Natural(912)))
            .unwrap();
        assert_eq!(
            readmit(
                &mut arena,
                &[token],
                &corrupt,
                &productions,
                &mut Budget(10_000_000)
            ),
            gandr_kernel_core::stage::replay(
                &mut arena,
                &[token],
                &corrupt,
                &mut Budget(10_000_000)
            )
        );
    }
}

#[test]
fn a_skeleton_divergent_family_yields_no_template()
{
    let (arena, mut family) = cancellations(Members(64), Arms(2));
    family.last_mut().unwrap().rule = Rule::QuoteSplice;
    let mut cache = InheritanceCache::new();
    assert!(
        matches!(produce(&arena, &family, PriceGate::Unmemoized, &mut cache, &mut Budget(1_000_000)).unwrap(), Production::Plain { reason: TemplateRefusal::SkeletonDivergence { member }, .. } if usize::from(member) == 63)
    );
    assert_eq!(usize::from(cache.checked()), 0);
}

#[test]
fn an_entry_a_decision_discriminates_on_yields_no_template()
{
    let (mut arena, mut family) = cancellations(Members(64), Arms(2));
    let bad = arena
        .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(7)))
        .unwrap();
    let source = arena.alloc(Term::Splice(bad)).unwrap();
    family.last_mut().unwrap().source = source;
    let mut cache = InheritanceCache::new();
    assert!(matches!(
        produce(
            &arena,
            &family,
            PriceGate::Unmemoized,
            &mut cache,
            &mut Budget(1_000_000)
        )
        .unwrap(),
        Production::Plain {
            reason: TemplateRefusal::NotInherited { .. } | TemplateRefusal::EntryOutsidePeak { .. },
            ..
        }
    ));
}

#[test]
fn a_family_with_no_shared_content_yields_no_template()
{
    let (arena, family) = cancellations(Members(64), Arms(64));
    let mut cache = InheritanceCache::new();
    assert!(matches!(
        produce(
            &arena,
            &family,
            PriceGate::Unmemoized,
            &mut cache,
            &mut Budget(1_000_000)
        )
        .unwrap(),
        Production::Plain {
            reason: TemplateRefusal::DoesNotPay { .. },
            ..
        }
    ));
    assert_eq!(usize::from(cache.checked()), 0);
}

#[test]
fn the_inheritance_check_runs_once_per_distinct_triple()
{
    let (arena, family) = cancellations(Members(64), Arms(2));
    let mut cache = InheritanceCache::new();
    let first = produce(
        &arena,
        &family,
        PriceGate::Unmemoized,
        &mut cache,
        &mut Budget(1_000_000),
    )
    .unwrap();
    assert!(matches!(first, Production::Go(_)));
    assert_eq!(usize::from(first.cost().triples_checked), 2);
    assert_eq!(usize::from(first.cost().cache_hits), 62);
    let second = produce(
        &arena,
        &family,
        PriceGate::Unmemoized,
        &mut cache,
        &mut Budget(0),
    )
    .unwrap();
    assert_eq!(usize::from(second.cost().triples_checked), 0);
    assert_eq!(usize::from(second.cost().cache_hits), 64);
    assert_eq!(usize::from(cache.distinct_triples()), 2);
    // The same content harvested in another program's arena reuses every
    // verdict: the region is content, not producer identity.
    let (other_arena, other_family) = cancellations(Members(64), Arms(2));
    let other = produce(
        &other_arena,
        &other_family,
        PriceGate::Unmemoized,
        &mut cache,
        &mut Budget(0),
    )
    .unwrap();
    assert!(matches!(other, Production::Go(_)));
    assert_eq!(usize::from(other.cost().triples_checked), 0);
    assert_eq!(usize::from(other.cost().cache_hits), 64);
}

#[test]
fn a_poisoned_inheritance_entry_is_caught_at_admission()
{
    let mut arena = Arena::default();
    let ty = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let identity = arena.alloc(Term::Lambda(ty, variable)).unwrap();
    let bad_head = arena
        .alloc(Term::Natural(Stage::Outer, Natural(3)))
        .unwrap();
    let argument = arena
        .alloc(Term::Natural(Stage::Outer, Natural(7)))
        .unwrap();
    let mut family = Vec::new();
    for member in 0_usize .. 64 {
        let head = if member == 63 { bad_head } else { identity };
        let source = arena.alloc(Term::Apply(head, argument)).unwrap();
        family.push(Step {
            source,
            target: argument,
            rule: Rule::Beta,
        });
    }
    let mut cache = InheritanceCache::new();
    let template = loop {
        match produce(
            &arena,
            &family,
            PriceGate::Unmemoized,
            &mut cache,
            &mut Budget(1_000_000),
        )
        .unwrap()
        {
            | Production::Go(template) => break template,
            | Production::Plain {
                reason: TemplateRefusal::NotInherited { key, .. },
                ..
            } => cache.record(key, InheritanceVerdict::Inherited),
            | result @ (Production::Plain { .. }
            | Production::WorkBoundExceeded { .. }
            | Production::SchemaWorkBound { .. }) => {
                panic!("unexpected refusal: {result:?}")
            },
        }
    };
    let honest = family.first().unwrap();
    assert_eq!(
        template.admit(&arena, honest.source, &mut Budget(100_000)),
        Ok(())
    );
    let bad = family.last().unwrap();
    assert_eq!(
        template.admit(&arena, bad.source, &mut Budget(100_000)),
        Err(StageError::InvalidCertificate)
    );
    assert_eq!(
        replay_equation(&mut arena, *bad, &mut Budget(100_000)),
        Err(StageError::InvalidCertificate)
    );
}

#[test]
fn peak_choices_are_correlated()
{
    let (mut arena, family) = cancellations(Members(64), Arms(2));
    let Production::Go(template) = produce(
        &arena,
        &family,
        PriceGate::Unmemoized,
        &mut InheritanceCache::new(),
        &mut Budget(1_000_000),
    )
    .unwrap()
    else {
        panic!("paying family");
    };
    let foreign = arena
        .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(99)))
        .unwrap();
    let quote = arena.alloc(Term::Quote(foreign)).unwrap();
    let source = arena.alloc(Term::Splice(quote)).unwrap();
    assert!(matches!(
        template.peak_substitution(&arena, source),
        Err(StageError::InvalidCertificate)
    ));
    assert!(matches!(
        template.instantiate(&Substitution(BTreeMap::new())),
        Err(StageError::InvalidCertificate)
    ));
    let mut family = Vec::new();
    for member in 0_usize .. 64 {
        let body = arena
            .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(member & 1)))
            .unwrap();
        let product = arena.alloc(Term::Multiply(body, body)).unwrap();
        let quote = arena.alloc(Term::Quote(product)).unwrap();
        let source = arena.alloc(Term::Splice(quote)).unwrap();
        family.push(Step {
            source,
            target: product,
            rule: Rule::SpliceQuote,
        });
    }
    let Production::Go(template) = produce(
        &arena,
        &family,
        PriceGate::Unmemoized,
        &mut InheritanceCache::new(),
        &mut Budget(1_000_000),
    )
    .unwrap()
    else {
        panic!("paying correlated family");
    };
    let zero = arena
        .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(0)))
        .unwrap();
    let one = arena
        .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(1)))
        .unwrap();
    let mixed = arena.alloc(Term::Multiply(zero, one)).unwrap();
    let quote = arena.alloc(Term::Quote(mixed)).unwrap();
    let source = arena.alloc(Term::Splice(quote)).unwrap();
    assert!(matches!(
        template.peak_substitution(&arena, source),
        Err(StageError::InvalidCertificate)
    ));
}

#[test]
fn families_keep_programs_and_decisions_separate()
{
    let (arena, mut steps) = cancellations(Members(8), Arms(2));
    let mut other = *steps.first().unwrap();
    other.rule = Rule::QuoteSplice;
    steps.push(other);
    let certificate = Certificate {
        source: other.source,
        target: other.target,
        steps,
    };
    let first = harvest(&arena, ProgramId(4), core::slice::from_ref(&certificate)).unwrap();
    let second = harvest(&arena, ProgramId(5), core::slice::from_ref(&certificate)).unwrap();
    assert_eq!(
        first
            .iter()
            .map(|family| family.members.len())
            .collect::<Vec<_>>(),
        [8, 1]
    );
    assert_eq!(
        first
            .iter()
            .flat_map(|family| &family.members)
            .copied()
            .collect::<Vec<_>>(),
        certificate.steps
    );
    assert!(first.iter().all(|family| family.program == ProgramId(4)));
    assert!(second.iter().all(|family| family.program == ProgramId(5)));
}

#[test]
fn cache_keys_include_classifier_content()
{
    let mut cache = InheritanceCache::new();
    for stage in [Stage::Outer, Stage::Inner(Model(0))] {
        let mut arena = Arena::default();
        let domain = arena.alloc_type(Type::Nat(stage)).unwrap();
        let argument = arena.alloc(Term::Variable(Index(0))).unwrap();
        let lambda = arena.alloc(Term::Lambda(domain, argument)).unwrap();
        let source = arena.alloc(Term::Apply(lambda, argument)).unwrap();
        let family = alloc::vec![Step { source, target: argument, rule: Rule::Beta }; 64];
        let production = produce(
            &arena,
            &family,
            PriceGate::Unmemoized,
            &mut cache,
            &mut Budget(100_000),
        )
        .unwrap();
        assert!(matches!(production, Production::Go(_)));
        assert_eq!(usize::from(production.cost().triples_checked), 1);
    }
    assert_eq!(usize::from(cache.distinct_triples()), 2);
}

#[test]
fn skolems_are_fresh_and_pairwise_distinct()
{
    let mut arena = Arena::default();
    let ty = arena.alloc_type(Type::In(Model(usize::MAX))).unwrap();
    let rigid = arena.alloc(Term::Code(ty)).unwrap();
    let mut graph = Graph::default();
    let mut roots = graph.import(&arena, &[rigid]).unwrap();
    for point in 0 .. 2 {
        roots.push(
            graph
                .intern(Node {
                    head: Head::Point(EntryIndex::from(point)),
                    children: Children([None; 3]),
                })
                .unwrap(),
        );
    }
    let mut exported = Arena::default();
    let roots = graph
        .export(&mut exported, &roots, &BTreeMap::new())
        .unwrap();
    let mut models = BTreeSet::new();
    for root in roots {
        let Term::Code(ty) = exported.term(root).unwrap()
        else {
            panic!("opaque code");
        };
        let Type::In(model) = exported.ty(ty).unwrap()
        else {
            panic!("model-token code");
        };
        assert!(models.insert(model), "every constant must be distinct");
    }
    assert_eq!(
        models,
        BTreeSet::from([
            Model(usize::MAX),
            Model(usize::MAX.checked_sub(1).unwrap()),
            Model(usize::MAX.checked_sub(2).unwrap())
        ])
    );
}

#[test]
fn independent_points_are_checked_with_other_points_rigid()
{
    let mut arena = Arena::default();
    let nat = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let identity = arena.alloc(Term::Lambda(nat, variable)).unwrap();
    let mut family = Vec::new();
    for member in 0_usize .. 64 {
        let initial = arena
            .alloc(Term::Natural(Stage::Outer, Natural(member & 1)))
            .unwrap();
        let argument = arena
            .alloc(Term::Natural(Stage::Outer, Natural((member >> 1) & 1)))
            .unwrap();
        let body = arena
            .alloc(Term::Iterate(variable, initial, identity))
            .unwrap();
        let lambda = arena.alloc(Term::Lambda(nat, body)).unwrap();
        let source = arena.alloc(Term::Apply(lambda, argument)).unwrap();
        let target = arena
            .alloc(Term::Iterate(argument, initial, identity))
            .unwrap();
        family.push(Step {
            source,
            target,
            rule: Rule::Beta,
        });
    }
    let mut cache = InheritanceCache::new();
    let production = produce(
        &arena,
        &family,
        PriceGate::Unmemoized,
        &mut cache,
        &mut Budget(1_000_000),
    )
    .unwrap();
    assert_eq!(usize::from(production.cost().triples_checked), 4);
    assert_eq!(usize::from(production.cost().cache_hits), 124);
    let Production::Go(template) = production
    else {
        panic!("independent points inherit");
    };
    for step in family {
        let certificate = Certificate {
            source: step.source,
            target: step.target,
            steps: Vec::from([step]),
        };
        let plain =
            gandr_kernel_core::stage::replay(&mut arena, &[], &certificate, &mut Budget(100_000));
        assert_eq!(plain, Ok(nat));
        assert_eq!(
            template.admit(&arena, step.source, &mut Budget(100_000)),
            plain.map(|_| ())
        );
    }
}

/// Literal-count probes; each target records the proposed predecessor
/// explicitly.
///
/// # Specification
/// - ensures: repeats the supplied outer or inner numeral pairs without
///   deriving their relation in the fixture; ordinary replay supplies the
///   positive oracle.
/// - panics: fixture allocation failure or an empty pair set.
///
/// # Adequacy
/// - hypothesis: L2/L3 — wrong offsets, zero and inner numerals distinguish the
///   producer's one allowed relation from arbitrary numeric generalization.
/// - witness: `template::tests::outer_predecessors_share_one_peak_point_and_replay`
/// - witness: `template::tests::predecessor_discovery_refuses_zero_inner_and_other_offsets`
#[spec(requires: !pairs.is_empty(), ensures: |output| output.1.len() == members.0)]
fn numeral_successors(
    stage: Stage,
    pairs: &[(Natural, Natural)],
    members: Members,
) -> (Arena, Vec<Step>)
{
    let mut arena = Arena::default();
    let nat = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let identity = arena.alloc(Term::Lambda(nat, variable)).unwrap();
    let initial = arena
        .alloc(Term::Natural(Stage::Outer, Natural(0)))
        .unwrap();
    let mut family = Vec::with_capacity(members.0);
    for index in 0 .. members.0 {
        let (source_count, target_count) = pairs[index.checked_rem(pairs.len()).unwrap()];
        let source_count = arena.alloc(Term::Natural(stage, source_count)).unwrap();
        let target_count = arena.alloc(Term::Natural(stage, target_count)).unwrap();
        let source = arena
            .alloc(Term::Iterate(source_count, initial, identity))
            .unwrap();
        let recursive = arena
            .alloc(Term::Iterate(target_count, initial, identity))
            .unwrap();
        let target = arena.alloc(Term::Apply(identity, recursive)).unwrap();
        family.push(Step {
            source,
            target,
            rule: Rule::IterateSuccessor,
        });
    }
    (arena, family)
}

#[test]
fn outer_predecessors_share_one_peak_point_and_replay()
{
    let pairs: Vec<_> = (1 ..= 8).map(|n| (Natural(n), Natural(n - 1))).collect();
    let (mut arena, family) = numeral_successors(Stage::Outer, &pairs, Members(36));
    let Analysis::Candidate(candidate) = analyze(&arena, &family).unwrap()
    else {
        panic!("uniform family");
    };
    assert_eq!(candidate.points().count(), 1);
    assert_eq!(usize::from(candidate.prices().triples), 8);
    assert!(candidate.prices().unmemoized.is_err());
    assert!(candidate.prices().memoized.is_ok());
    let mut cache = InheritanceCache::new();
    let Production::Go(template) = candidate
        .produce(PriceGate::Memoized, &mut cache, &mut Budget(100_000))
        .unwrap()
    else {
        panic!("the numeral family inherits");
    };
    assert_eq!(usize::from(cache.checked()), 8);
    assert_eq!(usize::from(cache.hits()), 28);
    for step in &family {
        let certificate = Certificate {
            source: step.source,
            target: step.target,
            steps: Vec::from([*step]),
        };
        let plain =
            gandr_kernel_core::stage::replay(&mut arena, &[], &certificate, &mut Budget(100_000));
        assert!(plain.is_ok());
        assert_eq!(
            template.admit(&arena, step.source, &mut Budget(100_000)),
            plain.map(|_| ())
        );
        let substitution = template.peak_substitution(&arena, step.source).unwrap();
        let (projected, projected_step) = template.instantiate(&substitution).unwrap();
        let mut actual_graph = Graph::default();
        let actual_roots = actual_graph
            .import(&arena, &[step.source, step.target])
            .unwrap();
        let mut projected_graph = Graph::default();
        let projected_roots = projected_graph
            .import(&projected, &[projected_step.source, projected_step.target])
            .unwrap();
        for (a, b) in actual_roots.into_iter().zip(projected_roots) {
            actual_graph.compare(a, &projected_graph, b).unwrap();
        }
    }
}

#[test]
fn predecessor_discovery_refuses_zero_inner_and_other_offsets()
{
    let inner: Vec<_> = (1 ..= 8).map(|n| (Natural(n), Natural(n - 1))).collect();
    let zero: Vec<_> = (0_usize .. 8)
        .map(|n| (Natural(n), Natural(n.saturating_sub(1))))
        .collect();
    let offset: Vec<_> = (2 ..= 9).map(|n| (Natural(n), Natural(n - 2))).collect();
    let mut mixed = inner.clone();
    mixed.last_mut().unwrap().1 = Natural(6);
    for (stage, pairs) in [
        (Stage::Inner(Model(0)), inner),
        (Stage::Outer, zero),
        (Stage::Outer, offset),
        (Stage::Outer, mixed),
    ] {
        let (arena, family) = numeral_successors(stage, &pairs, Members(64));
        let mut cache = InheritanceCache::new();
        let produced = produce(
            &arena,
            &family,
            PriceGate::Memoized,
            &mut cache,
            &mut Budget(100_000),
        )
        .unwrap();
        assert!(matches!(produced, Production::Plain {
            reason: TemplateRefusal::EntryOutsidePeak { .. },
            ..
        }));
        assert_eq!(usize::from(cache.checked()), 0);
    }
}

#[test]
fn memoized_checks_respect_the_priced_allowance()
{
    let mut arena = Arena::default();
    let nat = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let identity = arena.alloc(Term::Lambda(nat, variable)).unwrap();
    let argument = arena
        .alloc(Term::Natural(Stage::Outer, Natural(9)))
        .unwrap();
    let source = arena.alloc(Term::Apply(identity, argument)).unwrap();
    let family = alloc::vec![Step { source, target: argument, rule: Rule::Beta }; 64];
    let Analysis::Candidate(candidate) = analyze(&arena, &family).unwrap()
    else {
        panic!("uniform ground family");
    };
    let cap = usize::from(candidate.prices().check_bound);
    assert_eq!(usize::from(candidate.prices().triples), 1);
    assert!(candidate.prices().memoized.is_ok());
    let mut cache = InheritanceCache::new();
    let mut budget = Budget(100_000);
    let produced = candidate
        .produce(PriceGate::Memoized, &mut cache, &mut budget)
        .unwrap();
    assert!(matches!(produced, Production::WorkBoundExceeded { .. }));
    assert_eq!(100_000 - budget.0, cap);
    assert_eq!(usize::from(cache.distinct_triples()), 0);
    assert_eq!(
        produce(
            &arena,
            &family,
            PriceGate::Memoized,
            &mut cache,
            &mut Budget(0)
        )
        .unwrap_err(),
        StageError::Exhausted
    );
    let original = produce(
        &arena,
        &family,
        PriceGate::Unmemoized,
        &mut cache,
        &mut Budget(100_000),
    )
    .unwrap();
    assert!(matches!(original, Production::Go(_)));
    let cached = produce(
        &arena,
        &family,
        PriceGate::Memoized,
        &mut cache,
        &mut Budget(0),
    )
    .unwrap();
    assert!(matches!(cached, Production::Go(_)));
    assert_eq!(usize::from(cached.cost().triples_checked), 0);
}

/// Read a natural payload from the observer's actual JSON image.
///
/// # Specification
/// - ensures: retains the exact unsigned payload, without an estimated size.
/// - panics: a non-natural or machine-unrepresentable fixture payload.
///
/// # Adequacy
/// - hypothesis: L2 — kernel replay and original-syntax comparison observe the
///   decoded literals, classifiers and references rather than serializer
///   echoes.
/// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
#[spec(ensures: |output| u64::try_from(output.0).ok() == value.as_u64())]
fn image_natural(value: &serde_json::Value) -> Natural
{
    Natural(usize::try_from(value.as_u64().unwrap()).unwrap())
}

/// Read the outer tag or an inner model from an image.
///
/// # Specification
/// - ensures: preserves the represented stage and model.
/// - panics: malformed fixture tags or payloads.
///
/// # Adequacy
/// - hypothesis: L2 — typed replay and source comparison reject a changed
///   stage.
/// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
#[spec(ensures: |output| matches!(output, Stage::Outer) == (value == "outer"))]
fn image_stage(value: &serde_json::Value) -> Stage
{
    if value == "outer" {
        Stage::Outer
    }
    else {
        assert_eq!(value[0], "inner");
        Stage::Inner(Model(image_natural(&value[1]).0))
    }
}

/// Independent flat-image reader used only as a semantic measurement witness.
///
/// # Specification
/// - requires: a complete equation image, entry dictionary and one guard row.
/// - ensures: rebuilds all represented syntax, selecting point arms and
///   computing only positive outer predecessors. The caller replays and
///   compares it.
/// - panics: invalid fixture schema, references, guards or predecessor
///   payloads.
///
/// # Adequacy
/// - hypothesis: L2 — ordinary replay and original-input comparison distinguish
///   omitted classifiers, stale compacted addresses and wrong member choices.
/// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
#[spec(ensures: |output| output.0.term(output.1.source).is_ok()
    && output.0.term(output.1.target).is_ok())]
fn decode_equation_image(
    equation: &serde_json::Value,
    entries: &serde_json::Value,
    choices: &serde_json::Value,
) -> (Arena, Step)
{
    let mut arena = Arena::default();
    let mut types = BTreeMap::new();
    for pair in equation["graph"][0].as_array().unwrap() {
        let body = &pair[1];
        let ty = match body[0].as_str().unwrap() {
            | "nat" => Type::Nat(image_stage(&body[1])),
            | "in" => Type::In(Model(image_natural(&body[1]).0)),
            | "universe" => Type::Universe(Model(image_natural(&body[1]).0)),
            | "arrow" => Type::Arrow(
                types[&image_natural(&body[1]).0],
                types[&image_natural(&body[2]).0],
            ),
            | "lift" => Type::Lift(types[&image_natural(&body[1]).0]),
            | tag => panic!("unexpected classifier {tag}"),
        };
        types.insert(image_natural(&pair[0]).0, arena.alloc_type(ty).unwrap());
    }
    let mut terms = Vec::new();
    for node in equation["graph"][1].as_array().unwrap() {
        let head = &node["head"];
        let tag = head.as_str().unwrap_or_else(|| head[0].as_str().unwrap());
        let child = |slot| terms[image_natural(&node["children"][slot]).0];
        if tag == "point" {
            let point = image_natural(&head[1]).0;
            let entry = entries
                .as_array()
                .unwrap()
                .iter()
                .find(|entry| image_natural(&entry[0]).0 == point)
                .unwrap();
            let arm = entry[1]
                .as_array()
                .unwrap()
                .iter()
                .find(|arm| arm[1] == choices[point])
                .unwrap();
            terms.push(terms[image_natural(&arm[0]).0]);
            continue;
        }
        let term = match tag {
            | "variable" => Term::Variable(Index(image_natural(&head[1]).0)),
            | "outer-natural" => Term::Natural(Stage::Outer, image_natural(&head[1])),
            | "inner-natural" => Term::Natural(
                Stage::Inner(Model(image_natural(&head[1]).0)),
                image_natural(&head[2]),
            ),
            | "code" => Term::Code(types[&image_natural(&head[1]).0]),
            | "lambda" => Term::Lambda(types[&image_natural(&head[1]).0], child(0)),
            | "eliminate" => Term::Eliminate(child(0), types[&image_natural(&head[1]).0]),
            | "apply" => Term::Apply(child(0), child(1)),
            | "multiply" => Term::Multiply(child(0), child(1)),
            | "quote" => Term::Quote(child(0)),
            | "splice" => Term::Splice(child(0)),
            | "iterate" => Term::Iterate(child(0), child(1), child(2)),
            | "pred" => {
                let Term::Natural(Stage::Outer, Natural(n)) = arena.term(child(0)).unwrap()
                else {
                    panic!("outer predecessor");
                };
                Term::Natural(Stage::Outer, Natural(n.checked_sub(1).unwrap()))
            },
            | name => panic!("unexpected constructor {name}"),
        };
        terms.push(arena.alloc(term).unwrap());
    }
    let rule = match equation["rule"].as_str().unwrap() {
        | "beta" => Rule::Beta,
        | "congruence" => Rule::Congruence,
        | "iterate-zero" => Rule::IterateZero,
        | "iterate-successor" => Rule::IterateSuccessor,
        | "splice-quote" => Rule::SpliceQuote,
        | "quote-splice" => Rule::QuoteSplice,
        | "eliminate" => Rule::Eliminate,
        | tag => panic!("unexpected rule {tag}"),
    };
    let step = Step {
        source: terms[image_natural(&equation["sides"][0]).0],
        target: terms[image_natural(&equation["sides"][1]).0],
        rule,
    };
    (arena, step)
}

#[test]
fn serialized_images_reconstruct_the_original_equations()
{
    let pairs: Vec<_> = (1 ..= 8).map(|n| (Natural(n), Natural(n - 1))).collect();
    let mut fixtures = Vec::from([
        (
            numeral_successors(Stage::Outer, &pairs, Members(36)),
            Model(0),
        ),
        (cancellations(Members(64), Arms(2)), Model(0)),
    ]);
    let mut arena = Arena::default();
    let token = arena.alloc_type(Type::In(Model(7))).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(Model(7)))).unwrap();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let outer_number = arena
        .alloc(Term::Natural(Stage::Outer, Natural(usize::MAX)))
        .unwrap();
    let inner_number = arena
        .alloc(Term::Natural(Stage::Inner(Model(7)), Natural(6789)))
        .unwrap();
    let code = arena.alloc(Term::Code(inner)).unwrap();
    let function = arena.alloc(Term::Lambda(inner, variable)).unwrap();
    let quoted = arena.alloc(Term::Quote(inner_number)).unwrap();
    let eliminated = arena.alloc(Term::Eliminate(inner_number, inner)).unwrap();
    let mut family = Vec::new();
    for argument in [
        outer_number,
        inner_number,
        code,
        function,
        quoted,
        eliminated,
        variable,
    ] {
        let ty =
            gandr_kernel_core::stage::infer(&mut arena, &[token], argument, &mut Budget(100_000))
                .unwrap();
        let identity = arena.alloc(Term::Lambda(ty, variable)).unwrap();
        let source = arena.alloc(Term::Apply(identity, argument)).unwrap();
        family.push(Step {
            source,
            target: argument,
            rule: Rule::Beta,
        });
    }
    fixtures.push(((arena, family), Model(7)));
    for ((mut original, family), model) in fixtures {
        let Analysis::Candidate(candidate) = analyze(&original, &family).unwrap()
        else {
            panic!("uniform image family");
        };
        let encoded = serde_json::to_vec(&candidate.image().unwrap()).unwrap();
        let image: serde_json::Value = serde_json::from_slice(&encoded).unwrap();
        let rows: Vec<serde_json::Value> = candidate
            .substitutions()
            .map(|row| {
                let bytes = serde_json::to_vec(&row).unwrap();
                serde_json::from_slice(&bytes).unwrap()
            })
            .collect();
        assert_eq!(rows.len(), family.len());
        for (step, choices) in family.iter().zip(&rows) {
            let bytes = serde_json::to_vec(&plain_image(&original, step).unwrap()).unwrap();
            let plain: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
            let empty = serde_json::json!([]);
            for (equation, entries, choices) in [
                (&image["equation"], &image["entries"], choices),
                (&plain, &empty, &empty),
            ] {
                let (mut decoded, decoded_step) = decode_equation_image(equation, entries, choices);
                assert_eq!(decoded_step.rule, step.rule);
                let token = decoded.alloc_type(Type::In(model)).unwrap();
                let certificate = Certificate {
                    source: decoded_step.source,
                    target: decoded_step.target,
                    steps: Vec::from([decoded_step]),
                };
                let classifier = gandr_kernel_core::stage::replay(
                    &mut decoded,
                    &[token],
                    &certificate,
                    &mut Budget(100_000),
                )
                .unwrap();
                let original_token = original.alloc_type(Type::In(model)).unwrap();
                let expected = gandr_kernel_core::stage::infer(
                    &mut original,
                    &[original_token],
                    step.source,
                    &mut Budget(100_000),
                )
                .unwrap();
                let mut reference = Graph::default();
                let original_code = original.alloc(Term::Code(expected)).unwrap();
                let original_roots = reference
                    .import(&original, &[step.source, step.target, original_code])
                    .unwrap();
                let mut observed = reference.member();
                let decoded_code = decoded.alloc(Term::Code(classifier)).unwrap();
                let decoded_roots = observed
                    .import(&decoded, &[
                        decoded_step.source,
                        decoded_step.target,
                        decoded_code,
                    ])
                    .unwrap();
                for (left, right) in original_roots.into_iter().zip(decoded_roots) {
                    reference.compare(left, &observed, right).unwrap();
                }
            }
        }
    }
}

#[test]
fn compressed_admission_matches_plain_families()
{
    let pairs: Vec<_> = (1_usize ..= 8)
        .map(|n| (Natural(n), Natural(n.saturating_sub(1))))
        .collect();
    let fixtures = [
        cancellations(Members(64), Arms(4)),
        numeral_successors(Stage::Outer, &pairs, Members(72)),
    ];
    for (mut arena, family) in fixtures {
        let Analysis::Candidate(candidate) = analyze(&arena, &family).unwrap()
        else {
            panic!("candidate");
        };
        let input = candidate.admission_candidate().unwrap();
        let schema =
            gandr_kernel_core::admission::Schema::check(input.proposal, &mut Budget(1_000_000))
                .unwrap();
        let consumer = schema.bind(arena.clone(), &mut Budget(1_000_000)).unwrap();
        let mut buffer = gandr_kernel_core::admission::Row::default();
        for (choices, step) in input.rows.iter().zip(&family) {
            let mut row = schema
                .substitute(schema.classifiers(), choices, &mut buffer)
                .unwrap();
            assert_eq!(
                row.admit(&consumer, *step, &mut Budget(100_000))
                    .map(|_| ()),
                replay_equation(&mut arena, *step, &mut Budget(100_000))
                    .map_err(gandr_kernel_core::admission::Refusal::from)
            );
        }
    }
}

#[test]
fn empty_and_malformed_families_preserve_refusals()
{
    let arena = Arena::default();
    for gate in [PriceGate::Unmemoized, PriceGate::Memoized] {
        let mut cache = InheritanceCache::new();
        let result = produce(&arena, &[], gate, &mut cache, &mut Budget(0)).unwrap();
        assert!(
            matches!(result, Production::Plain { reason: TemplateRefusal::EmptyFamily, cost }
            if cost == FamilyCostReport::default())
        );
        assert_eq!(usize::from(cache.checked()), 0);
    }
    let missing = TermId(0);
    let step = Step {
        source: missing,
        target: missing,
        rule: Rule::SpliceQuote,
    };
    assert!(matches!(analyze(&arena, &[step]), Err(StageError::UnknownTerm(id)) if id == missing));
    assert!(
        matches!(plain_image(&arena, &step), Err(StageError::UnknownTerm(id)) if id == missing)
    );
    let certificate = Certificate {
        source: missing,
        target: missing,
        steps: Vec::from([step]),
    };
    assert!(
        matches!(harvest(&arena, ProgramId(0), &[certificate]), Err(StageError::UnknownTerm(id)) if id == missing)
    );
    let refusing = [
        (Natural(1), Natural(0)),
        (Natural(5), Natural(4)),
        (Natural(8), Natural(6)),
    ];
    let (arena, mut family) = numeral_successors(Stage::Outer, &refusing, Members(3));
    assert!(matches!(
        analyze(&arena, &[family[0], family[2]]),
        Ok(Analysis::Refused {
            reason: TemplateRefusal::EntryOutsidePeak { .. },
            ..
        })
    ));
    let absent = TermId(usize::MAX);
    family[1].source = absent;
    assert!(matches!(analyze(&arena, &family), Err(StageError::UnknownTerm(id)) if id == absent));
}

#[test]
fn projection_rejects_missing_graph_edges_and_invalid_predecessors()
{
    let mut graph = Graph::default();
    let missing = Id(0);
    assert_eq!(graph.node(missing), Err(StageError::Unbalanced));
    assert_eq!(graph.size(missing), Err(StageError::Unbalanced));
    assert_eq!(graph.address(missing), Err(StageError::Unbalanced));
    assert_eq!(
        graph.intern(Node {
            head: Head::Quote,
            children: Children([Some(missing), None, None])
        }),
        Err(StageError::Unbalanced)
    );
    assert!(matches!(
        graph.compact(&[missing]),
        Err(StageError::Unbalanced)
    ));
    let point = graph
        .intern(Node {
            head: Head::Point(EntryIndex::from(0)),
            children: Children([None; 3]),
        })
        .unwrap();
    let predecessor = graph
        .intern(Node {
            head: Head::Predecessor,
            children: Children([Some(point), None, None]),
        })
        .unwrap();
    for (head, error) in [
        (
            Head::OuterNatural(Natural(0)),
            StageError::InvalidCertificate,
        ),
        (
            Head::InnerNatural(Model(0), Natural(3)),
            StageError::InvalidCertificate,
        ),
        (Head::Quote, StageError::Unbalanced),
    ] {
        let arm = graph
            .intern(Node {
                head,
                children: Children([None; 3]),
            })
            .unwrap();
        let bindings = BTreeMap::from([(EntryIndex::from(0), arm)]);
        assert_eq!(
            graph.export(&mut Arena::default(), &[predecessor], &bindings),
            Err(error)
        );
    }
    let code = graph
        .intern(Node {
            head: Head::Code(TypeId(0)),
            children: Children([None; 3]),
        })
        .unwrap();
    assert_eq!(
        graph.export(&mut Arena::default(), &[code], &BTreeMap::new()),
        Err(StageError::Unbalanced)
    );
}

#[test]
fn member_selection_and_complete_replay_reject_near_misses()
{
    let (mut arena, family) = cancellations(Members(64), Arms(2));
    let Production::Go(template) = produce(
        &arena,
        &family,
        PriceGate::Memoized,
        &mut InheritanceCache::new(),
        &mut Budget(100_000),
    )
    .unwrap()
    else {
        panic!("paying family")
    };
    let outside = arena
        .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(99)))
        .unwrap();
    let quote = arena.alloc(Term::Quote(outside)).unwrap();
    let source = arena.alloc(Term::Splice(quote)).unwrap();
    for source in [source, quote] {
        assert!(matches!(
            template.peak_substitution(&arena, source),
            Err(StageError::InvalidCertificate)
        ));
    }
    let external = Substitution(BTreeMap::from([(EntryIndex::from(0), Id(usize::MAX))]));
    assert!(matches!(
        template.instantiate(&external),
        Err(StageError::InvalidCertificate)
    ));
    let step = family[0];
    assert_eq!(
        template.admit(&arena, step.source, &mut Budget(0)),
        Err(StageError::Exhausted)
    );
    let token = arena.alloc_type(Type::In(Model(0))).unwrap();
    let corrupt = Certificate {
        source: step.source,
        target: outside,
        steps: Vec::from([Step {
            target: outside,
            ..step
        }]),
    };
    assert_eq!(
        readmit(
            &mut arena,
            &[token],
            &corrupt,
            &[Production::Go(template)],
            &mut Budget(100_000)
        ),
        Err(StageError::InvalidCertificate)
    );
}

#[test]
fn image_substitutions_refuse_missing_members_and_guards()
{
    let (arena, family) = cancellations(Members(8), Arms(2));
    let Analysis::Candidate(mut candidate) = analyze(&arena, &family).unwrap()
    else {
        panic!("uniform family")
    };
    candidate.arms[0].clear();
    let row = candidate.substitutions().next().unwrap();
    assert_eq!(
        serde_json::to_vec(&row).unwrap_err().classify(),
        serde_json::error::Category::Data
    );
    drop(row);
    let Analysis::Candidate(mut candidate) = analyze(&arena, &family).unwrap()
    else {
        panic!("uniform family")
    };
    candidate.entries[0].arms.clear();
    let row = candidate.substitutions().next().unwrap();
    assert_eq!(
        serde_json::to_vec(&row).unwrap_err().classify(),
        serde_json::error::Category::Data
    );
}

#[test]
fn truncation_restores_the_imported_graph()
{
    let (arena, family) = cancellations(Members(2), Arms(2));
    let mut graph = Graph::default();
    let ids = import_members(&mut graph, &arena, &family).unwrap();
    let end = graph.end();
    let observed = ids
        .iter()
        .map(|id| (graph.size(*id).unwrap(), graph.address(*id).unwrap()))
        .collect::<Vec<_>>();
    let point = Node {
        head: Head::Point(EntryIndex::from(0)),
        children: Children([None; 3]),
    };
    let dropped = graph.intern(point).unwrap();
    let address = graph.address(dropped).unwrap();
    let pattern = graph
        .intern(Node {
            head: Head::Splice,
            children: Children([Some(dropped), None, None]),
        })
        .unwrap();
    assert_eq!(dropped, end);
    graph.truncate(end);
    assert_eq!(graph.end(), end);
    assert_eq!(graph.node(pattern), Err(StageError::Unbalanced));
    for (id, &(size, address)) in ids.iter().zip(&observed) {
        assert_eq!(graph.size(*id).unwrap(), size);
        assert_eq!(graph.address(*id).unwrap(), address);
    }
    let minted = graph.intern(point).unwrap();
    assert_eq!(minted, end);
    assert_eq!(graph.node(minted), Ok(point));
    assert_eq!(usize::from(graph.size(minted).unwrap()), 1);
    assert_eq!(graph.address(minted).unwrap(), address);
    assert_eq!(graph.import(&arena, &[family[0].source]).unwrap(), [ids[0]]);
}

/// The structural cost every analysis starts from: member counts only.
///
/// # Specification
/// trivial.
fn members_only(family: &[Step]) -> FamilyCostReport
{
    FamilyCostReport {
        members: MemberCount::from(family.len()),
        plain_replayed_steps: ReplayStepCount::from(family.len()),
        ..FamilyCostReport::default()
    }
}

/// The analysis every member imported into a fresh graph yields, the probe
/// skipped.
///
/// # Specification
/// - requires: a nonempty single-rule family of arena terms.
/// - ensures: the family's own generalization, priced, its cost counting every
///   member.
/// - panics: a malformed fixture.
///
/// # Adequacy
/// - hypothesis: L2 — the fresh import is the reference the probe's reuse is
///   compared against.
/// - witness: `template::tests::staged_families_keep_their_verdicts_under_the_probe`
#[spec(
    requires: !family.is_empty(),
    ensures: |output| match output {
        Analysis::Candidate(ref candidate) => candidate.cost().members,
        Analysis::Refused { cost, .. } => cost.members,
    } == MemberCount::from(family.len()),
)]
fn fresh_analysis(
    arena: &Arena,
    family: &[Step],
) -> Analysis
{
    conclude(
        generalize_all(arena, family).unwrap(),
        family[0].rule,
        members_only(family),
    )
    .unwrap()
}

/// Compare two analyses by everything a consumer observes of them.
///
/// # Specification
/// - ensures: returns only when both refuse with one reason and cost, or both
///   are candidates with one cost, both prices and one point count.
/// - panics: on any difference.
/// - executable: none — the assertions are the comparison; a predicate would
///   repeat them.
///
/// # Adequacy
/// - hypothesis: L2 — the observer behind every probe witness comparison.
/// - witness: `template::tests::staged_families_keep_their_verdicts_under_the_probe`
fn assert_same_analysis(
    actual: &Analysis,
    expected: &Analysis,
)
{
    match (actual, expected) {
        | (&Analysis::Candidate(ref actual), &Analysis::Candidate(ref expected)) => {
            assert_eq!(actual.cost(), expected.cost());
            assert_eq!(actual.prices(), expected.prices());
            assert_eq!(actual.points().count(), expected.points().count());
        },
        | (
            &Analysis::Refused { reason, cost },
            &Analysis::Refused {
                reason: expected_reason,
                cost: expected_cost,
            },
        ) => {
            assert_eq!(reason, expected_reason);
            assert_eq!(cost, expected_cost);
        },
        | _ => panic!("one analysis refuses and the other does not"),
    }
}

/// Compare two productions by verdict, payload and cost.
///
/// # Specification
/// - ensures: returns only when both share one verdict, its payload and cost.
/// - panics: on any difference.
/// - executable: none — the assertions are the comparison; a predicate would
///   repeat them.
///
/// # Adequacy
/// - hypothesis: L2 — the observer behind the staged production comparison.
/// - witness: `template::tests::staged_families_keep_their_verdicts_under_the_probe`
fn assert_same_production(
    actual: &Production,
    expected: &Production,
)
{
    match (actual, expected) {
        | (&Production::Go(_), &Production::Go(_))
        | (&Production::SchemaWorkBound { .. }, &Production::SchemaWorkBound { .. }) => {},
        | (
            &Production::WorkBoundExceeded { bound, .. },
            &Production::WorkBoundExceeded {
                bound: expected_bound,
                ..
            },
        ) => assert_eq!(bound, expected_bound),
        | (
            &Production::Plain { reason, .. },
            &Production::Plain {
                reason: expected_reason,
                ..
            },
        ) => assert_eq!(reason, expected_reason),
        | _ => panic!("the productions' verdicts differ"),
    }
    assert_eq!(actual.cost(), expected.cost());
}

#[test]
fn outside_peak_refusals_follow_from_the_first_and_last_members()
{
    let numerals = |values: &[(usize, usize)]| {
        values
            .iter()
            .map(|&(source, target)| (Natural(source), Natural(target)))
            .collect::<Vec<_>>()
    };
    // Each family, and whether its first and last members alone refuse it.
    let families = [
        // The two are the extremes and break the predecessor relation.
        (
            numerals(&[
                (1, 0),
                (2, 1),
                (3, 2),
                (4, 3),
                (5, 4),
                (6, 5),
                (7, 6),
                (8, 6),
            ]),
            true,
        ),
        // The extremes sit inside; the two still break the relation.
        (numerals(&[(5, 4), (1, 0), (8, 7), (3, 1)]), true),
        // The two keep the relation; a member between them breaks it.
        (numerals(&[(1, 0), (5, 3), (8, 7)]), false),
        // Every member keeps the relation.
        (
            numerals(&[
                (1, 0),
                (2, 1),
                (3, 2),
                (4, 3),
                (5, 4),
                (6, 5),
                (7, 6),
                (8, 7),
            ]),
            false,
        ),
    ];
    let mut refused_by_the_rest = 0_usize;
    for (pairs, refused_by_the_two) in families {
        let (arena, family) = numeral_successors(Stage::Outer, &pairs, Members(pairs.len()));
        let ends = [family[0], *family.last().unwrap()];
        let analysis = analyze(&arena, &family).unwrap();
        let whole = generalize_all(&arena, &family).unwrap();
        match probe(&arena, &family).unwrap() {
            | Probe::Outside(entry) => {
                assert!(refused_by_the_two);
                assert!(matches!(whole.rooting, PeakRoots::Missing(_)));
                assert!(matches!(
                    analyze(&arena, &ends).unwrap(),
                    Analysis::Refused { reason: TemplateRefusal::EntryOutsidePeak { entry: own }, .. }
                        if own == entry
                ));
                assert!(matches!(
                    analysis,
                    Analysis::Refused { reason: TemplateRefusal::EntryOutsidePeak { entry: refused }, cost }
                        if refused == entry && cost == members_only(&family)
                ));
            },
            | Probe::Open { graph, .. } => {
                assert!(!refused_by_the_two);
                let mut imported = Graph::default();
                import_members(&mut imported, &arena, &ends).unwrap();
                assert_eq!(graph.end(), imported.end());
                let expected = fresh_analysis(&arena, &family);
                assert_same_analysis(&analysis, &expected);
                if let Analysis::Refused { reason, cost } = analysis {
                    assert!(matches!(reason, TemplateRefusal::EntryOutsidePeak { .. }));
                    let plain = family.iter().fold(0_usize, |sum, step| {
                        sum.checked_add(usize::from(nodes(&arena, step.source)))
                            .unwrap()
                            .checked_add(usize::from(nodes(&arena, step.target)))
                            .unwrap()
                            .checked_add(1)
                            .unwrap()
                    });
                    assert_eq!(usize::from(cost.plain_size), plain);
                    refused_by_the_rest = refused_by_the_rest.checked_add(1).unwrap();
                }
            },
        }
    }
    assert_eq!(refused_by_the_rest, 1);
}

/// A staging observer program body.
#[derive(Clone, Copy)]
enum Body
{
    /// `pow`: `x^n` by repeated multiplication, its input left free.
    Power,
    /// `double`: step `p -> <~x * ~p * ~x>` over an inner input.
    Double,
    /// `triple`: step `p -> <~x * ~p * ~x * ~x>`, the double's body edited.
    Triple,
}

/// Exponents `low ..= high`.
#[derive(Clone, Copy)]
struct Exponents
{
    /// The first exponent.
    low: Natural,
    /// The last exponent.
    high: Natural,
}

/// One program of an edit trace.
#[derive(Clone, Copy)]
enum Edition
{
    /// A staging observer body normalized at each exponent and input.
    Staged
    {
        /// The program body.
        body: Body,
        /// The exponents, ascending.
        exponents: Exponents,
        /// The inner inputs per exponent; the power program reads one free
        /// input and ignores these.
        inputs: &'static [Natural],
    },
    /// Quote/splice cancellations of inner numerals cycling over `arms`
    /// bodies, one certificate per member.
    Generated
    {
        /// The certificate count.
        members: Members,
        /// The distinct bodies.
        arms: Arms,
    },
}

/// The double's inputs.
const TWO_THREE: &[Natural] = &[Natural(2), Natural(3)];

/// `pow:0..8`: nine certificates.
const POWER_TO_EIGHT: Edition = Edition::Staged {
    body: Body::Power,
    exponents: Exponents {
        low: Natural(0),
        high: Natural(8),
    },
    inputs: &[Natural(0)],
};

/// `double:0..8` over inputs two and three: eighteen certificates.
const DOUBLE_TO_EIGHT: Edition = Edition::Staged {
    body: Body::Double,
    exponents: Exponents {
        low: Natural(0),
        high: Natural(8),
    },
    inputs: TWO_THREE,
};

/// The edition of `body` at `low ..= high` over `inputs`.
///
/// # Specification
/// trivial.
const fn staged(
    body: Body,
    low: Natural,
    high: Natural,
    inputs: &'static [Natural],
) -> Edition
{
    Edition::Staged {
        body,
        exponents: Exponents { low, high },
        inputs,
    }
}

/// The product program, `p -> <~x * ~p * ~x>`, or with `Body::Triple` the
/// input multiplied once more.
///
/// # Specification
/// - ensures: a closed outer-exponent, lifted-input program term.
/// - panics: fixture allocation failure.
///
/// # Adequacy
/// - hypothesis: L2 — normalization and ordinary replay check every certificate
///   built from it.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| arena.term(output).is_ok())]
fn product_program(
    arena: &mut Arena,
    body: Body,
) -> TermId
{
    let outer = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(Model(0)))).unwrap();
    let lifted = arena.alloc_type(Type::Lift(inner)).unwrap();
    let one = arena
        .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(1)))
        .unwrap();
    let initial = arena.alloc(Term::Quote(one)).unwrap();
    let input = arena.alloc(Term::Variable(Index(1))).unwrap();
    let input = arena.alloc(Term::Splice(input)).unwrap();
    let previous = arena.alloc(Term::Variable(Index(0))).unwrap();
    let previous = arena.alloc(Term::Splice(previous)).unwrap();
    let product = arena.alloc(Term::Multiply(input, previous)).unwrap();
    let mut product = arena.alloc(Term::Multiply(product, input)).unwrap();
    if matches!(body, Body::Triple) {
        product = arena.alloc(Term::Multiply(product, input)).unwrap();
    }
    let body = arena.alloc(Term::Quote(product)).unwrap();
    let step = arena.alloc(Term::Lambda(lifted, body)).unwrap();
    let exponent = arena.alloc(Term::Variable(Index(1))).unwrap();
    let body = arena.alloc(Term::Iterate(exponent, initial, step)).unwrap();
    let body = arena.alloc(Term::Lambda(lifted, body)).unwrap();
    arena.alloc(Term::Lambda(outer, body)).unwrap()
}

/// Normalize one edition in a fresh arena.
///
/// # Specification
/// - ensures: one certificate per exponent and input, exponents outermost, or
///   one per generated member.
/// - panics: fixture allocation or normalization failure.
///
/// # Adequacy
/// - hypothesis: L2 — the families harvested from it are compared against fresh
///   full analyses and kernel admission, which do not depend on how they were
///   built.
/// - witness: `template::tests::staged_families_keep_their_verdicts_under_the_probe`
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| output.1.len() == match edition {
    Edition::Staged { body: Body::Power, exponents, .. } =>
        exponents.high.0.saturating_sub(exponents.low.0).saturating_add(1),
    Edition::Staged { exponents, inputs, .. } =>
        exponents.high.0.saturating_sub(exponents.low.0).saturating_add(1)
            .saturating_mul(inputs.len()),
    Edition::Generated { members, .. } => members.0,
})]
fn normalized(edition: Edition) -> (Arena, Vec<Certificate>)
{
    let mut arena = Arena::default();
    let mut certificates = Vec::new();
    let (body, exponents, inputs) = match edition {
        | Edition::Generated { members, arms } => {
            for member in 0 .. members.0 {
                let value = member.checked_rem(arms.0).unwrap();
                let body = arena
                    .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(value)))
                    .unwrap();
                let quote = arena.alloc(Term::Quote(body)).unwrap();
                let source = arena.alloc(Term::Splice(quote)).unwrap();
                certificates.push(
                    gandr_core_nbe::stage::normalize(&mut arena, source, &mut Budget(100_000))
                        .unwrap(),
                );
            }
            return (arena, certificates);
        },
        | Edition::Staged {
            body,
            exponents,
            inputs,
        } => (body, exponents, inputs),
    };
    arena.alloc_type(Type::In(Model(0))).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(Model(0)))).unwrap();
    let (program, inputs) = match body {
        | Body::Power => (
            gandr_core_nbe::stage::power(&mut arena, Model(0)).unwrap(),
            &[Natural(0)][..],
        ),
        | Body::Double | Body::Triple => (product_program(&mut arena, body), inputs),
    };
    for exponent in exponents.low.0 ..= exponents.high.0 {
        for input in inputs {
            let number = arena
                .alloc(Term::Natural(Stage::Outer, Natural(exponent)))
                .unwrap();
            let source = arena.alloc(Term::Apply(program, number)).unwrap();
            let input = match body {
                | Body::Power => arena.alloc(Term::Variable(Index(0))).unwrap(),
                | Body::Double | Body::Triple => arena
                    .alloc(Term::Natural(Stage::Inner(Model(0)), *input))
                    .unwrap(),
            };
            let input = arena.alloc(Term::Quote(input)).unwrap();
            let source = arena.alloc(Term::Apply(source, input)).unwrap();
            let source = match body {
                | Body::Power => {
                    let source = arena.alloc(Term::Splice(source)).unwrap();
                    let source = arena.alloc(Term::Lambda(inner, source)).unwrap();
                    arena.alloc(Term::Quote(source)).unwrap()
                },
                | Body::Double | Body::Triple => source,
            };
            certificates.push(
                gandr_core_nbe::stage::normalize(&mut arena, source, &mut Budget(10_000_000))
                    .unwrap(),
            );
        }
    }
    (arena, certificates)
}
#[test]
fn staged_families_keep_their_verdicts_under_the_probe()
{
    let mut decided_by_the_two = 0_usize;
    for edition in [POWER_TO_EIGHT, DOUBLE_TO_EIGHT] {
        let (arena, certificates) = normalized(edition);
        for family in harvest(&arena, ProgramId(0), &certificates).unwrap() {
            let members = &family.members;
            let analysis = analyze(&arena, members).unwrap();
            let expected = fresh_analysis(&arena, members);
            if members.len() > 2
                && let Probe::Outside(_) = probe(&arena, members).unwrap()
            {
                assert!(matches!(expected, Analysis::Refused {
                    reason: TemplateRefusal::EntryOutsidePeak { .. },
                    ..
                }));
                assert!(matches!(
                    analysis,
                    Analysis::Refused { reason: TemplateRefusal::EntryOutsidePeak { .. }, cost }
                        if cost == members_only(members)
                ));
                decided_by_the_two = decided_by_the_two.checked_add(1).unwrap();
                continue;
            }
            assert_same_analysis(&analysis, &expected);
            for gate in [PriceGate::Unmemoized, PriceGate::Memoized] {
                let (Analysis::Candidate(actual), Analysis::Candidate(expected)) = (
                    analyze(&arena, members).unwrap(),
                    fresh_analysis(&arena, members),
                )
                else {
                    continue;
                };
                let actual = actual
                    .produce(gate, &mut InheritanceCache::new(), &mut Budget(10_000_000))
                    .unwrap();
                let expected = expected
                    .produce(gate, &mut InheritanceCache::new(), &mut Budget(10_000_000))
                    .unwrap();
                assert_same_production(&actual, &expected);
            }
        }
    }
    assert!(decided_by_the_two > 0);
}

/// What a product step's target is, relative to its source `a * b`.
#[derive(Clone, Copy)]
enum Target
{
    /// `b * a`.
    Swapped,
    /// `a - 1`.
    LeftPredecessor,
}

/// Unreplayed steps over products of outer numerals, cycling over `pairs`.
///
/// # Specification
/// - ensures: `members` steps under one rule, member `i` from pair `i` modulo
///   the pair count; no rule is replayed.
/// - panics: fixture allocation failure, an empty pair set or a zero left
///   numeral under `Target::LeftPredecessor`.
///
/// # Adequacy
/// - hypothesis: L2 — the drafter's walk and departure checks read only the
///   syntax these build, and the producer's own analysis of the same steps is
///   the reference they are compared with.
/// - witness: `template::tests::drafts_refuse_what_a_fresh_run_would_generalize_differently`
#[spec(requires: !pairs.is_empty(), ensures: |output| output.1.len() == members.0)]
fn products(
    pairs: &[(Natural, Natural)],
    target: Target,
    members: Members,
) -> (Arena, Vec<Step>)
{
    let mut arena = Arena::default();
    let mut family = Vec::with_capacity(members.0);
    for &(left, right) in pairs.iter().cycle().take(members.0) {
        let a = arena.alloc(Term::Natural(Stage::Outer, left)).unwrap();
        let b = arena.alloc(Term::Natural(Stage::Outer, right)).unwrap();
        let source = arena.alloc(Term::Multiply(a, b)).unwrap();
        let target = match target {
            | Target::Swapped => arena.alloc(Term::Multiply(b, a)).unwrap(),
            | Target::LeftPredecessor => {
                let below = Natural(left.0.checked_sub(1).unwrap());
                arena.alloc(Term::Natural(Stage::Outer, below)).unwrap()
            },
        };
        family.push(Step {
            source,
            target,
            rule: Rule::Congruence,
        });
    }
    (arena, family)
}

/// A candidate's generalization as a template, unpriced and unreplayed.
///
/// # Specification
/// trivial.
fn unchecked(candidate: Candidate) -> Template
{
    let Candidate {
        graph,
        entries,
        sides,
        rule,
        cost,
        ..
    } = candidate;
    Template {
        graph,
        sides,
        rule,
        entries,
        cost,
    }
}

/// Generalize product steps into an unchecked template.
///
/// # Specification
/// - ensures: the producer's own generalization of 64 members cycling over
///   `pairs`.
/// - panics: a family the producer does not generalize.
///
/// # Adequacy
/// - hypothesis: L2 — the templates the departure checks draft from are the
///   producer's, not hand-built.
/// - witness: `template::tests::drafts_refuse_what_a_fresh_run_would_generalize_differently`
#[spec(ensures: |output| !output.entries.is_empty())]
fn product_template(
    pairs: &[(Natural, Natural)],
    target: Target,
) -> Template
{
    let (arena, family) = products(pairs, target, Members(64));
    let Analysis::Candidate(candidate) = analyze(&arena, &family).unwrap()
    else {
        panic!("the producer generalizes the products");
    };
    unchecked(candidate)
}

/// Draft product steps from a template, widening without rebase, and finish
/// under the unmemoized price.
///
/// # Specification
/// - ensures: the finished draft, and the producer's own proposal for the same
///   members when it generalizes them.
/// - panics: a member the walk misses, or a malformed fixture.
///
/// # Adequacy
/// - hypothesis: L2 — each departure is built to be the only difference from
///   the template, and the ready drafts are compared with the producer's
///   proposal.
/// - witness: `template::tests::drafts_refuse_what_a_fresh_run_would_generalize_differently`
#[spec(ensures: |output| matches!(output.0, Finished::Ready(_) | Finished::Unfit(_)))]
fn product_draft(
    template: &Template,
    pairs: &[(Natural, Natural)],
    target: Target,
    members: Members,
) -> (Finished, Maybe<Proposal, TemplateRefusal>)
{
    let (arena, family) = products(pairs, target, members);
    let mut drafter = Drafter::default();
    let walk = template
        .walk(
            &arena,
            &family,
            Widening::Widened,
            Rebasing::Never,
            &mut drafter,
        )
        .unwrap();
    let Walk::Matched { template, .. } = walk
    else {
        panic!("every product member matches");
    };
    let finished = template
        .finish(
            &arena,
            &family,
            draft::Coverage::Whole,
            &mut drafter,
            PriceGate::Unmemoized,
            &mut memo::tests::Stopped,
        )
        .unwrap();
    let fresh = match analyze(&arena, &family).unwrap() {
        | Analysis::Candidate(candidate) => {
            Maybe::Present(candidate.admission_candidate().unwrap().proposal)
        },
        | Analysis::Refused { reason, .. } => Maybe::Absent(reason),
    };
    (finished, fresh)
}

#[test]
fn drafts_refuse_what_a_fresh_run_would_generalize_differently()
{
    let n = Natural;
    let swapped = product_template(&[(n(1), n(2)), (n(3), n(4))], Target::Swapped);
    // Positive controls: the template's own members draft exactly, and new
    // bodies widen it; both are the producer's own proposal.
    for pairs in [[(n(1), n(2)), (n(3), n(4))], [(n(5), n(6)), (n(7), n(8))]] {
        let (finished, fresh) = product_draft(&swapped, &pairs, Target::Swapped, Members(64));
        let (Finished::Ready(draft), Maybe::Present(fresh)) = (finished, fresh)
        else {
            panic!("a fit draft and a fresh candidate");
        };
        assert_eq!(draft.proposal, fresh);
    }
    // One body at the first point: a fresh run keeps it rigid.
    let (finished, _) = product_draft(
        &swapped,
        &[(n(1), n(2)), (n(1), n(4))],
        Target::Swapped,
        Members(64),
    );
    assert!(
        matches!(finished, Finished::Unfit(Unfit::Collapsed(point)) if usize::from(point) == 0)
    );
    // Equal bodies at both points on every member: a fresh run makes one.
    let (finished, _) = product_draft(
        &swapped,
        &[(n(5), n(5)), (n(6), n(6))],
        Target::Swapped,
        Members(64),
    );
    assert!(matches!(
        finished,
        Finished::Unfit(Unfit::Merged(first, second))
            if usize::from(first) == 0 && usize::from(second) == 1
    ));
    // Too few members to pay: the producer's price refuses the draft too.
    let (finished, fresh) = product_draft(
        &swapped,
        &[(n(1), n(2)), (n(3), n(4))],
        Target::Swapped,
        Members(4),
    );
    assert!(matches!(finished, Finished::Unfit(Unfit::DoesNotPay(_))));
    assert!(matches!(fresh, Maybe::Present(_)));
    // The target read as the left point's predecessor.
    let below = product_template(&[(n(5), n(9)), (n(7), n(2))], Target::LeftPredecessor);
    let (finished, fresh) = product_draft(
        &below,
        &[(n(5), n(9)), (n(7), n(2))],
        Target::LeftPredecessor,
        Members(64),
    );
    let (Finished::Ready(draft), Maybe::Present(fresh)) = (finished, fresh)
    else {
        panic!("a fit draft and a fresh candidate");
    };
    assert_eq!(draft.proposal, fresh);
    // The right point's body equals that predecessor on every member: a fresh
    // run reads the right point there instead.
    let (finished, _) = product_draft(
        &below,
        &[(n(5), n(4)), (n(7), n(6))],
        Target::LeftPredecessor,
        Members(64),
    );
    assert!(matches!(
        finished,
        Finished::Unfit(Unfit::Shadowed(point, other))
            if usize::from(point) == 0 && usize::from(other) == 1
    ));
    // The walk's misses.
    let mut drafter = Drafter::default();
    let mut walk = |template: &Template, pairs: &[(Natural, Natural)], widening, rule| {
        let (arena, mut family) = products(pairs, Target::Swapped, Members(2));
        for step in &mut family {
            step.rule = rule;
        }
        match template
            .walk(&arena, &family, widening, Rebasing::Allowed, &mut drafter)
            .unwrap()
        {
            | Walk::Missed(miss) => Maybe::Absent(miss),
            | Walk::Matched { kind, .. } => Maybe::Present(kind),
        }
    };
    let pairs = [(n(1), n(2)), (n(3), n(4))];
    assert_eq!(
        walk(&swapped, &pairs, Widening::Widened, Rule::QuoteSplice),
        Maybe::Absent(Miss::Rule)
    );
    assert_eq!(
        walk(&swapped, &[(n(5), n(6))], Widening::Exact, Rule::Congruence),
        Maybe::Absent(Miss::Arm)
    );
    assert_eq!(
        walk(
            &swapped,
            &[(n(5), n(6))],
            Widening::Widened,
            Rule::Congruence
        ),
        Maybe::Present(DraftKind::Widened(ArmCount(2)))
    );
    let square = product_template(&[(n(1), n(1)), (n(2), n(2))], Target::Swapped);
    assert_eq!(
        walk(&square, &pairs, Widening::Widened, Rule::Congruence),
        Maybe::Absent(Miss::Correlation)
    );
    let (mut arena, mut family) = products(&pairs, Target::Swapped, Members(2));
    let numeral = arena.alloc(Term::Natural(Stage::Outer, n(9))).unwrap();
    for step in &mut family {
        step.source = numeral;
    }
    assert!(matches!(
        swapped
            .walk(
                &arena,
                &family,
                Widening::Widened,
                Rebasing::Allowed,
                &mut Drafter::default()
            )
            .unwrap(),
        Walk::Missed(Miss::Skeleton)
    ));
}

/// An edit trace: programs normalized in order, one memo carried through.
type Trace = Vec<Edition>;

#[test]
fn drafts_equal_fresh_runs_across_the_edit_traces()
{
    let n = Natural;
    let generated = |members, arms| Edition::Generated {
        members: Members(members),
        arms: Arms(arms),
    };
    let traces: Vec<Trace> = Vec::from([
        (1 ..= 4)
            .map(|k| staged(Body::Power, n(k), n(k), &[]))
            .collect(),
        (1 ..= 4)
            .map(|k| staged(Body::Double, n(k), n(k), TWO_THREE))
            .collect(),
        (2 ..= 5)
            .map(|top| staged(Body::Power, n(0), n(top), &[]))
            .collect(),
        (2 ..= 5)
            .map(|top| staged(Body::Double, n(0), n(top), TWO_THREE))
            .collect(),
        Vec::from([
            staged(Body::Double, n(6), n(6), TWO_THREE),
            staged(Body::Double, n(6), n(6), &[
                Natural(2),
                Natural(3),
                Natural(5),
            ]),
            staged(Body::Double, n(6), n(6), &[
                Natural(2),
                Natural(3),
                Natural(5),
                Natural(7),
            ]),
        ]),
        Vec::from([
            DOUBLE_TO_EIGHT,
            staged(Body::Double, n(0), n(8), &[
                Natural(2),
                Natural(3),
                Natural(5),
            ]),
        ]),
        Vec::from([
            staged(Body::Double, n(6), n(6), TWO_THREE),
            staged(Body::Triple, n(6), n(6), TWO_THREE),
        ]),
        Vec::from([DOUBLE_TO_EIGHT, staged(Body::Triple, n(0), n(8), TWO_THREE)]),
        Vec::from([
            generated(8, 2),
            generated(64, 2),
            generated(64, 4),
            generated(64, 8),
        ]),
        Vec::from([POWER_TO_EIGHT, DOUBLE_TO_EIGHT, POWER_TO_EIGHT]),
    ]);
    let mut exact = 0_usize;
    let mut widened = 0_usize;
    let mut rebased = 0_usize;
    let mut refused = 0_usize;
    for trace in &traces {
        let mut memo = Memo::default();
        let mut cache = InheritanceCache::new();
        for edition in trace {
            let (arena, certificates) = normalized(*edition);
            for family in harvest(&arena, ProgramId(0), &certificates).unwrap() {
                let report = memo
                    .admit_family(
                        &arena,
                        &family,
                        PriceGate::Memoized,
                        &mut cache,
                        &mut Budget(100_000_000),
                        &mut memo::tests::Stopped,
                    )
                    .unwrap();
                assert!(
                    !matches!(report.drafting, Drafting::Declined(_)),
                    "a stopped clock drafts every family with a template"
                );
                if let Drafting::Refused(_) = report.drafting {
                    refused = refused.checked_add(1).unwrap();
                }
                let FamilyAdmission::Admitted { origin, .. } = report.admission
                else {
                    continue;
                };
                let Maybe::Present(held) = memo.template(&family)
                else {
                    panic!("an admitted family's template is held");
                };
                let Analysis::Candidate(fresh) = analyze(&arena, &family.members).unwrap()
                else {
                    panic!("an admitted family is a candidate");
                };
                assert_eq!(
                    held.proposal().unwrap(),
                    fresh.admission_candidate().unwrap().proposal
                );
                let Origin::Drafted(kind) = origin
                else {
                    continue;
                };
                let cost = fresh.cost();
                assert_eq!(
                    (
                        held.cost.members,
                        held.cost.plain_size,
                        held.cost.template_size
                    ),
                    (cost.members, cost.plain_size, cost.template_size)
                );
                assert!(matches!(
                    fresh
                        .produce(
                            PriceGate::Memoized,
                            &mut InheritanceCache::new(),
                            &mut Budget(100_000_000)
                        )
                        .unwrap(),
                    Production::Go(_)
                ));
                let count = match kind {
                    | DraftKind::Exact => &mut exact,
                    | DraftKind::Widened(_) => &mut widened,
                    | DraftKind::Rebased(..) => &mut rebased,
                };
                *count = count.checked_add(1).unwrap();
            }
        }
    }
    assert_eq!(refused, 0, "the kernel refuses no draft of the corpus");
    assert!(
        exact > 0 && widened > 0 && rebased > 0,
        "{exact} {widened} {rebased}"
    );
}

#[test]
fn a_kernel_refused_draft_falls_back_to_the_producer()
{
    let edition = Edition::Generated {
        members: Members(64),
        arms: Arms(2),
    };
    let mut memo = Memo::default();
    let mut cache = InheritanceCache::new();
    let mut admit = |memo: &mut Memo| {
        let (arena, certificates) = normalized(edition);
        let families = harvest(&arena, ProgramId(0), &certificates).unwrap();
        let [ref family] = *families.as_slice()
        else {
            panic!("one cancellation family");
        };
        let report = memo
            .admit_family(
                &arena,
                family,
                PriceGate::Unmemoized,
                &mut cache,
                &mut Budget(1_000_000),
                &mut memo::tests::Stopped,
            )
            .unwrap();
        let Analysis::Candidate(fresh) = analyze(&arena, &family.members).unwrap()
        else {
            panic!("two arms over 64 members generalize");
        };
        (
            family.clone(),
            report,
            fresh.admission_candidate().unwrap().proposal,
        )
    };
    let (family, first, _) = admit(&mut memo);
    assert!(matches!(first.admission, FamilyAdmission::Admitted {
        origin: Origin::Produced,
        ..
    }));
    // A held template whose join is its peak: every member's target differs
    // from the drafted one.
    let Maybe::Present(held) = memo.template(&family)
    else {
        panic!("the produced template is held");
    };
    let mut corrupted = held.clone();
    let [peak, _] = corrupted.sides;
    corrupted.sides = [peak, peak];
    memo.hold(&family, corrupted);
    let (family, second, fresh) = admit(&mut memo);
    assert!(matches!(second.drafting, Drafting::Refused(_)));
    assert!(matches!(second.admission, FamilyAdmission::Admitted {
        origin: Origin::Produced,
        ..
    }));
    let Maybe::Present(held) = memo.template(&family)
    else {
        panic!("the producer's template replaces the refused one");
    };
    assert_eq!(held.proposal().unwrap(), fresh);
}

#[test]
fn a_work_bound_family_admits_its_template_subfamily()
{
    let mut memo = Memo::default();
    let mut cache = InheritanceCache::new();
    let mut partial = 0_usize;
    // `double:0..11` is the first edition whose `beta` family the kernel
    // refuses for its work bound; `double:0..10`'s template is the one held.
    for top in [10, 11] {
        let (arena, certificates) =
            normalized(staged(Body::Double, Natural(0), Natural(top), TWO_THREE));
        for family in harvest(&arena, ProgramId(0), &certificates).unwrap() {
            let held = match memo.template(&family) {
                | Maybe::Present(template) => Maybe::Present(template.proposal().unwrap()),
                | Maybe::Absent(reason) => Maybe::Absent(reason),
            };
            let report = memo
                .admit_family(
                    &arena,
                    &family,
                    PriceGate::Memoized,
                    &mut cache,
                    &mut Budget(100_000_000),
                    &mut memo::tests::Stopped,
                )
                .unwrap();
            if let FamilyAdmission::Partial { ref members, .. } = report.admission {
                assert!(!members.is_empty() && members.len() < family.members.len());
                // The widened draft hit the same bound as the producer's own
                // proposal, and the smaller template is kept.
                assert_eq!(report.drafting, Drafting::Refused(Refusal::SchemaWorkBound));
                let Maybe::Present(kept) = memo.template(&family)
                else {
                    panic!("the template is kept");
                };
                assert_eq!(Maybe::Present(kept.proposal().unwrap()), held);
                partial = partial.checked_add(1).unwrap();
            }
        }
    }
    assert_eq!(partial, 1);
}
#[test]
fn schema_work_is_bounded_before_producer_inheritance()
{
    for (edition, bounded) in [
        (POWER_TO_EIGHT, 0),
        (DOUBLE_TO_EIGHT, 0),
        (staged(Body::Double, Natural(0), Natural(9), TWO_THREE), 0),
        (staged(Body::Double, Natural(0), Natural(10), TWO_THREE), 0),
        (staged(Body::Double, Natural(0), Natural(11), TWO_THREE), 1),
        (staged(Body::Double, Natural(0), Natural(12), TWO_THREE), 1),
        (staged(Body::Triple, Natural(0), Natural(8), TWO_THREE), 0),
        (staged(Body::Double, Natural(0), Natural(32), TWO_THREE), 2),
        (staged(Body::Power, Natural(0), Natural(32), TWO_THREE), 1),
    ] {
        let (arena, certificates) = normalized(edition);
        let mut refused = 0_usize;
        for family in harvest(&arena, ProgramId(0), &certificates).unwrap() {
            let Analysis::Candidate(candidate) = analyze(&arena, &family.members).unwrap()
            else {
                continue;
            };
            if candidate.prices().memoized.is_err() {
                continue;
            }
            let proposal = candidate.admission_candidate().unwrap().proposal;
            let expected =
                gandr_kernel_core::admission::Schema::check(proposal, &mut Budget(usize::MAX));
            let mut cache = InheritanceCache::new();
            let mut budget = Budget(1_000_000);
            let actual = candidate
                .produce(PriceGate::Memoized, &mut cache, &mut budget)
                .unwrap();
            match expected {
                | Err(Refusal::SchemaWorkBound) => {
                    assert!(matches!(actual, Production::SchemaWorkBound { .. }));
                    assert_eq!(budget.0, 1_000_000);
                    assert_eq!(usize::from(cache.checked()), 0);
                    assert_eq!(usize::from(cache.hits()), 0);
                    assert_eq!(usize::from(actual.cost().triples_checked), 0);
                    refused = refused.checked_add(1).unwrap();
                },
                | Ok(_) | Err(_) => assert!(!matches!(actual, Production::SchemaWorkBound { .. })),
            }
        }
        assert_eq!(refused, bounded);
    }
}

/// Analyze a family with every member generalized, none read from a row: the
/// first and last members imported first, then every other member in family
/// order.
///
/// # Specification
/// - requires: a nonempty single-rule family of arena terms.
/// - ensures: the probe's refusal, or the family generalized over every member
///   in the coordinates the probe's import gives, priced.
/// - panics: a malformed fixture.
///
/// # Adequacy
/// - hypothesis: L2 — the reference the distinct-member analysis is compared
///   against, field by field.
/// - witness: `template::tests::distinct_members_generalize_as_every_member`
#[spec(requires: !family.is_empty())]
fn every_member_analysis(
    arena: &Arena,
    family: &[Step],
) -> Analysis
{
    let cost = members_only(family);
    let generalization = match *family {
        | [_, ref middle @ .., _] if !middle.is_empty() => match probe(arena, family).unwrap() {
            | Probe::Outside(entry) => {
                return Analysis::Refused {
                    reason: TemplateRefusal::EntryOutsidePeak { entry },
                    cost,
                };
            },
            | Probe::Open {
                mut graph,
                first,
                last,
            } => {
                let ids = import_members(&mut graph, arena, middle).unwrap();
                let mut members = Vec::from([first]);
                members.extend_from_slice(pairs(&ids).unwrap());
                members.push(last);
                let rows = Distinct::each(MemberCount::from(members.len()));
                generalize(graph, &members, &rows).unwrap()
            },
        },
        | _ => generalize_all(arena, family).unwrap(),
    };
    conclude(generalization, family[0].rule, cost).unwrap()
}

/// Compare two candidates field by field: every graph coordinate, every point
/// and guard, every member's arms, the sides, the cost and the triples.
///
/// # Specification
/// - ensures: returns only when both candidates hold the same graph, node for
///   node, the same classifier vocabulary, entries, arm columns, sides, rule,
///   cost and triples.
/// - panics: on any difference.
/// - executable: none — the assertions are the comparison; a predicate would
///   repeat them.
///
/// # Adequacy
/// - hypothesis: L2 — the observer behind the distinct-member comparison.
/// - witness: `template::tests::distinct_members_generalize_as_every_member`
fn assert_same_candidate(
    actual: &Candidate,
    expected: &Candidate,
)
{
    assert_eq!(actual.graph.end(), expected.graph.end());
    for index in 0 .. expected.graph.end().0 {
        let id = Id(index);
        assert_eq!(actual.graph.node(id), expected.graph.node(id));
        assert_eq!(actual.graph.size(id), expected.graph.size(id));
        assert_eq!(actual.graph.address(id), expected.graph.address(id));
    }
    assert_eq!(
        actual.graph.vocabulary_address(),
        expected.graph.vocabulary_address()
    );
    assert_eq!(actual.entries.len(), expected.entries.len());
    for (actual, expected) in actual.entries.iter().zip(&expected.entries) {
        assert_eq!(actual.point, expected.point);
        assert_eq!(actual.arms, expected.arms);
    }
    assert_eq!(actual.arms, expected.arms);
    assert_eq!(actual.sides, expected.sides);
    assert_eq!(actual.rule, expected.rule);
    assert_eq!(actual.cost, expected.cost);
    assert_eq!(actual.triples, expected.triples);
}

#[test]
fn distinct_members_generalize_as_every_member()
{
    let mut families = Vec::new();
    // Three distinct predecessor pairs cycled: the last member repeats none,
    // the first, a middle member, then both kinds of repetition at once.
    let pairs = [
        (Natural(1), Natural(0)),
        (Natural(2), Natural(1)),
        (Natural(3), Natural(2)),
    ];
    for count in 3 ..= 7 {
        families.push(numeral_successors(Stage::Outer, &pairs, Members(count)));
    }
    for edition in [POWER_TO_EIGHT, DOUBLE_TO_EIGHT] {
        let (arena, certificates) = normalized(edition);
        let harvested = harvest(&arena, ProgramId(0), &certificates).unwrap();
        for family in harvested {
            families.push((arena.clone(), family.members));
        }
    }
    let mut repeated = 0_usize;
    for workload in &families {
        let (arena, family) = (&workload.0, &workload.1);
        let actual = analyze(arena, family).unwrap();
        let expected = every_member_analysis(arena, family);
        match (&actual, &expected) {
            | (&Analysis::Candidate(ref actual), &Analysis::Candidate(ref expected)) => {
                assert_same_candidate(actual, expected);
                if Distinct::of(family).firsts.len() < family.len() {
                    repeated = repeated.checked_add(1).unwrap();
                }
            },
            | (
                &Analysis::Refused { reason, cost },
                &Analysis::Refused {
                    reason: expected_reason,
                    cost: expected_cost,
                },
            ) => {
                assert_eq!(reason, expected_reason);
                assert_eq!(cost, expected_cost);
            },
            | _ => panic!("one analysis refuses and the other does not"),
        }
    }
    assert!(repeated >= 4);
}
