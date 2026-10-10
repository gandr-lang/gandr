//! Gate clauses over staging equations and complete producer certificates.

use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Type;

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
fn cancellations(
    members: Members,
    arms: Arms,
) -> (Arena, Vec<Step>)
{
    let mut arena = Arena::default();
    let mut family = Vec::with_capacity(members.0);
    for member in 0 .. members.0 {
        let value = member.checked_rem(arms.0).unwrap();
        let body = arena
            .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(value)))
            .unwrap();
        let quote = arena.alloc(Term::Quote(body)).unwrap();
        let source = arena.alloc(Term::Splice(quote)).unwrap();
        let certificate =
            gandr_core_nbe::stage::normalize(&mut arena, source, &mut Budget(100_000)).unwrap();
        family.extend(certificate.steps);
    }
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
                ProgramId(0),
                &family,
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
            match produced {
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
        ProgramId(0),
        &family,
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
                    family.program,
                    &family.members,
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
        matches!(produce(&arena, ProgramId(0), &family, &mut cache, &mut Budget(1_000_000)).unwrap(), Production::Plain { reason: TemplateRefusal::SkeletonDivergence { member }, .. } if usize::from(member) == 63)
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
            ProgramId(0),
            &family,
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
            ProgramId(0),
            &family,
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
        ProgramId(0),
        &family,
        &mut cache,
        &mut Budget(1_000_000),
    )
    .unwrap();
    assert!(matches!(first, Production::Go(_)));
    assert_eq!(usize::from(first.cost().triples_checked), 2);
    assert_eq!(usize::from(first.cost().cache_hits), 62);
    let second = produce(&arena, ProgramId(0), &family, &mut cache, &mut Budget(0)).unwrap();
    assert_eq!(usize::from(second.cost().triples_checked), 0);
    assert_eq!(usize::from(second.cost().cache_hits), 64);
    assert_eq!(usize::from(cache.distinct_triples()), 2);
    let other = produce(
        &arena,
        ProgramId(1),
        &family,
        &mut cache,
        &mut Budget(1_000_000),
    )
    .unwrap();
    assert_eq!(usize::from(other.cost().triples_checked), 2);
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
            ProgramId(0),
            &family,
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
            | result @ Production::Plain { .. } => panic!("unexpected refusal: {result:?}"),
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
        ProgramId(0),
        &family,
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
        ProgramId(0),
        &family,
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
            ProgramId(0),
            &family,
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
        ProgramId(0),
        &family,
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
