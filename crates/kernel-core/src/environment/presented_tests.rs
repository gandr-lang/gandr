//! The tests of `presented` that build their fixtures with the judgement: each
//! one admits through `Environment` or reads through conversion, which stand
//! above the record, so it runs in this crate.
use alloc::alloc::Global;
use alloc::vec::Vec;

use gandr_kernel_core_base::fixture::presented::Letter;
use gandr_kernel_core_base::fixture::presented::base;
use gandr_kernel_core_base::fixture::presented::circle;
use gandr_kernel_core_base::fixture::presented::word;
use gandr_kernel_data::SmallVec;
use gandr_kernel_data::ThinShared;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Apartness;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::PresentedRule;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RuleFault;
use gandr_kernel_term::RuleIndex;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::RuleRefusal;
use gandr_kernel_term::RuleVariable;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;

use crate::Environment;
use crate::error::KernelError;

#[test]
fn a_circle_word_normalizes_keeping_what_it_did_not_touch()
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let own = staging.arena().value_type_data(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::new(),
            SmallVec::<_, 0, Global>::from_iter([
                SmallVec::<_, 0, Global>::from_iter([]),
                SmallVec::<_, 0, Global>::from_iter([own]),
                SmallVec::<_, 0, Global>::from_iter([own]),
            ]),
            kind,
        )
        .presented(circle());
    let _admitted = environment
        .add_decl(staged)
        .expect("the circle admits with its rules");
    let presentations = crate::presented::Presentations::of(environment.entries());
    let mut cloned = environment.arena().clone();
    let arena = &mut cloned;
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let written = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Loop.tag(),
        SmallVec::<_, 0, Global>::from_iter([variable]),
    );
    let unlooped = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Unloop.tag(),
        SmallVec::<_, 0, Global>::from_iter([written]),
    );
    let word = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Loop.tag(),
        SmallVec::<_, 0, Global>::from_iter([unlooped]),
    );
    let mut fuel = RewriteFuel::from(1_000_u64);
    let normal = crate::presented::normal_form(arena, &presentations, word, &mut fuel)
        .expect("the word normalizes within its fuel");
    assert!(
        matches!(
            arena.value(normal),
            Some(gandr_kernel_term::Value::Constructor { datatype, tag, fields, .. })
                if *datatype == own && *tag == Letter::Loop.tag() && fields.as_slice() == [variable]
        ),
        "`loop(unloop(loop(x)))` is `loop(x)`: the outer `loop` rebuilt over the variable \
         it now holds, the variable kept at its own id"
    );
    assert_eq!(
        crate::presented::normal_form(arena, &presentations, normal, &mut fuel),
        Ok(normal),
        "a normal form is its own normal form"
    );
    assert_eq!(
        crate::presented::normal_form(arena, &presentations, written, &mut fuel),
        Ok(written),
        "a reduced word is its own normal form"
    );
    let looped = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Loop.tag(),
        SmallVec::<_, 0, Global>::from_iter([written]),
    );
    let cancelled = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Unloop.tag(),
        SmallVec::<_, 0, Global>::from_iter([looped]),
    );
    assert_eq!(
        crate::presented::normal_form(arena, &presentations, cancelled, &mut fuel),
        Ok(written),
        "`unloop(loop(w))` is `w` itself: a written constructor the rewriting \
         left whole keeps its id"
    );
    let free = crate::presented::Presentations::default();
    assert_eq!(
        crate::presented::normal_form(arena, &free, word, &mut fuel),
        Ok(word),
        "without the declaration's rules the word is not read"
    );
}

/// Whether a family states a result at a field.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stated
{
    /// Each constructor stands at a constant.
    Closed,
    /// One constructor more, `At(w)`, stands at its own field.
    Open,
}

/// Admit `Width`, with the constants `Bit` and `Word`, and then the family
/// `Term : Width -> Type` under `rules`.
///
/// The family holds `Low` and `High` at `Bit`, and `Zero`, `One`, `Zext(b)`
/// and `Choose(c, x, y)` at `Word`, in tag order. The field `b` and the field
/// `c` stand at `Bit`, and the fields `x` and `y` at `Word`. The answer is the
/// position of `Width`, and the admission of the family at the position after
/// it. Each use of an index is its own node of the arena.
///
/// # Specification
/// trivial.
fn widths(
    environment: &mut Environment,
    rules: Presentation,
    stated: Stated,
) -> (ConstantIndex, Result<ConstantIndex, KernelError>)
{
    let width = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let declaration = staging.data(
        LevelSignature::monomorphic(),
        SmallVec::<_, 0, Global>::new(),
        SmallVec::<_, 0, Global>::from_iter([
            SmallVec::<_, 0, Global>::new(),
            SmallVec::<_, 0, Global>::new(),
        ]),
        kind,
    );
    let _width = environment
        .add_decl(declaration)
        .expect("the two widths admit");
    let family = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let arena = staging.arena();
    let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let sort = arena.value_type_data(width, SmallVec::<_, 0, Global>::new());
    let index = |arena: &mut TermArena, tag: usize| {
        arena.value_constructor(
            width,
            sort,
            ConstructorTag::from(tag),
            SmallVec::<_, 0, Global>::new(),
        )
    };
    let at = |arena: &mut TermArena, tag: usize| {
        let index = index(arena, tag);
        arena.value_type_data(family, SmallVec::<_, 0, Global>::from_iter([index]))
    };
    let (bit, word) = (0_usize, 1_usize);
    let mut fields = SmallVec::<SmallVec<_, 0, Global>, 0, Global>::from_iter([
        SmallVec::<_, 0, Global>::new(),
        SmallVec::<_, 0, Global>::new(),
        SmallVec::<_, 0, Global>::new(),
        SmallVec::<_, 0, Global>::new(),
        SmallVec::<_, 0, Global>::from_iter([at(arena, bit)]),
        SmallVec::<_, 0, Global>::from_iter([at(arena, bit), at(arena, word), at(arena, word)]),
    ]);
    let mut results = SmallVec::<SmallVec<_, 0, Global>, 0, Global>::new();
    for tag in [bit, bit, word, word, word, word] {
        results.push(SmallVec::<_, 0, Global>::from_iter([index(arena, tag)]));
    }
    if stated == Stated::Open {
        fields.push(SmallVec::<_, 0, Global>::from_iter([sort]));
        let field = arena.value_variable(DeBruijnIndex::from(0_u32));
        results.push(SmallVec::<_, 0, Global>::from_iter([field]));
    }
    let staged = staging
        .indexed(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::new(),
            (SmallVec::<_, 0, Global>::from_iter([sort]), fields, results),
            kind,
        )
        .presented(rules);
    (
        width,
        environment
            .add_decl(staged)
            .map(|admitted| admitted.position()),
    )
}

/// - see: #8338
#[test]
fn a_rule_of_a_family_keeps_its_index_in_the_kernel_8338()
{
    let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
    let v = |ordinal: u32| RuleNode::Variable(RuleVariable::from(ordinal));
    let rule =
        |left: &[RuleNode], right: &[RuleNode]| PresentedRule::new(left.into(), right.into());
    // `Choose(High, x, y) ==> x`, `Choose(Low, x, y) ==> y` and
    // `Zext(Low) ==> Zero`.
    let kept = Presentation::new(SmallVec::<_, 0, Global>::from_iter([
        rule(&[c(5), c(1), v(0), v(1)], &[v(0)]),
        rule(&[c(5), c(0), v(0), v(1)], &[v(1)]),
        rule(&[c(4), c(0)], &[c(2)]),
    ]));
    let mut environment = Environment::new();
    let (_width, admitted) = widths(&mut environment, kept.clone(), Stated::Closed);
    assert_eq!(
        admitted,
        Ok(ConstantIndex::from(1_usize)),
        "each rule keeps the index of each node"
    );
    for (left, right, fault, why) in [
        (
            &[c(4), v(0)][..],
            &[v(0)][..],
            RuleFault::SlotMismatch,
            "`Zext(b) ==> b` moves a bit to the place of a word",
        ),
        (
            &[c(4), c(0)],
            &[c(0)],
            RuleFault::NotOwnPosition,
            "`Zext(Low) ==> Low` puts a bit where the left side is a word",
        ),
        (
            &[c(5), c(2), v(0), v(1)],
            &[v(0)],
            RuleFault::NotOwnPosition,
            "`Choose(Zero, x, y)` holds a word where a bit stands",
        ),
    ] {
        let mut environment = Environment::new();
        let rules = Presentation::new(SmallVec::<_, 0, Global>::from_iter([rule(left, right)]));
        let (_width, refused) = widths(&mut environment, rules, Stated::Closed);
        assert_eq!(
            refused,
            Err(KernelError::RuleNotPresentable(RuleRefusal {
                rule: RuleIndex::from(0_usize),
                fault,
            })),
            "{why}"
        );
    }
    let mut environment = Environment::new();
    let (_width, refused) = widths(&mut environment, kept, Stated::Open);
    assert_eq!(
        refused,
        Err(KernelError::IndexedSignature),
        "a result that stands at a field has no class, so the family presents no rule"
    );
    let mut environment = Environment::new();
    let free = Presentation::new(SmallVec::<_, 0, Global>::new());
    let (_width, admitted) = widths(&mut environment, free, Stated::Open);
    assert_eq!(
        admitted,
        Ok(ConstantIndex::from(1_usize)),
        "the same family with no rule admits as before"
    );
}

/// - see: #8338
#[test]
fn a_rewrite_in_a_family_builds_each_node_at_its_index_8338()
{
    let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
    // `Choose(High, Zero, One) ==> Zext(Low)`: the right side holds a bit below
    // its root, and the redex is a word.
    let rules = Presentation::new(SmallVec::<_, 0, Global>::from_iter([PresentedRule::new(
        [c(5), c(1), c(2), c(3)].into(),
        [c(4), c(0)].into(),
    )]));
    let mut environment = Environment::new();
    let (width, admitted) = widths(&mut environment, rules, Stated::Closed);
    let family = admitted.expect("the rule keeps the index of each node");
    let presentations = crate::presented::Presentations::of(environment.entries());
    let mut cloned = environment.arena().clone();
    let arena = &mut cloned;
    let sort = arena.value_type_data(width, SmallVec::<_, 0, Global>::new());
    let term = |arena: &mut TermArena, at: usize, tag: usize, fields: &[ValueId]| {
        let index = arena.value_constructor(
            width,
            sort,
            ConstructorTag::from(at),
            SmallVec::<_, 0, Global>::new(),
        );
        let datatype = arena.value_type_data(family, SmallVec::<_, 0, Global>::from_iter([index]));
        arena.value_constructor(
            family,
            datatype,
            ConstructorTag::from(tag),
            fields.iter().copied().collect(),
        )
    };
    let (bit, word) = (0_usize, 1_usize);
    let high = term(arena, bit, 1, &[]);
    let zero = term(arena, word, 2, &[]);
    let one = term(arena, word, 3, &[]);
    let choice = term(arena, word, 5, &[high, zero, one]);
    let mut fuel = RewriteFuel::from(1_000_u64);
    let normal = crate::presented::normal_form(arena, &presentations, choice, &mut fuel)
        .expect("the choice normalizes within its fuel");
    // The tag of a term, the tag of the index its classifier holds, and its
    // fields.
    let read = |arena: &TermArena, value: ValueId| {
        let Some(&Value::Constructor {
            datatype,
            tag,
            ref fields,
            ..
        }) = arena.value(value)
        else {
            return None;
        };
        let Some(&ValueType::Data { ref arguments, .. }) = arena.value_type(datatype)
        else {
            return None;
        };
        let Some(&Value::Constructor { tag: index, .. }) = arena.value(*arguments.last()?)
        else {
            return None;
        };
        Some((tag, index, fields.iter().copied().collect::<Vec<_>>()))
    };
    let (tag, index, fields) =
        read(arena, normal).expect("the normal form is a term of the family");
    assert_eq!(
        (tag, index, fields.len()),
        (ConstructorTag::from(4_usize), ConstructorTag::from(word), 1),
        "`Choose(High, Zero, One)` is `Zext(…)`, a word as the redex is"
    );
    let below = fields.first().copied().and_then(|field| read(arena, field));
    assert_eq!(
        below,
        Some((
            ConstructorTag::from(0_usize),
            ConstructorTag::from(bit),
            Vec::new()
        )),
        "the `Low` that the rewrite built stands at `Bit`, the index its constructor states, \
         and not at the index of the redex"
    );
}

#[test]
fn endpoints_are_apart_by_their_normal_forms()
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let own = staging.arena().value_type_data(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::new(),
            SmallVec::<_, 0, Global>::from_iter([
                SmallVec::<_, 0, Global>::from_iter([]),
                SmallVec::<_, 0, Global>::from_iter([own]),
                SmallVec::<_, 0, Global>::from_iter([own]),
            ]),
            kind,
        )
        .presented(circle());
    let _circle = environment
        .add_decl(staged)
        .expect("the circle admits with its rules");
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let free = staging.arena().value_type_data(
        ConstantIndex::from(1_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let staged = staging.data(
        LevelSignature::monomorphic(),
        SmallVec::<_, 0, Global>::new(),
        SmallVec::<_, 0, Global>::from_iter([
            SmallVec::<_, 0, Global>::from_iter([]),
            SmallVec::<_, 0, Global>::from_iter([free]),
            SmallVec::<_, 0, Global>::from_iter([free]),
        ]),
        kind,
    );
    let _free = environment
        .add_decl(staged)
        .expect("the same table admits free");
    let mut staging = environment.stage();
    let circled = staging.arena().value_type_data(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let point = staging.arena().value_constructor(
        ConstantIndex::from(0_usize),
        circled,
        Letter::Base.tag(),
        SmallVec::<_, 0, Global>::new(),
    );
    let body = staging.arena().value_constructor(
        ConstantIndex::from(0_usize),
        circled,
        Letter::Loop.tag(),
        SmallVec::<_, 0, Global>::from_iter([point]),
    );
    let staged = staging.def(LevelSignature::monomorphic(), circled, body);
    let _named = environment
        .add_decl(staged)
        .expect("a definition of `loop(base)` admits");
    let mut cloned = environment.arena().clone();
    let arena = &mut cloned;
    let base = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Base.tag(),
        SmallVec::<_, 0, Global>::new(),
    );
    let looped = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Loop.tag(),
        SmallVec::<_, 0, Global>::from_iter([base]),
    );
    let unlooped = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Unloop.tag(),
        SmallVec::<_, 0, Global>::from_iter([looped]),
    );
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let open = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Loop.tag(),
        SmallVec::<_, 0, Global>::from_iter([variable]),
    );
    let entries = environment.entries();
    let circle = ConstantIndex::from(0_usize);
    assert_eq!(
        crate::presented::apart(arena, entries, circle, (looped, base)),
        Ok(Apartness::Apart)
    );
    assert_eq!(
        crate::presented::apart(arena, entries, circle, (unlooped, base)),
        Ok(Apartness::Agree),
        "`unloop(loop(base))` is `base` by the declaration's rules"
    );
    assert_eq!(
        crate::presented::apart(arena, entries, circle, (open, base)),
        Ok(Apartness::Open)
    );
    let named = arena.value_constant(ConstantIndex::from(2_usize));
    assert_eq!(
        crate::presented::apart(arena, entries, circle, (named, base)),
        Ok(Apartness::Apart),
        "a reference to `loop(base)` is read as its definition"
    );
    let free_base = arena.value_constructor(
        ConstantIndex::from(1_usize),
        free,
        Letter::Base.tag(),
        SmallVec::<_, 0, Global>::new(),
    );
    let free_looped = arena.value_constructor(
        ConstantIndex::from(1_usize),
        free,
        Letter::Loop.tag(),
        SmallVec::<_, 0, Global>::from_iter([free_base]),
    );
    let free_unlooped = arena.value_constructor(
        ConstantIndex::from(1_usize),
        free,
        Letter::Unloop.tag(),
        SmallVec::<_, 0, Global>::from_iter([free_looped]),
    );
    assert_eq!(
        crate::presented::apart(
            arena,
            entries,
            ConstantIndex::from(1_usize),
            (free_unlooped, free_base)
        ),
        Ok(Apartness::Apart),
        "without rules nothing cancels"
    );
    assert_eq!(
        crate::presented::apart(arena, entries, ConstantIndex::from(9_usize), (base, base)),
        Err(KernelError::NotADataType {
            index: ConstantIndex::from(9_usize)
        })
    );
}

/// An environment holding the circle at position zero, its terms read by
/// `presentation`.
///
/// # Specification
/// trivial.
fn circle_environment(presentation: Presentation) -> Environment
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let own = staging.arena().value_type_data(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::new(),
            SmallVec::<_, 0, Global>::from_iter([
                SmallVec::<_, 0, Global>::from_iter([]),
                SmallVec::<_, 0, Global>::from_iter([own]),
                SmallVec::<_, 0, Global>::from_iter([own]),
            ]),
            kind,
        )
        .presented(presentation);
    let _circle = environment.add_decl(staged).expect("the circle admits");
    environment
}

/// Offer `here(loop(base))` at `Path[.A = Circle](loop(unloop(loop(base))),
/// loop(base))`, then a constant naming it at `Path[.A =
/// Circle](loop(base), loop(base))`.
///
/// # Specification
/// trivial.
fn offer(environment: &mut Environment) -> [Result<(), KernelError>; 2]
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let own = arena.value_type_data(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let written = word(arena, &[Letter::Loop, Letter::Unloop, Letter::Loop]);
    let reduced = word(arena, &[Letter::Loop]);
    let declared = arena.value_type_path(own, written, reduced);
    let point = word(arena, &[Letter::Loop]);
    let here = arena.value_here(point);
    let staged = staging.def(LevelSignature::monomorphic(), declared, here);
    let reflexivity = environment.add_decl(staged).map(|_checked| ());
    let position = ConstantIndex::from(usize::from(environment.entries().len()).saturating_sub(1));
    let mut staging = environment.stage();
    let arena = staging.arena();
    let own = arena.value_type_data(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let reduced = word(arena, &[Letter::Loop]);
    let again = word(arena, &[Letter::Loop]);
    let declared = arena.value_type_path(own, reduced, again);
    let named = arena.value_constant(position);
    let staged = staging.def(LevelSignature::monomorphic(), declared, named);
    [reflexivity, environment.add_decl(staged).map(|_checked| ())]
}

/// One loop at `base` of the sort at `sort`.
///
/// # Specification
/// trivial.
fn looped(sort: ConstantIndex) -> gandr_kernel_term::FreeCells
{
    gandr_kernel_term::FreeCells::new(
        sort,
        SmallVec::<_, 0, Global>::from_iter([gandr_kernel_term::FreeCell::new(base(), base())]),
    )
}

/// An environment holding the one-point sort `base` at position zero.
///
/// # Specification
/// trivial.
fn point() -> Environment
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let staged = staging.data(
        LevelSignature::monomorphic(),
        SmallVec::<_, 0, Global>::new(),
        SmallVec::<_, 0, Global>::from_iter([SmallVec::<_, 0, Global>::from_iter([])]),
        kind,
    );
    let _sort = environment
        .add_decl(staged)
        .expect("a one-point sort admits");
    environment
}

/// Stage the words of one loop's table, presented by `presentation`.
///
/// # Specification
/// trivial.
fn words(
    environment: &mut Environment,
    presentation: Presentation,
) -> Result<ConstantIndex, KernelError>
{
    let position = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let own = staging
        .arena()
        .value_type_data(position, SmallVec::<_, 0, Global>::new());
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::new(),
            SmallVec::<_, 0, Global>::from_iter([
                SmallVec::<_, 0, Global>::from_iter([]),
                SmallVec::<_, 0, Global>::from_iter([own]),
                SmallVec::<_, 0, Global>::from_iter([own]),
            ]),
            kind,
        )
        .presented(presentation);
    environment
        .add_decl(staged)
        .map(crate::env::CheckedId::position)
}

#[test]
fn words_refuse_another_table_and_admit_one_type_per_point()
{
    use gandr_kernel_term::CellFault;

    /// Stage the words of the loop at `point` over the table `fields`
    /// names, `None` a field of the declaration's own type.
    ///
    /// # Specification
    /// trivial.
    fn stage(
        environment: &mut Environment,
        table: &[&[Option<()>]],
        point: ConstructorTag,
    ) -> Result<ConstantIndex, KernelError>
    {
        let position = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let own = arena.value_type_data(position, SmallVec::<_, 0, Global>::new());
        let unit = arena.value_type_unit();
        let table = table
            .iter()
            .map(|fields| {
                fields
                    .iter()
                    .map(|field| field.map_or(own, |()| unit))
                    .collect()
            })
            .collect();
        let at = ThinShared::from_iter([RuleNode::Constructor(point)]);
        let cells = gandr_kernel_term::FreeCells::new(
            ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::from_iter([gandr_kernel_term::FreeCell::new(at.clone(), at)]),
        );
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                SmallVec::<_, 0, Global>::new(),
                table,
                kind,
            )
            .presented(Presentation::words(cells));
        environment
            .add_decl(staged)
            .map(crate::env::CheckedId::position)
    }

    // A sort of two points.
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let staged = staging.data(
        LevelSignature::monomorphic(),
        SmallVec::<_, 0, Global>::new(),
        SmallVec::<_, 0, Global>::from_iter([
            SmallVec::<_, 0, Global>::from_iter([]),
            SmallVec::<_, 0, Global>::from_iter([]),
        ]),
        kind,
    );
    let _sort = environment
        .add_decl(staged)
        .expect("a two-point sort admits");
    let [first, second] = [0_usize, 1_usize].map(ConstructorTag::from);
    for (table, what) in [
        (
            [&[None][..], &[None], &[None]],
            "an empty word over a field",
        ),
        (
            [&[][..], &[Some(())], &[None]],
            "a letter over another type",
        ),
    ] {
        assert_eq!(
            stage(&mut environment, &table, first),
            Err(KernelError::WordsRefused(CellFault::NotMinted)),
            "{what} is not the mint"
        );
    }
    let minted: [&[Option<()>]; 3] = [&[], &[None], &[None]];
    assert!(stage(&mut environment, &minted, first).is_ok());
    assert!(
        stage(&mut environment, &minted, second).is_ok(),
        "the same sort's other point takes its own words"
    );
    assert_eq!(
        stage(&mut environment, &minted, second),
        Err(KernelError::WordsRefused(CellFault::Twice))
    );
}

/// #6621: a type of words over a sort reaches each entry after it whose
/// support holds the sort, directly or through an entry before it. It
/// reaches no entry before it, and the sort keeps its own verdict.
#[test]
fn a_type_of_words_reaches_the_entries_after_it_through_its_sort_6621()
{
    /// Admit a definition of the sort's type whose body is `body`, or an
    /// axiom of it when `body` is nothing.
    ///
    /// # Specification
    /// trivial.
    fn element(
        environment: &mut Environment,
        body: Option<ConstantIndex>,
    ) -> ConstantIndex
    {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_data(
            ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::new(),
        );
        let staged = match body {
            Some(named) => {
                let body = staging.arena().value_constant(named);
                staging.def(LevelSignature::monomorphic(), declared, body)
            },
            None => staging.axiom(LevelSignature::monomorphic(), declared),
        };
        environment
            .add_decl(staged)
            .map(crate::env::CheckedId::position)
            .expect("an element of the sort admits")
    }

    let mut environment = point();
    let sort = ConstantIndex::from(0_usize);
    let before = element(&mut environment, None);
    let words = words(&mut environment, Presentation::words(looped(sort)))
        .expect("the words of the loop at `base` admit");
    let after = element(&mut environment, None);
    let through = element(&mut environment, Some(before));
    let mut staging = environment.stage();
    let declared = staging.arena().value_type_unit();
    let body = staging.arena().value_unit();
    let unrelated = staging.def(LevelSignature::monomorphic(), declared, body);
    let _unrelated = environment
        .add_decl(unrelated)
        .expect("a unit definition admits");
    assert_eq!(
        &*environment.reach([words]),
        &[words, after, through],
        "an entry after the words holds them through the sort, and one before them does not"
    );
    assert_eq!(
        &*environment.reach([before]),
        &[before, through],
        "the entry that names an edited one is in the reach"
    );
    assert_eq!(
        &*environment.reach([sort]),
        &[sort, before, words, after, through],
        "each entry that names the sort is in its reach, and the unrelated one is not"
    );
}

/// #3476: the check of an entry waits on each position that it names and
/// on the types of words over each of them that rank below it. An entry
/// before the words does not wait on them.
#[test]
fn a_check_waits_on_the_words_over_each_sort_it_names_3476()
{
    /// Admit an axiom of the sort's type.
    ///
    /// # Specification
    /// trivial.
    fn element(environment: &mut Environment) -> ConstantIndex
    {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_data(
            ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::new(),
        );
        let staged = staging.axiom(LevelSignature::monomorphic(), declared);
        environment
            .add_decl(staged)
            .map(crate::env::CheckedId::position)
            .expect("an element of the sort admits")
    }

    let mut environment = point();
    let sort = ConstantIndex::from(0_usize);
    let before = element(&mut environment);
    let words = words(&mut environment, Presentation::words(looped(sort)))
        .expect("the words of the loop at `base` admit");
    let after = element(&mut environment);
    let entries = environment.entries();
    assert_eq!(
        entries.waits_on(after).collect::<Vec<_>>(),
        [sort, words],
        "an entry after the words waits on the sort and on the words over it"
    );
    assert_eq!(
        entries.waits_on(before).collect::<Vec<_>>(),
        [sort],
        "an entry before the words waits on the sort alone"
    );
    assert_eq!(
        entries.waits_on(ConstantIndex::from(99_usize)).count(),
        0,
        "a position past the entries waits on nothing"
    );
}

#[test]
fn a_path_that_computes_its_point_is_set_aside_against_its_words_5099()
{
    // `Path[.A = S](x, x)` against the words at `base`: neither endpoint spells
    // the point, so the walk sets the pair aside for its reader, in either
    // order. A path over a type the words do not loop in stays apart.
    let mut environment = point();
    let words_at = words(
        &mut environment,
        Presentation::words(looped(ConstantIndex::from(0_usize))),
    )
    .expect("the loop's words admit");
    let presentations = crate::presented::Presentations::of(environment.entries());
    let mut arena = environment.arena().clone();
    let carrier = arena.value_type_data(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let open = arena.value_variable(DeBruijnIndex::from(0_u32));
    let path = arena.value_type_path(carrier, open, open);
    let word_type = arena.value_type_data(words_at, SmallVec::<_, 0, Global>::new());
    for (one, other) in [(word_type, path), (path, word_type)] {
        let mut pending = Vec::new();
        assert_eq!(
            crate::conv::pending_endpoints(
                &arena,
                &presentations,
                crate::conv::ConversionGoal::ValueType(one, other),
                &mut pending
            ),
            crate::conv::Convertibility::Convertible
        );
        assert_eq!(pending, [crate::conv::SetAside::AtPoint {
            words: words_at,
            from: open,
            to: open
        }]);
    }
    let unlooped = arena.value_type_path(word_type, open, open);
    let mut pending = Vec::new();
    assert_eq!(
        crate::conv::pending_endpoints(
            &arena,
            &presentations,
            crate::conv::ConversionGoal::ValueType(word_type, unlooped),
            &mut pending
        ),
        crate::conv::Convertibility::Distinct,
        "no cell loops in the words themselves"
    );

    // `c = λy. return here(y)` at `(y : S) → F Path[.A = S](y, y)`, then
    // `λx. return ⟨force c x⟩` at `S → F words`: the path at an open `x`
    // reads as the words only if `x` reads as `base`, and it does not.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let carrier = arena.value_type_data(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let y = arena.value_variable(DeBruijnIndex::from(0_u32));
    let at_y = arena.value_type_path(carrier, y, y);
    let returns_path = arena.comp_type_returner(at_y);
    let pi = arena.comp_type_pi(carrier, returns_path);
    let declared = arena.value_type_thunk(pi);
    let here = arena.value_here(y);
    let returned = arena.computation_return(here);
    let lambda = arena.computation_lambda(returned);
    let body = arena.value_thunk(lambda);
    let staged = staging.def(LevelSignature::monomorphic(), declared, body);
    let reflexive = environment
        .add_decl(staged)
        .expect("reflexivity at every point admits")
        .position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let carrier = arena.value_type_data(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let word_type = arena.value_type_data(words_at, SmallVec::<_, 0, Global>::new());
    let named = arena.value_constant(reflexive);
    let forced = arena.computation_force(named);
    let x = arena.value_variable(DeBruijnIndex::from(0_u32));
    let applied = arena.computation_application(forced, x);
    let path = arena.value_returned(applied);
    let returned = arena.computation_return(path);
    let lambda = arena.computation_lambda(returned);
    let body = arena.value_thunk(lambda);
    let returns_words = arena.comp_type_returner(word_type);
    let arrow = arena.comp_type_arrow(carrier, returns_words);
    let declared = arena.value_type_thunk(arrow);
    let staged = staging.def(LevelSignature::monomorphic(), declared, body);
    assert!(
        environment.add_decl(staged).is_err(),
        "a path at an open point is apart from the words at `base`"
    );
}

#[test]
fn the_forced_loop_converts_circle_words_by_their_normal_forms()
{
    let mut presented = circle_environment(circle());
    let [reflexivity, _] = offer(&mut presented);
    assert_eq!(
        reflexivity,
        Ok(()),
        "`here(loop(base))` relates the word to its normal form with no dialogue"
    );
    let mut free = circle_environment(Presentation::default());
    let [reflexivity, _] = offer(&mut free);
    assert!(
        matches!(
            reflexivity,
            Err(KernelError::Identity(
                crate::error::identity::IdentityError::EndpointsDiffer { .. }
            ))
        ),
        "the same words over a free circle are two terms: {reflexivity:?}"
    );
}

#[test]
fn a_mode_switch_reads_circle_words_by_their_normal_forms()
{
    let mut presented = circle_environment(circle());
    assert_eq!(
        offer(&mut presented),
        [Ok(()), Ok(())],
        "the constant's path type and its declared one meet once both are normal"
    );
}

#[test]
fn words_admit_only_as_their_cells_mint_them()
{
    use gandr_kernel_term::CellFault;

    let mut environment = point();
    assert_eq!(
        words(
            &mut environment,
            Presentation::new(SmallVec::new()).carrying(looped(ConstantIndex::from(0_usize)))
        ),
        Err(KernelError::WordsRefused(CellFault::NotMinted)),
        "words whose cancellations were dropped are not the words their cell mints"
    );
    assert_eq!(
        words(
            &mut environment,
            Presentation::new(circle().rules()[.. 1].iter().cloned().collect())
                .carrying(looped(ConstantIndex::from(0_usize)))
        ),
        Err(KernelError::WordsRefused(CellFault::NotMinted)),
        "nor are words with one cancellation of two"
    );
    assert_eq!(
        words(
            &mut environment,
            Presentation::words(looped(ConstantIndex::from(1_usize)))
        ),
        Err(KernelError::WordsRefused(CellFault::Sort)),
        "the sort must be admitted before the words"
    );
    let unknown = gandr_kernel_term::FreeCells::new(
        ConstantIndex::from(0_usize),
        SmallVec::<_, 0, Global>::from_iter([gandr_kernel_term::FreeCell::new(
            ThinShared::from_iter([Letter::Loop.node(), Letter::Base.node()]),
            ThinShared::from_iter([Letter::Loop.node(), Letter::Base.node()]),
        )]),
    );
    assert_eq!(
        words(&mut environment, Presentation::words(unknown)),
        Err(KernelError::WordsRefused(CellFault::Endpoint(
            RuleFault::UnknownConstructor
        ))),
        "a point the sort's table does not spell"
    );
    assert_eq!(
        words(
            &mut environment,
            Presentation::words(looped(ConstantIndex::from(0_usize)))
        ),
        Ok(ConstantIndex::from(5_usize)),
        "the words the loop at `base` mints admit, past a vacancy for each \
         refused offer before them"
    );
    assert_eq!(
        words(
            &mut environment,
            Presentation::words(looped(ConstantIndex::from(0_usize)))
        ),
        Err(KernelError::WordsRefused(CellFault::Twice)),
        "one type of words per point"
    );
}

#[test]
fn a_path_at_a_looped_point_reads_as_its_words()
{
    let mut environment = point();
    let words_at = words(
        &mut environment,
        Presentation::words(looped(ConstantIndex::from(0_usize))),
    )
    .expect("the loop's words admit");
    let sort = ConstantIndex::from(0_usize);
    let presentations = crate::presented::Presentations::of(environment.entries());
    let mut arena = environment.arena().clone();
    let carrier = arena.value_type_data(sort, SmallVec::<_, 0, Global>::new());
    let point = arena.value_constructor(
        sort,
        carrier,
        Letter::Base.tag(),
        SmallVec::<_, 0, Global>::new(),
    );
    let again = arena.value_constructor(
        sort,
        carrier,
        Letter::Base.tag(),
        SmallVec::<_, 0, Global>::new(),
    );
    let open = arena.value_variable(DeBruijnIndex::from(0_u32));
    let word_type = arena.value_type_data(words_at, SmallVec::<_, 0, Global>::new());
    assert_eq!(
        presentations.words(&arena, carrier, (point, again)),
        Some(words_at)
    );
    assert_eq!(
        presentations.words(&arena, carrier, (point, open)),
        None,
        "an endpoint that is no constructor term spells no point"
    );
    assert_eq!(
        presentations.words(&arena, word_type, (point, again)),
        None,
        "no cell loops in the words themselves"
    );
    let path = arena.value_type_path(carrier, point, again);
    let identified = presentations.identified(&mut arena, path);
    assert!(matches!(
        arena.value_type(identified),
        Some(&gandr_kernel_term::ValueType::Data { declaration, .. }) if declaration == words_at
    ));

    // `loop : Path[.A = S](base, base)`, the word of one letter.
    let path_at = |arena: &mut TermArena| {
        let carrier = arena.value_type_data(sort, SmallVec::<_, 0, Global>::new());
        let point = arena.value_constructor(
            sort,
            carrier,
            Letter::Base.tag(),
            SmallVec::<_, 0, Global>::new(),
        );
        arena.value_type_path(carrier, point, point)
    };
    let mut staging = environment.stage();
    let arena = staging.arena();
    let declared = path_at(arena);
    let words = arena.value_type_data(words_at, SmallVec::<_, 0, Global>::new());
    let empty = arena.value_constructor(
        words_at,
        words,
        ConstructorTag::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let letter = arena.value_constructor(
        words_at,
        words,
        ConstructorTag::from(1_usize),
        SmallVec::<_, 0, Global>::from_iter([empty]),
    );
    let staged = staging.def(LevelSignature::monomorphic(), declared, letter);
    let loop_at = environment
        .add_decl(staged)
        .expect("a word checks at the path of its point")
        .position();

    // The constant read back at the words' own type.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let declared = arena.value_type_data(words_at, SmallVec::<_, 0, Global>::new());
    let named = arena.value_constant(loop_at);
    let staged = staging.def(LevelSignature::monomorphic(), declared, named);
    assert!(
        environment.add_decl(staged).is_ok(),
        "a path at the looped point converts with its words at a mode switch"
    );

    // `fix f. λp. case p { here ⇒ return here; g ∷ q ⇒ r ← f(q); return
    // g ∷ r; … }` at `Path[.A = S](base, base) → F Path[.A = S](base, base)`: a
    // case over a path splits its words, and each cancellation is
    // respected.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let path = path_at(arena);
    let words = arena.value_type_data(words_at, SmallVec::<_, 0, Global>::new());
    let motive = arena.comp_type_returner(path);
    let empty = arena.value_constructor(
        words_at,
        words,
        ConstructorTag::from(0_usize),
        SmallVec::<_, 0, Global>::new(),
    );
    let nil = arena.computation_return(empty);
    let mut arm = |tag: usize| {
        let recursive = arena.value_variable(DeBruijnIndex::from(2_u32));
        let field = arena.value_variable(DeBruijnIndex::from(0_u32));
        let forced = arena.computation_force(recursive);
        let folded = arena.computation_application(forced, field);
        let result = arena.value_variable(DeBruijnIndex::from(0_u32));
        let rebuilt = arena.value_constructor(
            words_at,
            words,
            ConstructorTag::from(tag),
            SmallVec::<_, 0, Global>::from_iter([result]),
        );
        let returned = arena.computation_return(rebuilt);
        let sequenced = arena.computation_bind(folded, returned);
        arena.computation_lambda(sequenced)
    };
    let letter = arm(1);
    let inverse = arm(2);
    let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
    let case = arena.computation_data_case(
        argument,
        motive,
        SmallVec::<_, 0, Global>::from_iter([nil, letter, inverse]),
    );
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(
        lambda,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let body = arena.value_thunk(fixpoint);
    let arrow = arena.comp_type_arrow(path, motive);
    let declared = arena.value_type_thunk(arrow);
    let staged = staging.def(LevelSignature::monomorphic(), declared, body);
    assert_eq!(
        environment.add_decl(staged).map(|_admitted| ()),
        Ok(()),
        "the identity fold over the words respects both cancellations"
    );
}
