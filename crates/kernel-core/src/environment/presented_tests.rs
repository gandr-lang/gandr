//! The tests of `presented` that build their fixtures with the judgement: each
//! one admits through `Environment` or reads through conversion, which stand
//! above the record, so it runs in this crate.
use alloc::vec::Vec;

use gandr_kernel_core_base::fixture::presented::Letter;
use gandr_kernel_core_base::fixture::presented::base;
use gandr_kernel_core_base::fixture::presented::circle;
use gandr_kernel_core_base::fixture::presented::word;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Apartness;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RuleFault;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::TermArena;

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
    let own = staging
        .arena()
        .value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            Vec::new(),
            alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
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
        alloc::vec![variable],
    );
    let unlooped = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Unloop.tag(),
        alloc::vec![written],
    );
    let word = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Loop.tag(),
        alloc::vec![unlooped],
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
        alloc::vec![written],
    );
    let cancelled = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Unloop.tag(),
        alloc::vec![looped],
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

#[test]
fn endpoints_are_apart_by_their_normal_forms()
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let own = staging
        .arena()
        .value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            Vec::new(),
            alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
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
    let free = staging
        .arena()
        .value_type_data(ConstantIndex::from(1_usize), Vec::new());
    let staged = staging.data(
        LevelSignature::monomorphic(),
        Vec::new(),
        alloc::vec![alloc::vec![], alloc::vec![free], alloc::vec![free]],
        kind,
    );
    let _free = environment
        .add_decl(staged)
        .expect("the same table admits free");
    let mut staging = environment.stage();
    let circled = staging
        .arena()
        .value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let point = staging.arena().value_constructor(
        ConstantIndex::from(0_usize),
        circled,
        Letter::Base.tag(),
        Vec::new(),
    );
    let body = staging.arena().value_constructor(
        ConstantIndex::from(0_usize),
        circled,
        Letter::Loop.tag(),
        alloc::vec![point],
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
        Vec::new(),
    );
    let looped = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Loop.tag(),
        alloc::vec![base],
    );
    let unlooped = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Unloop.tag(),
        alloc::vec![looped],
    );
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let open = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        Letter::Loop.tag(),
        alloc::vec![variable],
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
        Vec::new(),
    );
    let free_looped = arena.value_constructor(
        ConstantIndex::from(1_usize),
        free,
        Letter::Loop.tag(),
        alloc::vec![free_base],
    );
    let free_unlooped = arena.value_constructor(
        ConstantIndex::from(1_usize),
        free,
        Letter::Unloop.tag(),
        alloc::vec![free_looped],
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
    let own = staging
        .arena()
        .value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            Vec::new(),
            alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
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
    let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
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
    let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
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
    gandr_kernel_term::FreeCells::new(sort, alloc::vec![gandr_kernel_term::FreeCell::new(
        base(),
        base()
    )])
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
        Vec::new(),
        alloc::vec![alloc::vec![]],
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
    let own = staging.arena().value_type_data(position, Vec::new());
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            Vec::new(),
            alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
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
        let own = arena.value_type_data(position, Vec::new());
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
        let at: alloc::boxed::Box<[RuleNode]> = [RuleNode::Constructor(point)].into();
        let cells = gandr_kernel_term::FreeCells::new(ConstantIndex::from(0_usize), alloc::vec![
            gandr_kernel_term::FreeCell::new(at.clone(), at)
        ]);
        let staged = staging
            .data(LevelSignature::monomorphic(), Vec::new(), table, kind)
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
        Vec::new(),
        alloc::vec![alloc::vec![], alloc::vec![]],
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
        let declared = staging
            .arena()
            .value_type_data(ConstantIndex::from(0_usize), Vec::new());
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
        let declared = staging
            .arena()
            .value_type_data(ConstantIndex::from(0_usize), Vec::new());
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
    // `Path(S, x, x)` against the words at `base`: neither endpoint spells
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
    let carrier = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let open = arena.value_variable(DeBruijnIndex::from(0_u32));
    let path = arena.value_type_path(carrier, open, open);
    let word_type = arena.value_type_data(words_at, Vec::new());
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

    // `c = λy. return here(y)` at `(y : S) → F Path(S, y, y)`, then
    // `λx. return ⟨force c x⟩` at `S → F words`: the path at an open `x`
    // reads as the words only if `x` reads as `base`, and it does not.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let carrier = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
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
    let carrier = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let word_type = arena.value_type_data(words_at, Vec::new());
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
            Presentation::new(Vec::new()).carrying(looped(ConstantIndex::from(0_usize)))
        ),
        Err(KernelError::WordsRefused(CellFault::NotMinted)),
        "words whose cancellations were dropped are not the words their cell mints"
    );
    assert_eq!(
        words(
            &mut environment,
            Presentation::new(circle().rules()[.. 1].to_vec())
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
    let unknown = gandr_kernel_term::FreeCells::new(ConstantIndex::from(0_usize), alloc::vec![
        gandr_kernel_term::FreeCell::new(
            [Letter::Loop.node(), Letter::Base.node()].into(),
            [Letter::Loop.node(), Letter::Base.node()].into(),
        )
    ]);
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
    let carrier = arena.value_type_data(sort, Vec::new());
    let point = arena.value_constructor(sort, carrier, Letter::Base.tag(), Vec::new());
    let again = arena.value_constructor(sort, carrier, Letter::Base.tag(), Vec::new());
    let open = arena.value_variable(DeBruijnIndex::from(0_u32));
    let word_type = arena.value_type_data(words_at, Vec::new());
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
        let carrier = arena.value_type_data(sort, Vec::new());
        let point = arena.value_constructor(sort, carrier, Letter::Base.tag(), Vec::new());
        arena.value_type_path(carrier, point, point)
    };
    let mut staging = environment.stage();
    let arena = staging.arena();
    let declared = path_at(arena);
    let words = arena.value_type_data(words_at, Vec::new());
    let empty = arena.value_constructor(words_at, words, ConstructorTag::from(0_usize), Vec::new());
    let letter =
        arena.value_constructor(words_at, words, ConstructorTag::from(1_usize), alloc::vec![
            empty
        ]);
    let staged = staging.def(LevelSignature::monomorphic(), declared, letter);
    let loop_at = environment
        .add_decl(staged)
        .expect("a word checks at the path of its point")
        .position();

    // The constant read back at the words' own type.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let declared = arena.value_type_data(words_at, Vec::new());
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
    let words = arena.value_type_data(words_at, Vec::new());
    let motive = arena.comp_type_returner(path);
    let empty = arena.value_constructor(words_at, words, ConstructorTag::from(0_usize), Vec::new());
    let nil = arena.computation_return(empty);
    let mut arm = |tag: usize| {
        let recursive = arena.value_variable(DeBruijnIndex::from(2_u32));
        let field = arena.value_variable(DeBruijnIndex::from(0_u32));
        let forced = arena.computation_force(recursive);
        let folded = arena.computation_application(forced, field);
        let result = arena.value_variable(DeBruijnIndex::from(0_u32));
        let rebuilt =
            arena.value_constructor(words_at, words, ConstructorTag::from(tag), alloc::vec![
                result
            ]);
        let returned = arena.computation_return(rebuilt);
        let sequenced = arena.computation_bind(folded, returned);
        arena.computation_lambda(sequenced)
    };
    let letter = arm(1);
    let inverse = arm(2);
    let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
    let case = arena.computation_data_case(argument, motive, alloc::vec![nil, letter, inverse]);
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
