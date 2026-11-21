use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_core_term::world::WorldType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::error::LoweringRefusal;
use crate::fixture::hosted;
use crate::fixture::hosting;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::module::DeclarationOutcome;
use crate::module::LoweredModule;
use crate::module::Mark;
use crate::resolve::SurfaceName;

/// The admission position of the declaration `name` in `module`.
///
/// # Specification
/// trivial.
fn constant_of(
    module: &LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> ConstantIndex
{
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
    else {
        panic!("`{name}` is declared");
    };
    declaration.constant()
}

#[test]
fn a_world_declaration_names_its_world()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-world-declaration-names-its-world-module.gandr"
        )),
        &mut arena,
    );
    let outcomes: alloc::vec::Vec<_> = module
        .declarations()
        .iter()
        .map(|declaration| (declaration.name(), declaration.outcome()))
        .collect();
    assert_eq!(
        outcomes,
        [
            (SurfaceName::from("seat"), DeclarationOutcome::World),
            (SurfaceName::from("operator"), DeclarationOutcome::World),
        ],
        "each world takes a slot of its own, in source order, and lowers to no term"
    );
}

#[test]
fn a_world_declared_twice_is_refused()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-world-declared-twice-is-refused-module.gandr"
        )),
        &mut arena,
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("seat")),
            LoweringRefusal::DuplicateDefinition { name, .. } if name == SurfaceName::from("seat")
        ),
        "a second world of one name is the duplicate any name declared twice is"
    );
}

/// The effect theory a requirement row names under a label: values by key,
/// each operation handing what it reads on.
const STORE: &str = include_str!("tests/fixtures/store.gandr");

/// `world w requires [ … ] ;` files each entry of its row as a labelled row
/// writes it, and refuses its world at the first entry a row refuses: an
/// interface nothing declares, a theory under no label, a model theory, a
/// sort left unfixed and a label or an interface written twice (#3523).
#[test]
fn a_world_s_requirement_is_a_row_3523()
{
    let mut arena = CoreArena::new();
    let text = alloc::format!(
        "{STORE}{}",
        concat!(
            "theory Magma where { sort M : Type; oper mul : (x : M, y : M) --> M; }\n",
            "world near;\n",
            "world far requires [std.io.Console.Eff, store : Store with sort V = String];\n",
            "world lost requires [Missing];\n",
            "world bare requires [std.io.Console.Eff, Store with sort V = String];\n",
            "world modelled requires [m : Magma];\n",
            "world unfixed requires [store : Store];\n",
            "world twice requires [s : Store with sort V = String, s : Store with sort V = Integer];\n",
            "world doubled requires [std.io.Console.Eff, std.io.Console.Eff];\n",
        )
    );
    let text = hosting(text.as_str());
    let module = hosted(&text, &mut arena);
    let required = |name: &str| {
        let spelled = |span: gandr_surface_syntax::ByteSpan| {
            text.get(usize::from(span.start()) .. usize::from(span.end()))
        };
        let declaration = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))?;
        let Maybe::Present(entries) = module.requirement(declaration)
        else {
            return None;
        };
        entries
            .iter()
            .map(|entry| {
                let label = match entry.label {
                    Maybe::Present(span) => Some(spelled(span)?),
                    Maybe::Absent(_) => None,
                };
                Some((label, spelled(entry.interface)?, spelled(entry.written)?))
            })
            .collect::<Option<alloc::vec::Vec<_>>>()
    };
    assert_eq!(required("near"), None, "a bare world requires nothing");
    assert_eq!(
        required("far"),
        Some(alloc::vec![
            (None, "std.io.Console.Eff", "std.io.Console.Eff"),
            (Some("store"), "Store", "Store with sort V = String"),
        ]),
        "each entry is filed in written order, its label apart from its interface"
    );
    assert!(
        module.declarations().iter().any(|declaration| {
            declaration.name() == SurfaceName::from("far")
                && declaration.outcome() == DeclarationOutcome::World
        }),
        "a row of a host interface and a labelled theory at its sorts settles"
    );
    let refused = |name: &str| refusal_of(&module, SurfaceName::from(name));
    assert!(
        matches!(refused("lost"), LoweringRefusal::UnresolvedTypeHead { name, .. } if name == SurfaceName::from("Missing")),
        "an interface nothing declares: {:?}",
        refused("lost")
    );
    assert!(
        matches!(refused("bare"), LoweringRefusal::UnlabelledRequirement { name, .. } if name == SurfaceName::from("Store")),
        "a theory under no label: {:?}",
        refused("bare")
    );
    assert!(
        matches!(
            refused("modelled"),
            LoweringRefusal::UninterfacedMember { .. }
        ),
        "a model theory: {:?}",
        refused("modelled")
    );
    assert!(
        matches!(refused("unfixed"), LoweringRefusal::UninterfacedMember { name, .. } if name == SurfaceName::from("V")),
        "a value sort left unfixed: {:?}",
        refused("unfixed")
    );
    assert!(
        matches!(refused("twice"), LoweringRefusal::DuplicateDefinition { name, .. } if name == SurfaceName::from("s")),
        "a label written twice: {:?}",
        refused("twice")
    );
    assert!(
        matches!(refused("doubled"), LoweringRefusal::DuplicateDefinition { name, .. } if name == SurfaceName::from("std.io.Console.Eff")),
        "an interface named whole twice: {:?}",
        refused("doubled")
    );
}

/// A world's requirement mints its row: each interface named whole at its
/// signature, held. A world that requires nothing holds no row, and a
/// labelled entry adds nothing until its label binds an instance (#3545).
#[test]
fn a_world_s_requirement_mints_its_row_3545()
{
    let mut arena = CoreArena::new();
    let text = alloc::format!(
        "{STORE}{}",
        concat!(
            "world near;\n",
            "world far requires [std.io.Console.Eff, store : Store with sort V = String];\n",
            "world stored requires [store : Store with sort V = String];\n",
        )
    );
    let text = hosting(text.as_str());
    let module = hosted(&text, &mut arena);
    let row = |name: &str| {
        let declaration = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))?;
        match module.world_row(declaration) {
            Maybe::Present(row) => Some(row.clone()),
            Maybe::Absent(_) => None,
        }
    };
    assert_eq!(row("near"), None, "a bare world holds no row");
    assert_eq!(
        row("stored"),
        None,
        "a labelled entry adds nothing to the world's row"
    );
    let Some(far) = row("far")
    else {
        panic!("a world requiring an interface whole holds a row");
    };
    assert_eq!(
        far.signatures()
            .map(gandr_core_term::effect::EffectSig::name)
            .collect::<alloc::vec::Vec<_>>(),
        [&gandr_core_term::effect::EffectName::from(
            "std.io.Console.Eff"
        )],
        "the row holds the interface named whole and not the labelled one"
    );
    assert_eq!(
        far.regions().count(),
        0,
        "the interface is held, at no region of its own"
    );
}

/// `offers [ … ] ;` files a site's offer by its source, its host interfaces
/// and its labels with the modules answering them, a module declared after it
/// among them; an interface no host declares, a module the source does not
/// declare, an entry written twice and a second offer are each refused as
/// the offer's own, named `offers` (#3523).
#[test]
fn a_site_s_offer_answers_by_label_and_by_name_3523()
{
    let echo =
        include_str!("tests/fixtures/a-site-s-offer-answers-by-label-and-by-name-3523-echo.gandr");
    let offered = |offers: &str| {
        let text = alloc::format!(
            include_str!(
                "tests/unformatted/a-site-s-offer-answers-by-label-and-by-name-3523.gandr"
            ),
            echo = echo,
            offers = offers
        );
        let mut arena = CoreArena::new();
        let text = hosting(text.as_str());
        let module = hosted(&text, &mut arena);
        let spelled = |span: gandr_surface_syntax::ByteSpan| {
            alloc::string::String::from(
                text.get(usize::from(span.start()) .. usize::from(span.end()))
                    .unwrap_or_default(),
            )
        };
        match module.offer() {
            Maybe::Present(offer) => Ok((
                offer
                    .granted
                    .iter()
                    .map(|&span| spelled(span))
                    .collect::<alloc::vec::Vec<_>>(),
                offer
                    .answered
                    .iter()
                    .map(|label| (spelled(label.label), spelled(label.module)))
                    .collect::<alloc::vec::Vec<_>>(),
            )),
            Maybe::Absent(_) => Err(alloc::format!(
                "{:?}",
                module
                    .declarations()
                    .iter()
                    .filter(|declaration| declaration.name() == SurfaceName::from("offers"))
                    .map(crate::module::LoweredDeclaration::outcome)
                    .collect::<alloc::vec::Vec<_>>()
            )),
        }
    };
    assert_eq!(
        offered("offers [std.io.Console.Eff, store = Echo];"),
        Ok((
            alloc::vec![alloc::string::String::from("std.io.Console.Eff")],
            alloc::vec![(
                alloc::string::String::from("store"),
                alloc::string::String::from("Echo")
            )],
        )),
        "a host interface and a label answered by a module declared after the offer"
    );
    for (offers, refused) in [
        ("offers [Missing];", "UnresolvedTypeHead"),
        ("offers [store = Absent];", "UnresolvedName"),
        (
            "offers [std.io.Console.Eff, std.io.Console.Eff];",
            "DuplicateDefinition",
        ),
        (
            "offers [store = Echo, store = Echo];",
            "DuplicateDefinition",
        ),
    ] {
        let Err(outcomes) = offered(offers)
        else {
            panic!("`{offers}` is refused");
        };
        assert!(
            outcomes.contains(refused),
            "`{offers}` is refused {refused} as the offer's own: {outcomes}"
        );
    }
    let twice = offered(include_str!(
        "tests/fixtures/a-site-s-offer-answers-by-label-and-by-name-3523-twice.gandr"
    ));
    assert!(
        matches!(
            twice,
            Ok((ref granted, ref answered)) if granted.len() == 1 && answered.is_empty()
        ),
        "the first offer stands and a second is refused: {twice:?}"
    );
    // A site that imports no module of the interface it grants refuses it,
    // though its offer stands before the imports a source may write (#4523).
    let unimported = alloc::format!(
        include_str!(
            "tests/unformatted/a-site-s-offer-answers-by-label-and-by-name-3523-unimported.gandr"
        ),
        echo = echo
    );
    let mut arena = CoreArena::new();
    let module = crate::fixture::imported(&unimported, &mut arena);
    let outcomes = alloc::format!(
        "{:?}",
        module
            .declarations()
            .iter()
            .filter(|declaration| declaration.name() == SurfaceName::from("offers"))
            .map(crate::module::LoweredDeclaration::outcome)
            .collect::<alloc::vec::Vec<_>>()
    );
    assert!(
        matches!(module.offer(), Maybe::Absent(_)) && outcomes.contains("UnresolvedTypeHead"),
        "an unimported interface is refused as the offer's own: {outcomes}"
    );
}

/// An offer's label names the translation its module is read through: `via
/// f` resolves as an import's `via` does, to a flow declared before the
/// offer, with each member of the flow that does more than rename, and
/// `renaming { a as b }` keeps its pairs. A flow that does not resolve, a
/// renaming reading no member of the module, one giving a name the module
/// keeps and one giving a name twice are each refused as the offer's own
/// (#3461).
#[test]
fn an_offer_names_the_translation_it_answers_a_label_through_3461()
{
    let echo =
        include_str!("tests/fixtures/a-site-s-offer-answers-by-label-and-by-name-3523-echo.gandr");
    let flows = include_str!(
        "tests/unformatted/an-offer-names-the-translation-it-answers-a-label-through-3461-flows.gandr"
    );
    let offered = |before: &str, offers: &str, after: &str| {
        let text = alloc::format!(
            include_str!(
                "tests/unformatted/an-offer-names-the-translation-it-answers-a-label-through-3461.gandr"
            ),
            before = before,
            offers = offers,
            after = after,
            echo = echo,
        );
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(text.as_str()), &mut arena);
        let spelled = |span: gandr_surface_syntax::ByteSpan| {
            alloc::string::String::from(
                text.get(usize::from(span.start()) .. usize::from(span.end()))
                    .unwrap_or_default(),
            )
        };
        let mut members = alloc::vec::Vec::new();
        let mut renamings = alloc::vec::Vec::new();
        match module.offer() {
            Maybe::Present(offer) => Ok(offer
                .answered
                .iter()
                .map(|label| {
                    let through = match label.translation {
                        Maybe::Absent(_) => alloc::string::String::from("as it is"),
                        Maybe::Present(crate::module::OfferedTranslation::Via {
                            flow,
                            ref rewritten,
                        }) => {
                            members.clear();
                            members.extend(rewritten.iter().map(|&member| spelled(member)));
                            alloc::format!("via {} rewriting {members:?}", spelled(flow))
                        },
                        Maybe::Present(crate::module::OfferedTranslation::Renaming(ref pairs)) => {
                            renamings.clear();
                            renamings.extend(
                                pairs
                                    .iter()
                                    .map(|&(read, named)| (spelled(read), spelled(named))),
                            );
                            alloc::format!("renaming {renamings:?}")
                        },
                    };
                    alloc::format!(
                        "{} = {} {through}",
                        spelled(label.label),
                        spelled(label.module)
                    )
                })
                .collect::<alloc::vec::Vec<_>>()),
            Maybe::Absent(_) => Err(alloc::format!(
                "{:?}",
                module
                    .declarations()
                    .iter()
                    .filter(|declaration| declaration.name() == SurfaceName::from("offers"))
                    .map(crate::module::LoweredDeclaration::outcome)
                    .collect::<alloc::vec::Vec<_>>()
            )),
        }
    };
    assert_eq!(
        offered(
            flows,
            "offers [store = Echo renaming { get as fetch, V as W }, older = Replying via \
             renamed, newer = Replying via computed, kept = Echo];",
            ""
        ),
        Ok(alloc::vec![
            alloc::string::String::from(
                "store = Echo renaming [(\"get\", \"fetch\"), (\"V\", \"W\")]"
            ),
            alloc::string::String::from("older = Replying via renamed rewriting []"),
            alloc::string::String::from("newer = Replying via computed rewriting [\"tag\"]"),
            alloc::string::String::from("kept = Echo as it is"),
        ]),
        "a renaming keeps its pairs, and a flow names the members that do more than rename"
    );
    for (before, offers, after, refused) in [
        (
            "",
            "offers [older = Replying via renamed];",
            flows,
            "UnresolvedName",
        ),
        (
            flows,
            "offers [older = Replying via missing];",
            "",
            "UnresolvedName",
        ),
        (
            "",
            "offers [store = Echo renaming { lost as get }];",
            "",
            "UnknownMember",
        ),
        (
            "",
            "offers [store = Echo renaming { get as put }];",
            "",
            "DuplicateDefinition",
        ),
        (
            "",
            "offers [store = Echo renaming { get as fetch, put as fetch }];",
            "",
            "DuplicateDefinition",
        ),
    ] {
        let Err(outcomes) = offered(before, offers, after)
        else {
            panic!("`{offers}` is refused");
        };
        assert!(
            outcomes.contains(refused),
            "`{offers}` is refused {refused} as the offer's own: {outcomes}"
        );
    }
}

#[test]
fn the_located_forms_lower_to_their_world_forms()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/the-located-forms-lower-to-their-world-forms-module.gandr"
        )),
        &mut arena,
    );
    let seat = World::Declared(constant_of(&module, SurfaceName::from("seat")));

    let opened = tail_of(&arena, body_named(&module, SurfaceName::from("opened")));
    let Some(&Computation::World(WorldForm::Leta {
        world: written,
        value,
        body,
    })) = arena.computation(opened)
    else {
        panic!(
            "a `let x at w` opens its handle: {:?}",
            arena.computation(opened)
        );
    };
    assert_eq!(written, seat, "the opening writes the seat's world");
    let innermost = Value::Variable {
        zone: Zone::Intuitionistic,
        index: DeBruijnIndex::from(0_u32),
    };
    assert_eq!(
        arena.value(value),
        Some(&innermost),
        "the handle is the parameter"
    );
    let Some(&Computation::Return(returned)) = arena.computation(body)
    else {
        panic!("the rest of the block is the opening's body");
    };
    assert_eq!(
        arena.value(returned),
        Some(&innermost),
        "the body reads the opened name as its innermost variable"
    );
    let Some(DeclarationOutcome::Completed { declared_type, .. }) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("opened"))
        .map(crate::module::LoweredDeclaration::outcome)
    else {
        panic!("`opened` is signed");
    };
    let Some(&ValueType::Thunk(function)) = arena.value_type(declared_type)
    else {
        panic!("a function's type is a thunk");
    };
    let Some(&CompType::Arrow { domain, .. }) = arena.comp_type(function)
    else {
        panic!("over an arrow");
    };
    let Some(&ValueType::World(WorldType::At { inner, world })) = arena.value_type(domain)
    else {
        panic!(
            "the parameter's type is a handle: {:?}",
            arena.value_type(domain)
        );
    };
    assert_eq!(world, seat, "the handle names the declared world");
    assert!(
        matches!(arena.value_type(inner), Some(&ValueType::Base(_))),
        "the handle holds the written type"
    );

    let held = tail_of(&arena, body_named(&module, SurfaceName::from("held")));
    assert!(
        matches!(
            arena.computation(held),
            Some(&Computation::World(WorldForm::Hold { .. }))
        ),
        "a hold is the world form: {:?}",
        arena.computation(held)
    );

    let moved = tail_of(&arena, body_named(&module, SurfaceName::from("moved")));
    let Some(&Computation::World(WorldForm::Migrate { world, body })) = arena.computation(moved)
    else {
        panic!(
            "a migration is the world form: {:?}",
            arena.computation(moved)
        );
    };
    assert_eq!(world, seat, "the migration names the declared world");
    assert!(
        matches!(arena.computation(body), Some(&Computation::Return(_))),
        "the migration's block is its body"
    );
}

#[test]
fn a_world_named_where_none_is_declared_is_unresolved()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from("def lost() -> -F Integer { migrate [nowhere] { pure 1 } }\n"),
        &mut arena,
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("lost")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("nowhere")
        ),
        "a migration to a name nothing declares is refused at the name"
    );
}

#[test]
fn a_mobile_component_marks_its_sealing()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-mobile-component-marks-its-sealing-module.gandr"
        )),
        &mut arena,
    );
    let marks: alloc::vec::Vec<(SurfaceName<'_>, Mark)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| match declaration.outcome() {
            DeclarationOutcome::Abstract(sealing) => Some((declaration.name(), sealing.mark)),
            DeclarationOutcome::Completed { .. }
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_) => None,
        })
        .collect();
    assert_eq!(
        marks,
        [
            (SurfaceName::from("Mobile"), Mark::Mobile),
            (SurfaceName::from("Kept"), Mark::Unmarked),
        ],
        "the sealing carries the mark its signature writes, and only that one"
    );
}

#[test]
fn an_entry_names_its_home_then_its_capabilities()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/an-entry-names-its-home-then-its-capabilities-module.gandr"
        )),
        &mut arena,
    );
    let worlds = |name: &str| {
        let Some(declaration) = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
        else {
            panic!("`{name}` is declared");
        };
        module.worlds(declaration).to_vec()
    };
    let (operator, seat) = (
        constant_of(&module, SurfaceName::from("operator")),
        constant_of(&module, SurfaceName::from("seat")),
    );
    assert_eq!(
        worlds("entered"),
        [operator, seat],
        "an entry names its home, then the world of each capability, in written order"
    );
    assert_eq!(
        worlds("homed"),
        [operator],
        "one name is a home holding no capability"
    );
    assert!(
        worlds("placed").is_empty(),
        "an undecorated declaration names no world"
    );
}
