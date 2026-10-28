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
        SourceText::from("world seat;\nworld operator;\n"),
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
    let module = lowered(SourceText::from("world seat;\nworld seat;\n"), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("seat")),
            LoweringRefusal::DuplicateDefinition { name, .. } if name == SurfaceName::from("seat")
        ),
        "a second world of one name is the duplicate any name declared twice is"
    );
}

/// `world w requires R ;` files the bytes of `R` beside the world, a dotted
/// path whole; a world written with none requires nothing; a requirement
/// naming no theory refuses its world at the name (#3376).
#[test]
fn a_world_s_requirement_names_its_theory_3376()
{
    let mut arena = CoreArena::new();
    let text = concat!(
        "theory Needs { sort Key : Type; }\n",
        "theory Far.Store { sort Cell : Type; }\n",
        "world near;\n",
        "world far requires Needs;\n",
        "world deep requires Far.Store;\n",
        "world lost requires Missing;\n",
    );
    let module = lowered(SourceText::from(text), &mut arena);
    let required = |name: &str| {
        let declaration = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))?;
        let Maybe::Present(span) = module.requirement(declaration)
        else {
            return None;
        };
        text.get(usize::from(span.start()) .. usize::from(span.end()))
    };
    assert_eq!(required("near"), None, "a bare world requires nothing");
    assert_eq!(required("far"), Some("Needs"), "the theory's name is filed");
    assert_eq!(
        required("deep"),
        Some("Far.Store"),
        "a dotted path is filed whole"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("lost")),
            LoweringRefusal::UnresolvedTypeHead { name, .. } if name == SurfaceName::from("Missing")
        ),
        "a requirement naming no theory refuses its world at the name: {:?}",
        refusal_of(&module, SurfaceName::from("lost"))
    );
}

#[test]
fn the_located_forms_lower_to_their_world_forms()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            r"world seat;
def opened(h : Integer at seat) -> -F Integer { leta x = h; pure x }
def held() -> -F (Integer at seat) { (hold 1) }
def moved() -> -F Integer { migrate [seat] { pure 1 } }
",
        ),
        &mut arena,
    );
    let seat = World::Declared(constant_of(&module, SurfaceName::from("seat")));

    let opened = tail_of(&arena, body_named(&module, SurfaceName::from("opened")));
    let Some(&Computation::World(WorldForm::Leta { value, body })) = arena.computation(opened)
    else {
        panic!("a `leta` opens its handle: {:?}", arena.computation(opened));
    };
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
        SourceText::from(
            r"module Pair :> #{ mobile type Mobile, type Kept, one : Mobile, two : Kept } {
  type Mobile = Integer;
  type Kept = Integer;
  def one = 1;
  def two = 2;
}
",
        ),
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
        SourceText::from(
            r"world operator;
world seat;
@[ entry((operator, seat)) ]
def entered() -> -F Integer { pure 1 }
@[ entry(operator) ]
def homed() -> -F Integer { pure 1 }
def placed() -> -F Integer { pure 1 }
",
        ),
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
