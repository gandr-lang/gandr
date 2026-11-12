//! The described types of a lowered module: each family the module holds
//! enters the reading at its own declaration. The reading itself is in the
//! base crate, `tests::described`.

use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueType;
use gandr_kernel_term::GroundSort;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::described::DescribedRole;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_lowering_base::fixture::grammar;
use gandr_surface_lowering_base::fixture::parsed;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

/// #6908: each described data family answers at its own declaration, and a
/// codata family written in its own observation at its kind.
#[test]
fn each_family_answers_at_its_own_declaration_6908()
{
    let source = "data Left : Type where { | L : Left oper flip : (x : Left) --> Left; rule : flip L \
                  ==> L; } data Right : Type where { | R : Right oper flop : (x : Right) --> \
                  Right; rule : flop R ==> R; } codata Spot : Type[-] where { x : Integer; next \
                  : Spot; }";
    let grammar = grammar();
    let tree = parsed(&grammar, SourceText::from(source));
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let types = module.described_types(&mut arena);
    let at = |around: &str, inner: &str| {
        let outer = source
            .find(around)
            .expect("the surrounding text is written");
        let start = source
            .get(outer ..)
            .and_then(|rest| rest.find(inner))
            .map(|offset| outer.saturating_add(offset))
            .expect("the node is written inside it");
        ByteSpan::new(
            ByteOffset::from(start),
            ByteOffset::from(start.saturating_add(inner.len())),
        )
        .unwrap()
    };
    let answer = |span: ByteSpan, role: DescribedRole| {
        types
            .entries
            .iter()
            .find(|entry| entry.span == span && entry.role == role)
            .and_then(|entry| arena.value_type(entry.ty).cloned())
    };
    let declared = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| {
                declaration.role() == Role::Declared && declaration.name().as_ref() == name
            })
            .map(LoweredDeclaration::constant)
            .expect("the family is declared")
    };
    for (family, constructor) in [("Left", "L"), ("Right", "R")] {
        let constant = declared(family);
        assert!(
            matches!(
                answer(
                    at(&alloc::format!("| {constructor}"), constructor),
                    DescribedRole::Name
                ),
                Some(ValueType::Data { declaration, .. }) if declaration == constant
            ),
            "the constant of `{family}` answers at `{family}`"
        );
    }
    assert!(
        matches!(
            answer(at("next : Spot", "Spot"), DescribedRole::Type),
            Some(ValueType::Universe {
                sort: Sort::Ground(GroundSort::Computation),
                ..
            })
        ),
        "the codata family in its own observation at its kind, `Type[-]`"
    );
}
