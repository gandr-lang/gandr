//! Bridge witnesses: modules built by hand, each declaration typed at a
//! bridge, checked by the core's bridge mode and readmitted by the kernel at
//! its bridge node, clause by clause as the kernel's
//! `element_identity::bridge_tests` read the same codes.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::Summand;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::SealExtent;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::ValueType as KernelValueType;
use gandr_kernel_term::decode;
use quenchant_shape::shape::Maybe;

use super::super::Outcome;
use super::super::Readmitted;
use super::At;
use super::Stated;
use super::declaration;
use super::interfaced_atom_module;
use super::judge_and_readmit;
use super::origin;
use crate::declaration::AbstractType;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::module::Judged;
use crate::module::Verdict;
use crate::refusal::CheckRefusal;
use crate::seal::ComponentOrdinal;
use crate::seal::SealSite;
use crate::seal::SealingSite;

/// The value universe at the constant level `level`.
///
/// # Specification
/// trivial.
fn universe(
    arena: &mut CoreArena,
    level: LevelConstant,
) -> ValueTypeId
{
    arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::constant(level))
}

/// `thunk (λ_. λ_. return code)`, the relation relating every pair by the one
/// code.
///
/// # Specification
/// trivial.
fn relating_by(
    arena: &mut CoreArena,
    code: ValueId,
) -> ValueId
{
    let body = arena.computation_return(code);
    let inner = arena.computation_lambda(body);
    let outer = arena.computation_lambda(inner);
    arena.value_thunk(outer)
}

/// The list `[elements…]`, its first element outermost.
///
/// # Specification
/// trivial.
fn list(
    arena: &mut CoreArena,
    elements: &[ValueId],
) -> ValueId
{
    let mut list = arena.value_list_nil();
    for &element in elements.iter().rev() {
        list = arena.value_list_cons(element, list);
    }
    list
}

/// The string literal `text`.
///
/// # Specification
/// trivial.
fn text(
    arena: &mut CoreArena,
    text: String,
) -> ValueId
{
    arena.value_literal(Literal::Text(StringLiteral::new(text)))
}

/// Each declaration of `module`, its type and its body, judged and then
/// readmitted.
///
/// # Specification
/// trivial.
fn judged(
    arena: &mut CoreArena,
    module: &[(ValueTypeId, ValueId)],
) -> (Vec<Verdict>, Vec<Outcome>)
{
    let declarations: Vec<Declaration> = module
        .iter()
        .enumerate()
        .map(|(at, &(declared, body))| {
            declaration(At(at), Maybe::Present(declared), Maybe::Present(body))
        })
        .collect();
    let (report, readmission) = judge_and_readmit(arena, &declarations);
    (
        report.judged().iter().map(Judged::verdict).collect(),
        readmission
            .readmitted()
            .iter()
            .map(Readmitted::outcome)
            .cloned()
            .collect(),
    )
}

#[test]
fn a_bridge_at_the_universe_is_a_relation_in_both_checkers()
{
    // `Bridge(U₀, ⌜Unit⌝, ⌜String⌝)` is the type of relations `El ⌜Unit⌝ →
    // El ⌜String⌝ → U₀`, and the total relation inhabits it; at `U₁` between
    // two quotes of `U₀` the same; at `U₀ × U₀` a relation per component. No
    // reflexivity: `here` is refused, and so is `()`, which is no relation.
    let mut arena = CoreArena::new();
    let small = universe(&mut arena, LevelConstant::from(0_u64));
    let large = universe(&mut arena, LevelConstant::from(1_u64));
    let unit_type = arena.value_type_unit();
    let string = arena.value_type_base(BaseType::String);
    let unit_code = arena.value_quote(unit_type);
    let string_code = arena.value_quote(string);
    let small_code = arena.value_quote(small);
    let total = relating_by(&mut arena, unit_code);
    let at_small = arena.value_type_bridge(small, unit_code, string_code);
    let at_large = arena.value_type_bridge(large, small_code, small_code);
    let total_small = relating_by(&mut arena, small_code);
    let pairs = arena.value_type_product(&[small, small]);
    let forward = arena.value_tuple(&[unit_code, string_code]);
    let backward = arena.value_tuple(&[string_code, unit_code]);
    let at_pairs = arena.value_type_bridge(pairs, forward, backward);
    let both = arena.value_tuple(&[total, total]);
    let reflexive = arena.value_type_bridge(small, unit_code, unit_code);
    let here = arena.value_here(unit_code);
    let one = arena.value_unit();
    let (verdicts, outcomes) = judged(&mut arena, &[
        (at_small, total),
        (at_large, total_small),
        (at_pairs, both),
        (reflexive, here),
        (at_small, one),
    ]);
    assert!(
        matches!(verdicts.as_slice(), [
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            Verdict::Refused(CheckRefusal::ShapeMismatch { .. }),
            Verdict::Refused(CheckRefusal::TypeMismatch(_)),
        ]),
        "a relation inhabits a bridge at the universe, and neither `here` nor `()` \
         does: {verdicts:?}"
    );
    assert!(
        matches!(
            outcomes.get(.. 3),
            Some([
                Outcome::Defined { .. },
                Outcome::Defined { .. },
                Outcome::Defined { .. }
            ])
        ),
        "the kernel readmits each relation at its bridge: {outcomes:?}"
    );
}

#[test]
fn a_bridge_crosses_as_the_kernel_s_bridge_node()
{
    // def b : Bridge(U₀, ⌜Unit⌝, ⌜Unit⌝) = λ_ _. return ⌜Unit⌝ ;
    let mut arena = CoreArena::new();
    let small = universe(&mut arena, LevelConstant::from(0_u64));
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let bridged = arena.value_type_bridge(small, unit_code, unit_code);
    let total = relating_by(&mut arena, unit_code);
    let (_, readmission) = judge_and_readmit(&mut arena, &[declaration(
        At(0),
        Maybe::Present(bridged),
        Maybe::Present(total),
    )]);
    let artifact = decode(
        readmission
            .export(alloc::collections::BTreeMap::new())
            .as_image(),
    )
    .unwrap();
    let declared = artifact
        .declarations()
        .first()
        .map(|marked| marked.declaration().declared_id())
        .unwrap();
    assert!(
        matches!(
            artifact.arena().value_type(declared),
            Some(&KernelValueType::Bridge { .. })
        ),
        "the bridge crosses as the kernel's own former"
    );
}

#[test]
fn a_bridge_at_a_list_is_the_relation_lifting_in_both_checkers()
{
    // nil/nil is `Unit`; cons/cons the heads' fibre beside the tails' bridge;
    // unequal heads, or a nil against a cons, have an empty lifting; a list of
    // codes lifts the universe's clause; a declared list `xs` is read as
    // written, so no fibre is read at it and `()` meets the bridge itself.
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let lists = arena.value_type_list(string);
    let one = arena.value_unit();
    let [first, second] = ["a", "b"].map(|written| text(&mut arena, String::from(written)));
    let empty = list(&mut arena, &[]);
    let single = list(&mut arena, &[first]);
    let other = list(&mut arena, &[second]);
    let pair = list(&mut arena, &[first, second]);
    let lifted = arena.value_tuple(&[one, one]);
    let nested = arena.value_tuple(&[one, lifted]);
    let small = universe(&mut arena, LevelConstant::from(0_u64));
    let codes = arena.value_type_list(small);
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let string_code = arena.value_quote(string);
    let unit_codes = list(&mut arena, &[unit_code]);
    let string_codes = list(&mut arena, &[string_code]);
    let total = relating_by(&mut arena, unit_code);
    let related = arena.value_tuple(&[total, one]);
    let declared = arena.value_constant(ConstantIndex::from(0_usize));
    let module = [
        (lists, single),
        (arena.value_type_bridge(lists, empty, empty), one),
        (arena.value_type_bridge(lists, single, single), lifted),
        (arena.value_type_bridge(lists, pair, pair), nested),
        (
            arena.value_type_bridge(codes, unit_codes, string_codes),
            related,
        ),
        (arena.value_type_bridge(lists, single, other), lifted),
        (arena.value_type_bridge(lists, empty, single), one),
        (arena.value_type_bridge(lists, declared, single), one),
    ];
    let (verdicts, outcomes) = judged(&mut arena, &module);
    assert!(
        matches!(verdicts.as_slice(), [
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            Verdict::Refused(CheckRefusal::TypeMismatch(_)),
            Verdict::Refused(CheckRefusal::TypeMismatch(_)),
            Verdict::Refused(CheckRefusal::TypeMismatch(_)),
        ]),
        "the lifting relates equal lists and codes, and nothing else: {verdicts:?}"
    );
    assert!(
        matches!(
            outcomes.get(.. 5),
            Some([
                Outcome::Defined { .. },
                Outcome::Defined { .. },
                Outcome::Defined { .. },
                Outcome::Defined { .. },
                Outcome::Defined { .. }
            ])
        ),
        "the kernel readmits each lifting: {outcomes:?}"
    );
}

#[test]
fn a_bridge_at_a_base_or_a_sum_relates_as_its_identity_in_both_checkers()
{
    // At a base type and at a binary sum the bridge reads the identity's
    // fibre: `Unit` between equal literals or injections at one summand, the
    // empty sum between distinct ones.
    let mut arena = CoreArena::new();
    let functions = crate::fixture::booleans(&mut arena);
    let string = arena.value_type_base(BaseType::String);
    let one = arena.value_unit();
    let [first, second] = ["a", "b"].map(|written| text(&mut arena, String::from(written)));
    let [truth, falsity] =
        [0_usize, 1_usize].map(|summand| arena.value_injection(Summand::from(summand), one));
    let module = [
        (arena.value_type_bridge(string, first, first), one),
        (arena.value_type_bridge(functions.ty, truth, truth), one),
        (arena.value_type_bridge(string, first, second), one),
        (arena.value_type_bridge(functions.ty, truth, falsity), one),
    ];
    let (verdicts, outcomes) = judged(&mut arena, &module);
    assert!(
        matches!(verdicts.as_slice(), [
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            Verdict::Refused(_),
            Verdict::Refused(_),
        ]),
        "equal points are bridged by `()`, distinct ones by nothing: {verdicts:?}"
    );
    assert!(
        matches!(
            outcomes.get(.. 2),
            Some([Outcome::Defined { .. }, Outcome::Defined { .. }])
        ),
        "the kernel readmits both: {outcomes:?}"
    );
}

#[test]
fn a_bridge_at_a_data_type_relates_constructor_by_constructor()
{
    // data Two : Type { Both : (a : String, b : String) --> Two, None --> Two } ;
    // `Both(a, a)` is bridged to itself by `((), ())`, `None` to itself by
    // `()`, and `None` to `Both(a, a)` by nothing.
    let mut arena = CoreArena::new();
    let kind = universe(&mut arena, LevelConstant::from(0_u64));
    let string = arena.value_type_base(BaseType::String);
    let signature = Arc::new(DataSignature::new(
        Vec::new(),
        Vec::from([Vec::from([string, string]), Vec::new()]),
        kind,
    ));
    let two = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let letter = text(&mut arena, String::from("a"));
    let both = arena.value_constructor(
        two,
        ConstructorTag::from(0_usize),
        Vec::from([letter, letter]),
    );
    let none = arena.value_constructor(two, ConstructorTag::from(1_usize), Vec::new());
    let one = arena.value_unit();
    let fields = arena.value_tuple(&[one, one]);
    let at_both = arena.value_type_bridge(two, both, both);
    let at_none = arena.value_type_bridge(two, none, none);
    let apart = arena.value_type_bridge(two, none, both);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        Declaration::data(
            ConstantIndex::from(0_usize),
            signature,
            OriginToken::from(0_usize),
        ),
        declaration(At(1), Maybe::Present(at_both), Maybe::Present(fields)),
        declaration(At(2), Maybe::Present(at_none), Maybe::Present(one)),
        declaration(At(3), Maybe::Present(apart), Maybe::Present(one)),
    ]);
    let verdicts: Vec<_> = report.judged().iter().map(Judged::verdict).collect();
    assert!(
        matches!(verdicts.as_slice(), [
            Verdict::Data,
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            Verdict::Refused(_),
        ]),
        "one constructor relates field by field, two by nothing: {verdicts:?}"
    );
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(Readmitted::outcome)
        .collect();
    assert!(
        matches!(
            outcomes.get(1 .. 3),
            Some([Outcome::Defined { .. }, Outcome::Defined { .. }])
        ),
        "the kernel readmits both: {outcomes:?}"
    );
}

#[test]
fn an_interfaced_atom_bears_its_relation_as_its_bridge_in_both_checkers()
{
    // The atom relates every pair of its points by `Unit` and states no law:
    // a bridge between its two points is the relation between them, `()`, and
    // a bridge from a point to itself its reflexivity, `here`, though no
    // identity between the two points is read without the law.
    let mut arena = CoreArena::new();
    let mut module = interfaced_atom_module(&mut arena, Stated::Lawless);
    let atom = arena.value_type_abstract(ConstantIndex::from(3_usize));
    let [first, second] =
        [4_usize, 5_usize].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let between = arena.value_type_bridge(atom, first, second);
    let reflexive = arena.value_type_bridge(atom, first, first);
    let one = arena.value_unit();
    let here = arena.value_here(first);
    let at = module.len();
    module.push(declaration(
        At(at),
        Maybe::Present(between),
        Maybe::Present(one),
    ));
    module.push(declaration(
        At(at.saturating_add(1)),
        Maybe::Present(reflexive),
        Maybe::Present(here),
    ));
    let (report, readmission) = judge_and_readmit(&mut arena, &module);
    let verdicts: Vec<_> = report.judged().iter().map(Judged::verdict).collect();
    assert!(
        matches!(
            verdicts.get(at ..),
            Some([Verdict::Checked { .. }, Verdict::Checked { .. }])
        ),
        "the relation's evidence and the reflexivity inhabit the atom's bridges: \
         {verdicts:?}"
    );
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(Readmitted::outcome)
        .collect();
    assert!(
        matches!(
            outcomes.get(at ..),
            Some([Outcome::Defined { .. }, Outcome::Defined { .. }])
        ),
        "the kernel readmits both: {outcomes:?}"
    );
}

/// An atom over `Unit` stating no interface, at position zero, and a point of
/// it at position one.
///
/// # Specification
/// trivial.
fn sealed_atom(arena: &mut CoreArena) -> Vec<Declaration>
{
    let small = universe(arena, LevelConstant::from(0_u64));
    let unit = arena.value_type_unit();
    let one = arena.value_unit();
    let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
    Vec::from([
        Declaration::abstract_type(
            ConstantIndex::from(0_usize),
            AbstractType::new(
                small,
                unit,
                SealExtent::from(1_usize),
                SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(0_usize)),
            ),
            origin(At(0)),
        ),
        declaration(At(1), Maybe::Present(atom), Maybe::Present(one)),
    ])
}

#[test]
fn a_bridge_at_a_sealed_type_is_refused_by_name()
{
    // Bridges whose carriers reach an atom stating no interface — directly,
    // through a function's result and through a list's elements — do not
    // form; the identity at the same atom still does.
    let mut arena = CoreArena::new();
    let mut module = sealed_atom(&mut arena);
    let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let point = arena.value_constant(ConstantIndex::from(1_usize));
    let unit = arena.value_type_unit();
    let one = arena.value_unit();
    let returns = arena.comp_type_returner(atom);
    let arrow = arena.comp_type_arrow(unit, returns);
    let into_atom = arena.value_type_thunk(arrow);
    let body = arena.computation_return(point);
    let body = arena.computation_lambda(body);
    let constant = arena.value_thunk(body);
    let atoms = arena.value_type_list(atom);
    let empty = arena.value_list_nil();
    let identity = arena.value_type_path(atom, point, point);
    let here = arena.value_here(point);
    for (declared, body) in [
        (arena.value_type_bridge(atom, point, point), one),
        (arena.value_type_bridge(into_atom, constant, constant), one),
        (arena.value_type_bridge(atoms, empty, empty), one),
        (identity, here),
    ] {
        let at = module.len();
        module.push(declaration(
            At(at),
            Maybe::Present(declared),
            Maybe::Present(body),
        ));
    }
    let (report, _) = judge_and_readmit(&mut arena, &module);
    let verdicts: Vec<_> = report.judged().iter().map(Judged::verdict).collect();
    let sealed = ConstantIndex::from(0_usize);
    assert!(
        matches!(verdicts.get(2 ..), Some([
            Verdict::Refused(CheckRefusal::BridgeAtSealedType { atom: first, .. }),
            Verdict::Refused(CheckRefusal::BridgeAtSealedType { atom: second, .. }),
            Verdict::Refused(CheckRefusal::BridgeAtSealedType { atom: third, .. }),
            Verdict::Checked { .. },
        ]) if [*first, *second, *third] == [sealed; 3]),
        "each bridge reaching the atom is refused naming it, and its identity forms: \
         {verdicts:?}"
    );
}

#[test]
fn the_codes_outside_the_bridge_fold_are_refused_by_name()
{
    // A dependent arrow, a bridge at a bridge and a ternary product have no
    // clause of the fold: an introduction there is refused naming the code.
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let one = arena.value_unit();
    let returns = arena.comp_type_returner(unit);
    let dependent = arena.comp_type_pi(unit, returns);
    let dependent = arena.value_type_thunk(dependent);
    let body = arena.computation_return(one);
    let body = arena.computation_lambda(body);
    let constant = arena.value_thunk(body);
    let inner = arena.value_type_bridge(unit, one, one);
    let triple = arena.value_type_product(&[unit, unit, unit]);
    let ones = arena.value_tuple(&[one, one, one]);
    let module = [
        (
            arena.value_type_bridge(dependent, constant, constant),
            constant,
        ),
        (arena.value_type_bridge(inner, one, one), one),
        (arena.value_type_bridge(triple, ones, ones), ones),
    ];
    let codes = [dependent, inner, triple];
    let (verdicts, _) = judged(&mut arena, &module);
    assert_eq!(verdicts.len(), codes.len());
    for (verdict, expected) in verdicts.iter().zip(codes) {
        assert!(
            matches!(verdict, Verdict::Refused(CheckRefusal::OutsideFold { code, .. }) if *code == expected),
            "each code outside the fold is named: {verdicts:?}"
        );
    }
}

#[test]
fn a_funext_at_a_bridge_crosses_as_a_higher_evaluation()
{
    // def not, not_not, same : U (+{(), ()} -> F +{(), ()}) ;
    // def twice : Bridge(U (…), not_not, same) = funext(not_not, same) ;
    // The functions agree at every input, so they are bridged, and the kernel
    // replays the evaluation in its bridge fold.
    let mut arena = CoreArena::new();
    let functions = crate::fixture::booleans(&mut arena);
    let [not_not, same] =
        [1_usize, 2_usize].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let bridged = arena.value_type_bridge(functions.function, not_not, same);
    let funext = arena.value_funext(not_not, same);
    let declared = Maybe::Present(functions.function);
    let (report, readmission) = judge_and_readmit(&mut arena, &[
        declaration(At(0), declared, Maybe::Present(functions.not)),
        declaration(At(1), declared, Maybe::Present(functions.not_not)),
        declaration(At(2), declared, Maybe::Present(functions.same)),
        declaration(At(3), Maybe::Present(bridged), Maybe::Present(funext)),
    ]);
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "the extensionality checks at the bridge: {:?}",
        report.judged()[3].verdict()
    );
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel replays it at the bridge: {:?}",
        readmission.readmitted()
    );
}
