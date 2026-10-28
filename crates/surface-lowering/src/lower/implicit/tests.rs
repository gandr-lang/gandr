use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_checker::Verdict;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::equal_type_syntax;
use gandr_core_term::hole::HoleOrigin;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::error::LoweringRefusal;
use crate::lower::native::tests::assert_checked;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::preluded;
use crate::lower::native::tests::refusal_of;
use crate::model::Dependent;
use crate::module::DeclarationOutcome;
use crate::module::LoweredModule;
use crate::origin::Omitted;
use crate::resolve::SurfaceName;

/// The identity at a type supplied by name.
const SAME: &str = "def same @[a : Type] (y : a) -> -F a { return y }\n";

/// The first of two values, both of their types implicit.
const FIRST: &str = "def first @[a : Type, b : Type] (x : a, y : b) -> -F a { return x }\n";

/// The type `name`'s signature declares.
///
/// # Specification
/// trivial.
fn declared_type_of(
    module: &LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> ValueTypeId
{
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
    else {
        panic!("`{name}` is declared");
    };
    let DeclarationOutcome::Completed { declared_type, .. } = declaration.outcome()
    else {
        panic!("`{name}` declares a type: {:?}", declaration.outcome());
    };

    declared_type
}

#[test]
fn plicity_is_metadata_not_type_structure()
{
    let source = format!("{SAME}def twin(a : Type, y : a) -> -F a {{ return y }}\n");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert_eq!(
        equal_type_syntax(
            &arena,
            declared_type_of(&module, SurfaceName::from("same")),
            declared_type_of(&module, SurfaceName::from("twin")),
        ),
        CertificateEquality::Equal,
        "the implicit declares the type its explicit twin does"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn a_forward_reference_from_the_prefix_binds_after_its_target()
{
    let source = "def chosen @[x : t] (t : Type) -> -F t { return x }\ndef twin(t : Type, x : t) -> -F t { return x }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert_eq!(
        equal_type_syntax(
            &arena,
            declared_type_of(&module, SurfaceName::from("chosen")),
            declared_type_of(&module, SurfaceName::from("twin")),
        ),
        CertificateEquality::Equal,
        "`x : t` binds after `t`, the parameter its type names"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn a_telescope_names_its_implicits_in_the_merged_order_2267()
{
    // `x : t` binds after `t`, so the merged telescope is `t` then `x`; `twin`
    // writes no telescope and answers nothing.
    let source = "def chosen @[x : t] (t : Type) -> -F t { return x }\ndef twin(t : Type, x : t) -> -F t { return x }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let constant = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
            .map_or_else(
                || panic!("`{name}` is declared"),
                crate::module::LoweredDeclaration::constant,
            )
    };
    assert_eq!(module.implicits(constant("chosen")), [
        None,
        Some(SurfaceName::from("x"))
    ]);
    assert!(module.implicits(constant("twin")).is_empty());
}

#[test]
fn a_binder_of_an_implicit_s_type_mentions_no_parameter_1350()
{
    let source = "\
def named @[m : Type, combine : (x : m) => m] (x : m) -> -F m { become combine(x) }
def bare @[m : Type, combine : m => m] (x : m) -> -F m { become combine(x) }
def twin(m : Type, combine : m => m, x : m) -> -F m { become combine(x) }
def keyed @[c : (y : t) => t] (t : Type, v : t) -> -F t { become c(v) }
def keyedTwin(t : Type, c : t => t, v : t) -> -F t { become c(v) }
";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    for (implicit, explicit) in [("named", "twin"), ("bare", "twin"), ("keyed", "keyedTwin")] {
        assert_eq!(
            equal_type_syntax(
                &arena,
                declared_type_of(&module, SurfaceName::from(implicit)),
                declared_type_of(&module, SurfaceName::from(explicit)),
            ),
            CertificateEquality::Equal,
            "`{implicit}` binds in the order `{explicit}` writes: a name its implicit's type \
             binds mentions no parameter, and a name it reads still orders"
        );
    }
    assert_checked(&module, &mut arena);
}

#[test]
fn a_telescope_cycle_is_refused_naming_the_cycle()
{
    let source = "def tangled @[a : b, b : a] (x : a) -> -F a { return x }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("tangled")),
            LoweringRefusal::TelescopeCycle { first, second, .. }
                if first == SurfaceName::from("a") && second == SurfaceName::from("b")
        ),
        "the cycle names both of its parameters"
    );
}

#[test]
fn a_stage_telescope_merges_nothing()
{
    let source = "def staged @[i : Size] (x : Integer) -> -F Integer { return x }\ndef stagedRun : () => Integer ;\ndef stagedRun = thunk { become staged(1) } ;\ndef kept @[i : Size, a : Type] (n : Integer, y : a) -> -F a { return y }\ndef twin(a : Type, n : Integer, y : a) -> -F a { return y }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert_eq!(
        module.stages(
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name() == SurfaceName::from("kept"))
                .unwrap()
        ),
        [gandr_kernel_term::StageBound::Unbounded],
        "the stage beside an implicit is the signature's one quantifier"
    );
    assert_eq!(
        equal_type_syntax(
            &arena,
            declared_type_of(&module, SurfaceName::from("kept")),
            declared_type_of(&module, SurfaceName::from("twin")),
        ),
        CertificateEquality::Equal,
        "the stage binds no parameter; the implicit binds the first"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn supply_by_name_is_order_free()
{
    let source = format!(
        "{FIRST}def written : () => Integer ;\ndef written = thunk {{ become first[a = Integer, b = Unit](5, unit) }} ;\ndef swapped : () => Integer ;\ndef swapped = thunk {{ become first[b = Unit, a = Integer](5, unit) }} ;\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert_eq!(
        equal_certificate_syntax(
            &arena,
            body_named(&module, SurfaceName::from("written")),
            body_named(&module, SurfaceName::from("swapped")),
        ),
        CertificateEquality::Equal,
        "either order of the residents applies `first` alike"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn an_unsupplied_implicit_is_refused_with_its_slot_spelling()
{
    let source = format!("{SAME}def named : +U (Integer -> -F Integer) ;\ndef named = same ;\n");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("named")),
            LoweringRefusal::ImplicitUnsupplied { function, implicit, .. }
                if function == SurfaceName::from("same") && implicit == SurfaceName::from("a")
        ),
        "`same` standing as a value leaves its `a` unsupplied"
    );
}

/// The holes the elaborator nominated in the body of `name`, for omitted
/// implicits and for wildcards, in the order the walk meets them: the
/// arguments of an application before the function's, the last argument
/// first.
///
/// # Specification
/// trivial.
fn nominated_holes(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    name: SurfaceName<'_>,
) -> Vec<(gandr_core_term::ValueId, gandr_core_term::hole::HoleId)>
{
    let mut holes = Vec::new();
    let mut pending = Vec::from([body_named(module, name)]);
    let mut computations = Vec::new();
    while let Some(value) = pending.pop() {
        match arena.value(value) {
            Some(&Value::Thunk(computation)) => computations.push(computation),
            Some(&Value::Hole(hole))
                if matches!(hole.origin(), HoleOrigin::Nominated | HoleOrigin::Wildcard) =>
            {
                holes.push((value, hole));
            },
            _ => {},
        }
        while let Some(computation) = computations.pop() {
            match arena.computation(computation) {
                Some(&Computation::Lambda(body)) => computations.push(body),
                Some(&Computation::Application(function, argument)) => {
                    computations.push(function);
                    pending.push(argument);
                },
                _ => {},
            }
        }
    }
    holes
}

#[test]
fn an_omitted_implicit_is_a_nominated_hole()
{
    // `first(5, unit)`: one nominated hole per omitted implicit, applied in
    // the telescope's order, each recorded with the implicit it stands for;
    // the checker solves both.
    let source = format!(
        "{FIRST}def omitted : () => Integer ;\ndef omitted = thunk {{ become first(5, unit) }} ;\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let holes = nominated_holes(&module, &arena, SurfaceName::from("omitted"));
    let named: Vec<Maybe<&Omitted, _>> = holes
        .iter()
        .map(|&(at, _)| module.origins().omitted(at))
        .collect();
    let implicit = |name: &str| Omitted::Implicit {
        function: String::from("first"),
        implicit: String::from(name),
    };
    assert_eq!(
        named,
        [
            Maybe::Present(&implicit("a")),
            Maybe::Present(&implicit("b"))
        ],
        "each omitted implicit is a hole naming it, in the telescope's order"
    );
    assert_ne!(
        holes[0].1, holes[1].1,
        "the two holes are distinct metavariables"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn a_wildcard_is_a_nominated_hole_of_its_own()
{
    // `first[a = _](5, unit)`: the wildcard the slot writes for `a` and the
    // hole the call nominates for the `b` it omits are two metavariables,
    // the one recorded and named as a wildcard and the other naming its
    // implicit; the checker solves both, `5` forcing the wildcard and `unit`
    // the implicit.
    let source = format!(
        "{FIRST}def wild : () => Integer ;\ndef wild = thunk {{ become first[a = _](5, unit) \
         }} ;\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let holes = nominated_holes(&module, &arena, SurfaceName::from("wild"));
    let mut named: Vec<Maybe<&Omitted, _>> = holes
        .iter()
        .map(|&(at, _)| module.origins().omitted(at))
        .collect();
    named.sort_by_key(|omitted| matches!(omitted, Maybe::Present(Omitted::Implicit { .. })));
    let implicit = Omitted::Implicit {
        function: String::from("first"),
        implicit: String::from("b"),
    };
    assert_eq!(
        named,
        [
            Maybe::Present(&Omitted::Wildcard),
            Maybe::Present(&implicit)
        ],
        "the wildcard is recorded as one, the omitted implicit by its name"
    );
    assert_ne!(
        holes[0].1, holes[1].1,
        "the wildcard and the implicit are distinct metavariables"
    );
    assert!(
        holes.iter().all(|&(at, hole)| matches!(
            (module.origins().omitted(at), hole.origin()),
            (Maybe::Present(&Omitted::Wildcard), HoleOrigin::Wildcard)
                | (
                    Maybe::Present(&Omitted::Implicit { .. }),
                    HoleOrigin::Nominated
                )
        )),
        "each hole's name says whether the text wrote `_` there"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn a_wildcard_emits_the_body_written_by_hand_528()
{
    // `idAt(_, 3)` and `idAt(Integer, 3)`: the checker writes the term the
    // wildcard's comparison forces in its place, so the body it accepts is
    // the one the author could have written, the wildcard adding nothing.
    let source = "def idAt(a : Type, y : a) -> -F a { return y }\ndef forced : () => Integer \
                  ;\ndef forced = thunk { become idAt(_, 3) } ;\ndef written : () => Integer ;\n\
                  def written = thunk { become idAt(Integer, 3) } ;\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let report = judged(&module, &mut arena);
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("forced"))
    else {
        panic!("`forced` is declared");
    };
    let Some(Verdict::Checked { body, .. }) = report
        .judged()
        .iter()
        .find(|judged| judged.constant() == declaration.constant())
        .map(gandr_core_checker::Judged::verdict)
    else {
        panic!("`forced` checks: {report:?}");
    };
    assert_eq!(
        equal_certificate_syntax(
            &arena,
            body,
            body_named(&module, SurfaceName::from("written"))
        ),
        CertificateEquality::Equal,
        "the wildcard is solved as `Integer` and the body emitted with it written"
    );
}

#[test]
fn an_implicit_in_the_parentheses_is_refused()
{
    let source = format!(
        "{SAME}def inside : () => Integer ;\ndef inside = thunk {{ become same(Integer, 3) }} ;\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("inside")),
            LoweringRefusal::ImplicitInParentheses { function, implicit, .. }
                if function == SurfaceName::from("same") && implicit == SurfaceName::from("a")
        ),
        "one argument per parameter passes the implicit among the explicit ones"
    );
}

#[test]
fn a_resident_naming_no_implicit_is_unresolved()
{
    let source = format!(
        "{SAME}def stray : () => Integer ;\ndef stray = thunk {{ become same[b = Integer](3) }} ;\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("stray")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("b")
        ),
        "`b` names no implicit of `same`"
    );
}

#[test]
fn a_supplied_function_stands_as_a_value()
{
    let source = format!(
        "{SAME}def apply(f : (y : Integer) => Integer, x : Integer) -> -F Integer {{ become f(x) }}\ndef passed : () => Integer ;\ndef passed = thunk {{ become apply(same[a = Integer], 3) }} ;\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert_checked(&module, &mut arena);
}

#[test]
fn a_standing_supply_opens_a_lambda_per_explicit_before_it_1498()
{
    // `g`'s type names `s`, so `swapAt[g = …]` opens `λ s. λ t.`, `s`
    // outermost: the supply stands at the type binding `s` first and `v` at
    // `s`, and not at the one whose `v` is at `t`.
    let swap =
        "def swapAt @[g : (y : s) => s] (s : Type, t : Type, v : s) -> -F s { become g(v) }\n";
    // Whether every declaration checks with `standing` stated at `v : result`.
    let all_check = |result: &str| {
        let source = format!(
            "{swap}def standing : +U ((s : Type) -> (t : Type) -> (v : {result}) -> -F {result}) ;\ndef standing = swapAt[g = fn (y) {{ y }}] ;\n"
        );
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source.as_str()), &mut arena);
        let report = judged(&module, &mut arena);
        report.judged().len() == module.declarations().iter().len()
            && report
                .judged()
                .iter()
                .all(|verdict| matches!(verdict.verdict(), Verdict::Checked { .. }))
    };
    assert!(
        all_check("s"),
        "the supply abstracts `s` and `t` in written order"
    );
    assert!(
        !all_check("t"),
        "the lambdas bind `s` before `t`, so `v` is at `s`"
    );
}

#[test]
fn a_standing_stage_supply_stands_as_its_call_1498()
{
    // A stage crosses only at a call's head: `applyAt[i = k]` passed as a
    // value is `λ f. λ x. applyAt[i = k](f, x)`.
    let source = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\ndef applyAt @[i : Size] (f : Nat[<i] => Nat, x : Nat[<i]) -> -F Nat { f(x) }\ndef apply2 @[j : Size] (g : (f : Nat[<j] => Nat, x : Nat[<j]) => Nat, f : Nat[<j] => Nat, x : Nat[<j]) -> -F Nat { become g(f, x) }\ndef passAt @[k : Size] (f : Nat[<k] => Nat, x : Nat[<k]) -> -F Nat { become apply2[j = k](applyAt[i = k], f, x) }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let report = judged(&module, &mut arena);
    assert_eq!(
        report.judged().len(),
        module.declarations().iter().len(),
        "nothing is refused: {:?}",
        module.declarations()
    );
    assert!(
        report
            .judged()
            .iter()
            .all(|verdict| matches!(verdict.verdict(), Verdict::Checked { .. } | Verdict::Data)),
        "the naturals are data and every function checks, `passAt` among them: {report:?}"
    );
}

/// A counter theory, a counter that also resets, a module of each, and a
/// step over any counter its model implicit names.
const STEPPED: &str = "\
theory Counter { sort C : Type; oper zero : C; oper incr : (c : C) --> C; oper read : (c : C) --> Integer; }
theory ResetCounter { include Counter; oper reset : (c : C) --> C; }
module Up : Model(Counter) {
  type C = Integer;
  def zero = 0;
  def incr(c : Integer) -> -F Integer { c + 1 }
  def read(c : Integer) -> -F Integer { c }
}
module Tens : Model(ResetCounter) {
  type C = Integer;
  def zero = 0;
  def incr(c : Integer) -> -F Integer { c + 10 }
  def read(c : Integer) -> -F Integer { c }
  def reset(c : Integer) -> -F Integer { 0 }
}
def stepped @[s : Model(Counter)] (c : s.C) -> -F Integer { s.read(s.incr(c)) }
";

/// Each parameter the declared type `declared` binds, outermost first: its
/// domain beside whether its arrow is dependent.
///
/// # Specification
/// trivial.
fn parameters_of(
    arena: &CoreArena,
    declared: ValueTypeId,
) -> Vec<(ValueTypeId, Dependent)>
{
    let Some(&ValueType::Thunk(mut arrow)) = arena.value_type(declared)
    else {
        panic!("a function's declared type is a thunk");
    };
    let mut parameters = Vec::new();
    loop {
        match arena.comp_type(arrow) {
            Some(&CompType::Pi { domain, codomain }) => {
                parameters.push((domain, Dependent(true)));
                arrow = codomain;
            },
            Some(&CompType::Arrow { domain, codomain }) => {
                parameters.push((domain, Dependent(false)));
                arrow = codomain;
            },
            _ => return parameters,
        }
    }
}

#[test]
fn a_model_implicit_binds_one_parameter_per_component_739()
{
    // `@[s : Model(Counter)] (c : s.C)` binds the sort, the zero, the step
    // and the reading, each dependent, then `c` at the sort's variable three
    // binders out: no parameter holds a record of the model.
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(STEPPED), &mut arena);
    let parameters = parameters_of(
        &arena,
        declared_type_of(&module, SurfaceName::from("stepped")),
    );
    assert_eq!(
        parameters
            .iter()
            .map(|&(_, dependent)| dependent)
            .collect::<Vec<_>>(),
        [
            Dependent(true),
            Dependent(true),
            Dependent(true),
            Dependent(true),
            Dependent(false)
        ],
        "one dependent parameter per component, then `c`"
    );
    let domain = |at: usize| arena.value_type(parameters.get(at)?.0);
    assert!(
        matches!(domain(0), Some(&ValueType::Universe { .. })),
        "the sort is a type"
    );
    let decoded = |at: usize| match domain(at) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    assert_eq!(
        decoded(1),
        Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32)
        }),
        "the zero is an element of the sort just outside it"
    );
    assert_eq!(
        decoded(4),
        Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(3_u32)
        }),
        "`s.C` reads the sort's parameter past the zero, the step and the reading"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn a_manifest_model_implicit_binds_no_fixed_sort_739()
{
    // `@[s : Model(Counter) with sort C = Integer]` binds the zero, the step
    // and the reading at `Integer`, and no parameter for the fixed sort.
    let source = format!(
        "{STEPPED}def fixed @[s : Model(Counter) with sort C = Integer] (c : Integer) -> -F \
         Integer {{ s.read(s.incr(c + s.zero)) }}\ndef manifest() -> -F Integer {{ fixed[s = \
         Up](4) }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let parameters = parameters_of(
        &arena,
        declared_type_of(&module, SurfaceName::from("fixed")),
    );
    assert_eq!(
        parameters.len(),
        4,
        "the zero, the step, the reading and `c`"
    );
    assert!(
        matches!(
            parameters
                .first()
                .and_then(|&(domain, _)| arena.value_type(domain)),
            Some(&ValueType::Base(_))
        ),
        "the zero is an integer: the fixed sort is its type"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn a_telescope_writes_its_model_implicit_as_one_slot_2364()
{
    // `stepped`'s slot binds the sort, the zero, the step and the reading, so
    // its telescope leaves five parameters unnamed, `c` the last; `fixed`'s
    // binds no parameter for `C`, which it fixes at `Integer`, and keeps the
    // type it fixes.
    let source = format!(
        "{STEPPED}def fixed @[s : Model(Counter) with sort C = Integer] (c : Integer) -> -F \
         Integer {{ s.read(s.incr(c + s.zero)) }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let constant = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
            .map_or_else(
                || panic!("`{name}` is declared"),
                crate::module::LoweredDeclaration::constant,
            )
    };
    let components = |slot: &crate::module::FlattenedSlot<'_>| {
        slot.components
            .iter()
            .map(|&(ref name, sort)| (String::from(name.as_ref()), sort))
            .collect::<Vec<_>>()
    };
    assert_eq!(module.implicits(constant("stepped")), [None; 5]);
    let [ref stepped] = *module.model_slots(constant("stepped"))
    else {
        panic!("`stepped` writes one slot");
    };
    assert_eq!(
        (stepped.at, stepped.name, stepped.theory),
        (0, SurfaceName::from("s"), SurfaceName::from("Counter"))
    );
    assert_eq!(components(stepped), [
        (String::from("C"), true),
        (String::from("zero"), false),
        (String::from("incr"), false),
        (String::from("read"), false),
    ]);
    assert!(stepped.fixed.is_empty(), "`stepped`'s type fixes no sort");
    assert_eq!(module.implicits(constant("fixed")), [None; 4]);
    let [ref fixed] = *module.model_slots(constant("fixed"))
    else {
        panic!("`fixed` writes one slot");
    };
    assert_eq!(components(fixed), [
        (String::from("zero"), false),
        (String::from("incr"), false),
        (String::from("read"), false),
    ]);
    let [(ref sort, ty)] = *fixed.fixed
    else {
        panic!("`fixed` fixes one sort");
    };
    assert_eq!(sort.as_ref(), "C");
    assert!(
        matches!(arena.value_type(ty), Some(&ValueType::Base(_))),
        "`C` is fixed at `Integer`"
    );
}

#[test]
fn a_module_supplied_for_a_model_implicit_passes_its_members_739()
{
    // `stepped[s = Up](4)` passes `Up`'s carrier's code and its three members
    // as four arguments before `4`; a resetting counter passes the members a
    // counter's slot names, and a model implicit of the caller's passes its
    // own components on.
    let source = format!(
        "{STEPPED}def supplied() -> -F Integer {{ stepped[s = Up](4) }}\ndef reduct() -> -F \
         Integer {{ stepped[s = Tens](4) }}\ndef passed @[t : Model(Counter)] (c : t.C) -> -F \
         Integer {{ stepped[s = t](c) }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let Some(&Value::Thunk(mut at)) =
        arena.value(body_named(&module, SurfaceName::from("supplied")))
    else {
        panic!("`supplied`'s body is a thunk");
    };
    let mut arguments = Vec::new();
    while let Some(&Computation::Application(function, argument)) = arena.computation(at) {
        arguments.push(arena.value(argument).cloned());
        at = function;
    }
    arguments.reverse();
    assert!(
        matches!(arguments.as_slice(), [
            Some(Value::Quote(_)),
            Some(Value::Constant(_)),
            Some(Value::Constant(_)),
            Some(Value::Constant(_)),
            Some(Value::Literal(_)),
        ]),
        "the carrier's code, the three members, then `4`: {arguments:?}"
    );
    assert_checked(&module, &mut arena);

    let source = format!("{STEPPED}def nowhere() -> -F Integer {{ stepped[s = Nowhere](4) }}\n");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("nowhere")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("Nowhere")
        ),
        "no module answers `Nowhere`"
    );
}

#[test]
fn an_omitted_model_implicit_nominates_a_hole_per_component_739()
{
    // `stepped(4)` passes one hole per component, each naming the slot and
    // the modules that may answer it.
    let source = format!("{STEPPED}def omitted() -> -F Integer {{ stepped(4) }}\n");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let holes = nominated_holes(&module, &arena, SurfaceName::from("omitted"));
    let slot = Omitted::Model {
        function: String::from("stepped"),
        implicit: String::from("s"),
        candidates: Vec::from([String::from("Up"), String::from("Tens")]),
    };
    assert_eq!(
        holes
            .iter()
            .map(|&(at, _)| module.origins().omitted(at))
            .collect::<Vec<_>>(),
        [
            Maybe::Present(&slot),
            Maybe::Present(&slot),
            Maybe::Present(&slot),
            Maybe::Present(&slot)
        ],
        "one hole per component, each the slot's"
    );
}

/// The declaration of `module` named `name`.
///
/// # Specification
/// trivial.
fn declaration_named<'module, 'source>(
    module: &'module LoweredModule<'source>,
    name: SurfaceName<'_>,
) -> &'module crate::module::LoweredDeclaration<'source>
{
    module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
        .expect("the declaration is lowered")
}

#[test]
fn an_omitted_model_implicit_plans_each_module_of_its_theory_739()
{
    // `stepped(4)` beside `Up`, `Tens`, a resetting counter reached through
    // its include, and `Lone`, a model of another theory: the slot is filed
    // for `omitted` with `Up` and `Tens`, each passing four components; both
    // count the integers `4` forces, so the checker refuses the call naming
    // both places.
    let source = format!(
        "{STEPPED}theory Lonely {{ sort L : Type; oper lone : L; }}\nmodule Lone : \
         Model(Lonely) {{ type L = Integer; def lone = 0; }}\ndef omitted() -> -F Integer {{ \
         stepped(4) }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let omitted = declaration_named(&module, SurfaceName::from("omitted"));
    let slots = module.models(omitted);
    assert!(
        matches!(slots, [slot] if slot.holes.len() == 4
            && slot.candidates.len() == 2
            && slot.candidates.iter().all(|candidate| candidate.components.len() == 4)),
        "one slot of four holes, `Up` and `Tens` its candidates: {slots:?}"
    );
    let report = judged(&module, &mut arena);
    let verdict = report
        .judged()
        .iter()
        .find(|judged| judged.constant() == omitted.constant())
        .map(gandr_core_checker::Judged::verdict);
    assert!(
        matches!(
            verdict,
            Some(Verdict::Refused(gandr_core_checker::CheckRefusal::ModelAmbiguous { survivors, .. }))
                if survivors.places().map(usize::from).eq([0, 1])
        ),
        "both answer the integers: {verdict:?}"
    );
}

#[test]
fn equality_calls_the_prelude_s_eq_2302()
{
    // `==` calls the prelude's `eq`, its model of `PartialEq` omitted: one
    // slot of three holes, the carrier, the operation and its symmetry,
    // `PartialEqFloat` its candidate and `EqInteger` and `EqString` through
    // their theory's include, `OrdInteger` and `OrdString` through theirs
    // (#2333), and the operands force one. A source's own `eq` does not
    // capture its `==`; a unit with no prelude keeps the primitive.
    let source = "\
def integers() -> Bool { 3 == 3 }
def strings() -> Bool { \"types\" == \"types\" }
def eq(a : Bool) -> Bool { a }
def own() -> Bool { 3 == 4 }
";
    let (text, unit) = crate::prelude::lay(
        gandr_surface_syntax::SourceText::from(source),
        &crate::unit::Unit::single(),
    )
    .unwrap();
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    for name in ["integers", "strings", "own"] {
        let slots = module.models(declaration_named(&module, SurfaceName::from(name)));
        assert!(
            matches!(slots, [slot] if slot.holes.len() == 3
                && slot.candidates.len() == 5
                && slot.candidates.iter().all(|candidate| candidate.components.len() == 3)),
            "`{name}`'s `==` resolves a model of `PartialEq`: {slots:?}"
        );
    }
    assert_checked(&module, &mut arena);
    let mut alone = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut alone);
    assert!(
        module
            .models(declaration_named(&module, SurfaceName::from("integers")))
            .is_empty(),
        "with no prelude, `==` is the integer primitive"
    );
}

#[test]
fn a_boolean_literal_forces_its_model_at_bool_3350()
{
    // `true == false` resolves `PartialEq` at the literals' carrier, `Bool`,
    // as `3 == 3` does at `Integer`. No model in the prelude answers `Bool`,
    // so the call is unanswered, never ambiguous among the models at other
    // carriers.
    let source = "def differ() -> Bool { true == false }\n";
    let (text, unit) = crate::prelude::lay(
        gandr_surface_syntax::SourceText::from(source),
        &crate::unit::Unit::single(),
    )
    .unwrap();
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    let differ = declaration_named(&module, SurfaceName::from("differ"));
    let report = judged(&module, &mut arena);
    let verdict = report
        .judged()
        .iter()
        .find(|judged| judged.constant() == differ.constant())
        .map(gandr_core_checker::Judged::verdict);
    assert!(
        matches!(
            verdict,
            Some(Verdict::Refused(
                gandr_core_checker::CheckRefusal::ModelUnanswered { .. }
            ))
        ),
        "no model of `PartialEq` answers `Bool`: {verdict:?}"
    );
}

#[test]
fn an_order_calls_the_prelude_s_order_2333()
{
    // `<`, `<=`, `>` and `>=` call the prelude's `lt`, `le`, `gt` and `ge`,
    // their model of `Ord` omitted: one slot of eight holes, the carrier, the
    // included equality with its symmetry and reflexivity, and the four
    // operations, `OrdInteger` and `OrdString` its candidates, and the
    // operands force one. A source's own `lt` does not capture its `<`; a unit
    // with no prelude keeps the primitive.
    let source = "\
def below() -> Bool { 3 < 4 }
def atMost() -> Bool { 3 <= 4 }
def above() -> Bool { \"beta\" > \"alpha\" }
def atLeast() -> Bool { \"beta\" >= \"alpha\" }
def lt(a : Bool) -> Bool { a }
def own() -> Bool { 4 < 3 }
";
    let (text, unit) = crate::prelude::lay(
        gandr_surface_syntax::SourceText::from(source),
        &crate::unit::Unit::single(),
    )
    .unwrap();
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    for name in ["below", "atMost", "above", "atLeast", "own"] {
        let slots = module.models(declaration_named(&module, SurfaceName::from(name)));
        assert!(
            matches!(slots, [slot] if slot.holes.len() == 8
                && slot.candidates.len() == 2
                && slot.candidates.iter().all(|candidate| candidate.components.len() == 8)),
            "`{name}`'s operator resolves a model of `Ord`: {slots:?}"
        );
    }
    assert_checked(&module, &mut arena);
    let mut alone = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut alone);
    assert!(
        module
            .models(declaration_named(&module, SurfaceName::from("below")))
            .is_empty(),
        "with no prelude, `<` is the integer primitive"
    );
}

#[test]
fn a_model_slot_one_module_answers_checks_as_supplied_739()
{
    // `Up` counts integers and `Flips` flips a flag, a counter through its
    // include: `4` forces `Up`, an annotated flag forces `Flips`, and each
    // call checks as if it named its module.
    let source = "\
theory Counter { sort C : Type; oper zero : C; oper incr : (c : C) --> C; oper read : (c : C) --> Integer; }
theory ResetCounter { include Counter; oper reset : (c : C) --> C; }
module Up : Model(Counter) {
  type C = Integer;
  def zero = 0;
  def incr(c : Integer) -> -F Integer { c + 1 }
  def read(c : Integer) -> -F Integer { c }
}
module Flips : Model(ResetCounter) {
  type C = Bool;
  def zero = false;
  def incr(c : Bool) -> -F Bool { case c { true => false, false => true } }
  def read(c : Bool) -> -F Integer { case c { true => 1, false => 0 } }
  def reset(c : Bool) -> -F Bool { false }
}
def stepped @[s : Model(Counter)] (c : s.C) -> -F Integer { s.read(s.incr(c)) }
def counted() -> -F Integer { stepped(4) }
def flipped() -> -F Integer { stepped((false : Bool)) }
";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert_checked(&module, &mut arena);
}

#[test]
fn an_omitted_manifest_model_implicit_files_its_fixed_sorts_2317()
{
    // `fromZero()` over `Model(Counter) with sort C = Integer`, with `Up` over
    // the integers and `Flips` over flags in scope: the slot binds no hole for
    // `C`, so it files the integers' code and each candidate its own
    // carrier's, and the call checks as `Up` alone answers it.
    let source = "\
theory Counter { sort C : Type; oper zero : C; oper incr : (c : C) --> C; oper read : (c : C) --> Integer; }
module Up : Model(Counter) {
  type C = Integer;
  def zero = 0;
  def incr(c : Integer) -> -F Integer { c + 1 }
  def read(c : Integer) -> -F Integer { c }
}
module Flips : Model(Counter) {
  type C = Bool;
  def zero = false;
  def incr(c : Bool) -> -F Bool { case c { true => false, false => true } }
  def read(c : Bool) -> -F Integer { case c { true => 1, false => 0 } }
}
def fromZero @[s : Model(Counter) with sort C = Integer] () -> -F Integer { s.read(s.incr(s.zero)) }
def counted() -> -F Integer { fromZero() }
";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let counted = declaration_named(&module, SurfaceName::from("counted"));
    let slots = module.models(counted);
    let quoted = |id| matches!(arena.value(id), Some(Value::Quote(_)));
    assert!(
        matches!(slots, [slot] if slot.holes.len() == 3
            && matches!(slot.fixed.as_slice(), [code] if quoted(*code))
            && slot.candidates.len() == 2
            && slot.candidates.iter().all(|candidate| candidate.components.len() == 3
                && matches!(candidate.fixed.as_slice(), [code] if quoted(*code)))),
        "three holes, the integers' code, and each candidate's own carrier: {slots:?}"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn a_model_implicit_named_alone_is_refused_739()
{
    // `s` is its components: passed where a model value is asked, it is
    // refused naming it.
    let source = format!(
        "{STEPPED}def observe(m : Model(Counter)) -> -F Integer {{ 0 }}\ndef named \
         @[s : Model(Counter)] (c : s.C) -> -F Integer {{ observe(s) }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("named")),
            LoweringRefusal::ModelImplicitValue { implicit, .. } if implicit == SurfaceName::from("s")
        ),
        "the model implicit stands as no value"
    );
}

#[test]
fn a_model_implicit_supplied_by_a_value_is_refused_739()
{
    // A slot takes a module's name or a model implicit's, never a value: the
    // pack written out is refused naming the slot.
    let source = format!(
        "{STEPPED}def packed() -> -F Integer {{ stepped[s = pack Up at Model(Counter)](4) }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("packed")),
            LoweringRefusal::ModelImplicitValue { implicit, .. } if implicit == SurfaceName::from("s")
        ),
        "a value supplies no model implicit"
    );
}

/// A line printed through the instance `out` its row names.
const SAY: &str = "def say() -> -F [out : Console] Unit { out.print(\"x\") }\n";

/// A handler of `Console` answering 1, around `body`.
///
/// # Specification
/// trivial.
fn handled(
    binder: SurfaceName<'_>,
    body: SourceText<'_>,
) -> String
{
    format!(
        "handle {binder} : Console {{ {body} }} with {{ pure(v) => pure v, oper print(line, k) => pure 1 }}"
    )
}

#[test]
fn a_row_label_is_an_instance_after_every_parameter_2271()
{
    // `both` takes `r` and `s`, then a capability of `Console` per label of
    // its row, each at a region binder of its own: the type its explicit twin
    // writes. Its row's tail reads `r` past both instances, which no type
    // names, as the twin's reads it past `x` and `y`.
    let source = "def both @[r : Row] (s : String) -> -F [x : Console, y : Console | r] Unit { y.print(s) }\ndef twin @[r : Row, q : Region, q1 : Region] (s : String, x : Cap {print} at q, y : Cap {print} at q1) -> -F [q : Console, q1 : Console | r] Unit { y.print(s) }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert_eq!(
        equal_type_syntax(
            &arena,
            declared_type_of(&module, SurfaceName::from("both")),
            declared_type_of(&module, SurfaceName::from("twin")),
        ),
        CertificateEquality::Equal,
        "each label binds the capability of its instance, after `s`, and the tail reads `r`"
    );
    let both = declaration_named(&module, SurfaceName::from("both")).constant();
    assert_eq!(module.implicits(both), [
        Some(SurfaceName::from("r")),
        None,
        Some(SurfaceName::from("x")),
        Some(SurfaceName::from("y"))
    ]);
    assert_checked(&module, &mut arena);
}

#[test]
fn a_row_label_naming_a_region_binder_is_its_instance_2271()
{
    // `twin`'s labels name its region binders: they bind no parameter, and
    // every parameter it takes is written.
    let source = "def twin @[r : Region] (x : Cap {print} at r) -> -F [r : Console] Unit { x.print(\"x\") }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let twin = declaration_named(&module, SurfaceName::from("twin")).constant();
    assert!(
        module.implicits(twin).is_empty(),
        "a label naming a region binder adds no instance"
    );
    assert_eq!(
        parameters_of(&arena, declared_type_of(&module, SurfaceName::from("twin"))).len(),
        1_usize,
        "the capability written is the one parameter"
    );
    assert_checked(&module, &mut arena);
}

#[test]
fn an_omitted_instance_is_the_one_handled_in_scope_2271()
{
    // `say()` inside one scope passes its capability, as `say[out = a]()`
    // does; inside a function whose row labels an instance, it passes that.
    let source = format!(
        "{SAY}def resolved() -> -F Integer {{ {} }}\ndef named() -> -F Integer {{ {} }}\ndef relayed() -> -F [o : Console] Unit {{ say() }}\ndef relayedNamed() -> -F [o : Console] Unit {{ say[out = o]() }}\n",
        handled("a".into(), SourceText::from("say(); pure 0")),
        handled("a".into(), SourceText::from("say[out = a](); pure 0")),
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for (omitted, supplied) in [("resolved", "named"), ("relayed", "relayedNamed")] {
        assert_eq!(
            equal_certificate_syntax(
                &arena,
                body_named(&module, SurfaceName::from(omitted)),
                body_named(&module, SurfaceName::from(supplied)),
            ),
            CertificateEquality::Equal,
            "{omitted}: the omitted instance is the one in scope"
        );
    }
    assert_checked(&module, &mut arena);
}

#[test]
fn an_omitted_instance_is_refused_when_none_or_several_stand_2271()
{
    let inner = handled("b".into(), SourceText::from("say(); pure 0"));
    let source = format!(
        "{SAY}def none() -> -F [Console] Unit {{ say() }}\ndef several() -> -F Integer {{ {} }}\n",
        handled("a".into(), SourceText::from(inner.as_str())),
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("none")),
            LoweringRefusal::InstanceUnanswered { function, instance, interface, .. }
                if function == SurfaceName::from("say")
                    && instance == SurfaceName::from("out")
                    && interface == SurfaceName::from("Console")
        ),
        "the row's default is no instance a call may pass"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("several")),
            LoweringRefusal::InstanceAmbiguous { instance, first, second, .. }
                if instance == SurfaceName::from("out")
                    && first == SurfaceName::from("b")
                    && second == SurfaceName::from("a")
        ),
        "two scopes of `Console`, named innermost first"
    );
}
