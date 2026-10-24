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
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
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

/// Assert that every declaration of `module` checks, a theory forming as
/// data does.
///
/// # Specification
/// trivial.
fn assert_checked(
    module: &LoweredModule<'_>,
    arena: &mut CoreArena,
)
{
    let report = judged(module, arena);
    assert_eq!(
        report.judged().len(),
        module.declarations().len(),
        "nothing is refused: {:?}",
        module.declarations()
    );
    for verdict in report.judged() {
        assert!(
            matches!(verdict.verdict(), Verdict::Checked { .. } | Verdict::Data),
            "every declaration checks: {report:?}"
        );
    }
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
        report.judged().len() == module.declarations().len()
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
        module.declarations().len(),
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
    // `stepped(4)` passes one hole per component, each naming the slot.
    let source = format!("{STEPPED}def omitted() -> -F Integer {{ stepped(4) }}\n");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let holes = nominated_holes(&module, &arena, SurfaceName::from("omitted"));
    let slot = Omitted::Implicit {
        function: String::from("stepped"),
        implicit: String::from("s"),
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
