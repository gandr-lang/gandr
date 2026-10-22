//! Definitions whose body has the wrong shape for its declared type, or a
//! form no type can be synthesized for, each refused by the error that names
//! the mismatch; and the eliminators those refusals misapply, admitted at the
//! types they eliminate.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_kernel_core::CheckedId;
use gandr_kernel_core::Environment;
use gandr_kernel_core::ExpectedComputationShape;
use gandr_kernel_core::ExpectedValueShape;
use gandr_kernel_core::KernelError;
use gandr_kernel_core::NonInferableForm;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::Component;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Summand;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

/// A definition the kernel refuses, with the refusal it is refused by.
struct Refusal
{
    /// The definition, `body : declared`.
    what: &'static str,
    /// Builds the declared type and the body.
    build: fn(&mut TermArena) -> (ValueTypeId, ValueId),
    /// Whether an error is the refusal this definition names.
    refused: fn(&KernelError) -> bool,
}

/// The label `name`.
///
/// # Specification
/// trivial.
fn label(name: &Name) -> FieldLabel
{
    FieldLabel::from(String::from(name.0))
}

/// A field label's spelling.
#[repr(transparent)]
struct Name(&'static str);

/// The record `#{fields}`, each field at its label.
///
/// # Specification
/// trivial.
fn record<const N: usize>(
    arena: &mut TermArena,
    fields: [(&Name, ValueId); N],
) -> ValueId
{
    arena.value_record(
        fields
            .into_iter()
            .map(|(name, value)| (label(name), value))
            .collect(),
    )
}

/// The record type `#{fields}`, each field at its label.
///
/// # Specification
/// trivial.
fn record_type<const N: usize>(
    arena: &mut TermArena,
    fields: [(&Name, ValueTypeId); N],
) -> ValueTypeId
{
    arena.value_type_record(
        fields
            .into_iter()
            .map(|(name, ty)| (label(name), ty))
            .collect::<BTreeMap<_, _>>(),
    )
}

/// `U(domain → F 1)`.
///
/// # Specification
/// trivial.
fn consumer_of(
    arena: &mut TermArena,
    domain: ValueTypeId,
) -> ValueTypeId
{
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit);
    let arrow = arena.comp_type_arrow(domain, returns);
    arena.value_type_thunk(arrow)
}

/// Admit `body : declared` in a fresh environment.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The kernel's refusal of the definition.
fn admitted(build: fn(&mut TermArena) -> (ValueTypeId, ValueId)) -> Result<CheckedId, KernelError>
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let (declared, body) = build(staging.arena());
    let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
    environment.add_decl(declaration)
}

/// The definitions, one per refusal.
///
/// # Specification
/// trivial.
fn refusals() -> Vec<Refusal>
{
    Vec::from([
        Refusal {
            what: "#{x = ()} : Integer",
            build: |a| {
                let unit = a.value_unit();
                let body = record(a, [(&Name("x"), unit)]);
                (a.value_type_base(BaseType::Integer), body)
            },
            refused: |error| {
                matches!(error, KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Record,
                    ..
                })
            },
        },
        Refusal {
            what: "#{x = ()} : #{x : 1, y : 1}",
            build: |a| {
                let unit = a.value_unit();
                let body = record(a, [(&Name("x"), unit)]);
                let one = a.value_type_unit();
                (record_type(a, [(&Name("x"), one), (&Name("y"), one)]), body)
            },
            refused: |error| {
                *error
                    == KernelError::AbsentRecordField {
                        label: label(&Name("y")),
                    }
            },
        },
        Refusal {
            what: "#{x = (), y = nil} : #{x : 1}",
            build: |a| {
                let unit = a.value_unit();
                let nil = a.value_list_nil();
                let body = record(a, [(&Name("x"), unit), (&Name("y"), nil)]);
                let one = a.value_type_unit();
                (record_type(a, [(&Name("x"), one)]), body)
            },
            refused: |error| {
                *error
                    == KernelError::NotInferable {
                        form: NonInferableForm::List,
                    }
            },
        },
        Refusal {
            what: "#{x = (), y = inl ()} : #{x : 1}",
            build: |a| {
                let unit = a.value_unit();
                let left = a.value_injection(Summand::from(0_usize), unit);
                let body = record(a, [(&Name("x"), unit), (&Name("y"), left)]);
                let one = a.value_type_unit();
                (record_type(a, [(&Name("x"), one)]), body)
            },
            refused: |error| {
                *error
                    == KernelError::NotInferable {
                        form: NonInferableForm::Injection,
                    }
            },
        },
        Refusal {
            what: "() :: nil : Integer",
            build: |a| {
                let unit = a.value_unit();
                let nil = a.value_list_nil();
                let body = a.value_list_cons(unit, nil);
                (a.value_type_base(BaseType::Integer), body)
            },
            refused: |error| {
                matches!(error, KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::List,
                    ..
                })
            },
        },
        Refusal {
            what: "thunk (return ()) : Integer",
            build: |a| {
                let unit = a.value_unit();
                let returned = a.computation_return(unit);
                let body = a.value_thunk(returned);
                (a.value_type_base(BaseType::Integer), body)
            },
            refused: |error| {
                matches!(error, KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Thunk,
                    ..
                })
            },
        },
        Refusal {
            what: "thunk (return ()) : U(1 → F 1)",
            build: |a| {
                let unit = a.value_unit();
                let returned = a.computation_return(unit);
                let body = a.value_thunk(returned);
                let one = a.value_type_unit();
                (consumer_of(a, one), body)
            },
            refused: |error| {
                matches!(error, KernelError::ComputationShapeMismatch {
                    expected: ExpectedComputationShape::Returner,
                    ..
                })
            },
        },
        Refusal {
            what: "thunk (x <- λy. return (); return ()) : U(F 1)",
            build: |a| {
                let unit = a.value_unit();
                let inner = a.computation_return(unit);
                let lambda = a.computation_lambda(inner);
                let after = a.computation_return(unit);
                let bound = a.computation_bind(lambda, after);
                let body = a.value_thunk(bound);
                let one = a.value_type_unit();
                let returns = a.comp_type_returner(one);
                (a.value_type_thunk(returns), body)
            },
            refused: |error| {
                *error
                    == KernelError::NotInferable {
                        form: NonInferableForm::Lambda,
                    }
            },
        },
        Refusal {
            what: "thunk (x <- case nil of { nil ↦ return (); _ :: _ ↦ return () }; return ()) : U(F 1)",
            build: |a| {
                let unit = a.value_unit();
                let nil = a.value_list_nil();
                let on_nil = a.computation_return(unit);
                let on_cons = a.computation_return(unit);
                let case = a.computation_list_case(nil, on_nil, on_cons);
                let after = a.computation_return(unit);
                let bound = a.computation_bind(case, after);
                let body = a.value_thunk(bound);
                let one = a.value_type_unit();
                let returns = a.comp_type_returner(one);
                (a.value_type_thunk(returns), body)
            },
            refused: |error| {
                *error
                    == KernelError::NotInferable {
                        form: NonInferableForm::ListCase,
                    }
            },
        },
        Refusal {
            what: "thunk (λx. x.a) : U(Integer → F 1)",
            build: |a| {
                let x = a.value_variable(DeBruijnIndex::from(0));
                let projected = a.computation_record_projection(x, label(&Name("a")));
                let lambda = a.computation_lambda(projected);
                let body = a.value_thunk(lambda);
                let integer = a.value_type_base(BaseType::Integer);
                (consumer_of(a, integer), body)
            },
            refused: |error| {
                matches!(error, KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Record,
                    ..
                })
            },
        },
        Refusal {
            what: "thunk (λx. x.2) : U(Σ(_ : 1). 1 → F 1)",
            build: |a| {
                let x = a.value_variable(DeBruijnIndex::from(0));
                let projected = a.computation_tuple_projection(x, Component::from(2_usize));
                let lambda = a.computation_lambda(projected);
                let body = a.value_thunk(lambda);
                let one = a.value_type_unit();
                let pair = a.value_type_sigma(one, one);
                (consumer_of(a, pair), body)
            },
            refused: |error| {
                *error
                    == KernelError::AbsentTupleComponent {
                        component: Component::from(2_usize),
                    }
            },
        },
        Refusal {
            what: "thunk (λx. split x as (_, _) in return ()) : U(Integer → F 1)",
            build: |a| {
                let x = a.value_variable(DeBruijnIndex::from(0));
                let unit = a.value_unit();
                let returned = a.computation_return(unit);
                let one = a.value_type_unit();
                let motive = a.comp_type_returner(one);
                let split = a.computation_sigma_split(x, motive, returned);
                let lambda = a.computation_lambda(split);
                let body = a.value_thunk(lambda);
                let integer = a.value_type_base(BaseType::Integer);
                (consumer_of(a, integer), body)
            },
            refused: |error| {
                matches!(error, KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::Sigma,
                    ..
                })
            },
        },
        Refusal {
            what: "thunk (λx. case x of { nil ↦ return (); _ :: _ ↦ return () }) : U(Integer → F 1)",
            build: |a| {
                let x = a.value_variable(DeBruijnIndex::from(0));
                let unit = a.value_unit();
                let on_nil = a.computation_return(unit);
                let on_cons = a.computation_return(unit);
                let case = a.computation_list_case(x, on_nil, on_cons);
                let lambda = a.computation_lambda(case);
                let body = a.value_thunk(lambda);
                let integer = a.value_type_base(BaseType::Integer);
                (consumer_of(a, integer), body)
            },
            refused: |error| {
                matches!(error, KernelError::ValueShapeMismatch {
                    expected: ExpectedValueShape::List,
                    ..
                })
            },
        },
    ])
}

/// Each definition is refused by the error naming its mismatch: a value of
/// the wrong introduction form for its type, a record missing a declared
/// field, a form no type is synthesized for where synthesis is asked, and an
/// eliminator applied to a value of another type.
#[test]
fn each_ill_shaped_definition_is_refused_by_its_mismatch()
{
    for Refusal {
        what,
        build,
        refused,
    } in refusals()
    {
        let verdict = admitted(build);
        assert!(verdict.as_ref().is_err_and(refused), "{what}: {verdict:?}");
    }
}

/// A definition the kernel admits.
struct Admission
{
    /// The definition, `body : declared`.
    what: &'static str,
    /// Builds the declared type and the body.
    build: fn(&mut TermArena) -> (ValueTypeId, ValueId),
}

/// The eliminators the refusals misapply, each at a value of the type it
/// eliminates, and a lifted value synthesized beside a record's declared
/// fields.
///
/// # Specification
/// trivial.
fn admissions() -> Vec<Admission>
{
    Vec::from([
        Admission {
            what: "thunk (λx. split x as (_, _) in return ()) : U(Σ(_ : 1). 1 → F 1)",
            build: |a| {
                let x = a.value_variable(DeBruijnIndex::from(0));
                let unit = a.value_unit();
                let returned = a.computation_return(unit);
                let one = a.value_type_unit();
                let motive = a.comp_type_returner(one);
                let split = a.computation_sigma_split(x, motive, returned);
                let lambda = a.computation_lambda(split);
                let body = a.value_thunk(lambda);
                let pair = a.value_type_sigma(one, one);
                (consumer_of(a, pair), body)
            },
        },
        Admission {
            what: "thunk (λx. case x of { nil ↦ return (); _ :: _ ↦ return () }) : U(List 1 → F 1)",
            build: |a| {
                let x = a.value_variable(DeBruijnIndex::from(0));
                let unit = a.value_unit();
                let on_nil = a.computation_return(unit);
                let on_cons = a.computation_return(unit);
                let case = a.computation_list_case(x, on_nil, on_cons);
                let lambda = a.computation_lambda(case);
                let body = a.value_thunk(lambda);
                let one = a.value_type_unit();
                let list = a.value_type_list(one);
                (consumer_of(a, list), body)
            },
        },
        Admission {
            what: "thunk (λx. x.1) : U(Σ(_ : 1). 1 → F 1)",
            build: |a| {
                let x = a.value_variable(DeBruijnIndex::from(0));
                let projected = a.computation_tuple_projection(x, Component::from(1_usize));
                let lambda = a.computation_lambda(projected);
                let body = a.value_thunk(lambda);
                let one = a.value_type_unit();
                let pair = a.value_type_sigma(one, one);
                (consumer_of(a, pair), body)
            },
        },
        Admission {
            what: "#{x = (), y = lift ()} : #{x : 1}",
            build: |a| {
                let unit = a.value_unit();
                let above = Level::zero().succ().expect("level one");
                let lifted = a.value_lift(above, unit);
                let body = record(a, [(&Name("x"), unit), (&Name("y"), lifted)]);
                let one = a.value_type_unit();
                (record_type(a, [(&Name("x"), one)]), body)
            },
        },
    ])
}

/// Each eliminator is admitted at a value of the type it eliminates: a split
/// of a dependent pair, a case on a list, the second projection of a pair,
/// and a lift synthesized where a record holds a field its type does not
/// declare.
#[test]
fn each_eliminator_is_admitted_at_the_type_it_eliminates()
{
    for Admission { what, build } in admissions() {
        let verdict = admitted(build);
        assert!(verdict.is_ok(), "{what}: {verdict:?}");
    }
}
