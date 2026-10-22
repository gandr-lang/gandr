//! Codes compared by the structural conversion walk and by the replay of a
//! one-step dialogue: a code built by a former over one variable converts
//! with a second copy of itself and stays apart from its twin over another.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_core::Convertibility;
use gandr_kernel_core::EngineClaim;
use gandr_kernel_core::KernelVerdict;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_core::ReplayDecline;
use gandr_kernel_core::ReplayNode;
use gandr_kernel_core::ReplayRefusal;
use gandr_kernel_core::ReplaySides;
use gandr_kernel_core::TracePosition;
use gandr_kernel_core::Unfoldings;
use gandr_kernel_core::convertible_value_types;
use gandr_kernel_core::replay;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

/// A code former, holding the leaf it is given.
struct Former
{
    /// The code, over the leaf `c`.
    what: &'static str,
    /// Whether the code is rigid, so a shared comparison of its twins
    /// refutes them; a suspended eliminator over a variable might yet
    /// reduce, and its twins are left undecided.
    rigid: bool,
    /// Builds the code over the leaf it is given.
    build: fn(&mut TermArena, ValueId) -> ValueId,
}

/// The decoded type `El code`, the code kept as written.
///
/// # Specification
/// trivial.
fn decoded(
    arena: &mut TermArena,
    code: ValueId,
) -> ValueTypeId
{
    arena.value_type_element(code, Level::zero())
}

/// `F 1`.
///
/// # Specification
/// trivial.
fn returns_unit(arena: &mut TermArena) -> gandr_kernel_term::CompTypeId
{
    let unit = arena.value_type_unit();
    arena.comp_type_returner(unit)
}

/// `thunk (return ())`.
///
/// # Specification
/// trivial.
fn done(arena: &mut TermArena) -> gandr_kernel_term::ComputationId
{
    let unit = arena.value_unit();
    arena.computation_return(unit)
}

/// The formers, each over the constant `c` at one leaf.
///
/// # Specification
/// trivial.
fn formers() -> Vec<Former>
{
    Vec::from([
        Former {
            what: "#{a = c}",
            rigid: true,
            build: |a, c| {
                a.value_record(BTreeMap::from([(FieldLabel::from(String::from("a")), c)]))
            },
        },
        Former {
            what: "c ⊗ c",
            rigid: true,
            build: |a, c| a.value_path_product(c, c),
        },
        Former {
            what: "c ⊗~ c",
            rigid: true,
            build: |a, c| a.value_flow_product(c, c),
        },
        Former {
            what: "c :: nil",
            rigid: true,
            build: |a, c| {
                let nil = a.value_list_nil();
                a.value_list_cons(c, nil)
            },
        },
        Former {
            what: "c c, statically applied",
            rigid: true,
            build: |a, c| a.value_static_application(c, c),
        },
        Former {
            what: "refl c",
            rigid: true,
            build: |a, c| a.value_path_refl(c),
        },
        Former {
            what: "here c",
            rigid: true,
            build: |a, c| a.value_here(c),
        },
        Former {
            what: "stay c",
            rigid: true,
            build: |a, c| a.value_stay(c),
        },
        Former {
            what: "⌜Path(1, c, c)⌝",
            rigid: true,
            build: |a, c| {
                let one = a.value_type_unit();
                let path = a.value_type_path(one, c, c);
                a.value_quote(path)
            },
        },
        Former {
            what: "⌜c = c⌝, a path universe",
            rigid: true,
            build: |a, c| {
                let universe = a.value_type_path_universe(c, c);
                a.value_quote(universe)
            },
        },
        Former {
            what: "⌜c ~> c⌝, a flow universe",
            rigid: true,
            build: |a, c| {
                let universe = a.value_type_flow_universe(c, c);
                a.value_quote(universe)
            },
        },
        Former {
            what: "⌜#{a : El c}⌝",
            rigid: true,
            build: |a, c| {
                let element = decoded(a, c);
                let record = a.value_type_record(BTreeMap::from([(
                    FieldLabel::from(String::from("a")),
                    element,
                )]));
                a.value_quote(record)
            },
        },
        Former {
            what: "⌜Σ(_ : El c). El c⌝",
            rigid: true,
            build: |a, c| {
                let element = decoded(a, c);
                let sigma = a.value_type_sigma(element, element);
                a.value_quote(sigma)
            },
        },
        Former {
            what: "⌜El c ⇒ El c⌝, a static function type",
            rigid: true,
            build: |a, c| {
                let element = decoded(a, c);
                let static_pi = a.value_type_static_pi(element, element);
                a.value_quote(static_pi)
            },
        },
        Former {
            what: "⌜List (El c)⌝",
            rigid: true,
            build: |a, c| {
                let element = decoded(a, c);
                let list = a.value_type_list(element);
                a.value_quote(list)
            },
        },
        Former {
            what: "⌜Lift (El c)⌝",
            rigid: true,
            build: |a, c| {
                let element = decoded(a, c);
                let above = Level::zero().succ().expect("level one");
                let lifted = a.value_type_lift(element, above);
                a.value_quote(lifted)
            },
        },
        Former {
            what: "⌜F (El c)⌝",
            rigid: true,
            build: |a, c| {
                let element = decoded(a, c);
                let returner = a.comp_type_returner(element);
                a.value_quote_computation(returner)
            },
        },
        Former {
            what: "thunk (case c of { () ↦ return () })",
            rigid: false,
            build: |a, c| {
                let arm = done(a);
                let motive = returns_unit(a);
                let case = a.computation_data_case(c, motive, Vec::from([arm]));
                a.value_thunk(case)
            },
        },
        Former {
            what: "thunk (split c as (_, _) in return ())",
            rigid: false,
            build: |a, c| {
                let body = done(a);
                let motive = returns_unit(a);
                let split = a.computation_sigma_split(c, motive, body);
                a.value_thunk(split)
            },
        },
        Former {
            what: "thunk (c.a)",
            rigid: false,
            build: |a, c| {
                let projected =
                    a.computation_record_projection(c, FieldLabel::from(String::from("a")));
                a.value_thunk(projected)
            },
        },
        Former {
            what: "thunk (c.0)",
            rigid: false,
            build: |a, c| {
                let projected = a.computation_tuple_projection(c, Component::from(0_usize));
                a.value_thunk(projected)
            },
        },
        Former {
            what: "thunk (fold c { nil ↦ return (); _ :: _ ↦ return () })",
            rigid: false,
            build: |a, c| {
                let (on_nil, on_cons) = (done(a), done(a));
                let one = a.value_type_unit();
                let fold = a.computation_list_fold(one, one, c, on_nil, on_cons);
                a.value_thunk(fold)
            },
        },
        Former {
            what: "thunk (case c of { nil ↦ return (); _ :: _ ↦ return () })",
            rigid: false,
            build: |a, c| {
                let (on_nil, on_cons) = (done(a), done(a));
                let case = a.computation_list_case(c, on_nil, on_cons);
                a.value_thunk(case)
            },
        },
        Former {
            what: "thunk (transport (y. 1) along c of ())",
            rigid: false,
            build: |a, c| {
                let one = a.value_type_unit();
                let unit = a.value_unit();
                let transported = a.computation_path_transport(one, c, unit);
                a.value_thunk(transported)
            },
        },
        Former {
            what: "thunk (ride (y. 1) c ())",
            rigid: false,
            build: |a, c| {
                let one = a.value_type_unit();
                let unit = a.value_unit();
                let ridden = a.computation_ride(one, c, unit);
                a.value_thunk(ridden)
            },
        },
        Former {
            what: "thunk (transport (F 1) along c from () over () of ())",
            rigid: false,
            build: |a, c| {
                let motive = returns_unit(a);
                let unit = a.value_unit();
                let transported = a.computation_telescope_transport(motive, c, unit, unit, unit);
                a.value_thunk(transported)
            },
        },
        Former {
            what: "thunk (ride (F 1) c from () over () of ())",
            rigid: false,
            build: |a, c| {
                let motive = returns_unit(a);
                let unit = a.value_unit();
                let ridden = a.computation_telescope_ride(motive, c, unit, unit, unit);
                a.value_thunk(ridden)
            },
        },
        Former {
            what: "thunk (apply c at ((), ()) by () in return ())",
            rigid: false,
            build: |a, c| {
                let unit = a.value_unit();
                let body = done(a);
                let applied = a.computation_related_application(c, (unit, unit), unit, body);
                a.value_thunk(applied)
            },
        },
        Former {
            what: "thunk (fix rec. case c of { () ↦ return () })",
            rigid: false,
            build: |a, c| {
                let arm = done(a);
                let case = a.computation_case(c, &[arm]);
                let fixpoint = a.computation_fixpoint(case, FixpointEvidence::Partial);
                a.value_thunk(fixpoint)
            },
        },
        Former {
            what: "thunk ⟨case c of { () ↦ return () }, return ()⟩",
            rigid: false,
            build: |a, c| {
                let arm = done(a);
                let case = a.computation_case(c, &[arm]);
                let other = done(a);
                let with = a.computation_with(&[case, other]);
                a.value_thunk(with)
            },
        },
        Former {
            what: "thunk (⟨case c of { () ↦ return () }⟩.0)",
            rigid: false,
            build: |a, c| {
                let arm = done(a);
                let case = a.computation_case(c, &[arm]);
                let with = a.computation_with(&[case]);
                let projected = a.computation_project(Component::from(0_usize), with);
                a.value_thunk(projected)
            },
        },
        Former {
            what: "ua c",
            rigid: true,
            build: |a, c| a.value_univalence(c),
        },
        Former {
            what: "a function flow from c to c",
            rigid: true,
            build: |a, c| {
                let one = a.value_type_unit();
                let unit = a.value_unit();
                let flow = a.value_type_flow(one, unit, unit);
                a.value_function_flow(flow, c, c)
            },
        },
    ])
}

/// Each former's code over `c` converts with a second copy of itself, built
/// at fresh ids, and is apart from its twin over `d`: the walk descends into
/// every child the former holds.
#[test]
fn each_code_former_converts_with_its_copy_and_not_with_its_twin()
{
    for Former { what, build, .. } in formers() {
        let mut arena = TermArena::new();
        let c = arena.value_constant(ConstantIndex::from(0_usize));
        let d = arena.value_constant(ConstantIndex::from(1_usize));
        let [one, copy, twin] = [c, c, d].map(|leaf| {
            let code = build(&mut arena, leaf);
            decoded(&mut arena, code)
        });
        assert_eq!(
            Convertibility::Convertible,
            convertible_value_types(&arena, one, copy),
            "{what}: copies"
        );
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, one, twin),
            "{what}: twins"
        );
    }
}

/// The replay of a dialogue that compares two values as shared and stops
/// agrees with the structural walk on every former: copies replay
/// convertible. Twins over another variable replay not convertible where
/// the code is rigid; where a suspended eliminator might yet reduce, the
/// shared comparison is no refutation and the replay declines it as
/// inapplicable.
#[test]
fn each_code_former_replays_as_the_walk_decides()
{
    let unfoldings = Unfoldings::new(Vec::new());
    let shared = [ConversionDecision::ComparedShared {
        left: ReplayNode::Other,
        right: ReplayNode::Other,
    }];
    let inapplicable =
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0_usize),
        }));
    for Former { what, rigid, build } in formers() {
        let mut arena = TermArena::new();
        let x = arena.value_variable(DeBruijnIndex::from(0_u32));
        let y = arena.value_variable(DeBruijnIndex::from(1_u32));
        let [one, copy, twin] = [x, x, y].map(|leaf| build(&mut arena, leaf));
        let apart = if rigid {
            KernelVerdict::NotConvertible
        }
        else {
            inapplicable
        };
        for (other, claim, verdict) in [
            (copy, EngineClaim::Convertible, KernelVerdict::Convertible),
            (twin, EngineClaim::NotConvertible, apart),
        ] {
            assert_eq!(
                verdict,
                replay(
                    &mut arena,
                    &unfoldings,
                    ReplaySides::Values(one, other),
                    claim,
                    shared.iter().copied(),
                    ReplayBudget::from(256),
                ),
                "{what}"
            );
        }
    }
}
